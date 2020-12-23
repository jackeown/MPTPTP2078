%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:55 EST 2020

% Result     : Theorem 11.41s
% Output     : CNFRefutation 11.55s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 460 expanded)
%              Number of leaves         :   35 ( 165 expanded)
%              Depth                    :   14
%              Number of atoms          :  290 (1253 expanded)
%              Number of equality atoms :  108 ( 448 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_43,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ~ ( ~ ( A = k1_xboole_0
            & B != k1_xboole_0 )
        & ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ~ ( B = k1_relat_1(C)
                & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_82,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_78,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_21510,plain,(
    ! [C_4141,A_4142,B_4143] :
      ( m1_subset_1(C_4141,k1_zfmisc_1(k2_zfmisc_1(A_4142,B_4143)))
      | ~ r1_tarski(k2_relat_1(C_4141),B_4143)
      | ~ r1_tarski(k1_relat_1(C_4141),A_4142)
      | ~ v1_relat_1(C_4141) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_80,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_76,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'),'#skF_7')))
    | ~ v1_funct_2('#skF_8',k1_relat_1('#skF_8'),'#skF_7')
    | ~ v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_84,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'),'#skF_7')))
    | ~ v1_funct_2('#skF_8',k1_relat_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76])).

tff(c_98,plain,(
    ~ v1_funct_2('#skF_8',k1_relat_1('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_659,plain,(
    ! [C_160,A_161,B_162] :
      ( m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162)))
      | ~ r1_tarski(k2_relat_1(C_160),B_162)
      | ~ r1_tarski(k1_relat_1(C_160),A_161)
      | ~ v1_relat_1(C_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_60,plain,(
    ! [A_55,B_56,C_57] :
      ( k1_relset_1(A_55,B_56,C_57) = k1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_710,plain,(
    ! [A_166,B_167,C_168] :
      ( k1_relset_1(A_166,B_167,C_168) = k1_relat_1(C_168)
      | ~ r1_tarski(k2_relat_1(C_168),B_167)
      | ~ r1_tarski(k1_relat_1(C_168),A_166)
      | ~ v1_relat_1(C_168) ) ),
    inference(resolution,[status(thm)],[c_659,c_60])).

tff(c_716,plain,(
    ! [A_166] :
      ( k1_relset_1(A_166,'#skF_7','#skF_8') = k1_relat_1('#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_8'),A_166)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_78,c_710])).

tff(c_742,plain,(
    ! [A_174] :
      ( k1_relset_1(A_174,'#skF_7','#skF_8') = k1_relat_1('#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_8'),A_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_716])).

tff(c_747,plain,(
    k1_relset_1(k1_relat_1('#skF_8'),'#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_12,c_742])).

tff(c_62,plain,(
    ! [C_60,A_58,B_59] :
      ( m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ r1_tarski(k2_relat_1(C_60),B_59)
      | ~ r1_tarski(k1_relat_1(C_60),A_58)
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_730,plain,(
    ! [B_169,C_170,A_171] :
      ( k1_xboole_0 = B_169
      | v1_funct_2(C_170,A_171,B_169)
      | k1_relset_1(A_171,B_169,C_170) != A_171
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_171,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_7257,plain,(
    ! [B_445,C_446,A_447] :
      ( k1_xboole_0 = B_445
      | v1_funct_2(C_446,A_447,B_445)
      | k1_relset_1(A_447,B_445,C_446) != A_447
      | ~ r1_tarski(k2_relat_1(C_446),B_445)
      | ~ r1_tarski(k1_relat_1(C_446),A_447)
      | ~ v1_relat_1(C_446) ) ),
    inference(resolution,[status(thm)],[c_62,c_730])).

tff(c_7291,plain,(
    ! [A_447] :
      ( k1_xboole_0 = '#skF_7'
      | v1_funct_2('#skF_8',A_447,'#skF_7')
      | k1_relset_1(A_447,'#skF_7','#skF_8') != A_447
      | ~ r1_tarski(k1_relat_1('#skF_8'),A_447)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_78,c_7257])).

tff(c_7317,plain,(
    ! [A_447] :
      ( k1_xboole_0 = '#skF_7'
      | v1_funct_2('#skF_8',A_447,'#skF_7')
      | k1_relset_1(A_447,'#skF_7','#skF_8') != A_447
      | ~ r1_tarski(k1_relat_1('#skF_8'),A_447) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_7291])).

tff(c_7475,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_7317])).

tff(c_110,plain,(
    ! [A_76] :
      ( k2_relat_1(A_76) != k1_xboole_0
      | k1_xboole_0 = A_76
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_122,plain,
    ( k2_relat_1('#skF_8') != k1_xboole_0
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_82,c_110])).

tff(c_123,plain,(
    k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_16,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    ! [A_50,B_51] :
      ( k1_xboole_0 = A_50
      | k1_relat_1('#skF_6'(A_50,B_51)) = B_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_56,plain,(
    ! [A_50,B_51] :
      ( k1_xboole_0 = A_50
      | v1_relat_1('#skF_6'(A_50,B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_124,plain,(
    ! [A_77] :
      ( k1_relat_1(A_77) != k1_xboole_0
      | k1_xboole_0 = A_77
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_270,plain,(
    ! [A_101,B_102] :
      ( k1_relat_1('#skF_6'(A_101,B_102)) != k1_xboole_0
      | '#skF_6'(A_101,B_102) = k1_xboole_0
      | k1_xboole_0 = A_101 ) ),
    inference(resolution,[status(thm)],[c_56,c_124])).

tff(c_282,plain,(
    ! [B_103,A_104] :
      ( k1_xboole_0 != B_103
      | '#skF_6'(A_104,B_103) = k1_xboole_0
      | k1_xboole_0 = A_104
      | k1_xboole_0 = A_104 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_270])).

tff(c_134,plain,(
    ! [A_50,B_51] :
      ( k1_relat_1('#skF_6'(A_50,B_51)) != k1_xboole_0
      | '#skF_6'(A_50,B_51) = k1_xboole_0
      | k1_xboole_0 = A_50 ) ),
    inference(resolution,[status(thm)],[c_56,c_124])).

tff(c_288,plain,(
    ! [A_104,B_103] :
      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
      | '#skF_6'(A_104,B_103) = k1_xboole_0
      | k1_xboole_0 = A_104
      | k1_xboole_0 != B_103
      | k1_xboole_0 = A_104
      | k1_xboole_0 = A_104 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_134])).

tff(c_313,plain,(
    ! [A_104,B_103] :
      ( '#skF_6'(A_104,B_103) = k1_xboole_0
      | k1_xboole_0 != B_103
      | k1_xboole_0 = A_104 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_288])).

tff(c_44,plain,(
    ! [A_50,B_51] :
      ( k1_xboole_0 = A_50
      | r1_tarski(k2_relat_1('#skF_6'(A_50,B_51)),A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_243,plain,(
    ! [C_90,B_91,A_92] :
      ( r2_hidden(C_90,B_91)
      | ~ r2_hidden(C_90,A_92)
      | ~ r1_tarski(A_92,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_256,plain,(
    ! [A_95,B_96,B_97] :
      ( r2_hidden('#skF_1'(A_95,B_96),B_97)
      | ~ r1_tarski(A_95,B_97)
      | r1_tarski(A_95,B_96) ) ),
    inference(resolution,[status(thm)],[c_6,c_243])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_470,plain,(
    ! [A_125,B_126,B_127,B_128] :
      ( r2_hidden('#skF_1'(A_125,B_126),B_127)
      | ~ r1_tarski(B_128,B_127)
      | ~ r1_tarski(A_125,B_128)
      | r1_tarski(A_125,B_126) ) ),
    inference(resolution,[status(thm)],[c_256,c_2])).

tff(c_484,plain,(
    ! [A_131,B_132] :
      ( r2_hidden('#skF_1'(A_131,B_132),'#skF_7')
      | ~ r1_tarski(A_131,k2_relat_1('#skF_8'))
      | r1_tarski(A_131,B_132) ) ),
    inference(resolution,[status(thm)],[c_78,c_470])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_497,plain,(
    ! [A_133] :
      ( ~ r1_tarski(A_133,k2_relat_1('#skF_8'))
      | r1_tarski(A_133,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_484,c_4])).

tff(c_501,plain,(
    ! [B_51] :
      ( r1_tarski(k2_relat_1('#skF_6'(k2_relat_1('#skF_8'),B_51)),'#skF_7')
      | k2_relat_1('#skF_8') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_497])).

tff(c_517,plain,(
    ! [B_134] : r1_tarski(k2_relat_1('#skF_6'(k2_relat_1('#skF_8'),B_134)),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_501])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_535,plain,(
    ! [B_137] :
      ( k2_relat_1('#skF_6'(k2_relat_1('#skF_8'),B_137)) = '#skF_7'
      | ~ r1_tarski('#skF_7',k2_relat_1('#skF_6'(k2_relat_1('#skF_8'),B_137))) ) ),
    inference(resolution,[status(thm)],[c_517,c_8])).

tff(c_539,plain,(
    ! [B_103] :
      ( k2_relat_1('#skF_6'(k2_relat_1('#skF_8'),B_103)) = '#skF_7'
      | ~ r1_tarski('#skF_7',k2_relat_1(k1_xboole_0))
      | k1_xboole_0 != B_103
      | k2_relat_1('#skF_8') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_535])).

tff(c_544,plain,(
    ! [B_103] :
      ( k2_relat_1('#skF_6'(k2_relat_1('#skF_8'),B_103)) = '#skF_7'
      | ~ r1_tarski('#skF_7',k1_xboole_0)
      | k1_xboole_0 != B_103
      | k2_relat_1('#skF_8') = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_539])).

tff(c_545,plain,(
    ! [B_103] :
      ( k2_relat_1('#skF_6'(k2_relat_1('#skF_8'),B_103)) = '#skF_7'
      | ~ r1_tarski('#skF_7',k1_xboole_0)
      | k1_xboole_0 != B_103 ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_544])).

tff(c_547,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_545])).

tff(c_7582,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7475,c_547])).

tff(c_7608,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_7582])).

tff(c_7611,plain,(
    ! [A_454] :
      ( v1_funct_2('#skF_8',A_454,'#skF_7')
      | k1_relset_1(A_454,'#skF_7','#skF_8') != A_454
      | ~ r1_tarski(k1_relat_1('#skF_8'),A_454) ) ),
    inference(splitRight,[status(thm)],[c_7317])).

tff(c_7615,plain,
    ( v1_funct_2('#skF_8',k1_relat_1('#skF_8'),'#skF_7')
    | k1_relset_1(k1_relat_1('#skF_8'),'#skF_7','#skF_8') != k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_12,c_7611])).

tff(c_7618,plain,(
    v1_funct_2('#skF_8',k1_relat_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_747,c_7615])).

tff(c_7620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_7618])).

tff(c_7622,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_545])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_58,plain,(
    ! [B_54,A_53] :
      ( ~ r1_tarski(B_54,A_53)
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_377,plain,(
    ! [B_109,A_110,B_111] :
      ( ~ r1_tarski(B_109,'#skF_1'(A_110,B_111))
      | ~ r1_tarski(A_110,B_109)
      | r1_tarski(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_256,c_58])).

tff(c_392,plain,(
    ! [A_110,B_111] :
      ( ~ r1_tarski(A_110,k1_xboole_0)
      | r1_tarski(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_14,c_377])).

tff(c_7635,plain,(
    ! [B_111] : r1_tarski('#skF_7',B_111) ),
    inference(resolution,[status(thm)],[c_7622,c_392])).

tff(c_200,plain,(
    ! [B_85,A_86] :
      ( B_85 = A_86
      | ~ r1_tarski(B_85,A_86)
      | ~ r1_tarski(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_210,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_78,c_200])).

tff(c_235,plain,(
    ~ r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_7694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7635,c_235])).

tff(c_7695,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_7697,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7695,c_123])).

tff(c_8046,plain,(
    ! [C_520,A_521,B_522] :
      ( m1_subset_1(C_520,k1_zfmisc_1(k2_zfmisc_1(A_521,B_522)))
      | ~ r1_tarski(k2_relat_1(C_520),B_522)
      | ~ r1_tarski(k1_relat_1(C_520),A_521)
      | ~ v1_relat_1(C_520) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_8253,plain,(
    ! [A_541,B_542,C_543] :
      ( k1_relset_1(A_541,B_542,C_543) = k1_relat_1(C_543)
      | ~ r1_tarski(k2_relat_1(C_543),B_542)
      | ~ r1_tarski(k1_relat_1(C_543),A_541)
      | ~ v1_relat_1(C_543) ) ),
    inference(resolution,[status(thm)],[c_8046,c_60])).

tff(c_8276,plain,(
    ! [A_546,C_547] :
      ( k1_relset_1(A_546,k2_relat_1(C_547),C_547) = k1_relat_1(C_547)
      | ~ r1_tarski(k1_relat_1(C_547),A_546)
      | ~ v1_relat_1(C_547) ) ),
    inference(resolution,[status(thm)],[c_12,c_8253])).

tff(c_8292,plain,(
    ! [C_550] :
      ( k1_relset_1(k1_relat_1(C_550),k2_relat_1(C_550),C_550) = k1_relat_1(C_550)
      | ~ v1_relat_1(C_550) ) ),
    inference(resolution,[status(thm)],[c_12,c_8276])).

tff(c_8309,plain,
    ( k1_relset_1(k1_relat_1('#skF_8'),'#skF_7','#skF_8') = k1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_7695,c_8292])).

tff(c_8326,plain,(
    k1_relset_1(k1_relat_1('#skF_8'),'#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_8309])).

tff(c_8396,plain,(
    ! [B_559,C_560,A_561] :
      ( k1_xboole_0 = B_559
      | v1_funct_2(C_560,A_561,B_559)
      | k1_relset_1(A_561,B_559,C_560) != A_561
      | ~ m1_subset_1(C_560,k1_zfmisc_1(k2_zfmisc_1(A_561,B_559))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_13076,plain,(
    ! [B_789,C_790,A_791] :
      ( k1_xboole_0 = B_789
      | v1_funct_2(C_790,A_791,B_789)
      | k1_relset_1(A_791,B_789,C_790) != A_791
      | ~ r1_tarski(k2_relat_1(C_790),B_789)
      | ~ r1_tarski(k1_relat_1(C_790),A_791)
      | ~ v1_relat_1(C_790) ) ),
    inference(resolution,[status(thm)],[c_62,c_8396])).

tff(c_13092,plain,(
    ! [B_789,A_791] :
      ( k1_xboole_0 = B_789
      | v1_funct_2('#skF_8',A_791,B_789)
      | k1_relset_1(A_791,B_789,'#skF_8') != A_791
      | ~ r1_tarski('#skF_7',B_789)
      | ~ r1_tarski(k1_relat_1('#skF_8'),A_791)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7695,c_13076])).

tff(c_13141,plain,(
    ! [B_796,A_797] :
      ( k1_xboole_0 = B_796
      | v1_funct_2('#skF_8',A_797,B_796)
      | k1_relset_1(A_797,B_796,'#skF_8') != A_797
      | ~ r1_tarski('#skF_7',B_796)
      | ~ r1_tarski(k1_relat_1('#skF_8'),A_797) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_13092])).

tff(c_13147,plain,(
    ! [B_798] :
      ( k1_xboole_0 = B_798
      | v1_funct_2('#skF_8',k1_relat_1('#skF_8'),B_798)
      | k1_relset_1(k1_relat_1('#skF_8'),B_798,'#skF_8') != k1_relat_1('#skF_8')
      | ~ r1_tarski('#skF_7',B_798) ) ),
    inference(resolution,[status(thm)],[c_12,c_13141])).

tff(c_13152,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1(k1_relat_1('#skF_8'),'#skF_7','#skF_8') != k1_relat_1('#skF_8')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_13147,c_98])).

tff(c_13158,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8326,c_13152])).

tff(c_13160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7697,c_13158])).

tff(c_13161,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_13170,plain,(
    ! [A_8] : r1_tarski('#skF_8',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13161,c_14])).

tff(c_13172,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13161,c_13161,c_18])).

tff(c_13162,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_13177,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13161,c_13162])).

tff(c_13673,plain,(
    ! [C_869,A_870,B_871] :
      ( m1_subset_1(C_869,k1_zfmisc_1(k2_zfmisc_1(A_870,B_871)))
      | ~ r1_tarski(k2_relat_1(C_869),B_871)
      | ~ r1_tarski(k1_relat_1(C_869),A_870)
      | ~ v1_relat_1(C_869) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_13744,plain,(
    ! [A_877,B_878,C_879] :
      ( k1_relset_1(A_877,B_878,C_879) = k1_relat_1(C_879)
      | ~ r1_tarski(k2_relat_1(C_879),B_878)
      | ~ r1_tarski(k1_relat_1(C_879),A_877)
      | ~ v1_relat_1(C_879) ) ),
    inference(resolution,[status(thm)],[c_13673,c_60])).

tff(c_13748,plain,(
    ! [A_877,B_878] :
      ( k1_relset_1(A_877,B_878,'#skF_8') = k1_relat_1('#skF_8')
      | ~ r1_tarski('#skF_8',B_878)
      | ~ r1_tarski(k1_relat_1('#skF_8'),A_877)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13177,c_13744])).

tff(c_13754,plain,(
    ! [A_877,B_878] : k1_relset_1(A_877,B_878,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_13170,c_13172,c_13170,c_13172,c_13748])).

tff(c_68,plain,(
    ! [C_63,B_62] :
      ( v1_funct_2(C_63,k1_xboole_0,B_62)
      | k1_relset_1(k1_xboole_0,B_62,C_63) != k1_xboole_0
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_13643,plain,(
    ! [C_63,B_62] :
      ( v1_funct_2(C_63,'#skF_8',B_62)
      | k1_relset_1('#skF_8',B_62,C_63) != '#skF_8'
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1('#skF_8',B_62))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13161,c_13161,c_13161,c_13161,c_68])).

tff(c_20911,plain,(
    ! [C_4051,B_4052] :
      ( v1_funct_2(C_4051,'#skF_8',B_4052)
      | k1_relset_1('#skF_8',B_4052,C_4051) != '#skF_8'
      | ~ r1_tarski(k2_relat_1(C_4051),B_4052)
      | ~ r1_tarski(k1_relat_1(C_4051),'#skF_8')
      | ~ v1_relat_1(C_4051) ) ),
    inference(resolution,[status(thm)],[c_13673,c_13643])).

tff(c_20944,plain,(
    ! [B_4052] :
      ( v1_funct_2('#skF_8','#skF_8',B_4052)
      | k1_relset_1('#skF_8',B_4052,'#skF_8') != '#skF_8'
      | ~ r1_tarski('#skF_8',B_4052)
      | ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13177,c_20911])).

tff(c_20962,plain,(
    ! [B_4052] : v1_funct_2('#skF_8','#skF_8',B_4052) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_13170,c_13172,c_13170,c_13754,c_20944])).

tff(c_13193,plain,(
    ~ v1_funct_2('#skF_8','#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13172,c_98])).

tff(c_20966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20962,c_13193])).

tff(c_20967,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_21532,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7')
    | ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_21510,c_20967])).

tff(c_21543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_12,c_78,c_21532])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:41:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.41/4.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.41/4.41  
% 11.41/4.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.41/4.41  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 11.41/4.41  
% 11.41/4.41  %Foreground sorts:
% 11.41/4.41  
% 11.41/4.41  
% 11.41/4.41  %Background operators:
% 11.41/4.41  
% 11.41/4.41  
% 11.41/4.41  %Foreground operators:
% 11.41/4.41  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 11.41/4.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.41/4.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.41/4.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.41/4.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.41/4.41  tff('#skF_7', type, '#skF_7': $i).
% 11.41/4.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.41/4.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.41/4.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.41/4.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.41/4.41  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.41/4.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.41/4.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.41/4.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.41/4.41  tff('#skF_8', type, '#skF_8': $i).
% 11.41/4.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.41/4.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.41/4.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.41/4.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.41/4.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.41/4.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.41/4.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.41/4.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.41/4.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.41/4.41  
% 11.55/4.44  tff(f_131, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 11.55/4.44  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.55/4.44  tff(f_100, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 11.55/4.44  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.55/4.44  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.55/4.44  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 11.55/4.44  tff(f_43, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 11.55/4.44  tff(f_83, axiom, (![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 11.55/4.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.55/4.44  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.55/4.44  tff(f_88, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 11.55/4.44  tff(c_82, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_131])).
% 11.55/4.44  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.55/4.44  tff(c_78, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_131])).
% 11.55/4.44  tff(c_21510, plain, (![C_4141, A_4142, B_4143]: (m1_subset_1(C_4141, k1_zfmisc_1(k2_zfmisc_1(A_4142, B_4143))) | ~r1_tarski(k2_relat_1(C_4141), B_4143) | ~r1_tarski(k1_relat_1(C_4141), A_4142) | ~v1_relat_1(C_4141))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.55/4.44  tff(c_80, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_131])).
% 11.55/4.44  tff(c_76, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'), '#skF_7'))) | ~v1_funct_2('#skF_8', k1_relat_1('#skF_8'), '#skF_7') | ~v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_131])).
% 11.55/4.44  tff(c_84, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'), '#skF_7'))) | ~v1_funct_2('#skF_8', k1_relat_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76])).
% 11.55/4.44  tff(c_98, plain, (~v1_funct_2('#skF_8', k1_relat_1('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_84])).
% 11.55/4.44  tff(c_659, plain, (![C_160, A_161, B_162]: (m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))) | ~r1_tarski(k2_relat_1(C_160), B_162) | ~r1_tarski(k1_relat_1(C_160), A_161) | ~v1_relat_1(C_160))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.55/4.44  tff(c_60, plain, (![A_55, B_56, C_57]: (k1_relset_1(A_55, B_56, C_57)=k1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.55/4.44  tff(c_710, plain, (![A_166, B_167, C_168]: (k1_relset_1(A_166, B_167, C_168)=k1_relat_1(C_168) | ~r1_tarski(k2_relat_1(C_168), B_167) | ~r1_tarski(k1_relat_1(C_168), A_166) | ~v1_relat_1(C_168))), inference(resolution, [status(thm)], [c_659, c_60])).
% 11.55/4.44  tff(c_716, plain, (![A_166]: (k1_relset_1(A_166, '#skF_7', '#skF_8')=k1_relat_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_8'), A_166) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_78, c_710])).
% 11.55/4.44  tff(c_742, plain, (![A_174]: (k1_relset_1(A_174, '#skF_7', '#skF_8')=k1_relat_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_8'), A_174))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_716])).
% 11.55/4.44  tff(c_747, plain, (k1_relset_1(k1_relat_1('#skF_8'), '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_12, c_742])).
% 11.55/4.44  tff(c_62, plain, (![C_60, A_58, B_59]: (m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~r1_tarski(k2_relat_1(C_60), B_59) | ~r1_tarski(k1_relat_1(C_60), A_58) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.55/4.44  tff(c_730, plain, (![B_169, C_170, A_171]: (k1_xboole_0=B_169 | v1_funct_2(C_170, A_171, B_169) | k1_relset_1(A_171, B_169, C_170)!=A_171 | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_171, B_169))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.55/4.44  tff(c_7257, plain, (![B_445, C_446, A_447]: (k1_xboole_0=B_445 | v1_funct_2(C_446, A_447, B_445) | k1_relset_1(A_447, B_445, C_446)!=A_447 | ~r1_tarski(k2_relat_1(C_446), B_445) | ~r1_tarski(k1_relat_1(C_446), A_447) | ~v1_relat_1(C_446))), inference(resolution, [status(thm)], [c_62, c_730])).
% 11.55/4.44  tff(c_7291, plain, (![A_447]: (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', A_447, '#skF_7') | k1_relset_1(A_447, '#skF_7', '#skF_8')!=A_447 | ~r1_tarski(k1_relat_1('#skF_8'), A_447) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_78, c_7257])).
% 11.55/4.44  tff(c_7317, plain, (![A_447]: (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', A_447, '#skF_7') | k1_relset_1(A_447, '#skF_7', '#skF_8')!=A_447 | ~r1_tarski(k1_relat_1('#skF_8'), A_447))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_7291])).
% 11.55/4.44  tff(c_7475, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_7317])).
% 11.55/4.44  tff(c_110, plain, (![A_76]: (k2_relat_1(A_76)!=k1_xboole_0 | k1_xboole_0=A_76 | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.55/4.44  tff(c_122, plain, (k2_relat_1('#skF_8')!=k1_xboole_0 | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_82, c_110])).
% 11.55/4.44  tff(c_123, plain, (k2_relat_1('#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_122])).
% 11.55/4.44  tff(c_16, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.55/4.44  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.55/4.44  tff(c_48, plain, (![A_50, B_51]: (k1_xboole_0=A_50 | k1_relat_1('#skF_6'(A_50, B_51))=B_51)), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.55/4.44  tff(c_56, plain, (![A_50, B_51]: (k1_xboole_0=A_50 | v1_relat_1('#skF_6'(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.55/4.44  tff(c_124, plain, (![A_77]: (k1_relat_1(A_77)!=k1_xboole_0 | k1_xboole_0=A_77 | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.55/4.44  tff(c_270, plain, (![A_101, B_102]: (k1_relat_1('#skF_6'(A_101, B_102))!=k1_xboole_0 | '#skF_6'(A_101, B_102)=k1_xboole_0 | k1_xboole_0=A_101)), inference(resolution, [status(thm)], [c_56, c_124])).
% 11.55/4.44  tff(c_282, plain, (![B_103, A_104]: (k1_xboole_0!=B_103 | '#skF_6'(A_104, B_103)=k1_xboole_0 | k1_xboole_0=A_104 | k1_xboole_0=A_104)), inference(superposition, [status(thm), theory('equality')], [c_48, c_270])).
% 11.55/4.44  tff(c_134, plain, (![A_50, B_51]: (k1_relat_1('#skF_6'(A_50, B_51))!=k1_xboole_0 | '#skF_6'(A_50, B_51)=k1_xboole_0 | k1_xboole_0=A_50)), inference(resolution, [status(thm)], [c_56, c_124])).
% 11.55/4.44  tff(c_288, plain, (![A_104, B_103]: (k1_relat_1(k1_xboole_0)!=k1_xboole_0 | '#skF_6'(A_104, B_103)=k1_xboole_0 | k1_xboole_0=A_104 | k1_xboole_0!=B_103 | k1_xboole_0=A_104 | k1_xboole_0=A_104)), inference(superposition, [status(thm), theory('equality')], [c_282, c_134])).
% 11.55/4.44  tff(c_313, plain, (![A_104, B_103]: ('#skF_6'(A_104, B_103)=k1_xboole_0 | k1_xboole_0!=B_103 | k1_xboole_0=A_104)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_288])).
% 11.55/4.44  tff(c_44, plain, (![A_50, B_51]: (k1_xboole_0=A_50 | r1_tarski(k2_relat_1('#skF_6'(A_50, B_51)), A_50))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.55/4.44  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.55/4.44  tff(c_243, plain, (![C_90, B_91, A_92]: (r2_hidden(C_90, B_91) | ~r2_hidden(C_90, A_92) | ~r1_tarski(A_92, B_91))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.55/4.44  tff(c_256, plain, (![A_95, B_96, B_97]: (r2_hidden('#skF_1'(A_95, B_96), B_97) | ~r1_tarski(A_95, B_97) | r1_tarski(A_95, B_96))), inference(resolution, [status(thm)], [c_6, c_243])).
% 11.55/4.44  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.55/4.44  tff(c_470, plain, (![A_125, B_126, B_127, B_128]: (r2_hidden('#skF_1'(A_125, B_126), B_127) | ~r1_tarski(B_128, B_127) | ~r1_tarski(A_125, B_128) | r1_tarski(A_125, B_126))), inference(resolution, [status(thm)], [c_256, c_2])).
% 11.55/4.44  tff(c_484, plain, (![A_131, B_132]: (r2_hidden('#skF_1'(A_131, B_132), '#skF_7') | ~r1_tarski(A_131, k2_relat_1('#skF_8')) | r1_tarski(A_131, B_132))), inference(resolution, [status(thm)], [c_78, c_470])).
% 11.55/4.44  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.55/4.44  tff(c_497, plain, (![A_133]: (~r1_tarski(A_133, k2_relat_1('#skF_8')) | r1_tarski(A_133, '#skF_7'))), inference(resolution, [status(thm)], [c_484, c_4])).
% 11.55/4.44  tff(c_501, plain, (![B_51]: (r1_tarski(k2_relat_1('#skF_6'(k2_relat_1('#skF_8'), B_51)), '#skF_7') | k2_relat_1('#skF_8')=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_497])).
% 11.55/4.44  tff(c_517, plain, (![B_134]: (r1_tarski(k2_relat_1('#skF_6'(k2_relat_1('#skF_8'), B_134)), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_123, c_501])).
% 11.55/4.44  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.55/4.44  tff(c_535, plain, (![B_137]: (k2_relat_1('#skF_6'(k2_relat_1('#skF_8'), B_137))='#skF_7' | ~r1_tarski('#skF_7', k2_relat_1('#skF_6'(k2_relat_1('#skF_8'), B_137))))), inference(resolution, [status(thm)], [c_517, c_8])).
% 11.55/4.44  tff(c_539, plain, (![B_103]: (k2_relat_1('#skF_6'(k2_relat_1('#skF_8'), B_103))='#skF_7' | ~r1_tarski('#skF_7', k2_relat_1(k1_xboole_0)) | k1_xboole_0!=B_103 | k2_relat_1('#skF_8')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_313, c_535])).
% 11.55/4.44  tff(c_544, plain, (![B_103]: (k2_relat_1('#skF_6'(k2_relat_1('#skF_8'), B_103))='#skF_7' | ~r1_tarski('#skF_7', k1_xboole_0) | k1_xboole_0!=B_103 | k2_relat_1('#skF_8')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_539])).
% 11.55/4.44  tff(c_545, plain, (![B_103]: (k2_relat_1('#skF_6'(k2_relat_1('#skF_8'), B_103))='#skF_7' | ~r1_tarski('#skF_7', k1_xboole_0) | k1_xboole_0!=B_103)), inference(negUnitSimplification, [status(thm)], [c_123, c_544])).
% 11.55/4.44  tff(c_547, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_545])).
% 11.55/4.44  tff(c_7582, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_7475, c_547])).
% 11.55/4.44  tff(c_7608, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_7582])).
% 11.55/4.44  tff(c_7611, plain, (![A_454]: (v1_funct_2('#skF_8', A_454, '#skF_7') | k1_relset_1(A_454, '#skF_7', '#skF_8')!=A_454 | ~r1_tarski(k1_relat_1('#skF_8'), A_454))), inference(splitRight, [status(thm)], [c_7317])).
% 11.55/4.44  tff(c_7615, plain, (v1_funct_2('#skF_8', k1_relat_1('#skF_8'), '#skF_7') | k1_relset_1(k1_relat_1('#skF_8'), '#skF_7', '#skF_8')!=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_12, c_7611])).
% 11.55/4.44  tff(c_7618, plain, (v1_funct_2('#skF_8', k1_relat_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_747, c_7615])).
% 11.55/4.44  tff(c_7620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_7618])).
% 11.55/4.44  tff(c_7622, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_545])).
% 11.55/4.44  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.55/4.44  tff(c_58, plain, (![B_54, A_53]: (~r1_tarski(B_54, A_53) | ~r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.55/4.44  tff(c_377, plain, (![B_109, A_110, B_111]: (~r1_tarski(B_109, '#skF_1'(A_110, B_111)) | ~r1_tarski(A_110, B_109) | r1_tarski(A_110, B_111))), inference(resolution, [status(thm)], [c_256, c_58])).
% 11.55/4.44  tff(c_392, plain, (![A_110, B_111]: (~r1_tarski(A_110, k1_xboole_0) | r1_tarski(A_110, B_111))), inference(resolution, [status(thm)], [c_14, c_377])).
% 11.55/4.44  tff(c_7635, plain, (![B_111]: (r1_tarski('#skF_7', B_111))), inference(resolution, [status(thm)], [c_7622, c_392])).
% 11.55/4.44  tff(c_200, plain, (![B_85, A_86]: (B_85=A_86 | ~r1_tarski(B_85, A_86) | ~r1_tarski(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.55/4.44  tff(c_210, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_78, c_200])).
% 11.55/4.44  tff(c_235, plain, (~r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_210])).
% 11.55/4.44  tff(c_7694, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7635, c_235])).
% 11.55/4.44  tff(c_7695, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_210])).
% 11.55/4.44  tff(c_7697, plain, (k1_xboole_0!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_7695, c_123])).
% 11.55/4.44  tff(c_8046, plain, (![C_520, A_521, B_522]: (m1_subset_1(C_520, k1_zfmisc_1(k2_zfmisc_1(A_521, B_522))) | ~r1_tarski(k2_relat_1(C_520), B_522) | ~r1_tarski(k1_relat_1(C_520), A_521) | ~v1_relat_1(C_520))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.55/4.44  tff(c_8253, plain, (![A_541, B_542, C_543]: (k1_relset_1(A_541, B_542, C_543)=k1_relat_1(C_543) | ~r1_tarski(k2_relat_1(C_543), B_542) | ~r1_tarski(k1_relat_1(C_543), A_541) | ~v1_relat_1(C_543))), inference(resolution, [status(thm)], [c_8046, c_60])).
% 11.55/4.44  tff(c_8276, plain, (![A_546, C_547]: (k1_relset_1(A_546, k2_relat_1(C_547), C_547)=k1_relat_1(C_547) | ~r1_tarski(k1_relat_1(C_547), A_546) | ~v1_relat_1(C_547))), inference(resolution, [status(thm)], [c_12, c_8253])).
% 11.55/4.44  tff(c_8292, plain, (![C_550]: (k1_relset_1(k1_relat_1(C_550), k2_relat_1(C_550), C_550)=k1_relat_1(C_550) | ~v1_relat_1(C_550))), inference(resolution, [status(thm)], [c_12, c_8276])).
% 11.55/4.44  tff(c_8309, plain, (k1_relset_1(k1_relat_1('#skF_8'), '#skF_7', '#skF_8')=k1_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_7695, c_8292])).
% 11.55/4.44  tff(c_8326, plain, (k1_relset_1(k1_relat_1('#skF_8'), '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_8309])).
% 11.55/4.44  tff(c_8396, plain, (![B_559, C_560, A_561]: (k1_xboole_0=B_559 | v1_funct_2(C_560, A_561, B_559) | k1_relset_1(A_561, B_559, C_560)!=A_561 | ~m1_subset_1(C_560, k1_zfmisc_1(k2_zfmisc_1(A_561, B_559))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.55/4.44  tff(c_13076, plain, (![B_789, C_790, A_791]: (k1_xboole_0=B_789 | v1_funct_2(C_790, A_791, B_789) | k1_relset_1(A_791, B_789, C_790)!=A_791 | ~r1_tarski(k2_relat_1(C_790), B_789) | ~r1_tarski(k1_relat_1(C_790), A_791) | ~v1_relat_1(C_790))), inference(resolution, [status(thm)], [c_62, c_8396])).
% 11.55/4.44  tff(c_13092, plain, (![B_789, A_791]: (k1_xboole_0=B_789 | v1_funct_2('#skF_8', A_791, B_789) | k1_relset_1(A_791, B_789, '#skF_8')!=A_791 | ~r1_tarski('#skF_7', B_789) | ~r1_tarski(k1_relat_1('#skF_8'), A_791) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_7695, c_13076])).
% 11.55/4.44  tff(c_13141, plain, (![B_796, A_797]: (k1_xboole_0=B_796 | v1_funct_2('#skF_8', A_797, B_796) | k1_relset_1(A_797, B_796, '#skF_8')!=A_797 | ~r1_tarski('#skF_7', B_796) | ~r1_tarski(k1_relat_1('#skF_8'), A_797))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_13092])).
% 11.55/4.44  tff(c_13147, plain, (![B_798]: (k1_xboole_0=B_798 | v1_funct_2('#skF_8', k1_relat_1('#skF_8'), B_798) | k1_relset_1(k1_relat_1('#skF_8'), B_798, '#skF_8')!=k1_relat_1('#skF_8') | ~r1_tarski('#skF_7', B_798))), inference(resolution, [status(thm)], [c_12, c_13141])).
% 11.55/4.44  tff(c_13152, plain, (k1_xboole_0='#skF_7' | k1_relset_1(k1_relat_1('#skF_8'), '#skF_7', '#skF_8')!=k1_relat_1('#skF_8') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_13147, c_98])).
% 11.55/4.44  tff(c_13158, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_8326, c_13152])).
% 11.55/4.44  tff(c_13160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7697, c_13158])).
% 11.55/4.44  tff(c_13161, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_122])).
% 11.55/4.44  tff(c_13170, plain, (![A_8]: (r1_tarski('#skF_8', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_13161, c_14])).
% 11.55/4.44  tff(c_13172, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_13161, c_13161, c_18])).
% 11.55/4.44  tff(c_13162, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_122])).
% 11.55/4.44  tff(c_13177, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_13161, c_13162])).
% 11.55/4.44  tff(c_13673, plain, (![C_869, A_870, B_871]: (m1_subset_1(C_869, k1_zfmisc_1(k2_zfmisc_1(A_870, B_871))) | ~r1_tarski(k2_relat_1(C_869), B_871) | ~r1_tarski(k1_relat_1(C_869), A_870) | ~v1_relat_1(C_869))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.55/4.44  tff(c_13744, plain, (![A_877, B_878, C_879]: (k1_relset_1(A_877, B_878, C_879)=k1_relat_1(C_879) | ~r1_tarski(k2_relat_1(C_879), B_878) | ~r1_tarski(k1_relat_1(C_879), A_877) | ~v1_relat_1(C_879))), inference(resolution, [status(thm)], [c_13673, c_60])).
% 11.55/4.44  tff(c_13748, plain, (![A_877, B_878]: (k1_relset_1(A_877, B_878, '#skF_8')=k1_relat_1('#skF_8') | ~r1_tarski('#skF_8', B_878) | ~r1_tarski(k1_relat_1('#skF_8'), A_877) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_13177, c_13744])).
% 11.55/4.44  tff(c_13754, plain, (![A_877, B_878]: (k1_relset_1(A_877, B_878, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_13170, c_13172, c_13170, c_13172, c_13748])).
% 11.55/4.44  tff(c_68, plain, (![C_63, B_62]: (v1_funct_2(C_63, k1_xboole_0, B_62) | k1_relset_1(k1_xboole_0, B_62, C_63)!=k1_xboole_0 | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_62))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.55/4.44  tff(c_13643, plain, (![C_63, B_62]: (v1_funct_2(C_63, '#skF_8', B_62) | k1_relset_1('#skF_8', B_62, C_63)!='#skF_8' | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1('#skF_8', B_62))))), inference(demodulation, [status(thm), theory('equality')], [c_13161, c_13161, c_13161, c_13161, c_68])).
% 11.55/4.44  tff(c_20911, plain, (![C_4051, B_4052]: (v1_funct_2(C_4051, '#skF_8', B_4052) | k1_relset_1('#skF_8', B_4052, C_4051)!='#skF_8' | ~r1_tarski(k2_relat_1(C_4051), B_4052) | ~r1_tarski(k1_relat_1(C_4051), '#skF_8') | ~v1_relat_1(C_4051))), inference(resolution, [status(thm)], [c_13673, c_13643])).
% 11.55/4.44  tff(c_20944, plain, (![B_4052]: (v1_funct_2('#skF_8', '#skF_8', B_4052) | k1_relset_1('#skF_8', B_4052, '#skF_8')!='#skF_8' | ~r1_tarski('#skF_8', B_4052) | ~r1_tarski(k1_relat_1('#skF_8'), '#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_13177, c_20911])).
% 11.55/4.44  tff(c_20962, plain, (![B_4052]: (v1_funct_2('#skF_8', '#skF_8', B_4052))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_13170, c_13172, c_13170, c_13754, c_20944])).
% 11.55/4.44  tff(c_13193, plain, (~v1_funct_2('#skF_8', '#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13172, c_98])).
% 11.55/4.44  tff(c_20966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20962, c_13193])).
% 11.55/4.44  tff(c_20967, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'), '#skF_7')))), inference(splitRight, [status(thm)], [c_84])).
% 11.55/4.44  tff(c_21532, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7') | ~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_21510, c_20967])).
% 11.55/4.44  tff(c_21543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_12, c_78, c_21532])).
% 11.55/4.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.55/4.44  
% 11.55/4.44  Inference rules
% 11.55/4.44  ----------------------
% 11.55/4.44  #Ref     : 4
% 11.55/4.44  #Sup     : 4734
% 11.55/4.44  #Fact    : 0
% 11.55/4.44  #Define  : 0
% 11.55/4.44  #Split   : 41
% 11.55/4.44  #Chain   : 0
% 11.55/4.44  #Close   : 0
% 11.55/4.44  
% 11.55/4.44  Ordering : KBO
% 11.55/4.44  
% 11.55/4.44  Simplification rules
% 11.55/4.44  ----------------------
% 11.55/4.44  #Subsume      : 1685
% 11.55/4.44  #Demod        : 3129
% 11.55/4.44  #Tautology    : 920
% 11.55/4.44  #SimpNegUnit  : 303
% 11.55/4.44  #BackRed      : 271
% 11.55/4.44  
% 11.55/4.44  #Partial instantiations: 780
% 11.55/4.44  #Strategies tried      : 1
% 11.55/4.44  
% 11.55/4.44  Timing (in seconds)
% 11.55/4.44  ----------------------
% 11.55/4.44  Preprocessing        : 0.35
% 11.55/4.44  Parsing              : 0.18
% 11.55/4.44  CNF conversion       : 0.03
% 11.55/4.44  Main loop            : 3.30
% 11.55/4.44  Inferencing          : 0.85
% 11.55/4.44  Reduction            : 0.91
% 11.55/4.44  Demodulation         : 0.59
% 11.55/4.44  BG Simplification    : 0.10
% 11.55/4.44  Subsumption          : 1.23
% 11.55/4.44  Abstraction          : 0.13
% 11.55/4.44  MUC search           : 0.00
% 11.55/4.44  Cooper               : 0.00
% 11.55/4.44  Total                : 3.70
% 11.55/4.44  Index Insertion      : 0.00
% 11.55/4.44  Index Deletion       : 0.00
% 11.55/4.45  Index Matching       : 0.00
% 11.55/4.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
