%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:43 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 409 expanded)
%              Number of leaves         :   37 ( 151 expanded)
%              Depth                    :   13
%              Number of atoms          :  267 (1314 expanded)
%              Number of equality atoms :   65 ( 306 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_53,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(c_50,plain,
    ( '#skF_7' != '#skF_6'
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_72,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_22,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_110,plain,(
    ! [B_52,A_53] :
      ( v1_relat_1(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_116,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_110])).

tff(c_120,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_116])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_187,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_196,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_187])).

tff(c_233,plain,(
    ! [A_81,B_82,C_83] :
      ( m1_subset_1(k1_relset_1(A_81,B_82,C_83),k1_zfmisc_1(A_81))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_252,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_233])).

tff(c_257,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_252])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_265,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_257,c_16])).

tff(c_170,plain,(
    ! [A_66] :
      ( r2_hidden('#skF_3'(A_66),k1_relat_1(A_66))
      | v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1038,plain,(
    ! [A_176,B_177] :
      ( r2_hidden('#skF_3'(A_176),B_177)
      | ~ r1_tarski(k1_relat_1(A_176),B_177)
      | v2_funct_1(A_176)
      | ~ v1_funct_1(A_176)
      | ~ v1_relat_1(A_176) ) ),
    inference(resolution,[status(thm)],[c_170,c_2])).

tff(c_163,plain,(
    ! [A_65] :
      ( '#skF_2'(A_65) != '#skF_3'(A_65)
      | v2_funct_1(A_65)
      | ~ v1_funct_1(A_65)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_166,plain,
    ( '#skF_2'('#skF_5') != '#skF_3'('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_163,c_72])).

tff(c_169,plain,(
    '#skF_2'('#skF_5') != '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_48,c_166])).

tff(c_174,plain,(
    ! [A_67] :
      ( r2_hidden('#skF_2'(A_67),k1_relat_1(A_67))
      | v2_funct_1(A_67)
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_693,plain,(
    ! [A_132,B_133] :
      ( r2_hidden('#skF_2'(A_132),B_133)
      | ~ r1_tarski(k1_relat_1(A_132),B_133)
      | v2_funct_1(A_132)
      | ~ v1_funct_1(A_132)
      | ~ v1_relat_1(A_132) ) ),
    inference(resolution,[status(thm)],[c_174,c_2])).

tff(c_274,plain,(
    ! [A_84] :
      ( k1_funct_1(A_84,'#skF_2'(A_84)) = k1_funct_1(A_84,'#skF_3'(A_84))
      | v2_funct_1(A_84)
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_68,plain,(
    ! [D_40,C_39] :
      ( v2_funct_1('#skF_5')
      | D_40 = C_39
      | k1_funct_1('#skF_5',D_40) != k1_funct_1('#skF_5',C_39)
      | ~ r2_hidden(D_40,'#skF_4')
      | ~ r2_hidden(C_39,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_157,plain,(
    ! [D_40,C_39] :
      ( D_40 = C_39
      | k1_funct_1('#skF_5',D_40) != k1_funct_1('#skF_5',C_39)
      | ~ r2_hidden(D_40,'#skF_4')
      | ~ r2_hidden(C_39,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68])).

tff(c_280,plain,(
    ! [C_39] :
      ( C_39 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_39) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_39,'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_157])).

tff(c_289,plain,(
    ! [C_39] :
      ( C_39 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_39) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_39,'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_48,c_280])).

tff(c_290,plain,(
    ! [C_39] :
      ( C_39 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_39) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_39,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_289])).

tff(c_428,plain,(
    ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_698,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_693,c_428])).

tff(c_704,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_48,c_265,c_698])).

tff(c_706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_704])).

tff(c_708,plain,(
    r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_283,plain,(
    ! [D_40] :
      ( D_40 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_40) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_40,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_157])).

tff(c_292,plain,(
    ! [D_40] :
      ( D_40 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_40) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_40,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_48,c_283])).

tff(c_293,plain,(
    ! [D_40] :
      ( D_40 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_40) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_40,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_292])).

tff(c_713,plain,(
    ! [D_40] :
      ( D_40 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_40) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_40,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_293])).

tff(c_716,plain,
    ( '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_713])).

tff(c_717,plain,(
    ~ r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_716])).

tff(c_1043,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1038,c_717])).

tff(c_1049,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_48,c_265,c_1043])).

tff(c_1051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1049])).

tff(c_1052,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1103,plain,(
    ! [B_189,A_190] :
      ( v1_relat_1(B_189)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(A_190))
      | ~ v1_relat_1(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1109,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_1103])).

tff(c_1113,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1109])).

tff(c_1053,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_46,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_52,plain,
    ( k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1097,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_52])).

tff(c_54,plain,
    ( r2_hidden('#skF_7','#skF_4')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1058,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_54])).

tff(c_1566,plain,(
    ! [D_246,C_247,B_248,A_249] :
      ( k1_funct_1(k2_funct_1(D_246),k1_funct_1(D_246,C_247)) = C_247
      | k1_xboole_0 = B_248
      | ~ r2_hidden(C_247,A_249)
      | ~ v2_funct_1(D_246)
      | ~ m1_subset_1(D_246,k1_zfmisc_1(k2_zfmisc_1(A_249,B_248)))
      | ~ v1_funct_2(D_246,A_249,B_248)
      | ~ v1_funct_1(D_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1622,plain,(
    ! [D_255,B_256] :
      ( k1_funct_1(k2_funct_1(D_255),k1_funct_1(D_255,'#skF_7')) = '#skF_7'
      | k1_xboole_0 = B_256
      | ~ v2_funct_1(D_255)
      | ~ m1_subset_1(D_255,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_256)))
      | ~ v1_funct_2(D_255,'#skF_4',B_256)
      | ~ v1_funct_1(D_255) ) ),
    inference(resolution,[status(thm)],[c_1058,c_1566])).

tff(c_1633,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_1622])).

tff(c_1639,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_7'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1053,c_1097,c_1633])).

tff(c_1640,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1639])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1143,plain,(
    ! [C_195,B_196,A_197] :
      ( r2_hidden(C_195,B_196)
      | ~ r2_hidden(C_195,A_197)
      | ~ r1_tarski(A_197,B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1153,plain,(
    ! [B_198] :
      ( r2_hidden('#skF_7',B_198)
      | ~ r1_tarski('#skF_4',B_198) ) ),
    inference(resolution,[status(thm)],[c_1058,c_1143])).

tff(c_1161,plain,(
    ! [B_200,B_201] :
      ( r2_hidden('#skF_7',B_200)
      | ~ r1_tarski(B_201,B_200)
      | ~ r1_tarski('#skF_4',B_201) ) ),
    inference(resolution,[status(thm)],[c_1153,c_2])).

tff(c_1170,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_7',A_8)
      | ~ r1_tarski('#skF_4',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_1161])).

tff(c_1171,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1170])).

tff(c_1648,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1640,c_1171])).

tff(c_1654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1648])).

tff(c_1656,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1639])).

tff(c_1655,plain,(
    k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1639])).

tff(c_56,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1056,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_56])).

tff(c_1732,plain,(
    ! [D_264,B_265] :
      ( k1_funct_1(k2_funct_1(D_264),k1_funct_1(D_264,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_265
      | ~ v2_funct_1(D_264)
      | ~ m1_subset_1(D_264,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_265)))
      | ~ v1_funct_2(D_264,'#skF_4',B_265)
      | ~ v1_funct_1(D_264) ) ),
    inference(resolution,[status(thm)],[c_1056,c_1566])).

tff(c_1743,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_1732])).

tff(c_1749,plain,
    ( '#skF_7' = '#skF_6'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1053,c_1655,c_1743])).

tff(c_1751,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1656,c_1052,c_1749])).

tff(c_1753,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1170])).

tff(c_1069,plain,(
    ! [B_184,A_185] :
      ( B_184 = A_185
      | ~ r1_tarski(B_184,A_185)
      | ~ r1_tarski(A_185,B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1081,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_1069])).

tff(c_1773,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1753,c_1081])).

tff(c_1780,plain,(
    ! [A_8] : r1_tarski('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1773,c_14])).

tff(c_1152,plain,(
    ! [B_196] :
      ( r2_hidden('#skF_6',B_196)
      | ~ r1_tarski('#skF_4',B_196) ) ),
    inference(resolution,[status(thm)],[c_1056,c_1143])).

tff(c_1790,plain,(
    ! [B_196] : r2_hidden('#skF_6',B_196) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1780,c_1152])).

tff(c_1752,plain,(
    ! [A_8] : r2_hidden('#skF_7',A_8) ),
    inference(splitRight,[status(thm)],[c_1170])).

tff(c_2065,plain,(
    ! [B_296,A_297] :
      ( k1_funct_1(k2_funct_1(B_296),k1_funct_1(B_296,A_297)) = A_297
      | ~ r2_hidden(A_297,k1_relat_1(B_296))
      | ~ v2_funct_1(B_296)
      | ~ v1_funct_1(B_296)
      | ~ v1_relat_1(B_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2086,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_7'
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1097,c_2065])).

tff(c_2090,plain,(
    k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1113,c_48,c_1053,c_1752,c_2086])).

tff(c_36,plain,(
    ! [B_24,A_23] :
      ( k1_funct_1(k2_funct_1(B_24),k1_funct_1(B_24,A_23)) = A_23
      | ~ r2_hidden(A_23,k1_relat_1(B_24))
      | ~ v2_funct_1(B_24)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2159,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2090,c_36])).

tff(c_2166,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1113,c_48,c_1053,c_1790,c_2159])).

tff(c_2168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1052,c_2166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:24:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.06/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.71  
% 4.06/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.72  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 4.06/1.72  
% 4.06/1.72  %Foreground sorts:
% 4.06/1.72  
% 4.06/1.72  
% 4.06/1.72  %Background operators:
% 4.06/1.72  
% 4.06/1.72  
% 4.06/1.72  %Foreground operators:
% 4.06/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.06/1.72  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.06/1.72  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.06/1.72  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.06/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.06/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.06/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.06/1.72  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.06/1.72  tff('#skF_7', type, '#skF_7': $i).
% 4.06/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.06/1.72  tff('#skF_5', type, '#skF_5': $i).
% 4.06/1.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.06/1.72  tff('#skF_6', type, '#skF_6': $i).
% 4.06/1.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.06/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.06/1.72  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.06/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.06/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.06/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.06/1.72  tff('#skF_4', type, '#skF_4': $i).
% 4.06/1.72  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.06/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.06/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.06/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.06/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.06/1.72  
% 4.06/1.74  tff(f_120, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_funct_2)).
% 4.06/1.74  tff(f_53, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.06/1.74  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.06/1.74  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.06/1.74  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 4.06/1.74  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.06/1.74  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 4.06/1.74  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.06/1.74  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.06/1.74  tff(f_102, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 4.06/1.74  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.06/1.74  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 4.06/1.74  tff(c_50, plain, ('#skF_7'!='#skF_6' | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.06/1.74  tff(c_72, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_50])).
% 4.06/1.74  tff(c_22, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.06/1.74  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.06/1.74  tff(c_110, plain, (![B_52, A_53]: (v1_relat_1(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.06/1.74  tff(c_116, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_110])).
% 4.06/1.74  tff(c_120, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_116])).
% 4.06/1.74  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.06/1.74  tff(c_187, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.06/1.74  tff(c_196, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_187])).
% 4.06/1.74  tff(c_233, plain, (![A_81, B_82, C_83]: (m1_subset_1(k1_relset_1(A_81, B_82, C_83), k1_zfmisc_1(A_81)) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.06/1.74  tff(c_252, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_196, c_233])).
% 4.06/1.74  tff(c_257, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_252])).
% 4.06/1.74  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.06/1.74  tff(c_265, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_257, c_16])).
% 4.06/1.74  tff(c_170, plain, (![A_66]: (r2_hidden('#skF_3'(A_66), k1_relat_1(A_66)) | v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.06/1.74  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.06/1.74  tff(c_1038, plain, (![A_176, B_177]: (r2_hidden('#skF_3'(A_176), B_177) | ~r1_tarski(k1_relat_1(A_176), B_177) | v2_funct_1(A_176) | ~v1_funct_1(A_176) | ~v1_relat_1(A_176))), inference(resolution, [status(thm)], [c_170, c_2])).
% 4.06/1.74  tff(c_163, plain, (![A_65]: ('#skF_2'(A_65)!='#skF_3'(A_65) | v2_funct_1(A_65) | ~v1_funct_1(A_65) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.06/1.74  tff(c_166, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_163, c_72])).
% 4.06/1.74  tff(c_169, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_48, c_166])).
% 4.06/1.74  tff(c_174, plain, (![A_67]: (r2_hidden('#skF_2'(A_67), k1_relat_1(A_67)) | v2_funct_1(A_67) | ~v1_funct_1(A_67) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.06/1.74  tff(c_693, plain, (![A_132, B_133]: (r2_hidden('#skF_2'(A_132), B_133) | ~r1_tarski(k1_relat_1(A_132), B_133) | v2_funct_1(A_132) | ~v1_funct_1(A_132) | ~v1_relat_1(A_132))), inference(resolution, [status(thm)], [c_174, c_2])).
% 4.06/1.74  tff(c_274, plain, (![A_84]: (k1_funct_1(A_84, '#skF_2'(A_84))=k1_funct_1(A_84, '#skF_3'(A_84)) | v2_funct_1(A_84) | ~v1_funct_1(A_84) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.06/1.74  tff(c_68, plain, (![D_40, C_39]: (v2_funct_1('#skF_5') | D_40=C_39 | k1_funct_1('#skF_5', D_40)!=k1_funct_1('#skF_5', C_39) | ~r2_hidden(D_40, '#skF_4') | ~r2_hidden(C_39, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.06/1.74  tff(c_157, plain, (![D_40, C_39]: (D_40=C_39 | k1_funct_1('#skF_5', D_40)!=k1_funct_1('#skF_5', C_39) | ~r2_hidden(D_40, '#skF_4') | ~r2_hidden(C_39, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_72, c_68])).
% 4.06/1.74  tff(c_280, plain, (![C_39]: (C_39='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_39)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_39, '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_274, c_157])).
% 4.06/1.74  tff(c_289, plain, (![C_39]: (C_39='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_39)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_39, '#skF_4') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_48, c_280])).
% 4.06/1.74  tff(c_290, plain, (![C_39]: (C_39='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_39)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_39, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_72, c_289])).
% 4.06/1.74  tff(c_428, plain, (~r2_hidden('#skF_2'('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_290])).
% 4.06/1.74  tff(c_698, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_693, c_428])).
% 4.06/1.74  tff(c_704, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_48, c_265, c_698])).
% 4.06/1.74  tff(c_706, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_704])).
% 4.06/1.74  tff(c_708, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_290])).
% 4.06/1.74  tff(c_283, plain, (![D_40]: (D_40='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_40)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_40, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_274, c_157])).
% 4.06/1.74  tff(c_292, plain, (![D_40]: (D_40='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_40)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_40, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_48, c_283])).
% 4.06/1.74  tff(c_293, plain, (![D_40]: (D_40='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_40)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_40, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_72, c_292])).
% 4.06/1.74  tff(c_713, plain, (![D_40]: (D_40='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_40)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_40, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_708, c_293])).
% 4.06/1.74  tff(c_716, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_713])).
% 4.06/1.74  tff(c_717, plain, (~r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_169, c_716])).
% 4.06/1.74  tff(c_1043, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1038, c_717])).
% 4.06/1.74  tff(c_1049, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_48, c_265, c_1043])).
% 4.06/1.74  tff(c_1051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1049])).
% 4.06/1.74  tff(c_1052, plain, ('#skF_7'!='#skF_6'), inference(splitRight, [status(thm)], [c_50])).
% 4.06/1.74  tff(c_1103, plain, (![B_189, A_190]: (v1_relat_1(B_189) | ~m1_subset_1(B_189, k1_zfmisc_1(A_190)) | ~v1_relat_1(A_190))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.06/1.74  tff(c_1109, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_1103])).
% 4.06/1.74  tff(c_1113, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1109])).
% 4.06/1.74  tff(c_1053, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_50])).
% 4.06/1.74  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.06/1.74  tff(c_46, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.06/1.74  tff(c_52, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.06/1.74  tff(c_1097, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1053, c_52])).
% 4.06/1.74  tff(c_54, plain, (r2_hidden('#skF_7', '#skF_4') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.06/1.74  tff(c_1058, plain, (r2_hidden('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1053, c_54])).
% 4.06/1.74  tff(c_1566, plain, (![D_246, C_247, B_248, A_249]: (k1_funct_1(k2_funct_1(D_246), k1_funct_1(D_246, C_247))=C_247 | k1_xboole_0=B_248 | ~r2_hidden(C_247, A_249) | ~v2_funct_1(D_246) | ~m1_subset_1(D_246, k1_zfmisc_1(k2_zfmisc_1(A_249, B_248))) | ~v1_funct_2(D_246, A_249, B_248) | ~v1_funct_1(D_246))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.06/1.74  tff(c_1622, plain, (![D_255, B_256]: (k1_funct_1(k2_funct_1(D_255), k1_funct_1(D_255, '#skF_7'))='#skF_7' | k1_xboole_0=B_256 | ~v2_funct_1(D_255) | ~m1_subset_1(D_255, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_256))) | ~v1_funct_2(D_255, '#skF_4', B_256) | ~v1_funct_1(D_255))), inference(resolution, [status(thm)], [c_1058, c_1566])).
% 4.06/1.74  tff(c_1633, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_7'))='#skF_7' | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_1622])).
% 4.06/1.74  tff(c_1639, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_7' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1053, c_1097, c_1633])).
% 4.06/1.74  tff(c_1640, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1639])).
% 4.06/1.74  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.06/1.74  tff(c_1143, plain, (![C_195, B_196, A_197]: (r2_hidden(C_195, B_196) | ~r2_hidden(C_195, A_197) | ~r1_tarski(A_197, B_196))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.06/1.74  tff(c_1153, plain, (![B_198]: (r2_hidden('#skF_7', B_198) | ~r1_tarski('#skF_4', B_198))), inference(resolution, [status(thm)], [c_1058, c_1143])).
% 4.06/1.74  tff(c_1161, plain, (![B_200, B_201]: (r2_hidden('#skF_7', B_200) | ~r1_tarski(B_201, B_200) | ~r1_tarski('#skF_4', B_201))), inference(resolution, [status(thm)], [c_1153, c_2])).
% 4.06/1.74  tff(c_1170, plain, (![A_8]: (r2_hidden('#skF_7', A_8) | ~r1_tarski('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_1161])).
% 4.06/1.74  tff(c_1171, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1170])).
% 4.06/1.74  tff(c_1648, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1640, c_1171])).
% 4.06/1.74  tff(c_1654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1648])).
% 4.06/1.74  tff(c_1656, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_1639])).
% 4.06/1.74  tff(c_1655, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_7'), inference(splitRight, [status(thm)], [c_1639])).
% 4.06/1.74  tff(c_56, plain, (r2_hidden('#skF_6', '#skF_4') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.06/1.74  tff(c_1056, plain, (r2_hidden('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1053, c_56])).
% 4.06/1.74  tff(c_1732, plain, (![D_264, B_265]: (k1_funct_1(k2_funct_1(D_264), k1_funct_1(D_264, '#skF_6'))='#skF_6' | k1_xboole_0=B_265 | ~v2_funct_1(D_264) | ~m1_subset_1(D_264, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_265))) | ~v1_funct_2(D_264, '#skF_4', B_265) | ~v1_funct_1(D_264))), inference(resolution, [status(thm)], [c_1056, c_1566])).
% 4.06/1.74  tff(c_1743, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_1732])).
% 4.06/1.74  tff(c_1749, plain, ('#skF_7'='#skF_6' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1053, c_1655, c_1743])).
% 4.06/1.74  tff(c_1751, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1656, c_1052, c_1749])).
% 4.06/1.74  tff(c_1753, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1170])).
% 4.06/1.74  tff(c_1069, plain, (![B_184, A_185]: (B_184=A_185 | ~r1_tarski(B_184, A_185) | ~r1_tarski(A_185, B_184))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.06/1.74  tff(c_1081, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_1069])).
% 4.06/1.74  tff(c_1773, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1753, c_1081])).
% 4.06/1.74  tff(c_1780, plain, (![A_8]: (r1_tarski('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_1773, c_14])).
% 4.06/1.74  tff(c_1152, plain, (![B_196]: (r2_hidden('#skF_6', B_196) | ~r1_tarski('#skF_4', B_196))), inference(resolution, [status(thm)], [c_1056, c_1143])).
% 4.06/1.74  tff(c_1790, plain, (![B_196]: (r2_hidden('#skF_6', B_196))), inference(demodulation, [status(thm), theory('equality')], [c_1780, c_1152])).
% 4.06/1.74  tff(c_1752, plain, (![A_8]: (r2_hidden('#skF_7', A_8))), inference(splitRight, [status(thm)], [c_1170])).
% 4.06/1.74  tff(c_2065, plain, (![B_296, A_297]: (k1_funct_1(k2_funct_1(B_296), k1_funct_1(B_296, A_297))=A_297 | ~r2_hidden(A_297, k1_relat_1(B_296)) | ~v2_funct_1(B_296) | ~v1_funct_1(B_296) | ~v1_relat_1(B_296))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.06/1.74  tff(c_2086, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_7' | ~r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1097, c_2065])).
% 4.06/1.74  tff(c_2090, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1113, c_48, c_1053, c_1752, c_2086])).
% 4.06/1.74  tff(c_36, plain, (![B_24, A_23]: (k1_funct_1(k2_funct_1(B_24), k1_funct_1(B_24, A_23))=A_23 | ~r2_hidden(A_23, k1_relat_1(B_24)) | ~v2_funct_1(B_24) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.06/1.74  tff(c_2159, plain, ('#skF_7'='#skF_6' | ~r2_hidden('#skF_6', k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2090, c_36])).
% 4.06/1.74  tff(c_2166, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1113, c_48, c_1053, c_1790, c_2159])).
% 4.06/1.74  tff(c_2168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1052, c_2166])).
% 4.06/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.74  
% 4.06/1.74  Inference rules
% 4.06/1.74  ----------------------
% 4.06/1.74  #Ref     : 6
% 4.06/1.74  #Sup     : 456
% 4.06/1.74  #Fact    : 0
% 4.06/1.74  #Define  : 0
% 4.06/1.74  #Split   : 20
% 4.06/1.74  #Chain   : 0
% 4.06/1.74  #Close   : 0
% 4.06/1.74  
% 4.06/1.74  Ordering : KBO
% 4.06/1.74  
% 4.06/1.74  Simplification rules
% 4.06/1.74  ----------------------
% 4.06/1.74  #Subsume      : 49
% 4.06/1.74  #Demod        : 314
% 4.06/1.74  #Tautology    : 217
% 4.06/1.74  #SimpNegUnit  : 19
% 4.06/1.74  #BackRed      : 33
% 4.06/1.74  
% 4.06/1.74  #Partial instantiations: 0
% 4.06/1.74  #Strategies tried      : 1
% 4.06/1.74  
% 4.06/1.74  Timing (in seconds)
% 4.06/1.74  ----------------------
% 4.06/1.74  Preprocessing        : 0.34
% 4.06/1.74  Parsing              : 0.18
% 4.06/1.74  CNF conversion       : 0.02
% 4.06/1.74  Main loop            : 0.62
% 4.06/1.74  Inferencing          : 0.22
% 4.06/1.74  Reduction            : 0.20
% 4.06/1.74  Demodulation         : 0.14
% 4.06/1.74  BG Simplification    : 0.03
% 4.06/1.74  Subsumption          : 0.11
% 4.06/1.74  Abstraction          : 0.03
% 4.06/1.74  MUC search           : 0.00
% 4.06/1.74  Cooper               : 0.00
% 4.06/1.74  Total                : 1.00
% 4.06/1.74  Index Insertion      : 0.00
% 4.06/1.74  Index Deletion       : 0.00
% 4.06/1.74  Index Matching       : 0.00
% 4.06/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
