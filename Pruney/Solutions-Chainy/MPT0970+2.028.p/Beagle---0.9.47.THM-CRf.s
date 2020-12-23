%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:22 EST 2020

% Result     : Theorem 9.27s
% Output     : CNFRefutation 9.52s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 225 expanded)
%              Number of leaves         :   36 (  92 expanded)
%              Depth                    :   10
%              Number of atoms          :  174 ( 587 expanded)
%              Number of equality atoms :   42 ( 147 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
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

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_210,plain,(
    ! [A_81,B_82,C_83] :
      ( k2_relset_1(A_81,B_82,C_83) = k2_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_219,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_210])).

tff(c_46,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_220,plain,(
    k2_relat_1('#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_46])).

tff(c_342,plain,(
    ! [A_109,B_110,C_111] :
      ( m1_subset_1(k2_relset_1(A_109,B_110,C_111),k1_zfmisc_1(B_110))
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_366,plain,
    ( m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_342])).

tff(c_372,plain,(
    m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_366])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_376,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_372,c_18])).

tff(c_305,plain,(
    ! [A_103,B_104] :
      ( r2_hidden('#skF_2'(A_103,B_104),B_104)
      | r2_hidden('#skF_3'(A_103,B_104),A_103)
      | B_104 = A_103 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2747,plain,(
    ! [A_310,B_311,B_312] :
      ( r2_hidden('#skF_3'(A_310,B_311),B_312)
      | ~ r1_tarski(A_310,B_312)
      | r2_hidden('#skF_2'(A_310,B_311),B_311)
      | B_311 = A_310 ) ),
    inference(resolution,[status(thm)],[c_305,c_2])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2778,plain,(
    ! [A_310,B_312] :
      ( ~ r1_tarski(A_310,B_312)
      | r2_hidden('#skF_2'(A_310,B_312),B_312)
      | B_312 = A_310 ) ),
    inference(resolution,[status(thm)],[c_2747,c_10])).

tff(c_95,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_1'(A_51,B_52),A_51)
      | r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_103,plain,(
    ! [A_51] : r1_tarski(A_51,A_51) ),
    inference(resolution,[status(thm)],[c_95,c_4])).

tff(c_50,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_241,plain,(
    ! [A_87,B_88,C_89] :
      ( k1_relset_1(A_87,B_88,C_89) = k1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_250,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_241])).

tff(c_752,plain,(
    ! [B_139,A_140,C_141] :
      ( k1_xboole_0 = B_139
      | k1_relset_1(A_140,B_139,C_141) = A_140
      | ~ v1_funct_2(C_141,A_140,B_139)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_140,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_767,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_752])).

tff(c_774,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_250,c_767])).

tff(c_775,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_774])).

tff(c_56,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_7'(D_34),'#skF_4')
      | ~ r2_hidden(D_34,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_122,plain,(
    ! [C_57,B_58,A_59] :
      ( r2_hidden(C_57,B_58)
      | ~ r2_hidden(C_57,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_128,plain,(
    ! [D_34,B_58] :
      ( r2_hidden('#skF_7'(D_34),B_58)
      | ~ r1_tarski('#skF_4',B_58)
      | ~ r2_hidden(D_34,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_122])).

tff(c_85,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_94,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_85])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_54,plain,(
    ! [D_34] :
      ( k1_funct_1('#skF_6','#skF_7'(D_34)) = D_34
      | ~ r2_hidden(D_34,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_408,plain,(
    ! [B_115,A_116] :
      ( r2_hidden(k1_funct_1(B_115,A_116),k2_relat_1(B_115))
      | ~ r2_hidden(A_116,k1_relat_1(B_115))
      | ~ v1_funct_1(B_115)
      | ~ v1_relat_1(B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_416,plain,(
    ! [D_34] :
      ( r2_hidden(D_34,k2_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_7'(D_34),k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(D_34,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_408])).

tff(c_479,plain,(
    ! [D_120] :
      ( r2_hidden(D_120,k2_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_7'(D_120),k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_120,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_52,c_416])).

tff(c_484,plain,(
    ! [D_34] :
      ( r2_hidden(D_34,k2_relat_1('#skF_6'))
      | ~ r1_tarski('#skF_4',k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_34,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_128,c_479])).

tff(c_593,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_484])).

tff(c_776,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_775,c_593])).

tff(c_781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_776])).

tff(c_782,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_774])).

tff(c_16,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_804,plain,(
    ! [A_142] : r1_tarski('#skF_5',A_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_16])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_165,plain,(
    ! [A_70,B_71,B_72] :
      ( r2_hidden('#skF_1'(A_70,B_71),B_72)
      | ~ r1_tarski(A_70,B_72)
      | r1_tarski(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_6,c_122])).

tff(c_24,plain,(
    ! [B_15,A_14] :
      ( ~ r1_tarski(B_15,A_14)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_177,plain,(
    ! [B_72,A_70,B_71] :
      ( ~ r1_tarski(B_72,'#skF_1'(A_70,B_71))
      | ~ r1_tarski(A_70,B_72)
      | r1_tarski(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_165,c_24])).

tff(c_942,plain,(
    ! [A_156,B_157] :
      ( ~ r1_tarski(A_156,'#skF_5')
      | r1_tarski(A_156,B_157) ) ),
    inference(resolution,[status(thm)],[c_804,c_177])).

tff(c_953,plain,(
    ! [B_157] : r1_tarski(k2_relat_1('#skF_6'),B_157) ),
    inference(resolution,[status(thm)],[c_376,c_942])).

tff(c_799,plain,(
    ! [A_9] : r1_tarski('#skF_5',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_16])).

tff(c_1014,plain,(
    ! [B_161,A_162] :
      ( ~ r1_tarski(B_161,'#skF_2'(A_162,B_161))
      | r2_hidden('#skF_3'(A_162,B_161),A_162)
      | B_161 = A_162 ) ),
    inference(resolution,[status(thm)],[c_305,c_24])).

tff(c_1023,plain,(
    ! [A_163] :
      ( r2_hidden('#skF_3'(A_163,'#skF_5'),A_163)
      | A_163 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_799,c_1014])).

tff(c_1037,plain,(
    ! [A_164] :
      ( ~ r1_tarski(A_164,'#skF_3'(A_164,'#skF_5'))
      | A_164 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_1023,c_24])).

tff(c_1041,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_953,c_1037])).

tff(c_1049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_1041])).

tff(c_1050,plain,(
    ! [D_34] :
      ( r2_hidden(D_34,k2_relat_1('#skF_6'))
      | ~ r2_hidden(D_34,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_484])).

tff(c_157,plain,(
    ! [A_68,B_69] :
      ( ~ r2_hidden('#skF_2'(A_68,B_69),A_68)
      | r2_hidden('#skF_3'(A_68,B_69),A_68)
      | B_69 = A_68 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3282,plain,(
    ! [A_352,B_353,B_354] :
      ( r2_hidden('#skF_3'(A_352,B_353),B_354)
      | ~ r1_tarski(A_352,B_354)
      | ~ r2_hidden('#skF_2'(A_352,B_353),A_352)
      | B_353 = A_352 ) ),
    inference(resolution,[status(thm)],[c_157,c_2])).

tff(c_13498,plain,(
    ! [B_990,B_991] :
      ( r2_hidden('#skF_3'(k2_relat_1('#skF_6'),B_990),B_991)
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_991)
      | k2_relat_1('#skF_6') = B_990
      | ~ r2_hidden('#skF_2'(k2_relat_1('#skF_6'),B_990),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1050,c_3282])).

tff(c_1057,plain,(
    ! [D_165] :
      ( r2_hidden(D_165,k2_relat_1('#skF_6'))
      | ~ r2_hidden(D_165,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_484])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7),A_6)
      | ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1075,plain,(
    ! [B_7] :
      ( ~ r2_hidden('#skF_3'(k2_relat_1('#skF_6'),B_7),B_7)
      | k2_relat_1('#skF_6') = B_7
      | ~ r2_hidden('#skF_2'(k2_relat_1('#skF_6'),B_7),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1057,c_8])).

tff(c_13535,plain,(
    ! [B_992] :
      ( ~ r1_tarski(k2_relat_1('#skF_6'),B_992)
      | k2_relat_1('#skF_6') = B_992
      | ~ r2_hidden('#skF_2'(k2_relat_1('#skF_6'),B_992),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_13498,c_1075])).

tff(c_13561,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | k2_relat_1('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2778,c_13535])).

tff(c_13574,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_13561])).

tff(c_13576,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_13574])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:40:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.27/3.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.27/3.84  
% 9.27/3.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.27/3.85  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 9.27/3.85  
% 9.27/3.85  %Foreground sorts:
% 9.27/3.85  
% 9.27/3.85  
% 9.27/3.85  %Background operators:
% 9.27/3.85  
% 9.27/3.85  
% 9.27/3.85  %Foreground operators:
% 9.27/3.85  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.27/3.85  tff('#skF_7', type, '#skF_7': $i > $i).
% 9.27/3.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.27/3.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.27/3.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.27/3.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.27/3.85  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.27/3.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.27/3.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.27/3.85  tff('#skF_5', type, '#skF_5': $i).
% 9.27/3.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.27/3.85  tff('#skF_6', type, '#skF_6': $i).
% 9.27/3.85  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.27/3.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.27/3.85  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.27/3.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.27/3.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.27/3.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.27/3.85  tff('#skF_4', type, '#skF_4': $i).
% 9.27/3.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.27/3.85  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.27/3.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.27/3.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.27/3.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.27/3.85  
% 9.52/3.86  tff(f_111, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 9.52/3.86  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.52/3.86  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 9.52/3.86  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.52/3.86  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 9.52/3.86  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.52/3.86  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.52/3.86  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.52/3.86  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.52/3.86  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 9.52/3.86  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.52/3.86  tff(f_58, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 9.52/3.86  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.52/3.86  tff(c_210, plain, (![A_81, B_82, C_83]: (k2_relset_1(A_81, B_82, C_83)=k2_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.52/3.86  tff(c_219, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_210])).
% 9.52/3.86  tff(c_46, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.52/3.86  tff(c_220, plain, (k2_relat_1('#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_219, c_46])).
% 9.52/3.86  tff(c_342, plain, (![A_109, B_110, C_111]: (m1_subset_1(k2_relset_1(A_109, B_110, C_111), k1_zfmisc_1(B_110)) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.52/3.86  tff(c_366, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_219, c_342])).
% 9.52/3.86  tff(c_372, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_366])).
% 9.52/3.86  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.52/3.86  tff(c_376, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_372, c_18])).
% 9.52/3.86  tff(c_305, plain, (![A_103, B_104]: (r2_hidden('#skF_2'(A_103, B_104), B_104) | r2_hidden('#skF_3'(A_103, B_104), A_103) | B_104=A_103)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.52/3.86  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.52/3.86  tff(c_2747, plain, (![A_310, B_311, B_312]: (r2_hidden('#skF_3'(A_310, B_311), B_312) | ~r1_tarski(A_310, B_312) | r2_hidden('#skF_2'(A_310, B_311), B_311) | B_311=A_310)), inference(resolution, [status(thm)], [c_305, c_2])).
% 9.52/3.86  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | ~r2_hidden('#skF_3'(A_6, B_7), B_7) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.52/3.86  tff(c_2778, plain, (![A_310, B_312]: (~r1_tarski(A_310, B_312) | r2_hidden('#skF_2'(A_310, B_312), B_312) | B_312=A_310)), inference(resolution, [status(thm)], [c_2747, c_10])).
% 9.52/3.86  tff(c_95, plain, (![A_51, B_52]: (r2_hidden('#skF_1'(A_51, B_52), A_51) | r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.52/3.86  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.52/3.86  tff(c_103, plain, (![A_51]: (r1_tarski(A_51, A_51))), inference(resolution, [status(thm)], [c_95, c_4])).
% 9.52/3.86  tff(c_50, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.52/3.86  tff(c_241, plain, (![A_87, B_88, C_89]: (k1_relset_1(A_87, B_88, C_89)=k1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.52/3.86  tff(c_250, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_241])).
% 9.52/3.86  tff(c_752, plain, (![B_139, A_140, C_141]: (k1_xboole_0=B_139 | k1_relset_1(A_140, B_139, C_141)=A_140 | ~v1_funct_2(C_141, A_140, B_139) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_140, B_139))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.52/3.86  tff(c_767, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_752])).
% 9.52/3.86  tff(c_774, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_250, c_767])).
% 9.52/3.86  tff(c_775, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_774])).
% 9.52/3.86  tff(c_56, plain, (![D_34]: (r2_hidden('#skF_7'(D_34), '#skF_4') | ~r2_hidden(D_34, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.52/3.86  tff(c_122, plain, (![C_57, B_58, A_59]: (r2_hidden(C_57, B_58) | ~r2_hidden(C_57, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.52/3.86  tff(c_128, plain, (![D_34, B_58]: (r2_hidden('#skF_7'(D_34), B_58) | ~r1_tarski('#skF_4', B_58) | ~r2_hidden(D_34, '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_122])).
% 9.52/3.86  tff(c_85, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.52/3.86  tff(c_94, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_85])).
% 9.52/3.86  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.52/3.86  tff(c_54, plain, (![D_34]: (k1_funct_1('#skF_6', '#skF_7'(D_34))=D_34 | ~r2_hidden(D_34, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.52/3.86  tff(c_408, plain, (![B_115, A_116]: (r2_hidden(k1_funct_1(B_115, A_116), k2_relat_1(B_115)) | ~r2_hidden(A_116, k1_relat_1(B_115)) | ~v1_funct_1(B_115) | ~v1_relat_1(B_115))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.52/3.86  tff(c_416, plain, (![D_34]: (r2_hidden(D_34, k2_relat_1('#skF_6')) | ~r2_hidden('#skF_7'(D_34), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(D_34, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_408])).
% 9.52/3.86  tff(c_479, plain, (![D_120]: (r2_hidden(D_120, k2_relat_1('#skF_6')) | ~r2_hidden('#skF_7'(D_120), k1_relat_1('#skF_6')) | ~r2_hidden(D_120, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_52, c_416])).
% 9.52/3.86  tff(c_484, plain, (![D_34]: (r2_hidden(D_34, k2_relat_1('#skF_6')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_6')) | ~r2_hidden(D_34, '#skF_5'))), inference(resolution, [status(thm)], [c_128, c_479])).
% 9.52/3.86  tff(c_593, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_484])).
% 9.52/3.86  tff(c_776, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_775, c_593])).
% 9.52/3.86  tff(c_781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_776])).
% 9.52/3.86  tff(c_782, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_774])).
% 9.52/3.86  tff(c_16, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.52/3.86  tff(c_804, plain, (![A_142]: (r1_tarski('#skF_5', A_142))), inference(demodulation, [status(thm), theory('equality')], [c_782, c_16])).
% 9.52/3.86  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.52/3.86  tff(c_165, plain, (![A_70, B_71, B_72]: (r2_hidden('#skF_1'(A_70, B_71), B_72) | ~r1_tarski(A_70, B_72) | r1_tarski(A_70, B_71))), inference(resolution, [status(thm)], [c_6, c_122])).
% 9.52/3.86  tff(c_24, plain, (![B_15, A_14]: (~r1_tarski(B_15, A_14) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.52/3.86  tff(c_177, plain, (![B_72, A_70, B_71]: (~r1_tarski(B_72, '#skF_1'(A_70, B_71)) | ~r1_tarski(A_70, B_72) | r1_tarski(A_70, B_71))), inference(resolution, [status(thm)], [c_165, c_24])).
% 9.52/3.86  tff(c_942, plain, (![A_156, B_157]: (~r1_tarski(A_156, '#skF_5') | r1_tarski(A_156, B_157))), inference(resolution, [status(thm)], [c_804, c_177])).
% 9.52/3.86  tff(c_953, plain, (![B_157]: (r1_tarski(k2_relat_1('#skF_6'), B_157))), inference(resolution, [status(thm)], [c_376, c_942])).
% 9.52/3.86  tff(c_799, plain, (![A_9]: (r1_tarski('#skF_5', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_782, c_16])).
% 9.52/3.86  tff(c_1014, plain, (![B_161, A_162]: (~r1_tarski(B_161, '#skF_2'(A_162, B_161)) | r2_hidden('#skF_3'(A_162, B_161), A_162) | B_161=A_162)), inference(resolution, [status(thm)], [c_305, c_24])).
% 9.52/3.86  tff(c_1023, plain, (![A_163]: (r2_hidden('#skF_3'(A_163, '#skF_5'), A_163) | A_163='#skF_5')), inference(resolution, [status(thm)], [c_799, c_1014])).
% 9.52/3.86  tff(c_1037, plain, (![A_164]: (~r1_tarski(A_164, '#skF_3'(A_164, '#skF_5')) | A_164='#skF_5')), inference(resolution, [status(thm)], [c_1023, c_24])).
% 9.52/3.86  tff(c_1041, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_953, c_1037])).
% 9.52/3.86  tff(c_1049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_220, c_1041])).
% 9.52/3.86  tff(c_1050, plain, (![D_34]: (r2_hidden(D_34, k2_relat_1('#skF_6')) | ~r2_hidden(D_34, '#skF_5'))), inference(splitRight, [status(thm)], [c_484])).
% 9.52/3.86  tff(c_157, plain, (![A_68, B_69]: (~r2_hidden('#skF_2'(A_68, B_69), A_68) | r2_hidden('#skF_3'(A_68, B_69), A_68) | B_69=A_68)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.52/3.86  tff(c_3282, plain, (![A_352, B_353, B_354]: (r2_hidden('#skF_3'(A_352, B_353), B_354) | ~r1_tarski(A_352, B_354) | ~r2_hidden('#skF_2'(A_352, B_353), A_352) | B_353=A_352)), inference(resolution, [status(thm)], [c_157, c_2])).
% 9.52/3.86  tff(c_13498, plain, (![B_990, B_991]: (r2_hidden('#skF_3'(k2_relat_1('#skF_6'), B_990), B_991) | ~r1_tarski(k2_relat_1('#skF_6'), B_991) | k2_relat_1('#skF_6')=B_990 | ~r2_hidden('#skF_2'(k2_relat_1('#skF_6'), B_990), '#skF_5'))), inference(resolution, [status(thm)], [c_1050, c_3282])).
% 9.52/3.86  tff(c_1057, plain, (![D_165]: (r2_hidden(D_165, k2_relat_1('#skF_6')) | ~r2_hidden(D_165, '#skF_5'))), inference(splitRight, [status(thm)], [c_484])).
% 9.52/3.86  tff(c_8, plain, (![A_6, B_7]: (~r2_hidden('#skF_2'(A_6, B_7), A_6) | ~r2_hidden('#skF_3'(A_6, B_7), B_7) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.52/3.86  tff(c_1075, plain, (![B_7]: (~r2_hidden('#skF_3'(k2_relat_1('#skF_6'), B_7), B_7) | k2_relat_1('#skF_6')=B_7 | ~r2_hidden('#skF_2'(k2_relat_1('#skF_6'), B_7), '#skF_5'))), inference(resolution, [status(thm)], [c_1057, c_8])).
% 9.52/3.86  tff(c_13535, plain, (![B_992]: (~r1_tarski(k2_relat_1('#skF_6'), B_992) | k2_relat_1('#skF_6')=B_992 | ~r2_hidden('#skF_2'(k2_relat_1('#skF_6'), B_992), '#skF_5'))), inference(resolution, [status(thm)], [c_13498, c_1075])).
% 9.52/3.86  tff(c_13561, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | k2_relat_1('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_2778, c_13535])).
% 9.52/3.86  tff(c_13574, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_376, c_13561])).
% 9.52/3.86  tff(c_13576, plain, $false, inference(negUnitSimplification, [status(thm)], [c_220, c_13574])).
% 9.52/3.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.52/3.86  
% 9.52/3.86  Inference rules
% 9.52/3.86  ----------------------
% 9.52/3.86  #Ref     : 0
% 9.52/3.86  #Sup     : 2911
% 9.52/3.86  #Fact    : 0
% 9.52/3.86  #Define  : 0
% 9.52/3.86  #Split   : 37
% 9.52/3.86  #Chain   : 0
% 9.52/3.86  #Close   : 0
% 9.52/3.86  
% 9.52/3.86  Ordering : KBO
% 9.52/3.86  
% 9.52/3.86  Simplification rules
% 9.52/3.86  ----------------------
% 9.52/3.86  #Subsume      : 936
% 9.52/3.86  #Demod        : 1655
% 9.52/3.86  #Tautology    : 531
% 9.52/3.86  #SimpNegUnit  : 49
% 9.52/3.86  #BackRed      : 209
% 9.52/3.86  
% 9.52/3.86  #Partial instantiations: 0
% 9.52/3.86  #Strategies tried      : 1
% 9.52/3.86  
% 9.52/3.86  Timing (in seconds)
% 9.52/3.86  ----------------------
% 9.52/3.86  Preprocessing        : 0.34
% 9.52/3.87  Parsing              : 0.18
% 9.52/3.87  CNF conversion       : 0.02
% 9.52/3.87  Main loop            : 2.70
% 9.52/3.87  Inferencing          : 0.72
% 9.52/3.87  Reduction            : 0.84
% 9.52/3.87  Demodulation         : 0.57
% 9.52/3.87  BG Simplification    : 0.07
% 9.52/3.87  Subsumption          : 0.86
% 9.52/3.87  Abstraction          : 0.10
% 9.52/3.87  MUC search           : 0.00
% 9.52/3.87  Cooper               : 0.00
% 9.52/3.87  Total                : 3.07
% 9.52/3.87  Index Insertion      : 0.00
% 9.52/3.87  Index Deletion       : 0.00
% 9.52/3.87  Index Matching       : 0.00
% 9.52/3.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
