%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:52 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 293 expanded)
%              Number of leaves         :   41 ( 119 expanded)
%              Depth                    :    8
%              Number of atoms          :  147 ( 648 expanded)
%              Number of equality atoms :   84 ( 228 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_66,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_128,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_132,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_128])).

tff(c_28,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k9_relat_1(B_13,A_12),k2_relat_1(B_13))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_36,plain,(
    ! [A_17] :
      ( k1_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_139,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_132,c_36])).

tff(c_141,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_225,plain,(
    ! [B_90,A_91] :
      ( k1_tarski(k1_funct_1(B_90,A_91)) = k2_relat_1(B_90)
      | k1_tarski(A_91) != k1_relat_1(B_90)
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_211,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( k7_relset_1(A_85,B_86,C_87,D_88) = k9_relat_1(C_87,D_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_214,plain,(
    ! [D_88] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_88) = k9_relat_1('#skF_4',D_88) ),
    inference(resolution,[status(thm)],[c_54,c_211])).

tff(c_50,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_215,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_50])).

tff(c_231,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_215])).

tff(c_258,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_58,c_231])).

tff(c_260,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_185,plain,(
    ! [C_77,A_78,B_79] :
      ( v4_relat_1(C_77,A_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_189,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_185])).

tff(c_190,plain,(
    ! [B_80,A_81] :
      ( k7_relat_1(B_80,A_81) = B_80
      | ~ v4_relat_1(B_80,A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_193,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_189,c_190])).

tff(c_196,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_193])).

tff(c_38,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_19,A_18)),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_200,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_38])).

tff(c_204,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_200])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_265,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( k1_enumset1(A_94,B_95,C_96) = D_97
      | k2_tarski(A_94,C_96) = D_97
      | k2_tarski(B_95,C_96) = D_97
      | k2_tarski(A_94,B_95) = D_97
      | k1_tarski(C_96) = D_97
      | k1_tarski(B_95) = D_97
      | k1_tarski(A_94) = D_97
      | k1_xboole_0 = D_97
      | ~ r1_tarski(D_97,k1_enumset1(A_94,B_95,C_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_293,plain,(
    ! [A_3,B_4,D_97] :
      ( k1_enumset1(A_3,A_3,B_4) = D_97
      | k2_tarski(A_3,B_4) = D_97
      | k2_tarski(A_3,B_4) = D_97
      | k2_tarski(A_3,A_3) = D_97
      | k1_tarski(B_4) = D_97
      | k1_tarski(A_3) = D_97
      | k1_tarski(A_3) = D_97
      | k1_xboole_0 = D_97
      | ~ r1_tarski(D_97,k2_tarski(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_265])).

tff(c_360,plain,(
    ! [A_120,B_121,D_122] :
      ( k2_tarski(A_120,B_121) = D_122
      | k2_tarski(A_120,B_121) = D_122
      | k2_tarski(A_120,B_121) = D_122
      | k1_tarski(A_120) = D_122
      | k1_tarski(B_121) = D_122
      | k1_tarski(A_120) = D_122
      | k1_tarski(A_120) = D_122
      | k1_xboole_0 = D_122
      | ~ r1_tarski(D_122,k2_tarski(A_120,B_121)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_293])).

tff(c_382,plain,(
    ! [A_2,D_122] :
      ( k2_tarski(A_2,A_2) = D_122
      | k2_tarski(A_2,A_2) = D_122
      | k2_tarski(A_2,A_2) = D_122
      | k1_tarski(A_2) = D_122
      | k1_tarski(A_2) = D_122
      | k1_tarski(A_2) = D_122
      | k1_tarski(A_2) = D_122
      | k1_xboole_0 = D_122
      | ~ r1_tarski(D_122,k1_tarski(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_360])).

tff(c_446,plain,(
    ! [A_127,D_128] :
      ( k1_tarski(A_127) = D_128
      | k1_tarski(A_127) = D_128
      | k1_tarski(A_127) = D_128
      | k1_tarski(A_127) = D_128
      | k1_tarski(A_127) = D_128
      | k1_tarski(A_127) = D_128
      | k1_tarski(A_127) = D_128
      | k1_xboole_0 = D_128
      | ~ r1_tarski(D_128,k1_tarski(A_127)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_4,c_382])).

tff(c_455,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_204,c_446])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_260,c_260,c_260,c_260,c_260,c_260,c_260,c_455])).

tff(c_472,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_579,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_472])).

tff(c_583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_579])).

tff(c_584,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_589,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_2])).

tff(c_30,plain,(
    ! [A_14] : k9_relat_1(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_588,plain,(
    ! [A_14] : k9_relat_1('#skF_4',A_14) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_584,c_30])).

tff(c_692,plain,(
    ! [A_160,B_161,C_162,D_163] :
      ( k7_relset_1(A_160,B_161,C_162,D_163) = k9_relat_1(C_162,D_163)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_694,plain,(
    ! [D_163] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_163) = k9_relat_1('#skF_4',D_163) ),
    inference(resolution,[status(thm)],[c_54,c_692])).

tff(c_696,plain,(
    ! [D_163] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_163) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_694])).

tff(c_697,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_50])).

tff(c_700,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_697])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:59:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.44  
% 2.91/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.91/1.44  
% 2.91/1.44  %Foreground sorts:
% 2.91/1.44  
% 2.91/1.44  
% 2.91/1.44  %Background operators:
% 2.91/1.44  
% 2.91/1.44  
% 2.91/1.44  %Foreground operators:
% 2.91/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.91/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.91/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.91/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.91/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.91/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.91/1.44  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.91/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.91/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.91/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.91/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.91/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.91/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.91/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.91/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.91/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.91/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.91/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.91/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.91/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.91/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.91/1.44  
% 3.20/1.46  tff(f_118, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.20/1.46  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.20/1.46  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.20/1.46  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.20/1.46  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.20/1.46  tff(f_106, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.20/1.46  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.20/1.46  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.20/1.46  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.20/1.46  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.20/1.46  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.20/1.46  tff(f_60, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 3.20/1.46  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.20/1.46  tff(f_66, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 3.20/1.46  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.20/1.46  tff(c_128, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.20/1.46  tff(c_132, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_128])).
% 3.20/1.46  tff(c_28, plain, (![B_13, A_12]: (r1_tarski(k9_relat_1(B_13, A_12), k2_relat_1(B_13)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.20/1.46  tff(c_36, plain, (![A_17]: (k1_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.20/1.46  tff(c_139, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_132, c_36])).
% 3.20/1.46  tff(c_141, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_139])).
% 3.20/1.46  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.20/1.46  tff(c_225, plain, (![B_90, A_91]: (k1_tarski(k1_funct_1(B_90, A_91))=k2_relat_1(B_90) | k1_tarski(A_91)!=k1_relat_1(B_90) | ~v1_funct_1(B_90) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.20/1.46  tff(c_211, plain, (![A_85, B_86, C_87, D_88]: (k7_relset_1(A_85, B_86, C_87, D_88)=k9_relat_1(C_87, D_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.20/1.46  tff(c_214, plain, (![D_88]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_88)=k9_relat_1('#skF_4', D_88))), inference(resolution, [status(thm)], [c_54, c_211])).
% 3.20/1.46  tff(c_50, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.20/1.46  tff(c_215, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_50])).
% 3.20/1.46  tff(c_231, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_225, c_215])).
% 3.20/1.46  tff(c_258, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_58, c_231])).
% 3.20/1.46  tff(c_260, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_258])).
% 3.20/1.46  tff(c_185, plain, (![C_77, A_78, B_79]: (v4_relat_1(C_77, A_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.20/1.46  tff(c_189, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_54, c_185])).
% 3.20/1.46  tff(c_190, plain, (![B_80, A_81]: (k7_relat_1(B_80, A_81)=B_80 | ~v4_relat_1(B_80, A_81) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.20/1.46  tff(c_193, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_189, c_190])).
% 3.20/1.46  tff(c_196, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_193])).
% 3.20/1.46  tff(c_38, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(k7_relat_1(B_19, A_18)), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.20/1.46  tff(c_200, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_1')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_196, c_38])).
% 3.20/1.46  tff(c_204, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_200])).
% 3.20/1.46  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.20/1.46  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.46  tff(c_265, plain, (![A_94, B_95, C_96, D_97]: (k1_enumset1(A_94, B_95, C_96)=D_97 | k2_tarski(A_94, C_96)=D_97 | k2_tarski(B_95, C_96)=D_97 | k2_tarski(A_94, B_95)=D_97 | k1_tarski(C_96)=D_97 | k1_tarski(B_95)=D_97 | k1_tarski(A_94)=D_97 | k1_xboole_0=D_97 | ~r1_tarski(D_97, k1_enumset1(A_94, B_95, C_96)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.20/1.46  tff(c_293, plain, (![A_3, B_4, D_97]: (k1_enumset1(A_3, A_3, B_4)=D_97 | k2_tarski(A_3, B_4)=D_97 | k2_tarski(A_3, B_4)=D_97 | k2_tarski(A_3, A_3)=D_97 | k1_tarski(B_4)=D_97 | k1_tarski(A_3)=D_97 | k1_tarski(A_3)=D_97 | k1_xboole_0=D_97 | ~r1_tarski(D_97, k2_tarski(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_265])).
% 3.20/1.46  tff(c_360, plain, (![A_120, B_121, D_122]: (k2_tarski(A_120, B_121)=D_122 | k2_tarski(A_120, B_121)=D_122 | k2_tarski(A_120, B_121)=D_122 | k1_tarski(A_120)=D_122 | k1_tarski(B_121)=D_122 | k1_tarski(A_120)=D_122 | k1_tarski(A_120)=D_122 | k1_xboole_0=D_122 | ~r1_tarski(D_122, k2_tarski(A_120, B_121)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_293])).
% 3.20/1.46  tff(c_382, plain, (![A_2, D_122]: (k2_tarski(A_2, A_2)=D_122 | k2_tarski(A_2, A_2)=D_122 | k2_tarski(A_2, A_2)=D_122 | k1_tarski(A_2)=D_122 | k1_tarski(A_2)=D_122 | k1_tarski(A_2)=D_122 | k1_tarski(A_2)=D_122 | k1_xboole_0=D_122 | ~r1_tarski(D_122, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_360])).
% 3.20/1.46  tff(c_446, plain, (![A_127, D_128]: (k1_tarski(A_127)=D_128 | k1_tarski(A_127)=D_128 | k1_tarski(A_127)=D_128 | k1_tarski(A_127)=D_128 | k1_tarski(A_127)=D_128 | k1_tarski(A_127)=D_128 | k1_tarski(A_127)=D_128 | k1_xboole_0=D_128 | ~r1_tarski(D_128, k1_tarski(A_127)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_4, c_382])).
% 3.20/1.46  tff(c_455, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_204, c_446])).
% 3.20/1.46  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_141, c_260, c_260, c_260, c_260, c_260, c_260, c_260, c_455])).
% 3.20/1.46  tff(c_472, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_258])).
% 3.20/1.46  tff(c_579, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_472])).
% 3.20/1.46  tff(c_583, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_579])).
% 3.20/1.46  tff(c_584, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_139])).
% 3.20/1.46  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.20/1.46  tff(c_589, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_584, c_2])).
% 3.20/1.46  tff(c_30, plain, (![A_14]: (k9_relat_1(k1_xboole_0, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.20/1.46  tff(c_588, plain, (![A_14]: (k9_relat_1('#skF_4', A_14)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_584, c_584, c_30])).
% 3.20/1.46  tff(c_692, plain, (![A_160, B_161, C_162, D_163]: (k7_relset_1(A_160, B_161, C_162, D_163)=k9_relat_1(C_162, D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.20/1.46  tff(c_694, plain, (![D_163]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_163)=k9_relat_1('#skF_4', D_163))), inference(resolution, [status(thm)], [c_54, c_692])).
% 3.20/1.46  tff(c_696, plain, (![D_163]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_163)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_588, c_694])).
% 3.20/1.46  tff(c_697, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_696, c_50])).
% 3.20/1.46  tff(c_700, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_589, c_697])).
% 3.20/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.46  
% 3.20/1.46  Inference rules
% 3.20/1.46  ----------------------
% 3.20/1.46  #Ref     : 0
% 3.20/1.46  #Sup     : 134
% 3.20/1.46  #Fact    : 7
% 3.20/1.46  #Define  : 0
% 3.20/1.46  #Split   : 3
% 3.20/1.46  #Chain   : 0
% 3.20/1.46  #Close   : 0
% 3.20/1.46  
% 3.20/1.46  Ordering : KBO
% 3.20/1.46  
% 3.20/1.46  Simplification rules
% 3.20/1.46  ----------------------
% 3.20/1.46  #Subsume      : 12
% 3.20/1.46  #Demod        : 85
% 3.20/1.46  #Tautology    : 79
% 3.20/1.46  #SimpNegUnit  : 1
% 3.20/1.46  #BackRed      : 13
% 3.20/1.46  
% 3.20/1.46  #Partial instantiations: 0
% 3.20/1.46  #Strategies tried      : 1
% 3.20/1.46  
% 3.20/1.46  Timing (in seconds)
% 3.20/1.46  ----------------------
% 3.20/1.46  Preprocessing        : 0.33
% 3.20/1.46  Parsing              : 0.18
% 3.20/1.46  CNF conversion       : 0.02
% 3.20/1.46  Main loop            : 0.37
% 3.20/1.46  Inferencing          : 0.14
% 3.20/1.46  Reduction            : 0.12
% 3.20/1.46  Demodulation         : 0.09
% 3.20/1.46  BG Simplification    : 0.02
% 3.20/1.46  Subsumption          : 0.06
% 3.20/1.46  Abstraction          : 0.02
% 3.20/1.46  MUC search           : 0.00
% 3.20/1.46  Cooper               : 0.00
% 3.20/1.46  Total                : 0.73
% 3.20/1.46  Index Insertion      : 0.00
% 3.20/1.46  Index Deletion       : 0.00
% 3.20/1.46  Index Matching       : 0.00
% 3.20/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
