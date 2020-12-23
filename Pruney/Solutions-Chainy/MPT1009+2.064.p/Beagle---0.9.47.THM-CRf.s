%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:51 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 183 expanded)
%              Number of leaves         :   39 (  79 expanded)
%              Depth                    :    9
%              Number of atoms          :  143 ( 392 expanded)
%              Number of equality atoms :   79 ( 149 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_72,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_124,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_128,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_124])).

tff(c_32,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k9_relat_1(B_15,A_14),k2_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    ! [A_17] :
      ( k1_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_135,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_128,c_38])).

tff(c_137,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_200,plain,(
    ! [B_83,A_84] :
      ( k1_tarski(k1_funct_1(B_83,A_84)) = k2_relat_1(B_83)
      | k1_tarski(A_84) != k1_relat_1(B_83)
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_50,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_227,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_50])).

tff(c_233,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_58,c_227])).

tff(c_235,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_233])).

tff(c_190,plain,(
    ! [C_78,A_79,B_80] :
      ( v4_relat_1(C_78,A_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_194,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_190])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(B_13),A_12)
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_263,plain,(
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

tff(c_291,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_6,c_263])).

tff(c_354,plain,(
    ! [A_118,B_119,D_120] :
      ( k2_tarski(A_118,B_119) = D_120
      | k2_tarski(A_118,B_119) = D_120
      | k2_tarski(A_118,B_119) = D_120
      | k1_tarski(A_118) = D_120
      | k1_tarski(B_119) = D_120
      | k1_tarski(A_118) = D_120
      | k1_tarski(A_118) = D_120
      | k1_xboole_0 = D_120
      | ~ r1_tarski(D_120,k2_tarski(A_118,B_119)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_291])).

tff(c_393,plain,(
    ! [A_121,B_122,B_123] :
      ( k2_tarski(A_121,B_122) = k1_relat_1(B_123)
      | k1_tarski(B_122) = k1_relat_1(B_123)
      | k1_tarski(A_121) = k1_relat_1(B_123)
      | k1_relat_1(B_123) = k1_xboole_0
      | ~ v4_relat_1(B_123,k2_tarski(A_121,B_122))
      | ~ v1_relat_1(B_123) ) ),
    inference(resolution,[status(thm)],[c_30,c_354])).

tff(c_396,plain,(
    ! [A_2,B_123] :
      ( k2_tarski(A_2,A_2) = k1_relat_1(B_123)
      | k1_tarski(A_2) = k1_relat_1(B_123)
      | k1_tarski(A_2) = k1_relat_1(B_123)
      | k1_relat_1(B_123) = k1_xboole_0
      | ~ v4_relat_1(B_123,k1_tarski(A_2))
      | ~ v1_relat_1(B_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_393])).

tff(c_403,plain,(
    ! [A_128,B_129] :
      ( k1_tarski(A_128) = k1_relat_1(B_129)
      | k1_tarski(A_128) = k1_relat_1(B_129)
      | k1_tarski(A_128) = k1_relat_1(B_129)
      | k1_relat_1(B_129) = k1_xboole_0
      | ~ v4_relat_1(B_129,k1_tarski(A_128))
      | ~ v1_relat_1(B_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_396])).

tff(c_409,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_194,c_403])).

tff(c_412,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_409])).

tff(c_414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_235,c_412])).

tff(c_416,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_419,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_54])).

tff(c_48,plain,(
    ! [A_26,B_27,C_28,D_29] :
      ( k7_relset_1(A_26,B_27,C_28,D_29) = k9_relat_1(C_28,D_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_503,plain,(
    ! [D_29] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_29) = k9_relat_1('#skF_4',D_29) ),
    inference(resolution,[status(thm)],[c_419,c_48])).

tff(c_415,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_638,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_415])).

tff(c_639,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_638])).

tff(c_657,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_639])).

tff(c_661,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_657])).

tff(c_662,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_667,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_2])).

tff(c_34,plain,(
    ! [A_16] : k9_relat_1(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_666,plain,(
    ! [A_16] : k9_relat_1('#skF_4',A_16) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_662,c_34])).

tff(c_779,plain,(
    ! [A_184,B_185,C_186,D_187] :
      ( k7_relset_1(A_184,B_185,C_186,D_187) = k9_relat_1(C_186,D_187)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_781,plain,(
    ! [D_187] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_187) = k9_relat_1('#skF_4',D_187) ),
    inference(resolution,[status(thm)],[c_54,c_779])).

tff(c_783,plain,(
    ! [D_187] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_187) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_666,c_781])).

tff(c_784,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_50])).

tff(c_787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_667,c_784])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.76  
% 3.45/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.76  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.45/1.76  
% 3.45/1.76  %Foreground sorts:
% 3.45/1.76  
% 3.45/1.76  
% 3.45/1.76  %Background operators:
% 3.45/1.76  
% 3.45/1.76  
% 3.45/1.76  %Foreground operators:
% 3.45/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.45/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.45/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.45/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.45/1.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.45/1.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.45/1.76  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.45/1.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.45/1.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.45/1.76  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.45/1.76  tff('#skF_2', type, '#skF_2': $i).
% 3.45/1.76  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.45/1.76  tff('#skF_3', type, '#skF_3': $i).
% 3.45/1.76  tff('#skF_1', type, '#skF_1': $i).
% 3.45/1.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.45/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.45/1.76  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.45/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.45/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.45/1.76  tff('#skF_4', type, '#skF_4': $i).
% 3.45/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.76  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.45/1.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.45/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.45/1.76  
% 3.79/1.78  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.79/1.78  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.79/1.78  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.79/1.78  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.79/1.78  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.79/1.78  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.79/1.78  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.79/1.78  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.79/1.78  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.79/1.78  tff(f_60, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 3.79/1.78  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.79/1.78  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.79/1.78  tff(f_72, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 3.79/1.78  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.79/1.78  tff(c_124, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.79/1.78  tff(c_128, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_124])).
% 3.79/1.78  tff(c_32, plain, (![B_15, A_14]: (r1_tarski(k9_relat_1(B_15, A_14), k2_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.79/1.78  tff(c_38, plain, (![A_17]: (k1_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.79/1.78  tff(c_135, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_128, c_38])).
% 3.79/1.78  tff(c_137, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_135])).
% 3.79/1.78  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.79/1.78  tff(c_200, plain, (![B_83, A_84]: (k1_tarski(k1_funct_1(B_83, A_84))=k2_relat_1(B_83) | k1_tarski(A_84)!=k1_relat_1(B_83) | ~v1_funct_1(B_83) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.79/1.78  tff(c_50, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.79/1.78  tff(c_227, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_200, c_50])).
% 3.79/1.78  tff(c_233, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_58, c_227])).
% 3.79/1.78  tff(c_235, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_233])).
% 3.79/1.78  tff(c_190, plain, (![C_78, A_79, B_80]: (v4_relat_1(C_78, A_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.79/1.78  tff(c_194, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_54, c_190])).
% 3.79/1.78  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.79/1.78  tff(c_30, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(B_13), A_12) | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.79/1.78  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.79/1.78  tff(c_263, plain, (![A_94, B_95, C_96, D_97]: (k1_enumset1(A_94, B_95, C_96)=D_97 | k2_tarski(A_94, C_96)=D_97 | k2_tarski(B_95, C_96)=D_97 | k2_tarski(A_94, B_95)=D_97 | k1_tarski(C_96)=D_97 | k1_tarski(B_95)=D_97 | k1_tarski(A_94)=D_97 | k1_xboole_0=D_97 | ~r1_tarski(D_97, k1_enumset1(A_94, B_95, C_96)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.79/1.78  tff(c_291, plain, (![A_3, B_4, D_97]: (k1_enumset1(A_3, A_3, B_4)=D_97 | k2_tarski(A_3, B_4)=D_97 | k2_tarski(A_3, B_4)=D_97 | k2_tarski(A_3, A_3)=D_97 | k1_tarski(B_4)=D_97 | k1_tarski(A_3)=D_97 | k1_tarski(A_3)=D_97 | k1_xboole_0=D_97 | ~r1_tarski(D_97, k2_tarski(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_263])).
% 3.79/1.78  tff(c_354, plain, (![A_118, B_119, D_120]: (k2_tarski(A_118, B_119)=D_120 | k2_tarski(A_118, B_119)=D_120 | k2_tarski(A_118, B_119)=D_120 | k1_tarski(A_118)=D_120 | k1_tarski(B_119)=D_120 | k1_tarski(A_118)=D_120 | k1_tarski(A_118)=D_120 | k1_xboole_0=D_120 | ~r1_tarski(D_120, k2_tarski(A_118, B_119)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_291])).
% 3.79/1.78  tff(c_393, plain, (![A_121, B_122, B_123]: (k2_tarski(A_121, B_122)=k1_relat_1(B_123) | k1_tarski(B_122)=k1_relat_1(B_123) | k1_tarski(A_121)=k1_relat_1(B_123) | k1_relat_1(B_123)=k1_xboole_0 | ~v4_relat_1(B_123, k2_tarski(A_121, B_122)) | ~v1_relat_1(B_123))), inference(resolution, [status(thm)], [c_30, c_354])).
% 3.79/1.78  tff(c_396, plain, (![A_2, B_123]: (k2_tarski(A_2, A_2)=k1_relat_1(B_123) | k1_tarski(A_2)=k1_relat_1(B_123) | k1_tarski(A_2)=k1_relat_1(B_123) | k1_relat_1(B_123)=k1_xboole_0 | ~v4_relat_1(B_123, k1_tarski(A_2)) | ~v1_relat_1(B_123))), inference(superposition, [status(thm), theory('equality')], [c_4, c_393])).
% 3.79/1.78  tff(c_403, plain, (![A_128, B_129]: (k1_tarski(A_128)=k1_relat_1(B_129) | k1_tarski(A_128)=k1_relat_1(B_129) | k1_tarski(A_128)=k1_relat_1(B_129) | k1_relat_1(B_129)=k1_xboole_0 | ~v4_relat_1(B_129, k1_tarski(A_128)) | ~v1_relat_1(B_129))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_396])).
% 3.79/1.78  tff(c_409, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_194, c_403])).
% 3.79/1.78  tff(c_412, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_128, c_409])).
% 3.79/1.78  tff(c_414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_235, c_412])).
% 3.79/1.78  tff(c_416, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_233])).
% 3.79/1.78  tff(c_419, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_416, c_54])).
% 3.79/1.78  tff(c_48, plain, (![A_26, B_27, C_28, D_29]: (k7_relset_1(A_26, B_27, C_28, D_29)=k9_relat_1(C_28, D_29) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.79/1.78  tff(c_503, plain, (![D_29]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_29)=k9_relat_1('#skF_4', D_29))), inference(resolution, [status(thm)], [c_419, c_48])).
% 3.79/1.78  tff(c_415, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_233])).
% 3.79/1.78  tff(c_638, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_416, c_415])).
% 3.79/1.78  tff(c_639, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_638])).
% 3.79/1.78  tff(c_657, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_639])).
% 3.79/1.78  tff(c_661, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_657])).
% 3.79/1.78  tff(c_662, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_135])).
% 3.79/1.78  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.79/1.78  tff(c_667, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_662, c_2])).
% 3.79/1.78  tff(c_34, plain, (![A_16]: (k9_relat_1(k1_xboole_0, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.79/1.78  tff(c_666, plain, (![A_16]: (k9_relat_1('#skF_4', A_16)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_662, c_662, c_34])).
% 3.79/1.78  tff(c_779, plain, (![A_184, B_185, C_186, D_187]: (k7_relset_1(A_184, B_185, C_186, D_187)=k9_relat_1(C_186, D_187) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.79/1.78  tff(c_781, plain, (![D_187]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_187)=k9_relat_1('#skF_4', D_187))), inference(resolution, [status(thm)], [c_54, c_779])).
% 3.79/1.78  tff(c_783, plain, (![D_187]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_187)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_666, c_781])).
% 3.79/1.78  tff(c_784, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_783, c_50])).
% 3.79/1.78  tff(c_787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_667, c_784])).
% 3.79/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.78  
% 3.79/1.78  Inference rules
% 3.79/1.78  ----------------------
% 3.79/1.78  #Ref     : 0
% 3.79/1.78  #Sup     : 149
% 3.79/1.78  #Fact    : 0
% 3.79/1.78  #Define  : 0
% 3.79/1.78  #Split   : 3
% 3.79/1.78  #Chain   : 0
% 3.79/1.78  #Close   : 0
% 3.79/1.78  
% 3.79/1.78  Ordering : KBO
% 3.79/1.78  
% 3.79/1.78  Simplification rules
% 3.79/1.78  ----------------------
% 3.79/1.78  #Subsume      : 14
% 3.79/1.78  #Demod        : 112
% 3.79/1.78  #Tautology    : 91
% 3.79/1.78  #SimpNegUnit  : 4
% 3.79/1.78  #BackRed      : 13
% 3.79/1.78  
% 3.79/1.78  #Partial instantiations: 0
% 3.79/1.78  #Strategies tried      : 1
% 3.79/1.78  
% 3.79/1.78  Timing (in seconds)
% 3.79/1.78  ----------------------
% 3.84/1.78  Preprocessing        : 0.44
% 3.84/1.78  Parsing              : 0.23
% 3.84/1.78  CNF conversion       : 0.02
% 3.84/1.78  Main loop            : 0.51
% 3.84/1.78  Inferencing          : 0.20
% 3.84/1.78  Reduction            : 0.17
% 3.84/1.78  Demodulation         : 0.13
% 3.84/1.78  BG Simplification    : 0.03
% 3.84/1.78  Subsumption          : 0.08
% 3.84/1.78  Abstraction          : 0.03
% 3.84/1.78  MUC search           : 0.00
% 3.84/1.78  Cooper               : 0.00
% 3.84/1.78  Total                : 0.99
% 3.84/1.78  Index Insertion      : 0.00
% 3.84/1.78  Index Deletion       : 0.00
% 3.84/1.78  Index Matching       : 0.00
% 3.84/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
