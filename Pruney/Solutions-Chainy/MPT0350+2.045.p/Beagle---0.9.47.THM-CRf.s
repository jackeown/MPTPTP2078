%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:31 EST 2020

% Result     : Theorem 24.17s
% Output     : CNFRefutation 24.26s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 931 expanded)
%              Number of leaves         :   53 ( 340 expanded)
%              Depth                    :   24
%              Number of atoms          :  168 (1365 expanded)
%              Number of equality atoms :  106 ( 655 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_130,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_68,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_56,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_112,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_119,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_116,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_92,plain,(
    ! [A_70] : k2_subset_1(A_70) = A_70 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_102,plain,(
    k4_subset_1('#skF_8','#skF_9',k3_subset_1('#skF_8','#skF_9')) != k2_subset_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_105,plain,(
    k4_subset_1('#skF_8','#skF_9',k3_subset_1('#skF_8','#skF_9')) != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_102])).

tff(c_52,plain,(
    ! [A_28] : k5_xboole_0(A_28,k1_xboole_0) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_42,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_5'(A_17),A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_406,plain,(
    ! [D_111,B_112,A_113] :
      ( r2_hidden(D_111,B_112)
      | ~ r2_hidden(D_111,k3_xboole_0(A_113,B_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_61462,plain,(
    ! [A_1129,B_1130] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_1129,B_1130)),B_1130)
      | k3_xboole_0(A_1129,B_1130) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_406])).

tff(c_440,plain,(
    ! [D_115,A_116,B_117] :
      ( r2_hidden(D_115,A_116)
      | ~ r2_hidden(D_115,k3_xboole_0(A_116,B_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_60980,plain,(
    ! [A_1124,B_1125] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_1124,B_1125)),A_1124)
      | k3_xboole_0(A_1124,B_1125) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_440])).

tff(c_104,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_11933,plain,(
    ! [A_414,B_415] :
      ( k4_xboole_0(A_414,B_415) = k3_subset_1(A_414,B_415)
      | ~ m1_subset_1(B_415,k1_zfmisc_1(A_414)) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_11957,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k3_subset_1('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_104,c_11933])).

tff(c_26,plain,(
    ! [D_16,B_12,A_11] :
      ( ~ r2_hidden(D_16,B_12)
      | ~ r2_hidden(D_16,k4_xboole_0(A_11,B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_11965,plain,(
    ! [D_16] :
      ( ~ r2_hidden(D_16,'#skF_9')
      | ~ r2_hidden(D_16,k3_subset_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11957,c_26])).

tff(c_61128,plain,(
    ! [B_1125] :
      ( ~ r2_hidden('#skF_5'(k3_xboole_0(k3_subset_1('#skF_8','#skF_9'),B_1125)),'#skF_9')
      | k3_xboole_0(k3_subset_1('#skF_8','#skF_9'),B_1125) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_60980,c_11965])).

tff(c_61606,plain,(
    k3_xboole_0(k3_subset_1('#skF_8','#skF_9'),'#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61462,c_61128])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_61702,plain,(
    k3_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_61606,c_2])).

tff(c_98,plain,(
    ! [A_75] : ~ v1_xboole_0(k1_zfmisc_1(A_75)) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_319,plain,(
    ! [B_105,A_106] :
      ( r2_hidden(B_105,A_106)
      | ~ m1_subset_1(B_105,A_106)
      | v1_xboole_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_70,plain,(
    ! [C_65,A_61] :
      ( r1_tarski(C_65,A_61)
      | ~ r2_hidden(C_65,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_323,plain,(
    ! [B_105,A_61] :
      ( r1_tarski(B_105,A_61)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_61))
      | v1_xboole_0(k1_zfmisc_1(A_61)) ) ),
    inference(resolution,[status(thm)],[c_319,c_70])).

tff(c_327,plain,(
    ! [B_107,A_108] :
      ( r1_tarski(B_107,A_108)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_108)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_323])).

tff(c_336,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_104,c_327])).

tff(c_48,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_340,plain,(
    k3_xboole_0('#skF_9','#skF_8') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_336,c_48])).

tff(c_11338,plain,(
    ! [A_401,B_402] : k5_xboole_0(k5_xboole_0(A_401,B_402),k3_xboole_0(A_401,B_402)) = k2_xboole_0(A_401,B_402) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_11540,plain,(
    ! [A_406] : k5_xboole_0(A_406,k3_xboole_0(A_406,k1_xboole_0)) = k2_xboole_0(A_406,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_11338])).

tff(c_44,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_11560,plain,(
    ! [A_406] : k4_xboole_0(A_406,k1_xboole_0) = k2_xboole_0(A_406,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11540,c_44])).

tff(c_286,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k3_xboole_0(A_102,B_103)) = k4_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_302,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_286])).

tff(c_375,plain,(
    k3_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_2])).

tff(c_55669,plain,(
    ! [A_1005,B_1006,C_1007] : k5_xboole_0(k3_xboole_0(A_1005,B_1006),k3_xboole_0(C_1007,B_1006)) = k3_xboole_0(k5_xboole_0(A_1005,C_1007),B_1006) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_55752,plain,(
    ! [C_1007] : k5_xboole_0('#skF_9',k3_xboole_0(C_1007,'#skF_9')) = k3_xboole_0(k5_xboole_0('#skF_8',C_1007),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_55669])).

tff(c_55918,plain,(
    ! [C_1013] : k3_xboole_0('#skF_9',k5_xboole_0('#skF_8',C_1013)) = k4_xboole_0('#skF_9',C_1013) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_302,c_55752])).

tff(c_55991,plain,(
    k4_xboole_0('#skF_9',k1_xboole_0) = k3_xboole_0('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_55918])).

tff(c_55997,plain,(
    k2_xboole_0('#skF_9',k1_xboole_0) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_11560,c_55991])).

tff(c_11613,plain,(
    ! [A_409] : k4_xboole_0(A_409,k1_xboole_0) = k2_xboole_0(A_409,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11540,c_44])).

tff(c_50,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_11635,plain,(
    ! [A_409] : k4_xboole_0(A_409,k2_xboole_0(A_409,k1_xboole_0)) = k3_xboole_0(A_409,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11613,c_50])).

tff(c_56075,plain,(
    k4_xboole_0('#skF_9','#skF_9') = k3_xboole_0('#skF_9',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_55997,c_11635])).

tff(c_391,plain,(
    k5_xboole_0('#skF_8','#skF_9') = k4_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_44])).

tff(c_11958,plain,(
    k5_xboole_0('#skF_8','#skF_9') = k3_subset_1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11957,c_391])).

tff(c_55955,plain,(
    k3_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = k4_xboole_0('#skF_9','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_11958,c_55918])).

tff(c_56407,plain,(
    k3_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = k3_xboole_0('#skF_9',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56075,c_55955])).

tff(c_61783,plain,(
    k3_xboole_0('#skF_9',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61702,c_56407])).

tff(c_372,plain,(
    k5_xboole_0('#skF_9','#skF_9') = k4_xboole_0('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_44])).

tff(c_11414,plain,(
    ! [A_28] : k5_xboole_0(A_28,k3_xboole_0(A_28,k1_xboole_0)) = k2_xboole_0(A_28,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_11338])).

tff(c_56432,plain,(
    k5_xboole_0('#skF_9',k3_xboole_0('#skF_9',k1_xboole_0)) = k4_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56407,c_44])).

tff(c_56438,plain,(
    k4_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55997,c_11414,c_56432])).

tff(c_11971,plain,(
    k4_xboole_0('#skF_8',k3_subset_1('#skF_8','#skF_9')) = k3_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_11957,c_50])).

tff(c_11974,plain,(
    k4_xboole_0('#skF_8',k3_subset_1('#skF_8','#skF_9')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_11971])).

tff(c_11988,plain,(
    k3_xboole_0('#skF_8',k3_subset_1('#skF_8','#skF_9')) = k4_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_11974,c_50])).

tff(c_11991,plain,(
    k3_xboole_0('#skF_8',k3_subset_1('#skF_8','#skF_9')) = k3_subset_1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11957,c_11988])).

tff(c_56277,plain,(
    k5_xboole_0('#skF_8',k3_subset_1('#skF_8','#skF_9')) = k4_xboole_0('#skF_8',k3_subset_1('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11991,c_44])).

tff(c_56282,plain,(
    k5_xboole_0('#skF_8',k3_subset_1('#skF_8','#skF_9')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11974,c_56277])).

tff(c_55805,plain,(
    ! [C_1007] : k3_xboole_0('#skF_9',k5_xboole_0('#skF_8',C_1007)) = k4_xboole_0('#skF_9',C_1007) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_302,c_55752])).

tff(c_56287,plain,(
    k4_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = k3_xboole_0('#skF_9','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_56282,c_55805])).

tff(c_56480,plain,(
    k3_xboole_0('#skF_9','#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56438,c_56287])).

tff(c_56496,plain,(
    k5_xboole_0('#skF_9','#skF_9') = k4_xboole_0('#skF_9','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_56480,c_302])).

tff(c_56511,plain,(
    k4_xboole_0('#skF_9','#skF_8') = k3_xboole_0('#skF_9',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56075,c_372,c_56496])).

tff(c_61897,plain,(
    k4_xboole_0('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61783,c_56511])).

tff(c_54,plain,(
    ! [A_29,B_30,C_31] : k5_xboole_0(k5_xboole_0(A_29,B_30),C_31) = k5_xboole_0(A_29,k5_xboole_0(B_30,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_11350,plain,(
    ! [A_401,B_402] : k5_xboole_0(A_401,k5_xboole_0(B_402,k3_xboole_0(A_401,B_402))) = k2_xboole_0(A_401,B_402) ),
    inference(superposition,[status(thm),theory(equality)],[c_11338,c_54])).

tff(c_11417,plain,(
    ! [A_401,B_402] : k5_xboole_0(A_401,k4_xboole_0(B_402,A_401)) = k2_xboole_0(A_401,B_402) ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_11350])).

tff(c_62321,plain,(
    k5_xboole_0('#skF_8',k1_xboole_0) = k2_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_61897,c_11417])).

tff(c_62335,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_62321])).

tff(c_11962,plain,(
    k5_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = k2_xboole_0('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_11957,c_11417])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_11384,plain,(
    k5_xboole_0(k5_xboole_0('#skF_8','#skF_9'),'#skF_9') = k2_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_11338])).

tff(c_11423,plain,(
    k5_xboole_0('#skF_9',k4_xboole_0('#skF_8','#skF_9')) = k2_xboole_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_391,c_11384])).

tff(c_56118,plain,(
    k2_xboole_0('#skF_9','#skF_8') = k2_xboole_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11962,c_11957,c_11423])).

tff(c_56121,plain,(
    k5_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = k2_xboole_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56118,c_11962])).

tff(c_126,plain,(
    ! [B_83,A_84] : k5_xboole_0(B_83,A_84) = k5_xboole_0(A_84,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_142,plain,(
    ! [A_84] : k5_xboole_0(k1_xboole_0,A_84) = A_84 ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_52])).

tff(c_11175,plain,(
    ! [A_393,B_394,C_395] : k5_xboole_0(k5_xboole_0(A_393,B_394),C_395) = k5_xboole_0(A_393,k5_xboole_0(B_394,C_395)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_58363,plain,(
    ! [B_1080,A_1081,B_1082] : k5_xboole_0(B_1080,k5_xboole_0(A_1081,B_1082)) = k5_xboole_0(A_1081,k5_xboole_0(B_1082,B_1080)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_11175])).

tff(c_58656,plain,(
    ! [A_1083,B_1084] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_1083,B_1084)) = k5_xboole_0(B_1084,A_1083) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_58363])).

tff(c_58745,plain,(
    ! [B_402,A_401] : k5_xboole_0(k4_xboole_0(B_402,A_401),A_401) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_401,B_402)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11417,c_58656])).

tff(c_59446,plain,(
    ! [B_1097,A_1098] : k5_xboole_0(k4_xboole_0(B_1097,A_1098),A_1098) = k2_xboole_0(A_1098,B_1097) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_58745])).

tff(c_59531,plain,(
    k5_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = k2_xboole_0(k3_subset_1('#skF_8','#skF_9'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_56438,c_59446])).

tff(c_59596,plain,(
    k2_xboole_0(k3_subset_1('#skF_8','#skF_9'),'#skF_9') = k2_xboole_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56121,c_59531])).

tff(c_96,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(k3_subset_1(A_73,B_74),k1_zfmisc_1(A_73))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_56536,plain,(
    ! [A_1038,B_1039,C_1040] :
      ( k4_subset_1(A_1038,B_1039,C_1040) = k2_xboole_0(B_1039,C_1040)
      | ~ m1_subset_1(C_1040,k1_zfmisc_1(A_1038))
      | ~ m1_subset_1(B_1039,k1_zfmisc_1(A_1038)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_56572,plain,(
    ! [B_1041] :
      ( k4_subset_1('#skF_8',B_1041,'#skF_9') = k2_xboole_0(B_1041,'#skF_9')
      | ~ m1_subset_1(B_1041,k1_zfmisc_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_104,c_56536])).

tff(c_57205,plain,(
    ! [B_1053] :
      ( k4_subset_1('#skF_8',k3_subset_1('#skF_8',B_1053),'#skF_9') = k2_xboole_0(k3_subset_1('#skF_8',B_1053),'#skF_9')
      | ~ m1_subset_1(B_1053,k1_zfmisc_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_96,c_56572])).

tff(c_57231,plain,(
    k4_subset_1('#skF_8',k3_subset_1('#skF_8','#skF_9'),'#skF_9') = k2_xboole_0(k3_subset_1('#skF_8','#skF_9'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_104,c_57205])).

tff(c_60339,plain,(
    k4_subset_1('#skF_8',k3_subset_1('#skF_8','#skF_9'),'#skF_9') = k2_xboole_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59596,c_57231])).

tff(c_62504,plain,(
    k4_subset_1('#skF_8',k3_subset_1('#skF_8','#skF_9'),'#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62335,c_60339])).

tff(c_60468,plain,(
    ! [B_1116,A_1117] : k5_xboole_0(k5_xboole_0(B_1116,A_1117),k3_xboole_0(A_1117,B_1116)) = k2_xboole_0(A_1117,B_1116) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_11338])).

tff(c_60496,plain,(
    ! [B_1116,A_1117] : k5_xboole_0(B_1116,k5_xboole_0(A_1117,k3_xboole_0(A_1117,B_1116))) = k2_xboole_0(A_1117,B_1116) ),
    inference(superposition,[status(thm),theory(equality)],[c_60468,c_54])).

tff(c_60710,plain,(
    ! [B_1116,A_1117] : k2_xboole_0(B_1116,A_1117) = k2_xboole_0(A_1117,B_1116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11417,c_44,c_60496])).

tff(c_56592,plain,(
    ! [B_74] :
      ( k4_subset_1('#skF_8',k3_subset_1('#skF_8',B_74),'#skF_9') = k2_xboole_0(k3_subset_1('#skF_8',B_74),'#skF_9')
      | ~ m1_subset_1(B_74,k1_zfmisc_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_96,c_56572])).

tff(c_64344,plain,(
    ! [B_1157] :
      ( k4_subset_1('#skF_8',k3_subset_1('#skF_8',B_1157),'#skF_9') = k2_xboole_0('#skF_9',k3_subset_1('#skF_8',B_1157))
      | ~ m1_subset_1(B_1157,k1_zfmisc_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60710,c_56592])).

tff(c_64363,plain,(
    k4_subset_1('#skF_8',k3_subset_1('#skF_8','#skF_9'),'#skF_9') = k2_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_104,c_64344])).

tff(c_64371,plain,(
    k2_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62504,c_64363])).

tff(c_98025,plain,(
    ! [A_1573,B_1574,B_1575] :
      ( k4_subset_1(A_1573,B_1574,k3_subset_1(A_1573,B_1575)) = k2_xboole_0(B_1574,k3_subset_1(A_1573,B_1575))
      | ~ m1_subset_1(B_1574,k1_zfmisc_1(A_1573))
      | ~ m1_subset_1(B_1575,k1_zfmisc_1(A_1573)) ) ),
    inference(resolution,[status(thm)],[c_96,c_56536])).

tff(c_98126,plain,(
    ! [B_1576] :
      ( k4_subset_1('#skF_8','#skF_9',k3_subset_1('#skF_8',B_1576)) = k2_xboole_0('#skF_9',k3_subset_1('#skF_8',B_1576))
      | ~ m1_subset_1(B_1576,k1_zfmisc_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_104,c_98025])).

tff(c_98197,plain,(
    k4_subset_1('#skF_8','#skF_9',k3_subset_1('#skF_8','#skF_9')) = k2_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_104,c_98126])).

tff(c_98244,plain,(
    k4_subset_1('#skF_8','#skF_9',k3_subset_1('#skF_8','#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64371,c_98197])).

tff(c_98246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_98244])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:15:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.17/14.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.26/15.00  
% 24.26/15.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.26/15.00  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7
% 24.26/15.00  
% 24.26/15.00  %Foreground sorts:
% 24.26/15.00  
% 24.26/15.00  
% 24.26/15.00  %Background operators:
% 24.26/15.00  
% 24.26/15.00  
% 24.26/15.00  %Foreground operators:
% 24.26/15.00  tff('#skF_5', type, '#skF_5': $i > $i).
% 24.26/15.00  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 24.26/15.00  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 24.26/15.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.26/15.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 24.26/15.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 24.26/15.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 24.26/15.00  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 24.26/15.00  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 24.26/15.00  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 24.26/15.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.26/15.00  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 24.26/15.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 24.26/15.00  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 24.26/15.00  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 24.26/15.00  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 24.26/15.00  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 24.26/15.00  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 24.26/15.00  tff('#skF_9', type, '#skF_9': $i).
% 24.26/15.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 24.26/15.00  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 24.26/15.00  tff('#skF_8', type, '#skF_8': $i).
% 24.26/15.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.26/15.00  tff(k3_tarski, type, k3_tarski: $i > $i).
% 24.26/15.00  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 24.26/15.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.26/15.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 24.26/15.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 24.26/15.00  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 24.26/15.00  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 24.26/15.00  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 24.26/15.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 24.26/15.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 24.26/15.00  
% 24.26/15.02  tff(f_108, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 24.26/15.02  tff(f_130, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 24.26/15.02  tff(f_68, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 24.26/15.02  tff(f_56, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 24.26/15.02  tff(f_38, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 24.26/15.02  tff(f_112, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 24.26/15.02  tff(f_48, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 24.26/15.02  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 24.26/15.02  tff(f_119, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 24.26/15.02  tff(f_106, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 24.26/15.02  tff(f_91, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 24.26/15.02  tff(f_64, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 24.26/15.02  tff(f_72, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 24.26/15.02  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 24.26/15.02  tff(f_60, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 24.26/15.02  tff(f_66, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 24.26/15.02  tff(f_70, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 24.26/15.02  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 24.26/15.02  tff(f_116, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 24.26/15.02  tff(f_125, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 24.26/15.02  tff(c_92, plain, (![A_70]: (k2_subset_1(A_70)=A_70)), inference(cnfTransformation, [status(thm)], [f_108])).
% 24.26/15.02  tff(c_102, plain, (k4_subset_1('#skF_8', '#skF_9', k3_subset_1('#skF_8', '#skF_9'))!=k2_subset_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_130])).
% 24.26/15.02  tff(c_105, plain, (k4_subset_1('#skF_8', '#skF_9', k3_subset_1('#skF_8', '#skF_9'))!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_102])).
% 24.26/15.02  tff(c_52, plain, (![A_28]: (k5_xboole_0(A_28, k1_xboole_0)=A_28)), inference(cnfTransformation, [status(thm)], [f_68])).
% 24.26/15.02  tff(c_42, plain, (![A_17]: (r2_hidden('#skF_5'(A_17), A_17) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_56])).
% 24.26/15.02  tff(c_406, plain, (![D_111, B_112, A_113]: (r2_hidden(D_111, B_112) | ~r2_hidden(D_111, k3_xboole_0(A_113, B_112)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 24.26/15.02  tff(c_61462, plain, (![A_1129, B_1130]: (r2_hidden('#skF_5'(k3_xboole_0(A_1129, B_1130)), B_1130) | k3_xboole_0(A_1129, B_1130)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_406])).
% 24.26/15.02  tff(c_440, plain, (![D_115, A_116, B_117]: (r2_hidden(D_115, A_116) | ~r2_hidden(D_115, k3_xboole_0(A_116, B_117)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 24.26/15.02  tff(c_60980, plain, (![A_1124, B_1125]: (r2_hidden('#skF_5'(k3_xboole_0(A_1124, B_1125)), A_1124) | k3_xboole_0(A_1124, B_1125)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_440])).
% 24.26/15.02  tff(c_104, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 24.26/15.02  tff(c_11933, plain, (![A_414, B_415]: (k4_xboole_0(A_414, B_415)=k3_subset_1(A_414, B_415) | ~m1_subset_1(B_415, k1_zfmisc_1(A_414)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 24.26/15.02  tff(c_11957, plain, (k4_xboole_0('#skF_8', '#skF_9')=k3_subset_1('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_104, c_11933])).
% 24.26/15.02  tff(c_26, plain, (![D_16, B_12, A_11]: (~r2_hidden(D_16, B_12) | ~r2_hidden(D_16, k4_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 24.26/15.02  tff(c_11965, plain, (![D_16]: (~r2_hidden(D_16, '#skF_9') | ~r2_hidden(D_16, k3_subset_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_11957, c_26])).
% 24.26/15.02  tff(c_61128, plain, (![B_1125]: (~r2_hidden('#skF_5'(k3_xboole_0(k3_subset_1('#skF_8', '#skF_9'), B_1125)), '#skF_9') | k3_xboole_0(k3_subset_1('#skF_8', '#skF_9'), B_1125)=k1_xboole_0)), inference(resolution, [status(thm)], [c_60980, c_11965])).
% 24.26/15.02  tff(c_61606, plain, (k3_xboole_0(k3_subset_1('#skF_8', '#skF_9'), '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_61462, c_61128])).
% 24.26/15.02  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 24.26/15.02  tff(c_61702, plain, (k3_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_61606, c_2])).
% 24.26/15.02  tff(c_98, plain, (![A_75]: (~v1_xboole_0(k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 24.26/15.02  tff(c_319, plain, (![B_105, A_106]: (r2_hidden(B_105, A_106) | ~m1_subset_1(B_105, A_106) | v1_xboole_0(A_106))), inference(cnfTransformation, [status(thm)], [f_106])).
% 24.26/15.02  tff(c_70, plain, (![C_65, A_61]: (r1_tarski(C_65, A_61) | ~r2_hidden(C_65, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 24.26/15.02  tff(c_323, plain, (![B_105, A_61]: (r1_tarski(B_105, A_61) | ~m1_subset_1(B_105, k1_zfmisc_1(A_61)) | v1_xboole_0(k1_zfmisc_1(A_61)))), inference(resolution, [status(thm)], [c_319, c_70])).
% 24.26/15.02  tff(c_327, plain, (![B_107, A_108]: (r1_tarski(B_107, A_108) | ~m1_subset_1(B_107, k1_zfmisc_1(A_108)))), inference(negUnitSimplification, [status(thm)], [c_98, c_323])).
% 24.26/15.02  tff(c_336, plain, (r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_104, c_327])).
% 24.26/15.02  tff(c_48, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_64])).
% 24.26/15.02  tff(c_340, plain, (k3_xboole_0('#skF_9', '#skF_8')='#skF_9'), inference(resolution, [status(thm)], [c_336, c_48])).
% 24.26/15.02  tff(c_11338, plain, (![A_401, B_402]: (k5_xboole_0(k5_xboole_0(A_401, B_402), k3_xboole_0(A_401, B_402))=k2_xboole_0(A_401, B_402))), inference(cnfTransformation, [status(thm)], [f_72])).
% 24.26/15.02  tff(c_11540, plain, (![A_406]: (k5_xboole_0(A_406, k3_xboole_0(A_406, k1_xboole_0))=k2_xboole_0(A_406, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_52, c_11338])).
% 24.26/15.02  tff(c_44, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 24.26/15.02  tff(c_11560, plain, (![A_406]: (k4_xboole_0(A_406, k1_xboole_0)=k2_xboole_0(A_406, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_11540, c_44])).
% 24.26/15.02  tff(c_286, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k3_xboole_0(A_102, B_103))=k4_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_58])).
% 24.26/15.02  tff(c_302, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_286])).
% 24.26/15.02  tff(c_375, plain, (k3_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_340, c_2])).
% 24.26/15.02  tff(c_55669, plain, (![A_1005, B_1006, C_1007]: (k5_xboole_0(k3_xboole_0(A_1005, B_1006), k3_xboole_0(C_1007, B_1006))=k3_xboole_0(k5_xboole_0(A_1005, C_1007), B_1006))), inference(cnfTransformation, [status(thm)], [f_60])).
% 24.26/15.02  tff(c_55752, plain, (![C_1007]: (k5_xboole_0('#skF_9', k3_xboole_0(C_1007, '#skF_9'))=k3_xboole_0(k5_xboole_0('#skF_8', C_1007), '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_375, c_55669])).
% 24.26/15.02  tff(c_55918, plain, (![C_1013]: (k3_xboole_0('#skF_9', k5_xboole_0('#skF_8', C_1013))=k4_xboole_0('#skF_9', C_1013))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_302, c_55752])).
% 24.26/15.02  tff(c_55991, plain, (k4_xboole_0('#skF_9', k1_xboole_0)=k3_xboole_0('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_52, c_55918])).
% 24.26/15.02  tff(c_55997, plain, (k2_xboole_0('#skF_9', k1_xboole_0)='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_340, c_11560, c_55991])).
% 24.26/15.02  tff(c_11613, plain, (![A_409]: (k4_xboole_0(A_409, k1_xboole_0)=k2_xboole_0(A_409, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_11540, c_44])).
% 24.26/15.02  tff(c_50, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_66])).
% 24.26/15.02  tff(c_11635, plain, (![A_409]: (k4_xboole_0(A_409, k2_xboole_0(A_409, k1_xboole_0))=k3_xboole_0(A_409, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_11613, c_50])).
% 24.26/15.02  tff(c_56075, plain, (k4_xboole_0('#skF_9', '#skF_9')=k3_xboole_0('#skF_9', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_55997, c_11635])).
% 24.26/15.02  tff(c_391, plain, (k5_xboole_0('#skF_8', '#skF_9')=k4_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_375, c_44])).
% 24.26/15.02  tff(c_11958, plain, (k5_xboole_0('#skF_8', '#skF_9')=k3_subset_1('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_11957, c_391])).
% 24.26/15.02  tff(c_55955, plain, (k3_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))=k4_xboole_0('#skF_9', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_11958, c_55918])).
% 24.26/15.02  tff(c_56407, plain, (k3_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))=k3_xboole_0('#skF_9', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56075, c_55955])).
% 24.26/15.02  tff(c_61783, plain, (k3_xboole_0('#skF_9', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_61702, c_56407])).
% 24.26/15.02  tff(c_372, plain, (k5_xboole_0('#skF_9', '#skF_9')=k4_xboole_0('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_340, c_44])).
% 24.26/15.02  tff(c_11414, plain, (![A_28]: (k5_xboole_0(A_28, k3_xboole_0(A_28, k1_xboole_0))=k2_xboole_0(A_28, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_52, c_11338])).
% 24.26/15.02  tff(c_56432, plain, (k5_xboole_0('#skF_9', k3_xboole_0('#skF_9', k1_xboole_0))=k4_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_56407, c_44])).
% 24.26/15.02  tff(c_56438, plain, (k4_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_55997, c_11414, c_56432])).
% 24.26/15.02  tff(c_11971, plain, (k4_xboole_0('#skF_8', k3_subset_1('#skF_8', '#skF_9'))=k3_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_11957, c_50])).
% 24.26/15.02  tff(c_11974, plain, (k4_xboole_0('#skF_8', k3_subset_1('#skF_8', '#skF_9'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_375, c_11971])).
% 24.26/15.02  tff(c_11988, plain, (k3_xboole_0('#skF_8', k3_subset_1('#skF_8', '#skF_9'))=k4_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_11974, c_50])).
% 24.26/15.02  tff(c_11991, plain, (k3_xboole_0('#skF_8', k3_subset_1('#skF_8', '#skF_9'))=k3_subset_1('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_11957, c_11988])).
% 24.26/15.02  tff(c_56277, plain, (k5_xboole_0('#skF_8', k3_subset_1('#skF_8', '#skF_9'))=k4_xboole_0('#skF_8', k3_subset_1('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_11991, c_44])).
% 24.26/15.02  tff(c_56282, plain, (k5_xboole_0('#skF_8', k3_subset_1('#skF_8', '#skF_9'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_11974, c_56277])).
% 24.26/15.02  tff(c_55805, plain, (![C_1007]: (k3_xboole_0('#skF_9', k5_xboole_0('#skF_8', C_1007))=k4_xboole_0('#skF_9', C_1007))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_302, c_55752])).
% 24.26/15.02  tff(c_56287, plain, (k4_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))=k3_xboole_0('#skF_9', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_56282, c_55805])).
% 24.26/15.02  tff(c_56480, plain, (k3_xboole_0('#skF_9', '#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_56438, c_56287])).
% 24.26/15.02  tff(c_56496, plain, (k5_xboole_0('#skF_9', '#skF_9')=k4_xboole_0('#skF_9', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_56480, c_302])).
% 24.26/15.02  tff(c_56511, plain, (k4_xboole_0('#skF_9', '#skF_8')=k3_xboole_0('#skF_9', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56075, c_372, c_56496])).
% 24.26/15.02  tff(c_61897, plain, (k4_xboole_0('#skF_9', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_61783, c_56511])).
% 24.26/15.02  tff(c_54, plain, (![A_29, B_30, C_31]: (k5_xboole_0(k5_xboole_0(A_29, B_30), C_31)=k5_xboole_0(A_29, k5_xboole_0(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 24.26/15.02  tff(c_11350, plain, (![A_401, B_402]: (k5_xboole_0(A_401, k5_xboole_0(B_402, k3_xboole_0(A_401, B_402)))=k2_xboole_0(A_401, B_402))), inference(superposition, [status(thm), theory('equality')], [c_11338, c_54])).
% 24.26/15.02  tff(c_11417, plain, (![A_401, B_402]: (k5_xboole_0(A_401, k4_xboole_0(B_402, A_401))=k2_xboole_0(A_401, B_402))), inference(demodulation, [status(thm), theory('equality')], [c_302, c_11350])).
% 24.26/15.02  tff(c_62321, plain, (k5_xboole_0('#skF_8', k1_xboole_0)=k2_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_61897, c_11417])).
% 24.26/15.02  tff(c_62335, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_62321])).
% 24.26/15.02  tff(c_11962, plain, (k5_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))=k2_xboole_0('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_11957, c_11417])).
% 24.26/15.02  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 24.26/15.02  tff(c_11384, plain, (k5_xboole_0(k5_xboole_0('#skF_8', '#skF_9'), '#skF_9')=k2_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_375, c_11338])).
% 24.26/15.02  tff(c_11423, plain, (k5_xboole_0('#skF_9', k4_xboole_0('#skF_8', '#skF_9'))=k2_xboole_0('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_391, c_11384])).
% 24.26/15.02  tff(c_56118, plain, (k2_xboole_0('#skF_9', '#skF_8')=k2_xboole_0('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_11962, c_11957, c_11423])).
% 24.26/15.02  tff(c_56121, plain, (k5_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))=k2_xboole_0('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_56118, c_11962])).
% 24.26/15.02  tff(c_126, plain, (![B_83, A_84]: (k5_xboole_0(B_83, A_84)=k5_xboole_0(A_84, B_83))), inference(cnfTransformation, [status(thm)], [f_29])).
% 24.26/15.02  tff(c_142, plain, (![A_84]: (k5_xboole_0(k1_xboole_0, A_84)=A_84)), inference(superposition, [status(thm), theory('equality')], [c_126, c_52])).
% 24.26/15.02  tff(c_11175, plain, (![A_393, B_394, C_395]: (k5_xboole_0(k5_xboole_0(A_393, B_394), C_395)=k5_xboole_0(A_393, k5_xboole_0(B_394, C_395)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 24.26/15.02  tff(c_58363, plain, (![B_1080, A_1081, B_1082]: (k5_xboole_0(B_1080, k5_xboole_0(A_1081, B_1082))=k5_xboole_0(A_1081, k5_xboole_0(B_1082, B_1080)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_11175])).
% 24.26/15.02  tff(c_58656, plain, (![A_1083, B_1084]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_1083, B_1084))=k5_xboole_0(B_1084, A_1083))), inference(superposition, [status(thm), theory('equality')], [c_142, c_58363])).
% 24.26/15.02  tff(c_58745, plain, (![B_402, A_401]: (k5_xboole_0(k4_xboole_0(B_402, A_401), A_401)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_401, B_402)))), inference(superposition, [status(thm), theory('equality')], [c_11417, c_58656])).
% 24.26/15.02  tff(c_59446, plain, (![B_1097, A_1098]: (k5_xboole_0(k4_xboole_0(B_1097, A_1098), A_1098)=k2_xboole_0(A_1098, B_1097))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_58745])).
% 24.26/15.02  tff(c_59531, plain, (k5_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))=k2_xboole_0(k3_subset_1('#skF_8', '#skF_9'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_56438, c_59446])).
% 24.26/15.02  tff(c_59596, plain, (k2_xboole_0(k3_subset_1('#skF_8', '#skF_9'), '#skF_9')=k2_xboole_0('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_56121, c_59531])).
% 24.26/15.02  tff(c_96, plain, (![A_73, B_74]: (m1_subset_1(k3_subset_1(A_73, B_74), k1_zfmisc_1(A_73)) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_116])).
% 24.26/15.02  tff(c_56536, plain, (![A_1038, B_1039, C_1040]: (k4_subset_1(A_1038, B_1039, C_1040)=k2_xboole_0(B_1039, C_1040) | ~m1_subset_1(C_1040, k1_zfmisc_1(A_1038)) | ~m1_subset_1(B_1039, k1_zfmisc_1(A_1038)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 24.26/15.02  tff(c_56572, plain, (![B_1041]: (k4_subset_1('#skF_8', B_1041, '#skF_9')=k2_xboole_0(B_1041, '#skF_9') | ~m1_subset_1(B_1041, k1_zfmisc_1('#skF_8')))), inference(resolution, [status(thm)], [c_104, c_56536])).
% 24.26/15.02  tff(c_57205, plain, (![B_1053]: (k4_subset_1('#skF_8', k3_subset_1('#skF_8', B_1053), '#skF_9')=k2_xboole_0(k3_subset_1('#skF_8', B_1053), '#skF_9') | ~m1_subset_1(B_1053, k1_zfmisc_1('#skF_8')))), inference(resolution, [status(thm)], [c_96, c_56572])).
% 24.26/15.02  tff(c_57231, plain, (k4_subset_1('#skF_8', k3_subset_1('#skF_8', '#skF_9'), '#skF_9')=k2_xboole_0(k3_subset_1('#skF_8', '#skF_9'), '#skF_9')), inference(resolution, [status(thm)], [c_104, c_57205])).
% 24.26/15.02  tff(c_60339, plain, (k4_subset_1('#skF_8', k3_subset_1('#skF_8', '#skF_9'), '#skF_9')=k2_xboole_0('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_59596, c_57231])).
% 24.26/15.02  tff(c_62504, plain, (k4_subset_1('#skF_8', k3_subset_1('#skF_8', '#skF_9'), '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_62335, c_60339])).
% 24.26/15.02  tff(c_60468, plain, (![B_1116, A_1117]: (k5_xboole_0(k5_xboole_0(B_1116, A_1117), k3_xboole_0(A_1117, B_1116))=k2_xboole_0(A_1117, B_1116))), inference(superposition, [status(thm), theory('equality')], [c_4, c_11338])).
% 24.26/15.02  tff(c_60496, plain, (![B_1116, A_1117]: (k5_xboole_0(B_1116, k5_xboole_0(A_1117, k3_xboole_0(A_1117, B_1116)))=k2_xboole_0(A_1117, B_1116))), inference(superposition, [status(thm), theory('equality')], [c_60468, c_54])).
% 24.26/15.02  tff(c_60710, plain, (![B_1116, A_1117]: (k2_xboole_0(B_1116, A_1117)=k2_xboole_0(A_1117, B_1116))), inference(demodulation, [status(thm), theory('equality')], [c_11417, c_44, c_60496])).
% 24.26/15.02  tff(c_56592, plain, (![B_74]: (k4_subset_1('#skF_8', k3_subset_1('#skF_8', B_74), '#skF_9')=k2_xboole_0(k3_subset_1('#skF_8', B_74), '#skF_9') | ~m1_subset_1(B_74, k1_zfmisc_1('#skF_8')))), inference(resolution, [status(thm)], [c_96, c_56572])).
% 24.26/15.02  tff(c_64344, plain, (![B_1157]: (k4_subset_1('#skF_8', k3_subset_1('#skF_8', B_1157), '#skF_9')=k2_xboole_0('#skF_9', k3_subset_1('#skF_8', B_1157)) | ~m1_subset_1(B_1157, k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_60710, c_56592])).
% 24.26/15.02  tff(c_64363, plain, (k4_subset_1('#skF_8', k3_subset_1('#skF_8', '#skF_9'), '#skF_9')=k2_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_104, c_64344])).
% 24.26/15.02  tff(c_64371, plain, (k2_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_62504, c_64363])).
% 24.26/15.02  tff(c_98025, plain, (![A_1573, B_1574, B_1575]: (k4_subset_1(A_1573, B_1574, k3_subset_1(A_1573, B_1575))=k2_xboole_0(B_1574, k3_subset_1(A_1573, B_1575)) | ~m1_subset_1(B_1574, k1_zfmisc_1(A_1573)) | ~m1_subset_1(B_1575, k1_zfmisc_1(A_1573)))), inference(resolution, [status(thm)], [c_96, c_56536])).
% 24.26/15.02  tff(c_98126, plain, (![B_1576]: (k4_subset_1('#skF_8', '#skF_9', k3_subset_1('#skF_8', B_1576))=k2_xboole_0('#skF_9', k3_subset_1('#skF_8', B_1576)) | ~m1_subset_1(B_1576, k1_zfmisc_1('#skF_8')))), inference(resolution, [status(thm)], [c_104, c_98025])).
% 24.26/15.02  tff(c_98197, plain, (k4_subset_1('#skF_8', '#skF_9', k3_subset_1('#skF_8', '#skF_9'))=k2_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_104, c_98126])).
% 24.26/15.02  tff(c_98244, plain, (k4_subset_1('#skF_8', '#skF_9', k3_subset_1('#skF_8', '#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_64371, c_98197])).
% 24.26/15.02  tff(c_98246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_98244])).
% 24.26/15.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.26/15.02  
% 24.26/15.02  Inference rules
% 24.26/15.02  ----------------------
% 24.26/15.02  #Ref     : 0
% 24.26/15.02  #Sup     : 23853
% 24.26/15.02  #Fact    : 0
% 24.26/15.02  #Define  : 0
% 24.26/15.02  #Split   : 14
% 24.26/15.02  #Chain   : 0
% 24.26/15.02  #Close   : 0
% 24.26/15.02  
% 24.26/15.02  Ordering : KBO
% 24.26/15.02  
% 24.26/15.02  Simplification rules
% 24.26/15.02  ----------------------
% 24.26/15.02  #Subsume      : 2007
% 24.26/15.02  #Demod        : 30428
% 24.26/15.02  #Tautology    : 11278
% 24.26/15.02  #SimpNegUnit  : 538
% 24.26/15.02  #BackRed      : 177
% 24.26/15.02  
% 24.26/15.02  #Partial instantiations: 0
% 24.26/15.02  #Strategies tried      : 1
% 24.26/15.02  
% 24.26/15.02  Timing (in seconds)
% 24.26/15.02  ----------------------
% 24.26/15.02  Preprocessing        : 0.36
% 24.26/15.02  Parsing              : 0.17
% 24.26/15.02  CNF conversion       : 0.03
% 24.26/15.02  Main loop            : 13.84
% 24.26/15.02  Inferencing          : 2.16
% 24.26/15.02  Reduction            : 7.98
% 24.26/15.02  Demodulation         : 7.09
% 24.26/15.02  BG Simplification    : 0.29
% 24.26/15.02  Subsumption          : 2.61
% 24.26/15.02  Abstraction          : 0.47
% 24.26/15.02  MUC search           : 0.00
% 24.26/15.02  Cooper               : 0.00
% 24.26/15.02  Total                : 14.25
% 24.26/15.02  Index Insertion      : 0.00
% 24.26/15.02  Index Deletion       : 0.00
% 24.26/15.02  Index Matching       : 0.00
% 24.26/15.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
