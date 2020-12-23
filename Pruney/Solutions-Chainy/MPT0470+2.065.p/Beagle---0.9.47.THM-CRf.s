%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:10 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 267 expanded)
%              Number of leaves         :   35 ( 102 expanded)
%              Depth                    :   17
%              Number of atoms          :  175 ( 452 expanded)
%              Number of equality atoms :   49 ( 117 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > #nlpp > k4_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_102,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_44,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k6_subset_1(A,B)) = k6_subset_1(k4_relat_1(A),k4_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(c_40,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_66,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_60,plain,(
    ! [A_30] :
      ( v1_relat_1(A_30)
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_64,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_60])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k5_relat_1(A_15,B_16))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_231,plain,(
    ! [A_61,B_62] :
      ( k1_relat_1(k5_relat_1(A_61,B_62)) = k1_relat_1(A_61)
      | ~ r1_tarski(k2_relat_1(A_61),k1_relat_1(B_62))
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_237,plain,(
    ! [B_62] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_62)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_62))
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_231])).

tff(c_242,plain,(
    ! [B_63] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_63)) = k1_xboole_0
      | ~ v1_relat_1(B_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6,c_38,c_237])).

tff(c_26,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(k1_relat_1(A_17))
      | ~ v1_relat_1(A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_251,plain,(
    ! [B_63] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_63))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_63))
      | ~ v1_relat_1(B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_26])).

tff(c_342,plain,(
    ! [B_68] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_68))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_68))
      | ~ v1_relat_1(B_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_251])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_351,plain,(
    ! [B_69] :
      ( k5_relat_1(k1_xboole_0,B_69) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_69))
      | ~ v1_relat_1(B_69) ) ),
    inference(resolution,[status(thm)],[c_342,c_4])).

tff(c_355,plain,(
    ! [B_16] :
      ( k5_relat_1(k1_xboole_0,B_16) = k1_xboole_0
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_351])).

tff(c_366,plain,(
    ! [B_71] :
      ( k5_relat_1(k1_xboole_0,B_71) = k1_xboole_0
      | ~ v1_relat_1(B_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_355])).

tff(c_378,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_366])).

tff(c_385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_378])).

tff(c_386,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_14,plain,(
    ! [A_9,B_10] : k6_subset_1(A_9,B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    ! [A_7,B_8] : m1_subset_1(k6_subset_1(A_7,B_8),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_44,plain,(
    ! [A_7,B_8] : m1_subset_1(k4_xboole_0(A_7,B_8),k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12])).

tff(c_430,plain,(
    ! [A_81,B_82] :
      ( r1_tarski(A_81,B_82)
      | ~ m1_subset_1(A_81,k1_zfmisc_1(B_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_438,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(resolution,[status(thm)],[c_44,c_430])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_xboole_0(k4_xboole_0(A_5,B_6),B_6) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_446,plain,(
    ! [B_87,A_88] :
      ( ~ r1_xboole_0(B_87,A_88)
      | ~ r1_tarski(B_87,A_88)
      | v1_xboole_0(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_451,plain,(
    ! [A_89,B_90] :
      ( ~ r1_tarski(k4_xboole_0(A_89,B_90),B_90)
      | v1_xboole_0(k4_xboole_0(A_89,B_90)) ) ),
    inference(resolution,[status(thm)],[c_10,c_446])).

tff(c_457,plain,(
    ! [A_91] : v1_xboole_0(k4_xboole_0(A_91,A_91)) ),
    inference(resolution,[status(thm)],[c_438,c_451])).

tff(c_465,plain,(
    ! [A_91] : k4_xboole_0(A_91,A_91) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_457,c_4])).

tff(c_30,plain,(
    ! [A_19,B_21] :
      ( k6_subset_1(k4_relat_1(A_19),k4_relat_1(B_21)) = k4_relat_1(k6_subset_1(A_19,B_21))
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_43,plain,(
    ! [A_19,B_21] :
      ( k4_xboole_0(k4_relat_1(A_19),k4_relat_1(B_21)) = k4_relat_1(k4_xboole_0(A_19,B_21))
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_30])).

tff(c_506,plain,(
    ! [A_95] : k4_xboole_0(A_95,A_95) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_457,c_4])).

tff(c_530,plain,(
    ! [B_21] :
      ( k4_relat_1(k4_xboole_0(B_21,B_21)) = k1_xboole_0
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_506])).

tff(c_537,plain,(
    ! [B_21] :
      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_530])).

tff(c_570,plain,(
    ! [B_100] :
      ( ~ v1_relat_1(B_100)
      | ~ v1_relat_1(B_100) ) ),
    inference(splitLeft,[status(thm)],[c_537])).

tff(c_576,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_64,c_570])).

tff(c_584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_576])).

tff(c_585,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_537])).

tff(c_34,plain,(
    ! [B_27,A_25] :
      ( k5_relat_1(k4_relat_1(B_27),k4_relat_1(A_25)) = k4_relat_1(k5_relat_1(A_25,B_27))
      | ~ v1_relat_1(B_27)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_589,plain,(
    ! [A_25] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_25)) = k4_relat_1(k5_relat_1(A_25,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_34])).

tff(c_787,plain,(
    ! [A_112] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_112)) = k4_relat_1(k5_relat_1(A_112,k1_xboole_0))
      | ~ v1_relat_1(A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_589])).

tff(c_22,plain,(
    ! [A_14] :
      ( v1_relat_1(k4_relat_1(A_14))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_621,plain,(
    ! [A_101,B_102] :
      ( k1_relat_1(k5_relat_1(A_101,B_102)) = k1_relat_1(A_101)
      | ~ r1_tarski(k2_relat_1(A_101),k1_relat_1(B_102))
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_627,plain,(
    ! [B_102] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_102)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_102))
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_621])).

tff(c_632,plain,(
    ! [B_103] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_103)) = k1_xboole_0
      | ~ v1_relat_1(B_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6,c_38,c_627])).

tff(c_641,plain,(
    ! [B_103] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_103))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_103))
      | ~ v1_relat_1(B_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_26])).

tff(c_687,plain,(
    ! [B_107] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_107))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_107))
      | ~ v1_relat_1(B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_641])).

tff(c_701,plain,(
    ! [B_108] :
      ( k5_relat_1(k1_xboole_0,B_108) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_108))
      | ~ v1_relat_1(B_108) ) ),
    inference(resolution,[status(thm)],[c_687,c_4])).

tff(c_705,plain,(
    ! [B_16] :
      ( k5_relat_1(k1_xboole_0,B_16) = k1_xboole_0
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_701])).

tff(c_714,plain,(
    ! [B_109] :
      ( k5_relat_1(k1_xboole_0,B_109) = k1_xboole_0
      | ~ v1_relat_1(B_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_705])).

tff(c_728,plain,(
    ! [A_14] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_14)) = k1_xboole_0
      | ~ v1_relat_1(A_14) ) ),
    inference(resolution,[status(thm)],[c_22,c_714])).

tff(c_821,plain,(
    ! [A_113] :
      ( k4_relat_1(k5_relat_1(A_113,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_787,c_728])).

tff(c_28,plain,(
    ! [A_18] :
      ( k4_relat_1(k4_relat_1(A_18)) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_848,plain,(
    ! [A_113] :
      ( k5_relat_1(A_113,k1_xboole_0) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_113,k1_xboole_0))
      | ~ v1_relat_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_821,c_28])).

tff(c_1681,plain,(
    ! [A_141] :
      ( k5_relat_1(A_141,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_141,k1_xboole_0))
      | ~ v1_relat_1(A_141)
      | ~ v1_relat_1(A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_848])).

tff(c_1691,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_15) ) ),
    inference(resolution,[status(thm)],[c_24,c_1681])).

tff(c_1697,plain,(
    ! [A_142] :
      ( k5_relat_1(A_142,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1691])).

tff(c_1718,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_1697])).

tff(c_1729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_386,c_1718])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:45:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.78/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.72  
% 3.78/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.72  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > #nlpp > k4_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.78/1.72  
% 3.78/1.72  %Foreground sorts:
% 3.78/1.72  
% 3.78/1.72  
% 3.78/1.72  %Background operators:
% 3.78/1.72  
% 3.78/1.72  
% 3.78/1.72  %Foreground operators:
% 3.78/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.78/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.78/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.78/1.72  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.78/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.78/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.78/1.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.78/1.72  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.78/1.72  tff('#skF_1', type, '#skF_1': $i).
% 3.78/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.78/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.78/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.78/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.78/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.78/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.78/1.72  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.78/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.78/1.72  
% 4.10/1.74  tff(f_109, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 4.10/1.74  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.10/1.74  tff(f_54, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 4.10/1.74  tff(f_64, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 4.10/1.74  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.10/1.74  tff(f_102, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.10/1.74  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 4.10/1.74  tff(f_72, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 4.10/1.74  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.10/1.74  tff(f_46, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 4.10/1.74  tff(f_44, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 4.10/1.74  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.10/1.74  tff(f_42, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.10/1.74  tff(f_40, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 4.10/1.74  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k6_subset_1(A, B)) = k6_subset_1(k4_relat_1(A), k4_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_relat_1)).
% 4.10/1.74  tff(f_99, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 4.10/1.74  tff(f_58, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 4.10/1.74  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 4.10/1.74  tff(c_40, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.10/1.74  tff(c_66, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 4.10/1.74  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.10/1.74  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.10/1.74  tff(c_60, plain, (![A_30]: (v1_relat_1(A_30) | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.10/1.74  tff(c_64, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_60])).
% 4.10/1.74  tff(c_24, plain, (![A_15, B_16]: (v1_relat_1(k5_relat_1(A_15, B_16)) | ~v1_relat_1(B_16) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.10/1.74  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.10/1.74  tff(c_38, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.10/1.74  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.10/1.74  tff(c_231, plain, (![A_61, B_62]: (k1_relat_1(k5_relat_1(A_61, B_62))=k1_relat_1(A_61) | ~r1_tarski(k2_relat_1(A_61), k1_relat_1(B_62)) | ~v1_relat_1(B_62) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.10/1.74  tff(c_237, plain, (![B_62]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_62))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_62)) | ~v1_relat_1(B_62) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_231])).
% 4.10/1.74  tff(c_242, plain, (![B_63]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_63))=k1_xboole_0 | ~v1_relat_1(B_63))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6, c_38, c_237])).
% 4.10/1.74  tff(c_26, plain, (![A_17]: (~v1_xboole_0(k1_relat_1(A_17)) | ~v1_relat_1(A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.10/1.74  tff(c_251, plain, (![B_63]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_63)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_63)) | ~v1_relat_1(B_63))), inference(superposition, [status(thm), theory('equality')], [c_242, c_26])).
% 4.10/1.74  tff(c_342, plain, (![B_68]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_68)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_68)) | ~v1_relat_1(B_68))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_251])).
% 4.10/1.74  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.10/1.74  tff(c_351, plain, (![B_69]: (k5_relat_1(k1_xboole_0, B_69)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_69)) | ~v1_relat_1(B_69))), inference(resolution, [status(thm)], [c_342, c_4])).
% 4.10/1.74  tff(c_355, plain, (![B_16]: (k5_relat_1(k1_xboole_0, B_16)=k1_xboole_0 | ~v1_relat_1(B_16) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_351])).
% 4.10/1.74  tff(c_366, plain, (![B_71]: (k5_relat_1(k1_xboole_0, B_71)=k1_xboole_0 | ~v1_relat_1(B_71))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_355])).
% 4.10/1.74  tff(c_378, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_366])).
% 4.10/1.74  tff(c_385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_378])).
% 4.10/1.74  tff(c_386, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 4.10/1.74  tff(c_14, plain, (![A_9, B_10]: (k6_subset_1(A_9, B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.10/1.74  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(k6_subset_1(A_7, B_8), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.10/1.74  tff(c_44, plain, (![A_7, B_8]: (m1_subset_1(k4_xboole_0(A_7, B_8), k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12])).
% 4.10/1.74  tff(c_430, plain, (![A_81, B_82]: (r1_tarski(A_81, B_82) | ~m1_subset_1(A_81, k1_zfmisc_1(B_82)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.10/1.74  tff(c_438, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(resolution, [status(thm)], [c_44, c_430])).
% 4.10/1.74  tff(c_10, plain, (![A_5, B_6]: (r1_xboole_0(k4_xboole_0(A_5, B_6), B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.10/1.74  tff(c_446, plain, (![B_87, A_88]: (~r1_xboole_0(B_87, A_88) | ~r1_tarski(B_87, A_88) | v1_xboole_0(B_87))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.10/1.74  tff(c_451, plain, (![A_89, B_90]: (~r1_tarski(k4_xboole_0(A_89, B_90), B_90) | v1_xboole_0(k4_xboole_0(A_89, B_90)))), inference(resolution, [status(thm)], [c_10, c_446])).
% 4.10/1.74  tff(c_457, plain, (![A_91]: (v1_xboole_0(k4_xboole_0(A_91, A_91)))), inference(resolution, [status(thm)], [c_438, c_451])).
% 4.10/1.74  tff(c_465, plain, (![A_91]: (k4_xboole_0(A_91, A_91)=k1_xboole_0)), inference(resolution, [status(thm)], [c_457, c_4])).
% 4.10/1.74  tff(c_30, plain, (![A_19, B_21]: (k6_subset_1(k4_relat_1(A_19), k4_relat_1(B_21))=k4_relat_1(k6_subset_1(A_19, B_21)) | ~v1_relat_1(B_21) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.10/1.74  tff(c_43, plain, (![A_19, B_21]: (k4_xboole_0(k4_relat_1(A_19), k4_relat_1(B_21))=k4_relat_1(k4_xboole_0(A_19, B_21)) | ~v1_relat_1(B_21) | ~v1_relat_1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_30])).
% 4.10/1.74  tff(c_506, plain, (![A_95]: (k4_xboole_0(A_95, A_95)=k1_xboole_0)), inference(resolution, [status(thm)], [c_457, c_4])).
% 4.10/1.74  tff(c_530, plain, (![B_21]: (k4_relat_1(k4_xboole_0(B_21, B_21))=k1_xboole_0 | ~v1_relat_1(B_21) | ~v1_relat_1(B_21))), inference(superposition, [status(thm), theory('equality')], [c_43, c_506])).
% 4.10/1.74  tff(c_537, plain, (![B_21]: (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_21) | ~v1_relat_1(B_21))), inference(demodulation, [status(thm), theory('equality')], [c_465, c_530])).
% 4.10/1.74  tff(c_570, plain, (![B_100]: (~v1_relat_1(B_100) | ~v1_relat_1(B_100))), inference(splitLeft, [status(thm)], [c_537])).
% 4.10/1.74  tff(c_576, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_570])).
% 4.10/1.74  tff(c_584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_576])).
% 4.10/1.74  tff(c_585, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_537])).
% 4.10/1.74  tff(c_34, plain, (![B_27, A_25]: (k5_relat_1(k4_relat_1(B_27), k4_relat_1(A_25))=k4_relat_1(k5_relat_1(A_25, B_27)) | ~v1_relat_1(B_27) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.10/1.74  tff(c_589, plain, (![A_25]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_25))=k4_relat_1(k5_relat_1(A_25, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_25))), inference(superposition, [status(thm), theory('equality')], [c_585, c_34])).
% 4.10/1.74  tff(c_787, plain, (![A_112]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_112))=k4_relat_1(k5_relat_1(A_112, k1_xboole_0)) | ~v1_relat_1(A_112))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_589])).
% 4.10/1.74  tff(c_22, plain, (![A_14]: (v1_relat_1(k4_relat_1(A_14)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.10/1.74  tff(c_621, plain, (![A_101, B_102]: (k1_relat_1(k5_relat_1(A_101, B_102))=k1_relat_1(A_101) | ~r1_tarski(k2_relat_1(A_101), k1_relat_1(B_102)) | ~v1_relat_1(B_102) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.10/1.74  tff(c_627, plain, (![B_102]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_102))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_102)) | ~v1_relat_1(B_102) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_621])).
% 4.10/1.74  tff(c_632, plain, (![B_103]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_103))=k1_xboole_0 | ~v1_relat_1(B_103))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6, c_38, c_627])).
% 4.10/1.74  tff(c_641, plain, (![B_103]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_103)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_103)) | ~v1_relat_1(B_103))), inference(superposition, [status(thm), theory('equality')], [c_632, c_26])).
% 4.10/1.74  tff(c_687, plain, (![B_107]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_107)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_107)) | ~v1_relat_1(B_107))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_641])).
% 4.10/1.74  tff(c_701, plain, (![B_108]: (k5_relat_1(k1_xboole_0, B_108)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_108)) | ~v1_relat_1(B_108))), inference(resolution, [status(thm)], [c_687, c_4])).
% 4.10/1.74  tff(c_705, plain, (![B_16]: (k5_relat_1(k1_xboole_0, B_16)=k1_xboole_0 | ~v1_relat_1(B_16) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_701])).
% 4.10/1.74  tff(c_714, plain, (![B_109]: (k5_relat_1(k1_xboole_0, B_109)=k1_xboole_0 | ~v1_relat_1(B_109))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_705])).
% 4.10/1.74  tff(c_728, plain, (![A_14]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_14))=k1_xboole_0 | ~v1_relat_1(A_14))), inference(resolution, [status(thm)], [c_22, c_714])).
% 4.10/1.74  tff(c_821, plain, (![A_113]: (k4_relat_1(k5_relat_1(A_113, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_113) | ~v1_relat_1(A_113))), inference(superposition, [status(thm), theory('equality')], [c_787, c_728])).
% 4.10/1.74  tff(c_28, plain, (![A_18]: (k4_relat_1(k4_relat_1(A_18))=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.10/1.74  tff(c_848, plain, (![A_113]: (k5_relat_1(A_113, k1_xboole_0)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_113, k1_xboole_0)) | ~v1_relat_1(A_113) | ~v1_relat_1(A_113))), inference(superposition, [status(thm), theory('equality')], [c_821, c_28])).
% 4.10/1.74  tff(c_1681, plain, (![A_141]: (k5_relat_1(A_141, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_141, k1_xboole_0)) | ~v1_relat_1(A_141) | ~v1_relat_1(A_141))), inference(demodulation, [status(thm), theory('equality')], [c_585, c_848])).
% 4.10/1.74  tff(c_1691, plain, (![A_15]: (k5_relat_1(A_15, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_15))), inference(resolution, [status(thm)], [c_24, c_1681])).
% 4.10/1.74  tff(c_1697, plain, (![A_142]: (k5_relat_1(A_142, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_142))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1691])).
% 4.10/1.74  tff(c_1718, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_1697])).
% 4.10/1.74  tff(c_1729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_386, c_1718])).
% 4.10/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.74  
% 4.10/1.74  Inference rules
% 4.10/1.74  ----------------------
% 4.10/1.74  #Ref     : 0
% 4.10/1.74  #Sup     : 393
% 4.10/1.74  #Fact    : 0
% 4.10/1.74  #Define  : 0
% 4.10/1.74  #Split   : 3
% 4.10/1.74  #Chain   : 0
% 4.10/1.74  #Close   : 0
% 4.10/1.74  
% 4.10/1.74  Ordering : KBO
% 4.10/1.74  
% 4.10/1.74  Simplification rules
% 4.10/1.74  ----------------------
% 4.10/1.74  #Subsume      : 20
% 4.10/1.74  #Demod        : 401
% 4.10/1.74  #Tautology    : 189
% 4.10/1.74  #SimpNegUnit  : 2
% 4.10/1.74  #BackRed      : 4
% 4.10/1.74  
% 4.10/1.74  #Partial instantiations: 0
% 4.10/1.74  #Strategies tried      : 1
% 4.10/1.74  
% 4.10/1.74  Timing (in seconds)
% 4.10/1.74  ----------------------
% 4.10/1.75  Preprocessing        : 0.33
% 4.10/1.75  Parsing              : 0.18
% 4.10/1.75  CNF conversion       : 0.02
% 4.10/1.75  Main loop            : 0.64
% 4.10/1.75  Inferencing          : 0.23
% 4.10/1.75  Reduction            : 0.20
% 4.10/1.75  Demodulation         : 0.15
% 4.10/1.75  BG Simplification    : 0.03
% 4.10/1.75  Subsumption          : 0.13
% 4.10/1.75  Abstraction          : 0.03
% 4.10/1.75  MUC search           : 0.00
% 4.10/1.75  Cooper               : 0.00
% 4.10/1.75  Total                : 1.01
% 4.10/1.75  Index Insertion      : 0.00
% 4.10/1.75  Index Deletion       : 0.00
% 4.10/1.75  Index Matching       : 0.00
% 4.10/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
