%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:10 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 187 expanded)
%              Number of leaves         :   25 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :  158 ( 358 expanded)
%              Number of equality atoms :   46 (  93 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_83,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_54,axiom,(
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

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(c_30,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_54,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_48,plain,(
    ! [A_18] :
      ( v1_relat_1(A_18)
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_52,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_48])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k5_relat_1(A_5,B_6))
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_220,plain,(
    ! [A_31,B_32] :
      ( k1_relat_1(k5_relat_1(A_31,B_32)) = k1_relat_1(A_31)
      | ~ r1_tarski(k2_relat_1(A_31),k1_relat_1(B_32))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_232,plain,(
    ! [B_32] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_32)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_32))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_220])).

tff(c_237,plain,(
    ! [B_33] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_33)) = k1_xboole_0
      | ~ v1_relat_1(B_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6,c_28,c_232])).

tff(c_14,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(k1_relat_1(A_7))
      | ~ v1_relat_1(A_7)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_246,plain,(
    ! [B_33] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_33))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_33))
      | ~ v1_relat_1(B_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_14])).

tff(c_287,plain,(
    ! [B_34] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_34))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_34))
      | ~ v1_relat_1(B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_246])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_299,plain,(
    ! [B_35] :
      ( k5_relat_1(k1_xboole_0,B_35) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_35))
      | ~ v1_relat_1(B_35) ) ),
    inference(resolution,[status(thm)],[c_287,c_4])).

tff(c_306,plain,(
    ! [B_6] :
      ( k5_relat_1(k1_xboole_0,B_6) = k1_xboole_0
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_299])).

tff(c_310,plain,(
    ! [B_36] :
      ( k5_relat_1(k1_xboole_0,B_36) = k1_xboole_0
      | ~ v1_relat_1(B_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_306])).

tff(c_322,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_310])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_322])).

tff(c_330,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_10,plain,(
    ! [A_4] :
      ( v1_relat_1(k4_relat_1(A_4))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_20,plain,(
    ! [A_9] :
      ( k1_relat_1(k4_relat_1(A_9)) = k2_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_368,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(k1_relat_1(A_39))
      | ~ v1_relat_1(A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_413,plain,(
    ! [A_45] :
      ( ~ v1_xboole_0(k2_relat_1(A_45))
      | ~ v1_relat_1(k4_relat_1(A_45))
      | v1_xboole_0(k4_relat_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_368])).

tff(c_425,plain,(
    ! [A_46] :
      ( k4_relat_1(A_46) = k1_xboole_0
      | ~ v1_xboole_0(k2_relat_1(A_46))
      | ~ v1_relat_1(k4_relat_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_413,c_4])).

tff(c_431,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_425])).

tff(c_433,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2,c_431])).

tff(c_434,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_433])).

tff(c_437,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_434])).

tff(c_441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_437])).

tff(c_442,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_433])).

tff(c_24,plain,(
    ! [B_15,A_13] :
      ( k5_relat_1(k4_relat_1(B_15),k4_relat_1(A_13)) = k4_relat_1(k5_relat_1(A_13,B_15))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_450,plain,(
    ! [A_13] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_13)) = k4_relat_1(k5_relat_1(A_13,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_24])).

tff(c_639,plain,(
    ! [A_55] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_55)) = k4_relat_1(k5_relat_1(A_55,k1_xboole_0))
      | ~ v1_relat_1(A_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_450])).

tff(c_483,plain,(
    ! [A_47,B_48] :
      ( k1_relat_1(k5_relat_1(A_47,B_48)) = k1_relat_1(A_47)
      | ~ r1_tarski(k2_relat_1(A_47),k1_relat_1(B_48))
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_495,plain,(
    ! [B_48] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_48)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_48))
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_483])).

tff(c_501,plain,(
    ! [B_49] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_49)) = k1_xboole_0
      | ~ v1_relat_1(B_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6,c_28,c_495])).

tff(c_510,plain,(
    ! [B_49] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_49))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_49))
      | ~ v1_relat_1(B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_14])).

tff(c_523,plain,(
    ! [B_50] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_50))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_50))
      | ~ v1_relat_1(B_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_510])).

tff(c_537,plain,(
    ! [B_51] :
      ( k5_relat_1(k1_xboole_0,B_51) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_51))
      | ~ v1_relat_1(B_51) ) ),
    inference(resolution,[status(thm)],[c_523,c_4])).

tff(c_541,plain,(
    ! [B_6] :
      ( k5_relat_1(k1_xboole_0,B_6) = k1_xboole_0
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_537])).

tff(c_550,plain,(
    ! [B_52] :
      ( k5_relat_1(k1_xboole_0,B_52) = k1_xboole_0
      | ~ v1_relat_1(B_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_541])).

tff(c_564,plain,(
    ! [A_4] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_4)) = k1_xboole_0
      | ~ v1_relat_1(A_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_550])).

tff(c_682,plain,(
    ! [A_57] :
      ( k4_relat_1(k5_relat_1(A_57,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_639,c_564])).

tff(c_16,plain,(
    ! [A_8] :
      ( k4_relat_1(k4_relat_1(A_8)) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_712,plain,(
    ! [A_57] :
      ( k5_relat_1(A_57,k1_xboole_0) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_57,k1_xboole_0))
      | ~ v1_relat_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_682,c_16])).

tff(c_1089,plain,(
    ! [A_67] :
      ( k5_relat_1(A_67,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_67,k1_xboole_0))
      | ~ v1_relat_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_712])).

tff(c_1099,plain,(
    ! [A_5] :
      ( k5_relat_1(A_5,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_1089])).

tff(c_1105,plain,(
    ! [A_68] :
      ( k5_relat_1(A_68,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1099])).

tff(c_1126,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_1105])).

tff(c_1137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_330,c_1126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:46:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.79/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.99  
% 3.79/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/2.00  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.79/2.00  
% 3.79/2.00  %Foreground sorts:
% 3.79/2.00  
% 3.79/2.00  
% 3.79/2.00  %Background operators:
% 3.79/2.00  
% 3.79/2.00  
% 3.79/2.00  %Foreground operators:
% 3.79/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.79/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.79/2.00  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.79/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.79/2.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.79/2.00  tff('#skF_1', type, '#skF_1': $i).
% 3.79/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.79/2.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.79/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.79/2.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.79/2.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.79/2.00  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.79/2.00  
% 3.79/2.02  tff(f_90, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.79/2.02  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.79/2.02  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.79/2.02  tff(f_46, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.79/2.02  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.79/2.02  tff(f_83, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.79/2.02  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 3.79/2.02  tff(f_54, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 3.79/2.02  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.79/2.02  tff(f_40, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.79/2.02  tff(f_64, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 3.79/2.02  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 3.79/2.02  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 3.79/2.02  tff(c_30, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.79/2.02  tff(c_54, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_30])).
% 3.79/2.02  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.79/2.02  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.79/2.02  tff(c_48, plain, (![A_18]: (v1_relat_1(A_18) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.79/2.02  tff(c_52, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_48])).
% 3.79/2.02  tff(c_12, plain, (![A_5, B_6]: (v1_relat_1(k5_relat_1(A_5, B_6)) | ~v1_relat_1(B_6) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.79/2.02  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.79/2.02  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.79/2.02  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.79/2.02  tff(c_220, plain, (![A_31, B_32]: (k1_relat_1(k5_relat_1(A_31, B_32))=k1_relat_1(A_31) | ~r1_tarski(k2_relat_1(A_31), k1_relat_1(B_32)) | ~v1_relat_1(B_32) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.79/2.02  tff(c_232, plain, (![B_32]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_32))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_32)) | ~v1_relat_1(B_32) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_220])).
% 3.79/2.02  tff(c_237, plain, (![B_33]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_33))=k1_xboole_0 | ~v1_relat_1(B_33))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6, c_28, c_232])).
% 3.79/2.02  tff(c_14, plain, (![A_7]: (~v1_xboole_0(k1_relat_1(A_7)) | ~v1_relat_1(A_7) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.79/2.02  tff(c_246, plain, (![B_33]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_33)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_33)) | ~v1_relat_1(B_33))), inference(superposition, [status(thm), theory('equality')], [c_237, c_14])).
% 3.79/2.02  tff(c_287, plain, (![B_34]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_34)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_34)) | ~v1_relat_1(B_34))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_246])).
% 3.79/2.02  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.79/2.02  tff(c_299, plain, (![B_35]: (k5_relat_1(k1_xboole_0, B_35)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_35)) | ~v1_relat_1(B_35))), inference(resolution, [status(thm)], [c_287, c_4])).
% 3.79/2.02  tff(c_306, plain, (![B_6]: (k5_relat_1(k1_xboole_0, B_6)=k1_xboole_0 | ~v1_relat_1(B_6) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_299])).
% 3.79/2.02  tff(c_310, plain, (![B_36]: (k5_relat_1(k1_xboole_0, B_36)=k1_xboole_0 | ~v1_relat_1(B_36))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_306])).
% 3.79/2.02  tff(c_322, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_310])).
% 3.79/2.02  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_322])).
% 3.79/2.02  tff(c_330, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 3.79/2.02  tff(c_10, plain, (![A_4]: (v1_relat_1(k4_relat_1(A_4)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.79/2.02  tff(c_20, plain, (![A_9]: (k1_relat_1(k4_relat_1(A_9))=k2_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.79/2.02  tff(c_368, plain, (![A_39]: (~v1_xboole_0(k1_relat_1(A_39)) | ~v1_relat_1(A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.79/2.02  tff(c_413, plain, (![A_45]: (~v1_xboole_0(k2_relat_1(A_45)) | ~v1_relat_1(k4_relat_1(A_45)) | v1_xboole_0(k4_relat_1(A_45)) | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_20, c_368])).
% 3.79/2.02  tff(c_425, plain, (![A_46]: (k4_relat_1(A_46)=k1_xboole_0 | ~v1_xboole_0(k2_relat_1(A_46)) | ~v1_relat_1(k4_relat_1(A_46)) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_413, c_4])).
% 3.79/2.02  tff(c_431, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_425])).
% 3.79/2.02  tff(c_433, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2, c_431])).
% 3.79/2.02  tff(c_434, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_433])).
% 3.79/2.02  tff(c_437, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_434])).
% 3.79/2.02  tff(c_441, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_437])).
% 3.79/2.02  tff(c_442, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_433])).
% 3.79/2.02  tff(c_24, plain, (![B_15, A_13]: (k5_relat_1(k4_relat_1(B_15), k4_relat_1(A_13))=k4_relat_1(k5_relat_1(A_13, B_15)) | ~v1_relat_1(B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.79/2.02  tff(c_450, plain, (![A_13]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_13))=k4_relat_1(k5_relat_1(A_13, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_442, c_24])).
% 3.79/2.02  tff(c_639, plain, (![A_55]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_55))=k4_relat_1(k5_relat_1(A_55, k1_xboole_0)) | ~v1_relat_1(A_55))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_450])).
% 3.79/2.02  tff(c_483, plain, (![A_47, B_48]: (k1_relat_1(k5_relat_1(A_47, B_48))=k1_relat_1(A_47) | ~r1_tarski(k2_relat_1(A_47), k1_relat_1(B_48)) | ~v1_relat_1(B_48) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.79/2.02  tff(c_495, plain, (![B_48]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_48))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_48)) | ~v1_relat_1(B_48) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_483])).
% 3.79/2.02  tff(c_501, plain, (![B_49]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_49))=k1_xboole_0 | ~v1_relat_1(B_49))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6, c_28, c_495])).
% 3.79/2.02  tff(c_510, plain, (![B_49]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_49)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_49)) | ~v1_relat_1(B_49))), inference(superposition, [status(thm), theory('equality')], [c_501, c_14])).
% 3.79/2.02  tff(c_523, plain, (![B_50]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_50)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_50)) | ~v1_relat_1(B_50))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_510])).
% 3.79/2.02  tff(c_537, plain, (![B_51]: (k5_relat_1(k1_xboole_0, B_51)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_51)) | ~v1_relat_1(B_51))), inference(resolution, [status(thm)], [c_523, c_4])).
% 3.79/2.02  tff(c_541, plain, (![B_6]: (k5_relat_1(k1_xboole_0, B_6)=k1_xboole_0 | ~v1_relat_1(B_6) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_537])).
% 3.79/2.02  tff(c_550, plain, (![B_52]: (k5_relat_1(k1_xboole_0, B_52)=k1_xboole_0 | ~v1_relat_1(B_52))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_541])).
% 3.79/2.02  tff(c_564, plain, (![A_4]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_4))=k1_xboole_0 | ~v1_relat_1(A_4))), inference(resolution, [status(thm)], [c_10, c_550])).
% 3.79/2.02  tff(c_682, plain, (![A_57]: (k4_relat_1(k5_relat_1(A_57, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_57) | ~v1_relat_1(A_57))), inference(superposition, [status(thm), theory('equality')], [c_639, c_564])).
% 3.79/2.02  tff(c_16, plain, (![A_8]: (k4_relat_1(k4_relat_1(A_8))=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.79/2.02  tff(c_712, plain, (![A_57]: (k5_relat_1(A_57, k1_xboole_0)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_57, k1_xboole_0)) | ~v1_relat_1(A_57) | ~v1_relat_1(A_57))), inference(superposition, [status(thm), theory('equality')], [c_682, c_16])).
% 3.79/2.02  tff(c_1089, plain, (![A_67]: (k5_relat_1(A_67, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_67, k1_xboole_0)) | ~v1_relat_1(A_67) | ~v1_relat_1(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_442, c_712])).
% 3.79/2.02  tff(c_1099, plain, (![A_5]: (k5_relat_1(A_5, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_12, c_1089])).
% 3.79/2.02  tff(c_1105, plain, (![A_68]: (k5_relat_1(A_68, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1099])).
% 3.79/2.02  tff(c_1126, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_1105])).
% 3.79/2.02  tff(c_1137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_330, c_1126])).
% 3.79/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/2.02  
% 3.79/2.02  Inference rules
% 3.79/2.02  ----------------------
% 3.79/2.02  #Ref     : 0
% 3.79/2.02  #Sup     : 258
% 3.79/2.02  #Fact    : 0
% 3.79/2.02  #Define  : 0
% 3.79/2.02  #Split   : 3
% 3.79/2.02  #Chain   : 0
% 3.79/2.02  #Close   : 0
% 3.79/2.02  
% 3.79/2.02  Ordering : KBO
% 3.79/2.02  
% 3.79/2.02  Simplification rules
% 3.79/2.02  ----------------------
% 3.79/2.02  #Subsume      : 13
% 3.79/2.02  #Demod        : 279
% 3.79/2.02  #Tautology    : 148
% 3.79/2.02  #SimpNegUnit  : 2
% 3.79/2.02  #BackRed      : 0
% 3.79/2.02  
% 3.79/2.02  #Partial instantiations: 0
% 3.79/2.02  #Strategies tried      : 1
% 3.79/2.02  
% 3.79/2.02  Timing (in seconds)
% 3.79/2.02  ----------------------
% 3.79/2.03  Preprocessing        : 0.45
% 3.79/2.03  Parsing              : 0.25
% 3.79/2.03  CNF conversion       : 0.03
% 3.79/2.03  Main loop            : 0.63
% 3.79/2.03  Inferencing          : 0.24
% 3.79/2.03  Reduction            : 0.18
% 3.79/2.03  Demodulation         : 0.12
% 3.79/2.03  BG Simplification    : 0.03
% 3.79/2.03  Subsumption          : 0.13
% 3.79/2.03  Abstraction          : 0.03
% 3.79/2.03  MUC search           : 0.00
% 3.79/2.03  Cooper               : 0.00
% 3.79/2.03  Total                : 1.14
% 3.79/2.03  Index Insertion      : 0.00
% 3.79/2.03  Index Deletion       : 0.00
% 3.79/2.03  Index Matching       : 0.00
% 3.79/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
