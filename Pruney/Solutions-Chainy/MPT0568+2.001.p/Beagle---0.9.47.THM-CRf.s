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
% DateTime   : Thu Dec  3 10:01:20 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   64 (  78 expanded)
%              Number of leaves         :   34 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  69 expanded)
%              Number of equality atoms :   37 (  48 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_67,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_34,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_36,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_32,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_30,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_72,plain,(
    ! [A_46] :
      ( v1_relat_1(A_46)
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_76,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_72])).

tff(c_38,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_201,plain,(
    ! [A_57] :
      ( k10_relat_1(A_57,k2_relat_1(A_57)) = k1_relat_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_210,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_201])).

tff(c_214,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_38,c_210])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_128,plain,(
    ! [A_53,B_54] : k5_xboole_0(A_53,k4_xboole_0(B_54,A_53)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_137,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = k2_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_128])).

tff(c_141,plain,(
    ! [A_55] : k2_xboole_0(A_55,k1_xboole_0) = A_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_137])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_147,plain,(
    ! [A_55] : k2_xboole_0(k1_xboole_0,A_55) = A_55 ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_2])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_221,plain,(
    ! [A_58,B_59] : k5_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_230,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_221])).

tff(c_234,plain,(
    ! [A_60] : k4_xboole_0(A_60,k1_xboole_0) = A_60 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_230])).

tff(c_14,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_240,plain,(
    ! [A_60] : k5_xboole_0(k1_xboole_0,A_60) = k2_xboole_0(k1_xboole_0,A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_14])).

tff(c_258,plain,(
    ! [A_61] : k5_xboole_0(k1_xboole_0,A_61) = A_61 ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_240])).

tff(c_6,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_265,plain,(
    ! [B_4] : k4_xboole_0(k1_xboole_0,B_4) = k3_xboole_0(k1_xboole_0,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_6])).

tff(c_290,plain,(
    ! [B_4] : k3_xboole_0(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_265])).

tff(c_335,plain,(
    ! [B_70,A_71] :
      ( k10_relat_1(B_70,k3_xboole_0(k2_relat_1(B_70),A_71)) = k10_relat_1(B_70,A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_348,plain,(
    ! [A_71] :
      ( k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_71)) = k10_relat_1(k1_xboole_0,A_71)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_335])).

tff(c_353,plain,(
    ! [A_71] : k10_relat_1(k1_xboole_0,A_71) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_214,c_290,c_348])).

tff(c_40,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_357,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:59:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.56  
% 2.54/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.56  %$ v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.54/1.56  
% 2.54/1.56  %Foreground sorts:
% 2.54/1.56  
% 2.54/1.56  
% 2.54/1.56  %Background operators:
% 2.54/1.56  
% 2.54/1.56  
% 2.54/1.56  %Foreground operators:
% 2.54/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.54/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.54/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.54/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.54/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.54/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.54/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.54/1.56  tff('#skF_1', type, '#skF_1': $i).
% 2.54/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.56  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.54/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.54/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.54/1.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.54/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.54/1.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.54/1.56  
% 2.54/1.58  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.54/1.58  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.54/1.58  tff(f_67, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.54/1.58  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.54/1.58  tff(f_34, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.54/1.58  tff(f_36, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.54/1.58  tff(f_38, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.54/1.58  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.54/1.58  tff(f_32, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.54/1.58  tff(f_30, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.54/1.58  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 2.54/1.58  tff(f_70, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.54/1.58  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.54/1.58  tff(c_72, plain, (![A_46]: (v1_relat_1(A_46) | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.54/1.58  tff(c_76, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_72])).
% 2.54/1.58  tff(c_38, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.54/1.58  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.54/1.58  tff(c_201, plain, (![A_57]: (k10_relat_1(A_57, k2_relat_1(A_57))=k1_relat_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.54/1.58  tff(c_210, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_201])).
% 2.54/1.58  tff(c_214, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_76, c_38, c_210])).
% 2.54/1.58  tff(c_10, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.54/1.58  tff(c_12, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.54/1.58  tff(c_128, plain, (![A_53, B_54]: (k5_xboole_0(A_53, k4_xboole_0(B_54, A_53))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.54/1.58  tff(c_137, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=k2_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_128])).
% 2.54/1.58  tff(c_141, plain, (![A_55]: (k2_xboole_0(A_55, k1_xboole_0)=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_137])).
% 2.54/1.58  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.54/1.58  tff(c_147, plain, (![A_55]: (k2_xboole_0(k1_xboole_0, A_55)=A_55)), inference(superposition, [status(thm), theory('equality')], [c_141, c_2])).
% 2.54/1.58  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.54/1.58  tff(c_221, plain, (![A_58, B_59]: (k5_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.54/1.58  tff(c_230, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_221])).
% 2.54/1.58  tff(c_234, plain, (![A_60]: (k4_xboole_0(A_60, k1_xboole_0)=A_60)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_230])).
% 2.54/1.58  tff(c_14, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.54/1.58  tff(c_240, plain, (![A_60]: (k5_xboole_0(k1_xboole_0, A_60)=k2_xboole_0(k1_xboole_0, A_60))), inference(superposition, [status(thm), theory('equality')], [c_234, c_14])).
% 2.54/1.58  tff(c_258, plain, (![A_61]: (k5_xboole_0(k1_xboole_0, A_61)=A_61)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_240])).
% 2.54/1.58  tff(c_6, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.54/1.58  tff(c_265, plain, (![B_4]: (k4_xboole_0(k1_xboole_0, B_4)=k3_xboole_0(k1_xboole_0, B_4))), inference(superposition, [status(thm), theory('equality')], [c_258, c_6])).
% 2.54/1.58  tff(c_290, plain, (![B_4]: (k3_xboole_0(k1_xboole_0, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_265])).
% 2.54/1.58  tff(c_335, plain, (![B_70, A_71]: (k10_relat_1(B_70, k3_xboole_0(k2_relat_1(B_70), A_71))=k10_relat_1(B_70, A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.54/1.58  tff(c_348, plain, (![A_71]: (k10_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_71))=k10_relat_1(k1_xboole_0, A_71) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_335])).
% 2.54/1.58  tff(c_353, plain, (![A_71]: (k10_relat_1(k1_xboole_0, A_71)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_214, c_290, c_348])).
% 2.54/1.58  tff(c_40, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.54/1.58  tff(c_357, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_353, c_40])).
% 2.54/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.58  
% 2.54/1.58  Inference rules
% 2.54/1.58  ----------------------
% 2.54/1.58  #Ref     : 0
% 2.54/1.58  #Sup     : 74
% 2.54/1.58  #Fact    : 0
% 2.54/1.58  #Define  : 0
% 2.54/1.58  #Split   : 0
% 2.54/1.58  #Chain   : 0
% 2.54/1.58  #Close   : 0
% 2.54/1.58  
% 2.54/1.58  Ordering : KBO
% 2.54/1.58  
% 2.54/1.58  Simplification rules
% 2.54/1.58  ----------------------
% 2.54/1.58  #Subsume      : 0
% 2.54/1.58  #Demod        : 26
% 2.54/1.58  #Tautology    : 67
% 2.54/1.58  #SimpNegUnit  : 0
% 2.54/1.58  #BackRed      : 1
% 2.54/1.58  
% 2.54/1.58  #Partial instantiations: 0
% 2.54/1.58  #Strategies tried      : 1
% 2.54/1.58  
% 2.54/1.58  Timing (in seconds)
% 2.54/1.58  ----------------------
% 2.54/1.59  Preprocessing        : 0.51
% 2.54/1.59  Parsing              : 0.28
% 2.54/1.59  CNF conversion       : 0.03
% 2.54/1.59  Main loop            : 0.28
% 2.54/1.59  Inferencing          : 0.11
% 2.54/1.59  Reduction            : 0.09
% 2.54/1.59  Demodulation         : 0.07
% 2.54/1.59  BG Simplification    : 0.02
% 2.54/1.59  Subsumption          : 0.03
% 2.54/1.59  Abstraction          : 0.02
% 2.54/1.59  MUC search           : 0.00
% 2.54/1.59  Cooper               : 0.00
% 2.54/1.59  Total                : 0.84
% 2.54/1.59  Index Insertion      : 0.00
% 2.54/1.59  Index Deletion       : 0.00
% 2.54/1.59  Index Matching       : 0.00
% 2.54/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
