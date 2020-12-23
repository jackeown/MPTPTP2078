%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:37 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   63 (  77 expanded)
%              Number of leaves         :   33 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   49 (  65 expanded)
%              Number of equality atoms :   39 (  52 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_63,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_51,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_62,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_36,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_51,plain,(
    ! [A_36] : v1_relat_1(k6_relat_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_53,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_51])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_201,plain,(
    ! [A_50] :
      ( k9_relat_1(A_50,k1_relat_1(A_50)) = k2_relat_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_210,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_201])).

tff(c_214,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_32,c_210])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_128,plain,(
    ! [A_46,B_47] : k5_xboole_0(A_46,k4_xboole_0(B_47,A_46)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_137,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = k2_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_128])).

tff(c_141,plain,(
    ! [A_48] : k2_xboole_0(A_48,k1_xboole_0) = A_48 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_137])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_147,plain,(
    ! [A_48] : k2_xboole_0(k1_xboole_0,A_48) = A_48 ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_2])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_221,plain,(
    ! [A_51,B_52] : k5_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k4_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_230,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_221])).

tff(c_234,plain,(
    ! [A_53] : k4_xboole_0(A_53,k1_xboole_0) = A_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_230])).

tff(c_12,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_240,plain,(
    ! [A_53] : k5_xboole_0(k1_xboole_0,A_53) = k2_xboole_0(k1_xboole_0,A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_12])).

tff(c_258,plain,(
    ! [A_54] : k5_xboole_0(k1_xboole_0,A_54) = A_54 ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_240])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_265,plain,(
    ! [B_4] : k4_xboole_0(k1_xboole_0,B_4) = k3_xboole_0(k1_xboole_0,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_4])).

tff(c_290,plain,(
    ! [B_4] : k3_xboole_0(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_265])).

tff(c_326,plain,(
    ! [B_59,A_60] :
      ( k9_relat_1(B_59,k3_xboole_0(k1_relat_1(B_59),A_60)) = k9_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_339,plain,(
    ! [A_60] :
      ( k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_60)) = k9_relat_1(k1_xboole_0,A_60)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_326])).

tff(c_344,plain,(
    ! [A_60] : k9_relat_1(k1_xboole_0,A_60) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_214,c_290,c_339])).

tff(c_38,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:03:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.21  
% 2.03/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.21  %$ v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.03/1.21  
% 2.03/1.21  %Foreground sorts:
% 2.03/1.21  
% 2.03/1.21  
% 2.03/1.21  %Background operators:
% 2.03/1.21  
% 2.03/1.21  
% 2.03/1.21  %Foreground operators:
% 2.03/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.03/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.03/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.03/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.03/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.21  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.03/1.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.03/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.03/1.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.03/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.03/1.21  
% 2.13/1.22  tff(f_63, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.13/1.22  tff(f_51, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.13/1.22  tff(f_62, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.13/1.22  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.13/1.22  tff(f_33, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.13/1.22  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.13/1.22  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.13/1.22  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.13/1.22  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.13/1.22  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.13/1.22  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_relat_1)).
% 2.13/1.22  tff(f_66, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 2.13/1.22  tff(c_36, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.13/1.22  tff(c_51, plain, (![A_36]: (v1_relat_1(k6_relat_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.13/1.22  tff(c_53, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_51])).
% 2.13/1.22  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.13/1.22  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.13/1.22  tff(c_201, plain, (![A_50]: (k9_relat_1(A_50, k1_relat_1(A_50))=k2_relat_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.13/1.22  tff(c_210, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_201])).
% 2.13/1.22  tff(c_214, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_53, c_32, c_210])).
% 2.13/1.22  tff(c_8, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.22  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.22  tff(c_128, plain, (![A_46, B_47]: (k5_xboole_0(A_46, k4_xboole_0(B_47, A_46))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.22  tff(c_137, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=k2_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_128])).
% 2.13/1.22  tff(c_141, plain, (![A_48]: (k2_xboole_0(A_48, k1_xboole_0)=A_48)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_137])).
% 2.13/1.22  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.13/1.22  tff(c_147, plain, (![A_48]: (k2_xboole_0(k1_xboole_0, A_48)=A_48)), inference(superposition, [status(thm), theory('equality')], [c_141, c_2])).
% 2.13/1.22  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.22  tff(c_221, plain, (![A_51, B_52]: (k5_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k4_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.22  tff(c_230, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_221])).
% 2.13/1.22  tff(c_234, plain, (![A_53]: (k4_xboole_0(A_53, k1_xboole_0)=A_53)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_230])).
% 2.13/1.22  tff(c_12, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.22  tff(c_240, plain, (![A_53]: (k5_xboole_0(k1_xboole_0, A_53)=k2_xboole_0(k1_xboole_0, A_53))), inference(superposition, [status(thm), theory('equality')], [c_234, c_12])).
% 2.13/1.22  tff(c_258, plain, (![A_54]: (k5_xboole_0(k1_xboole_0, A_54)=A_54)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_240])).
% 2.13/1.22  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.22  tff(c_265, plain, (![B_4]: (k4_xboole_0(k1_xboole_0, B_4)=k3_xboole_0(k1_xboole_0, B_4))), inference(superposition, [status(thm), theory('equality')], [c_258, c_4])).
% 2.13/1.22  tff(c_290, plain, (![B_4]: (k3_xboole_0(k1_xboole_0, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_265])).
% 2.13/1.22  tff(c_326, plain, (![B_59, A_60]: (k9_relat_1(B_59, k3_xboole_0(k1_relat_1(B_59), A_60))=k9_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.13/1.22  tff(c_339, plain, (![A_60]: (k9_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_60))=k9_relat_1(k1_xboole_0, A_60) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_326])).
% 2.13/1.22  tff(c_344, plain, (![A_60]: (k9_relat_1(k1_xboole_0, A_60)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_53, c_214, c_290, c_339])).
% 2.13/1.22  tff(c_38, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.13/1.22  tff(c_348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_344, c_38])).
% 2.13/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.22  
% 2.13/1.22  Inference rules
% 2.13/1.22  ----------------------
% 2.13/1.22  #Ref     : 0
% 2.13/1.22  #Sup     : 74
% 2.13/1.22  #Fact    : 0
% 2.13/1.22  #Define  : 0
% 2.13/1.22  #Split   : 0
% 2.13/1.22  #Chain   : 0
% 2.13/1.22  #Close   : 0
% 2.13/1.22  
% 2.13/1.22  Ordering : KBO
% 2.13/1.22  
% 2.13/1.22  Simplification rules
% 2.13/1.22  ----------------------
% 2.13/1.22  #Subsume      : 0
% 2.13/1.22  #Demod        : 26
% 2.13/1.22  #Tautology    : 67
% 2.13/1.22  #SimpNegUnit  : 0
% 2.13/1.22  #BackRed      : 1
% 2.13/1.22  
% 2.13/1.22  #Partial instantiations: 0
% 2.13/1.22  #Strategies tried      : 1
% 2.13/1.22  
% 2.13/1.22  Timing (in seconds)
% 2.13/1.22  ----------------------
% 2.13/1.23  Preprocessing        : 0.31
% 2.13/1.23  Parsing              : 0.17
% 2.13/1.23  CNF conversion       : 0.02
% 2.13/1.23  Main loop            : 0.17
% 2.13/1.23  Inferencing          : 0.07
% 2.13/1.23  Reduction            : 0.06
% 2.13/1.23  Demodulation         : 0.05
% 2.13/1.23  BG Simplification    : 0.01
% 2.13/1.23  Subsumption          : 0.02
% 2.13/1.23  Abstraction          : 0.01
% 2.13/1.23  MUC search           : 0.00
% 2.13/1.23  Cooper               : 0.00
% 2.13/1.23  Total                : 0.50
% 2.13/1.23  Index Insertion      : 0.00
% 2.13/1.23  Index Deletion       : 0.00
% 2.13/1.23  Index Matching       : 0.00
% 2.13/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
