%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:38 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   51 (  59 expanded)
%              Number of leaves         :   31 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  47 expanded)
%              Number of equality atoms :   27 (  34 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_61,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_49,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_60,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_34,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_49,plain,(
    ! [A_40] : v1_relat_1(k6_relat_1(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_51,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_49])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_204,plain,(
    ! [A_53] :
      ( k9_relat_1(A_53,k1_relat_1(A_53)) = k2_relat_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_213,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_204])).

tff(c_217,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_30,c_213])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_173,plain,(
    ! [A_50,B_51] : k5_xboole_0(A_50,k3_xboole_0(A_50,B_51)) = k4_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_68,plain,(
    ! [B_43,A_44] : k5_xboole_0(B_43,A_44) = k5_xboole_0(A_44,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_84,plain,(
    ! [A_44] : k5_xboole_0(k1_xboole_0,A_44) = A_44 ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_8])).

tff(c_180,plain,(
    ! [B_51] : k4_xboole_0(k1_xboole_0,B_51) = k3_xboole_0(k1_xboole_0,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_84])).

tff(c_189,plain,(
    ! [B_51] : k3_xboole_0(k1_xboole_0,B_51) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_180])).

tff(c_240,plain,(
    ! [B_61,A_62] :
      ( k9_relat_1(B_61,k3_xboole_0(k1_relat_1(B_61),A_62)) = k9_relat_1(B_61,A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_249,plain,(
    ! [A_62] :
      ( k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_62)) = k9_relat_1(k1_xboole_0,A_62)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_240])).

tff(c_253,plain,(
    ! [A_62] : k9_relat_1(k1_xboole_0,A_62) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_217,c_189,c_249])).

tff(c_36,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:07:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.31  
% 1.80/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.31  %$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.80/1.31  
% 1.80/1.31  %Foreground sorts:
% 1.80/1.31  
% 1.80/1.31  
% 1.80/1.31  %Background operators:
% 1.80/1.31  
% 1.80/1.31  
% 1.80/1.31  %Foreground operators:
% 1.80/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.80/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.80/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.80/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.80/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.80/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.80/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.80/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.80/1.31  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.80/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.80/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.31  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.80/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.80/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.80/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.80/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.80/1.31  
% 1.80/1.32  tff(f_61, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.80/1.32  tff(f_49, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.80/1.32  tff(f_60, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.80/1.32  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 1.80/1.32  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.80/1.32  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.80/1.32  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 1.80/1.32  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.80/1.32  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_relat_1)).
% 1.80/1.32  tff(f_64, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.80/1.32  tff(c_34, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.80/1.32  tff(c_49, plain, (![A_40]: (v1_relat_1(k6_relat_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.80/1.32  tff(c_51, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_49])).
% 1.80/1.32  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.80/1.32  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.80/1.32  tff(c_204, plain, (![A_53]: (k9_relat_1(A_53, k1_relat_1(A_53))=k2_relat_1(A_53) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.80/1.32  tff(c_213, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_204])).
% 1.80/1.32  tff(c_217, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_51, c_30, c_213])).
% 1.80/1.32  tff(c_6, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.80/1.32  tff(c_173, plain, (![A_50, B_51]: (k5_xboole_0(A_50, k3_xboole_0(A_50, B_51))=k4_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.80/1.32  tff(c_68, plain, (![B_43, A_44]: (k5_xboole_0(B_43, A_44)=k5_xboole_0(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.80/1.32  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.80/1.32  tff(c_84, plain, (![A_44]: (k5_xboole_0(k1_xboole_0, A_44)=A_44)), inference(superposition, [status(thm), theory('equality')], [c_68, c_8])).
% 1.80/1.32  tff(c_180, plain, (![B_51]: (k4_xboole_0(k1_xboole_0, B_51)=k3_xboole_0(k1_xboole_0, B_51))), inference(superposition, [status(thm), theory('equality')], [c_173, c_84])).
% 1.80/1.32  tff(c_189, plain, (![B_51]: (k3_xboole_0(k1_xboole_0, B_51)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_180])).
% 1.80/1.32  tff(c_240, plain, (![B_61, A_62]: (k9_relat_1(B_61, k3_xboole_0(k1_relat_1(B_61), A_62))=k9_relat_1(B_61, A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.80/1.32  tff(c_249, plain, (![A_62]: (k9_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_62))=k9_relat_1(k1_xboole_0, A_62) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_240])).
% 1.80/1.32  tff(c_253, plain, (![A_62]: (k9_relat_1(k1_xboole_0, A_62)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_51, c_217, c_189, c_249])).
% 1.80/1.32  tff(c_36, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.80/1.32  tff(c_257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_253, c_36])).
% 1.80/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.32  
% 1.80/1.32  Inference rules
% 1.80/1.32  ----------------------
% 1.80/1.32  #Ref     : 0
% 1.80/1.32  #Sup     : 54
% 1.80/1.32  #Fact    : 0
% 1.80/1.32  #Define  : 0
% 1.80/1.32  #Split   : 0
% 1.80/1.32  #Chain   : 0
% 1.80/1.32  #Close   : 0
% 1.80/1.32  
% 1.80/1.32  Ordering : KBO
% 1.80/1.32  
% 1.80/1.32  Simplification rules
% 1.80/1.32  ----------------------
% 1.80/1.32  #Subsume      : 0
% 1.80/1.32  #Demod        : 19
% 1.80/1.32  #Tautology    : 50
% 1.80/1.32  #SimpNegUnit  : 0
% 1.80/1.32  #BackRed      : 1
% 1.80/1.32  
% 1.80/1.32  #Partial instantiations: 0
% 1.80/1.32  #Strategies tried      : 1
% 1.80/1.32  
% 1.80/1.32  Timing (in seconds)
% 1.80/1.32  ----------------------
% 1.80/1.33  Preprocessing        : 0.28
% 1.80/1.33  Parsing              : 0.14
% 1.80/1.33  CNF conversion       : 0.02
% 1.80/1.33  Main loop            : 0.14
% 1.80/1.33  Inferencing          : 0.05
% 1.80/1.33  Reduction            : 0.05
% 1.80/1.33  Demodulation         : 0.04
% 1.80/1.33  BG Simplification    : 0.01
% 1.80/1.33  Subsumption          : 0.02
% 1.80/1.33  Abstraction          : 0.01
% 1.80/1.33  MUC search           : 0.00
% 1.80/1.33  Cooper               : 0.00
% 1.80/1.33  Total                : 0.45
% 1.80/1.33  Index Insertion      : 0.00
% 1.80/1.33  Index Deletion       : 0.00
% 1.80/1.33  Index Matching       : 0.00
% 1.80/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
