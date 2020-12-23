%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:21 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   50 (  53 expanded)
%              Number of leaves         :   30 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 (  40 expanded)
%              Number of equality atoms :   25 (  29 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0

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

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_61,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_34,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_32,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_30,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_34,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_43,plain,(
    ! [A_33] :
      ( v1_relat_1(A_33)
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_47,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_43])).

tff(c_10,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_64,plain,(
    ! [B_36,A_37] : k3_xboole_0(B_36,A_37) = k3_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [A_37] : k3_xboole_0(k1_xboole_0,A_37) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_8])).

tff(c_174,plain,(
    ! [A_45,B_46] : k5_xboole_0(A_45,k3_xboole_0(A_45,B_46)) = k4_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_183,plain,(
    ! [A_37] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_174])).

tff(c_209,plain,(
    ! [A_48] : k4_xboole_0(k1_xboole_0,A_48) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_183])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_218,plain,(
    ! [A_48] : k5_xboole_0(A_48,k1_xboole_0) = k2_xboole_0(A_48,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_12])).

tff(c_227,plain,(
    ! [A_48] : k2_xboole_0(A_48,k1_xboole_0) = A_48 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_218])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_333,plain,(
    ! [A_56] :
      ( k2_xboole_0(k1_relat_1(A_56),k2_relat_1(A_56)) = k3_relat_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_342,plain,
    ( k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_333])).

tff(c_349,plain,(
    k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_227,c_32,c_342])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:46:17 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.20  
% 1.99/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.20  %$ v1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0
% 1.99/1.20  
% 1.99/1.20  %Foreground sorts:
% 1.99/1.20  
% 1.99/1.20  
% 1.99/1.20  %Background operators:
% 1.99/1.20  
% 1.99/1.20  
% 1.99/1.20  %Foreground operators:
% 1.99/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.99/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.99/1.20  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.99/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.99/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.99/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.99/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.99/1.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.99/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.99/1.20  
% 1.99/1.21  tff(f_61, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_relat_1)).
% 1.99/1.21  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.99/1.21  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.99/1.21  tff(f_34, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 1.99/1.21  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.99/1.21  tff(f_32, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.99/1.21  tff(f_30, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.99/1.21  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.99/1.21  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.99/1.21  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 1.99/1.21  tff(c_34, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.99/1.21  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.99/1.21  tff(c_43, plain, (![A_33]: (v1_relat_1(A_33) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.99/1.21  tff(c_47, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_43])).
% 1.99/1.21  tff(c_10, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.99/1.21  tff(c_64, plain, (![B_36, A_37]: (k3_xboole_0(B_36, A_37)=k3_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.99/1.21  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.99/1.21  tff(c_80, plain, (![A_37]: (k3_xboole_0(k1_xboole_0, A_37)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_64, c_8])).
% 1.99/1.21  tff(c_174, plain, (![A_45, B_46]: (k5_xboole_0(A_45, k3_xboole_0(A_45, B_46))=k4_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.99/1.21  tff(c_183, plain, (![A_37]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_37))), inference(superposition, [status(thm), theory('equality')], [c_80, c_174])).
% 1.99/1.21  tff(c_209, plain, (![A_48]: (k4_xboole_0(k1_xboole_0, A_48)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_183])).
% 1.99/1.21  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.99/1.21  tff(c_218, plain, (![A_48]: (k5_xboole_0(A_48, k1_xboole_0)=k2_xboole_0(A_48, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_209, c_12])).
% 1.99/1.21  tff(c_227, plain, (![A_48]: (k2_xboole_0(A_48, k1_xboole_0)=A_48)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_218])).
% 1.99/1.21  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.99/1.21  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.99/1.21  tff(c_333, plain, (![A_56]: (k2_xboole_0(k1_relat_1(A_56), k2_relat_1(A_56))=k3_relat_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.21  tff(c_342, plain, (k2_xboole_0(k1_relat_1(k1_xboole_0), k1_xboole_0)=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_333])).
% 1.99/1.21  tff(c_349, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_47, c_227, c_32, c_342])).
% 1.99/1.21  tff(c_351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_349])).
% 1.99/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.21  
% 1.99/1.21  Inference rules
% 1.99/1.21  ----------------------
% 1.99/1.21  #Ref     : 0
% 1.99/1.21  #Sup     : 75
% 1.99/1.21  #Fact    : 0
% 1.99/1.21  #Define  : 0
% 1.99/1.21  #Split   : 0
% 1.99/1.21  #Chain   : 0
% 1.99/1.21  #Close   : 0
% 1.99/1.21  
% 1.99/1.21  Ordering : KBO
% 1.99/1.21  
% 1.99/1.21  Simplification rules
% 1.99/1.21  ----------------------
% 1.99/1.21  #Subsume      : 0
% 1.99/1.21  #Demod        : 36
% 1.99/1.21  #Tautology    : 66
% 1.99/1.21  #SimpNegUnit  : 1
% 1.99/1.21  #BackRed      : 0
% 1.99/1.21  
% 1.99/1.21  #Partial instantiations: 0
% 1.99/1.21  #Strategies tried      : 1
% 1.99/1.21  
% 1.99/1.21  Timing (in seconds)
% 1.99/1.21  ----------------------
% 1.99/1.21  Preprocessing        : 0.30
% 1.99/1.21  Parsing              : 0.17
% 1.99/1.21  CNF conversion       : 0.02
% 1.99/1.21  Main loop            : 0.15
% 1.99/1.21  Inferencing          : 0.06
% 1.99/1.21  Reduction            : 0.05
% 1.99/1.21  Demodulation         : 0.04
% 1.99/1.21  BG Simplification    : 0.01
% 1.99/1.21  Subsumption          : 0.02
% 1.99/1.21  Abstraction          : 0.01
% 1.99/1.21  MUC search           : 0.00
% 1.99/1.21  Cooper               : 0.00
% 1.99/1.21  Total                : 0.48
% 1.99/1.21  Index Insertion      : 0.00
% 1.99/1.21  Index Deletion       : 0.00
% 1.99/1.21  Index Matching       : 0.00
% 1.99/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
