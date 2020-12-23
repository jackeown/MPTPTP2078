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
% DateTime   : Thu Dec  3 10:06:44 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   37 (  42 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 (  54 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k2_xboole_0 > k2_wellord1 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k2_wellord1(A,k3_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_wellord1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k8_relat_1(A,k7_relat_1(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_wellord1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_66,plain,(
    ! [A_18] :
      ( k2_xboole_0(k1_relat_1(A_18),k2_relat_1(A_18)) = k3_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    ! [A_18] :
      ( r1_tarski(k1_relat_1(A_18),k3_relat_1(A_18))
      | ~ v1_relat_1(A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_4])).

tff(c_164,plain,(
    ! [B_30,A_31] :
      ( k7_relat_1(B_30,A_31) = B_30
      | ~ r1_tarski(k1_relat_1(B_30),A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_179,plain,(
    ! [A_32] :
      ( k7_relat_1(A_32,k3_relat_1(A_32)) = A_32
      | ~ v1_relat_1(A_32) ) ),
    inference(resolution,[status(thm)],[c_75,c_164])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k8_relat_1(A_10,k7_relat_1(B_11,A_10)) = k2_wellord1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_244,plain,(
    ! [A_37] :
      ( k8_relat_1(k3_relat_1(A_37),A_37) = k2_wellord1(A_37,k3_relat_1(A_37))
      | ~ v1_relat_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_12])).

tff(c_18,plain,(
    ! [B_14,A_15] : k2_xboole_0(B_14,A_15) = k2_xboole_0(A_15,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_33,plain,(
    ! [A_15,B_14] : r1_tarski(A_15,k2_xboole_0(B_14,A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4])).

tff(c_72,plain,(
    ! [A_18] :
      ( r1_tarski(k2_relat_1(A_18),k3_relat_1(A_18))
      | ~ v1_relat_1(A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_33])).

tff(c_84,plain,(
    ! [A_21,B_22] :
      ( k8_relat_1(A_21,B_22) = B_22
      | ~ r1_tarski(k2_relat_1(B_22),A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_96,plain,(
    ! [A_18] :
      ( k8_relat_1(k3_relat_1(A_18),A_18) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(resolution,[status(thm)],[c_72,c_84])).

tff(c_259,plain,(
    ! [A_38] :
      ( k2_wellord1(A_38,k3_relat_1(A_38)) = A_38
      | ~ v1_relat_1(A_38)
      | ~ v1_relat_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_96])).

tff(c_14,plain,(
    k2_wellord1('#skF_1',k3_relat_1('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_265,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_14])).

tff(c_273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_265])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:21:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.24  
% 1.86/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.24  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k2_xboole_0 > k2_wellord1 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1
% 1.98/1.24  
% 1.98/1.24  %Foreground sorts:
% 1.98/1.24  
% 1.98/1.24  
% 1.98/1.24  %Background operators:
% 1.98/1.24  
% 1.98/1.24  
% 1.98/1.24  %Foreground operators:
% 1.98/1.24  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.98/1.24  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.98/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.98/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.98/1.24  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.98/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.99/1.24  
% 1.99/1.25  tff(f_54, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k2_wellord1(A, k3_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_wellord1)).
% 1.99/1.25  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 1.99/1.25  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.99/1.25  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 1.99/1.25  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k8_relat_1(A, k7_relat_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_wellord1)).
% 1.99/1.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.99/1.25  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 1.99/1.25  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.99/1.25  tff(c_66, plain, (![A_18]: (k2_xboole_0(k1_relat_1(A_18), k2_relat_1(A_18))=k3_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.25  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.99/1.25  tff(c_75, plain, (![A_18]: (r1_tarski(k1_relat_1(A_18), k3_relat_1(A_18)) | ~v1_relat_1(A_18))), inference(superposition, [status(thm), theory('equality')], [c_66, c_4])).
% 1.99/1.25  tff(c_164, plain, (![B_30, A_31]: (k7_relat_1(B_30, A_31)=B_30 | ~r1_tarski(k1_relat_1(B_30), A_31) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.99/1.25  tff(c_179, plain, (![A_32]: (k7_relat_1(A_32, k3_relat_1(A_32))=A_32 | ~v1_relat_1(A_32))), inference(resolution, [status(thm)], [c_75, c_164])).
% 1.99/1.25  tff(c_12, plain, (![A_10, B_11]: (k8_relat_1(A_10, k7_relat_1(B_11, A_10))=k2_wellord1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.99/1.25  tff(c_244, plain, (![A_37]: (k8_relat_1(k3_relat_1(A_37), A_37)=k2_wellord1(A_37, k3_relat_1(A_37)) | ~v1_relat_1(A_37) | ~v1_relat_1(A_37))), inference(superposition, [status(thm), theory('equality')], [c_179, c_12])).
% 1.99/1.25  tff(c_18, plain, (![B_14, A_15]: (k2_xboole_0(B_14, A_15)=k2_xboole_0(A_15, B_14))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.99/1.25  tff(c_33, plain, (![A_15, B_14]: (r1_tarski(A_15, k2_xboole_0(B_14, A_15)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_4])).
% 1.99/1.25  tff(c_72, plain, (![A_18]: (r1_tarski(k2_relat_1(A_18), k3_relat_1(A_18)) | ~v1_relat_1(A_18))), inference(superposition, [status(thm), theory('equality')], [c_66, c_33])).
% 1.99/1.25  tff(c_84, plain, (![A_21, B_22]: (k8_relat_1(A_21, B_22)=B_22 | ~r1_tarski(k2_relat_1(B_22), A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.99/1.25  tff(c_96, plain, (![A_18]: (k8_relat_1(k3_relat_1(A_18), A_18)=A_18 | ~v1_relat_1(A_18))), inference(resolution, [status(thm)], [c_72, c_84])).
% 1.99/1.25  tff(c_259, plain, (![A_38]: (k2_wellord1(A_38, k3_relat_1(A_38))=A_38 | ~v1_relat_1(A_38) | ~v1_relat_1(A_38) | ~v1_relat_1(A_38))), inference(superposition, [status(thm), theory('equality')], [c_244, c_96])).
% 1.99/1.25  tff(c_14, plain, (k2_wellord1('#skF_1', k3_relat_1('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.99/1.25  tff(c_265, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_259, c_14])).
% 1.99/1.25  tff(c_273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_265])).
% 1.99/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.25  
% 1.99/1.25  Inference rules
% 1.99/1.25  ----------------------
% 1.99/1.25  #Ref     : 0
% 1.99/1.25  #Sup     : 60
% 1.99/1.25  #Fact    : 0
% 1.99/1.25  #Define  : 0
% 1.99/1.25  #Split   : 0
% 1.99/1.25  #Chain   : 0
% 1.99/1.25  #Close   : 0
% 1.99/1.26  
% 1.99/1.26  Ordering : KBO
% 1.99/1.26  
% 1.99/1.26  Simplification rules
% 1.99/1.26  ----------------------
% 1.99/1.26  #Subsume      : 10
% 1.99/1.26  #Demod        : 4
% 1.99/1.26  #Tautology    : 34
% 1.99/1.26  #SimpNegUnit  : 0
% 1.99/1.26  #BackRed      : 0
% 1.99/1.26  
% 1.99/1.26  #Partial instantiations: 0
% 1.99/1.26  #Strategies tried      : 1
% 1.99/1.26  
% 1.99/1.26  Timing (in seconds)
% 1.99/1.26  ----------------------
% 1.99/1.26  Preprocessing        : 0.25
% 1.99/1.26  Parsing              : 0.14
% 1.99/1.26  CNF conversion       : 0.01
% 1.99/1.26  Main loop            : 0.18
% 1.99/1.26  Inferencing          : 0.08
% 1.99/1.26  Reduction            : 0.06
% 1.99/1.26  Demodulation         : 0.05
% 1.99/1.26  BG Simplification    : 0.01
% 1.99/1.26  Subsumption          : 0.03
% 1.99/1.26  Abstraction          : 0.01
% 1.99/1.26  MUC search           : 0.00
% 1.99/1.26  Cooper               : 0.00
% 1.99/1.26  Total                : 0.46
% 1.99/1.26  Index Insertion      : 0.00
% 1.99/1.26  Index Deletion       : 0.00
% 1.99/1.26  Index Matching       : 0.00
% 1.99/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
