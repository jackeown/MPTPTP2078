%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:44 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  45 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 (  63 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k2_wellord1(A,k3_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k7_relat_1(k8_relat_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ! [A_12] :
      ( k2_xboole_0(k1_relat_1(A_12),k2_relat_1(A_12)) = k3_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_77,plain,(
    ! [A_32,B_33] :
      ( k8_relat_1(A_32,B_33) = B_33
      | ~ r1_tarski(k2_relat_1(B_33),A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_292,plain,(
    ! [C_61,B_62,B_63] :
      ( k8_relat_1(k2_xboole_0(C_61,B_62),B_63) = B_63
      | ~ v1_relat_1(B_63)
      | ~ r1_tarski(k2_relat_1(B_63),B_62) ) ),
    inference(resolution,[status(thm)],[c_8,c_77])).

tff(c_309,plain,(
    ! [C_64,B_65] :
      ( k8_relat_1(k2_xboole_0(C_64,k2_relat_1(B_65)),B_65) = B_65
      | ~ v1_relat_1(B_65) ) ),
    inference(resolution,[status(thm)],[c_6,c_292])).

tff(c_334,plain,(
    ! [A_66] :
      ( k8_relat_1(k3_relat_1(A_66),A_66) = A_66
      | ~ v1_relat_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_309])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( k7_relat_1(k8_relat_1(A_17,B_18),A_17) = k2_wellord1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_498,plain,(
    ! [A_89] :
      ( k7_relat_1(A_89,k3_relat_1(A_89)) = k2_wellord1(A_89,k3_relat_1(A_89))
      | ~ v1_relat_1(A_89)
      | ~ v1_relat_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_22])).

tff(c_62,plain,(
    ! [A_31] :
      ( k2_xboole_0(k1_relat_1(A_31),k2_relat_1(A_31)) = k3_relat_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,(
    ! [A_31] :
      ( r1_tarski(k1_relat_1(A_31),k3_relat_1(A_31))
      | ~ v1_relat_1(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_10])).

tff(c_124,plain,(
    ! [B_40,A_41] :
      ( k7_relat_1(B_40,A_41) = B_40
      | ~ r1_tarski(k1_relat_1(B_40),A_41)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_140,plain,(
    ! [A_31] :
      ( k7_relat_1(A_31,k3_relat_1(A_31)) = A_31
      | ~ v1_relat_1(A_31) ) ),
    inference(resolution,[status(thm)],[c_71,c_124])).

tff(c_513,plain,(
    ! [A_90] :
      ( k2_wellord1(A_90,k3_relat_1(A_90)) = A_90
      | ~ v1_relat_1(A_90)
      | ~ v1_relat_1(A_90)
      | ~ v1_relat_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_140])).

tff(c_24,plain,(
    k2_wellord1('#skF_1',k3_relat_1('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_519,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_24])).

tff(c_527,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_519])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:03:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.27  
% 2.21/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.27  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1
% 2.21/1.27  
% 2.21/1.27  %Foreground sorts:
% 2.21/1.27  
% 2.21/1.27  
% 2.21/1.27  %Background operators:
% 2.21/1.27  
% 2.21/1.27  
% 2.21/1.27  %Foreground operators:
% 2.21/1.27  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.21/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.21/1.27  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.21/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.21/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.21/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.21/1.27  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.21/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.27  
% 2.21/1.28  tff(f_66, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k2_wellord1(A, k3_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_wellord1)).
% 2.21/1.28  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.21/1.28  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.21/1.28  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.21/1.28  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.21/1.28  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k7_relat_1(k8_relat_1(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_wellord1)).
% 2.21/1.28  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.21/1.28  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.21/1.28  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.21/1.28  tff(c_16, plain, (![A_12]: (k2_xboole_0(k1_relat_1(A_12), k2_relat_1(A_12))=k3_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.21/1.28  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.21/1.28  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.21/1.28  tff(c_77, plain, (![A_32, B_33]: (k8_relat_1(A_32, B_33)=B_33 | ~r1_tarski(k2_relat_1(B_33), A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.21/1.28  tff(c_292, plain, (![C_61, B_62, B_63]: (k8_relat_1(k2_xboole_0(C_61, B_62), B_63)=B_63 | ~v1_relat_1(B_63) | ~r1_tarski(k2_relat_1(B_63), B_62))), inference(resolution, [status(thm)], [c_8, c_77])).
% 2.21/1.28  tff(c_309, plain, (![C_64, B_65]: (k8_relat_1(k2_xboole_0(C_64, k2_relat_1(B_65)), B_65)=B_65 | ~v1_relat_1(B_65))), inference(resolution, [status(thm)], [c_6, c_292])).
% 2.21/1.28  tff(c_334, plain, (![A_66]: (k8_relat_1(k3_relat_1(A_66), A_66)=A_66 | ~v1_relat_1(A_66) | ~v1_relat_1(A_66))), inference(superposition, [status(thm), theory('equality')], [c_16, c_309])).
% 2.21/1.28  tff(c_22, plain, (![A_17, B_18]: (k7_relat_1(k8_relat_1(A_17, B_18), A_17)=k2_wellord1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.21/1.28  tff(c_498, plain, (![A_89]: (k7_relat_1(A_89, k3_relat_1(A_89))=k2_wellord1(A_89, k3_relat_1(A_89)) | ~v1_relat_1(A_89) | ~v1_relat_1(A_89) | ~v1_relat_1(A_89))), inference(superposition, [status(thm), theory('equality')], [c_334, c_22])).
% 2.21/1.28  tff(c_62, plain, (![A_31]: (k2_xboole_0(k1_relat_1(A_31), k2_relat_1(A_31))=k3_relat_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.21/1.28  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.21/1.28  tff(c_71, plain, (![A_31]: (r1_tarski(k1_relat_1(A_31), k3_relat_1(A_31)) | ~v1_relat_1(A_31))), inference(superposition, [status(thm), theory('equality')], [c_62, c_10])).
% 2.21/1.28  tff(c_124, plain, (![B_40, A_41]: (k7_relat_1(B_40, A_41)=B_40 | ~r1_tarski(k1_relat_1(B_40), A_41) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.21/1.28  tff(c_140, plain, (![A_31]: (k7_relat_1(A_31, k3_relat_1(A_31))=A_31 | ~v1_relat_1(A_31))), inference(resolution, [status(thm)], [c_71, c_124])).
% 2.21/1.28  tff(c_513, plain, (![A_90]: (k2_wellord1(A_90, k3_relat_1(A_90))=A_90 | ~v1_relat_1(A_90) | ~v1_relat_1(A_90) | ~v1_relat_1(A_90) | ~v1_relat_1(A_90))), inference(superposition, [status(thm), theory('equality')], [c_498, c_140])).
% 2.21/1.28  tff(c_24, plain, (k2_wellord1('#skF_1', k3_relat_1('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.21/1.28  tff(c_519, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_513, c_24])).
% 2.21/1.28  tff(c_527, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_519])).
% 2.21/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.28  
% 2.21/1.28  Inference rules
% 2.21/1.28  ----------------------
% 2.21/1.28  #Ref     : 0
% 2.21/1.28  #Sup     : 112
% 2.21/1.28  #Fact    : 0
% 2.21/1.28  #Define  : 0
% 2.21/1.28  #Split   : 0
% 2.21/1.28  #Chain   : 0
% 2.21/1.28  #Close   : 0
% 2.21/1.28  
% 2.21/1.28  Ordering : KBO
% 2.21/1.28  
% 2.21/1.28  Simplification rules
% 2.21/1.28  ----------------------
% 2.21/1.28  #Subsume      : 3
% 2.21/1.28  #Demod        : 3
% 2.21/1.28  #Tautology    : 61
% 2.21/1.28  #SimpNegUnit  : 0
% 2.21/1.28  #BackRed      : 0
% 2.21/1.28  
% 2.21/1.28  #Partial instantiations: 0
% 2.21/1.28  #Strategies tried      : 1
% 2.21/1.28  
% 2.21/1.28  Timing (in seconds)
% 2.21/1.28  ----------------------
% 2.21/1.28  Preprocessing        : 0.28
% 2.21/1.28  Parsing              : 0.15
% 2.21/1.28  CNF conversion       : 0.02
% 2.21/1.28  Main loop            : 0.26
% 2.21/1.29  Inferencing          : 0.11
% 2.21/1.29  Reduction            : 0.06
% 2.21/1.29  Demodulation         : 0.05
% 2.21/1.29  BG Simplification    : 0.02
% 2.21/1.29  Subsumption          : 0.05
% 2.21/1.29  Abstraction          : 0.02
% 2.21/1.29  MUC search           : 0.00
% 2.21/1.29  Cooper               : 0.00
% 2.21/1.29  Total                : 0.56
% 2.21/1.29  Index Insertion      : 0.00
% 2.21/1.29  Index Deletion       : 0.00
% 2.21/1.29  Index Matching       : 0.00
% 2.21/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
