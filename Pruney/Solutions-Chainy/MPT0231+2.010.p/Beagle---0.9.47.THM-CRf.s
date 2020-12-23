%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:16 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   47 (  64 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   39 (  72 expanded)
%              Number of equality atoms :   24 (  42 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_36,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    ! [B_38] : r1_tarski(k1_xboole_0,k1_tarski(B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_94,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_110,plain,(
    ! [B_38] : k3_xboole_0(k1_xboole_0,k1_tarski(B_38)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_94])).

tff(c_38,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_169,plain,(
    ! [B_69,A_70] :
      ( k1_tarski(B_69) = A_70
      | k1_xboole_0 = A_70
      | ~ r1_tarski(A_70,k1_tarski(B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_179,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_169])).

tff(c_206,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_32,plain,(
    ! [A_39,B_40] : r1_tarski(k1_tarski(A_39),k2_tarski(A_39,B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_108,plain,(
    ! [A_39,B_40] : k3_xboole_0(k1_tarski(A_39),k2_tarski(A_39,B_40)) = k1_tarski(A_39) ),
    inference(resolution,[status(thm)],[c_32,c_94])).

tff(c_212,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k1_xboole_0) = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_108])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_242,plain,(
    k3_xboole_0(k1_xboole_0,k1_tarski('#skF_1')) = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_2])).

tff(c_254,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_242])).

tff(c_34,plain,(
    ! [B_42,A_41] :
      ( B_42 = A_41
      | ~ r1_tarski(k1_tarski(A_41),k1_tarski(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_281,plain,(
    ! [B_42] :
      ( B_42 = '#skF_1'
      | ~ r1_tarski(k1_xboole_0,k1_tarski(B_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_34])).

tff(c_312,plain,(
    ! [B_78] : B_78 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_281])).

tff(c_374,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_36])).

tff(c_375,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_386,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_32])).

tff(c_407,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_386,c_34])).

tff(c_416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_407])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.33  
% 2.47/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.33  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.47/1.33  
% 2.47/1.33  %Foreground sorts:
% 2.47/1.33  
% 2.47/1.33  
% 2.47/1.33  %Background operators:
% 2.47/1.33  
% 2.47/1.33  
% 2.47/1.33  %Foreground operators:
% 2.47/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.47/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.47/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.33  
% 2.47/1.34  tff(f_74, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 2.47/1.34  tff(f_63, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.47/1.34  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.47/1.34  tff(f_65, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.47/1.34  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.47/1.34  tff(f_69, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.47/1.34  tff(c_36, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.47/1.34  tff(c_30, plain, (![B_38]: (r1_tarski(k1_xboole_0, k1_tarski(B_38)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.47/1.34  tff(c_94, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=A_54 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.34  tff(c_110, plain, (![B_38]: (k3_xboole_0(k1_xboole_0, k1_tarski(B_38))=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_94])).
% 2.47/1.34  tff(c_38, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.47/1.34  tff(c_169, plain, (![B_69, A_70]: (k1_tarski(B_69)=A_70 | k1_xboole_0=A_70 | ~r1_tarski(A_70, k1_tarski(B_69)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.47/1.34  tff(c_179, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3') | k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_169])).
% 2.47/1.34  tff(c_206, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_179])).
% 2.47/1.34  tff(c_32, plain, (![A_39, B_40]: (r1_tarski(k1_tarski(A_39), k2_tarski(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.47/1.34  tff(c_108, plain, (![A_39, B_40]: (k3_xboole_0(k1_tarski(A_39), k2_tarski(A_39, B_40))=k1_tarski(A_39))), inference(resolution, [status(thm)], [c_32, c_94])).
% 2.47/1.34  tff(c_212, plain, (k3_xboole_0(k1_tarski('#skF_1'), k1_xboole_0)=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_206, c_108])).
% 2.47/1.34  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.47/1.34  tff(c_242, plain, (k3_xboole_0(k1_xboole_0, k1_tarski('#skF_1'))=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_212, c_2])).
% 2.47/1.34  tff(c_254, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_110, c_242])).
% 2.47/1.34  tff(c_34, plain, (![B_42, A_41]: (B_42=A_41 | ~r1_tarski(k1_tarski(A_41), k1_tarski(B_42)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.47/1.34  tff(c_281, plain, (![B_42]: (B_42='#skF_1' | ~r1_tarski(k1_xboole_0, k1_tarski(B_42)))), inference(superposition, [status(thm), theory('equality')], [c_254, c_34])).
% 2.47/1.34  tff(c_312, plain, (![B_78]: (B_78='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_281])).
% 2.47/1.34  tff(c_374, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_312, c_36])).
% 2.47/1.34  tff(c_375, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_179])).
% 2.47/1.34  tff(c_386, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_375, c_32])).
% 2.47/1.34  tff(c_407, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_386, c_34])).
% 2.47/1.34  tff(c_416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_407])).
% 2.47/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.34  
% 2.47/1.34  Inference rules
% 2.47/1.34  ----------------------
% 2.47/1.34  #Ref     : 0
% 2.47/1.34  #Sup     : 104
% 2.47/1.34  #Fact    : 0
% 2.47/1.34  #Define  : 0
% 2.47/1.34  #Split   : 1
% 2.47/1.34  #Chain   : 0
% 2.47/1.34  #Close   : 0
% 2.47/1.34  
% 2.47/1.34  Ordering : KBO
% 2.47/1.34  
% 2.47/1.34  Simplification rules
% 2.47/1.34  ----------------------
% 2.47/1.34  #Subsume      : 12
% 2.47/1.34  #Demod        : 36
% 2.47/1.34  #Tautology    : 45
% 2.47/1.34  #SimpNegUnit  : 1
% 2.47/1.34  #BackRed      : 6
% 2.47/1.34  
% 2.47/1.34  #Partial instantiations: 0
% 2.47/1.34  #Strategies tried      : 1
% 2.47/1.34  
% 2.47/1.34  Timing (in seconds)
% 2.47/1.34  ----------------------
% 2.47/1.34  Preprocessing        : 0.33
% 2.47/1.34  Parsing              : 0.18
% 2.47/1.34  CNF conversion       : 0.02
% 2.47/1.34  Main loop            : 0.24
% 2.47/1.34  Inferencing          : 0.10
% 2.47/1.34  Reduction            : 0.08
% 2.47/1.34  Demodulation         : 0.06
% 2.47/1.35  BG Simplification    : 0.02
% 2.47/1.35  Subsumption          : 0.04
% 2.47/1.35  Abstraction          : 0.01
% 2.47/1.35  MUC search           : 0.00
% 2.47/1.35  Cooper               : 0.00
% 2.47/1.35  Total                : 0.59
% 2.47/1.35  Index Insertion      : 0.00
% 2.47/1.35  Index Deletion       : 0.00
% 2.47/1.35  Index Matching       : 0.00
% 2.47/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
