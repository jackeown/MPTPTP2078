%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:16 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   52 (  68 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   41 (  72 expanded)
%              Number of equality atoms :   24 (  41 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_92,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_48,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    ! [B_49] : r1_tarski(k1_xboole_0,k1_tarski(B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_112,plain,(
    ! [A_69,B_70] :
      ( k3_xboole_0(A_69,B_70) = A_69
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_133,plain,(
    ! [B_49] : k3_xboole_0(k1_xboole_0,k1_tarski(B_49)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_112])).

tff(c_50,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_378,plain,(
    ! [B_96,A_97] :
      ( k1_tarski(B_96) = A_97
      | k1_xboole_0 = A_97
      | ~ r1_tarski(A_97,k1_tarski(B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_392,plain,
    ( k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5')
    | k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_378])).

tff(c_401,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_392])).

tff(c_40,plain,(
    ! [A_50,B_51] : r1_tarski(k1_tarski(A_50),k2_tarski(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_410,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_40])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_417,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_410,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_453,plain,(
    k3_xboole_0(k1_xboole_0,k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_2])).

tff(c_465,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_453])).

tff(c_46,plain,(
    ! [B_55,A_54] :
      ( B_55 = A_54
      | ~ r1_tarski(k1_tarski(A_54),k1_tarski(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_493,plain,(
    ! [B_55] :
      ( B_55 = '#skF_3'
      | ~ r1_tarski(k1_xboole_0,k1_tarski(B_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_46])).

tff(c_534,plain,(
    ! [B_101] : B_101 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_493])).

tff(c_663,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_48])).

tff(c_664,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_392])).

tff(c_676,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_664,c_40])).

tff(c_686,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_676,c_46])).

tff(c_694,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_686])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:18:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.48  
% 2.96/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.48  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.96/1.48  
% 2.96/1.48  %Foreground sorts:
% 2.96/1.48  
% 2.96/1.48  
% 2.96/1.48  %Background operators:
% 2.96/1.48  
% 2.96/1.48  
% 2.96/1.48  %Foreground operators:
% 2.96/1.48  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.96/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.96/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.96/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.96/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.96/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.96/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.96/1.48  tff('#skF_5', type, '#skF_5': $i).
% 2.96/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.96/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.96/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.96/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.96/1.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.96/1.48  
% 2.96/1.49  tff(f_97, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 2.96/1.49  tff(f_81, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.96/1.49  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.96/1.49  tff(f_83, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.96/1.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.96/1.49  tff(f_92, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.96/1.49  tff(c_48, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.96/1.49  tff(c_38, plain, (![B_49]: (r1_tarski(k1_xboole_0, k1_tarski(B_49)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.96/1.49  tff(c_112, plain, (![A_69, B_70]: (k3_xboole_0(A_69, B_70)=A_69 | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.96/1.49  tff(c_133, plain, (![B_49]: (k3_xboole_0(k1_xboole_0, k1_tarski(B_49))=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_112])).
% 2.96/1.49  tff(c_50, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.96/1.49  tff(c_378, plain, (![B_96, A_97]: (k1_tarski(B_96)=A_97 | k1_xboole_0=A_97 | ~r1_tarski(A_97, k1_tarski(B_96)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.96/1.49  tff(c_392, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5') | k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_378])).
% 2.96/1.49  tff(c_401, plain, (k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_392])).
% 2.96/1.49  tff(c_40, plain, (![A_50, B_51]: (r1_tarski(k1_tarski(A_50), k2_tarski(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.96/1.49  tff(c_410, plain, (r1_tarski(k1_tarski('#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_401, c_40])).
% 2.96/1.49  tff(c_14, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.96/1.49  tff(c_417, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_410, c_14])).
% 2.96/1.49  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.96/1.49  tff(c_453, plain, (k3_xboole_0(k1_xboole_0, k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_417, c_2])).
% 2.96/1.49  tff(c_465, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_133, c_453])).
% 2.96/1.49  tff(c_46, plain, (![B_55, A_54]: (B_55=A_54 | ~r1_tarski(k1_tarski(A_54), k1_tarski(B_55)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.96/1.49  tff(c_493, plain, (![B_55]: (B_55='#skF_3' | ~r1_tarski(k1_xboole_0, k1_tarski(B_55)))), inference(superposition, [status(thm), theory('equality')], [c_465, c_46])).
% 2.96/1.49  tff(c_534, plain, (![B_101]: (B_101='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_493])).
% 2.96/1.49  tff(c_663, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_534, c_48])).
% 2.96/1.49  tff(c_664, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_392])).
% 2.96/1.49  tff(c_676, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_664, c_40])).
% 2.96/1.49  tff(c_686, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_676, c_46])).
% 2.96/1.49  tff(c_694, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_686])).
% 2.96/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.49  
% 2.96/1.49  Inference rules
% 2.96/1.49  ----------------------
% 2.96/1.49  #Ref     : 0
% 2.96/1.49  #Sup     : 194
% 2.96/1.49  #Fact    : 0
% 2.96/1.49  #Define  : 0
% 2.96/1.49  #Split   : 1
% 2.96/1.49  #Chain   : 0
% 2.96/1.49  #Close   : 0
% 2.96/1.49  
% 2.96/1.49  Ordering : KBO
% 2.96/1.49  
% 2.96/1.49  Simplification rules
% 2.96/1.49  ----------------------
% 2.96/1.49  #Subsume      : 22
% 2.96/1.49  #Demod        : 62
% 2.96/1.49  #Tautology    : 82
% 2.96/1.49  #SimpNegUnit  : 1
% 2.96/1.49  #BackRed      : 9
% 2.96/1.49  
% 2.96/1.49  #Partial instantiations: 34
% 2.96/1.49  #Strategies tried      : 1
% 2.96/1.49  
% 2.96/1.49  Timing (in seconds)
% 2.96/1.49  ----------------------
% 2.96/1.49  Preprocessing        : 0.35
% 2.96/1.49  Parsing              : 0.19
% 2.96/1.49  CNF conversion       : 0.02
% 2.96/1.49  Main loop            : 0.32
% 2.96/1.49  Inferencing          : 0.13
% 2.96/1.49  Reduction            : 0.11
% 2.96/1.49  Demodulation         : 0.08
% 2.96/1.49  BG Simplification    : 0.02
% 2.96/1.49  Subsumption          : 0.05
% 2.96/1.49  Abstraction          : 0.01
% 2.96/1.49  MUC search           : 0.00
% 2.96/1.49  Cooper               : 0.00
% 2.96/1.49  Total                : 0.70
% 2.96/1.49  Index Insertion      : 0.00
% 2.96/1.50  Index Deletion       : 0.00
% 2.96/1.50  Index Matching       : 0.00
% 2.96/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
