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
% DateTime   : Thu Dec  3 09:49:37 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   34 (  36 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  41 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
        & A != B
        & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(c_22,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [A_18,B_19] : r1_tarski(k1_tarski(A_18),k2_tarski(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_81,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = A_31
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_91,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) = k2_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_81])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_107,plain,(
    ! [A_34,B_35,C_36] :
      ( r1_tarski(A_34,B_35)
      | ~ r1_tarski(A_34,k3_xboole_0(B_35,C_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_136,plain,(
    ! [A_39,A_40,B_41] :
      ( r1_tarski(A_39,A_40)
      | ~ r1_tarski(A_39,k3_xboole_0(B_41,A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_107])).

tff(c_189,plain,(
    ! [A_53] :
      ( r1_tarski(A_53,k2_tarski('#skF_3','#skF_4'))
      | ~ r1_tarski(A_53,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_136])).

tff(c_18,plain,(
    ! [C_22,A_20,B_21] :
      ( C_22 = A_20
      | B_21 = A_20
      | ~ r1_tarski(k1_tarski(A_20),k2_tarski(B_21,C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_204,plain,(
    ! [A_57] :
      ( A_57 = '#skF_4'
      | A_57 = '#skF_3'
      | ~ r1_tarski(k1_tarski(A_57),k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_189,c_18])).

tff(c_211,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_204])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_20,c_211])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:56:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.24  
% 1.95/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.25  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.95/1.25  
% 1.95/1.25  %Foreground sorts:
% 1.95/1.25  
% 1.95/1.25  
% 1.95/1.25  %Background operators:
% 1.95/1.25  
% 1.95/1.25  
% 1.95/1.25  %Foreground operators:
% 1.95/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.95/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.25  
% 1.95/1.25  tff(f_64, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 1.95/1.25  tff(f_45, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.95/1.25  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.95/1.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.95/1.25  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 1.95/1.25  tff(f_54, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 1.95/1.25  tff(c_22, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.95/1.25  tff(c_20, plain, ('#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.95/1.25  tff(c_16, plain, (![A_18, B_19]: (r1_tarski(k1_tarski(A_18), k2_tarski(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.95/1.25  tff(c_24, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.95/1.25  tff(c_81, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=A_31 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.95/1.25  tff(c_91, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))=k2_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_81])).
% 1.95/1.25  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.95/1.25  tff(c_107, plain, (![A_34, B_35, C_36]: (r1_tarski(A_34, B_35) | ~r1_tarski(A_34, k3_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.25  tff(c_136, plain, (![A_39, A_40, B_41]: (r1_tarski(A_39, A_40) | ~r1_tarski(A_39, k3_xboole_0(B_41, A_40)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_107])).
% 1.95/1.25  tff(c_189, plain, (![A_53]: (r1_tarski(A_53, k2_tarski('#skF_3', '#skF_4')) | ~r1_tarski(A_53, k2_tarski('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_91, c_136])).
% 1.95/1.25  tff(c_18, plain, (![C_22, A_20, B_21]: (C_22=A_20 | B_21=A_20 | ~r1_tarski(k1_tarski(A_20), k2_tarski(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.95/1.25  tff(c_204, plain, (![A_57]: (A_57='#skF_4' | A_57='#skF_3' | ~r1_tarski(k1_tarski(A_57), k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_189, c_18])).
% 1.95/1.25  tff(c_211, plain, ('#skF_1'='#skF_4' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_16, c_204])).
% 1.95/1.25  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_20, c_211])).
% 1.95/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.25  
% 1.95/1.25  Inference rules
% 1.95/1.25  ----------------------
% 1.95/1.25  #Ref     : 0
% 1.95/1.25  #Sup     : 46
% 1.95/1.25  #Fact    : 0
% 1.95/1.25  #Define  : 0
% 1.95/1.25  #Split   : 0
% 1.95/1.25  #Chain   : 0
% 1.95/1.25  #Close   : 0
% 1.95/1.25  
% 1.95/1.25  Ordering : KBO
% 1.95/1.25  
% 1.95/1.25  Simplification rules
% 1.95/1.25  ----------------------
% 1.95/1.25  #Subsume      : 4
% 1.95/1.25  #Demod        : 1
% 1.95/1.25  #Tautology    : 29
% 1.95/1.25  #SimpNegUnit  : 1
% 1.95/1.25  #BackRed      : 0
% 1.95/1.25  
% 1.95/1.25  #Partial instantiations: 0
% 1.95/1.25  #Strategies tried      : 1
% 1.95/1.25  
% 1.95/1.25  Timing (in seconds)
% 1.95/1.25  ----------------------
% 1.95/1.26  Preprocessing        : 0.30
% 1.95/1.26  Parsing              : 0.16
% 1.95/1.26  CNF conversion       : 0.02
% 1.95/1.26  Main loop            : 0.16
% 1.95/1.26  Inferencing          : 0.06
% 1.95/1.26  Reduction            : 0.05
% 1.95/1.26  Demodulation         : 0.04
% 1.95/1.26  BG Simplification    : 0.01
% 1.95/1.26  Subsumption          : 0.03
% 1.95/1.26  Abstraction          : 0.01
% 1.95/1.26  MUC search           : 0.00
% 1.95/1.26  Cooper               : 0.00
% 1.95/1.26  Total                : 0.48
% 1.95/1.26  Index Insertion      : 0.00
% 1.95/1.26  Index Deletion       : 0.00
% 1.95/1.26  Index Matching       : 0.00
% 1.95/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
