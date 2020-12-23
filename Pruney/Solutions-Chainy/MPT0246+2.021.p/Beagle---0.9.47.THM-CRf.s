%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:02 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   44 (  52 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 (  74 expanded)
%              Number of equality atoms :   24 (  40 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_40,plain,(
    k1_tarski('#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_51,plain,(
    ! [A_46,B_47] : r1_tarski(k3_xboole_0(A_46,B_47),A_46) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_54,plain,(
    ! [A_6] : r1_tarski(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_51])).

tff(c_78,plain,(
    ! [A_56,B_57] :
      ( r2_hidden(A_56,B_57)
      | ~ r1_tarski(k1_tarski(A_56),B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_87,plain,(
    ! [A_56] : r2_hidden(A_56,k1_tarski(A_56)) ),
    inference(resolution,[status(thm)],[c_54,c_78])).

tff(c_89,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_1'(A_59,B_60),A_59)
      | r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    ! [C_43] :
      ( C_43 = '#skF_3'
      | ~ r2_hidden(C_43,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_94,plain,(
    ! [B_60] :
      ( '#skF_1'('#skF_2',B_60) = '#skF_3'
      | r1_tarski('#skF_2',B_60) ) ),
    inference(resolution,[status(thm)],[c_89,c_36])).

tff(c_119,plain,(
    ! [B_70,A_71] :
      ( k1_tarski(B_70) = A_71
      | k1_xboole_0 = A_71
      | ~ r1_tarski(A_71,k1_tarski(B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_123,plain,(
    ! [B_70] :
      ( k1_tarski(B_70) = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | '#skF_1'('#skF_2',k1_tarski(B_70)) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_94,c_119])).

tff(c_148,plain,(
    ! [B_72] :
      ( k1_tarski(B_72) = '#skF_2'
      | '#skF_1'('#skF_2',k1_tarski(B_72)) = '#skF_3' ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_123])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_239,plain,(
    ! [B_81] :
      ( ~ r2_hidden('#skF_3',k1_tarski(B_81))
      | r1_tarski('#skF_2',k1_tarski(B_81))
      | k1_tarski(B_81) = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_4])).

tff(c_249,plain,
    ( r1_tarski('#skF_2',k1_tarski('#skF_3'))
    | k1_tarski('#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_87,c_239])).

tff(c_254,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_249])).

tff(c_30,plain,(
    ! [B_41,A_40] :
      ( k1_tarski(B_41) = A_40
      | k1_xboole_0 = A_40
      | ~ r1_tarski(A_40,k1_tarski(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_268,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_254,c_30])).

tff(c_275,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_40,c_268])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:20:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.24  
% 2.14/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.24  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.14/1.24  
% 2.14/1.24  %Foreground sorts:
% 2.14/1.24  
% 2.14/1.24  
% 2.14/1.24  %Background operators:
% 2.14/1.24  
% 2.14/1.24  
% 2.14/1.24  %Foreground operators:
% 2.14/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.14/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.14/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.24  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.14/1.24  
% 2.14/1.25  tff(f_75, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.14/1.25  tff(f_34, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.14/1.25  tff(f_36, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.14/1.25  tff(f_54, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.14/1.25  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.14/1.25  tff(f_60, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.14/1.25  tff(c_38, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.14/1.25  tff(c_40, plain, (k1_tarski('#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.14/1.25  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.14/1.25  tff(c_51, plain, (![A_46, B_47]: (r1_tarski(k3_xboole_0(A_46, B_47), A_46))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.14/1.25  tff(c_54, plain, (![A_6]: (r1_tarski(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_51])).
% 2.14/1.25  tff(c_78, plain, (![A_56, B_57]: (r2_hidden(A_56, B_57) | ~r1_tarski(k1_tarski(A_56), B_57))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.14/1.25  tff(c_87, plain, (![A_56]: (r2_hidden(A_56, k1_tarski(A_56)))), inference(resolution, [status(thm)], [c_54, c_78])).
% 2.14/1.25  tff(c_89, plain, (![A_59, B_60]: (r2_hidden('#skF_1'(A_59, B_60), A_59) | r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.14/1.25  tff(c_36, plain, (![C_43]: (C_43='#skF_3' | ~r2_hidden(C_43, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.14/1.25  tff(c_94, plain, (![B_60]: ('#skF_1'('#skF_2', B_60)='#skF_3' | r1_tarski('#skF_2', B_60))), inference(resolution, [status(thm)], [c_89, c_36])).
% 2.14/1.25  tff(c_119, plain, (![B_70, A_71]: (k1_tarski(B_70)=A_71 | k1_xboole_0=A_71 | ~r1_tarski(A_71, k1_tarski(B_70)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.14/1.25  tff(c_123, plain, (![B_70]: (k1_tarski(B_70)='#skF_2' | k1_xboole_0='#skF_2' | '#skF_1'('#skF_2', k1_tarski(B_70))='#skF_3')), inference(resolution, [status(thm)], [c_94, c_119])).
% 2.14/1.25  tff(c_148, plain, (![B_72]: (k1_tarski(B_72)='#skF_2' | '#skF_1'('#skF_2', k1_tarski(B_72))='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_123])).
% 2.14/1.25  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.14/1.25  tff(c_239, plain, (![B_81]: (~r2_hidden('#skF_3', k1_tarski(B_81)) | r1_tarski('#skF_2', k1_tarski(B_81)) | k1_tarski(B_81)='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_148, c_4])).
% 2.14/1.25  tff(c_249, plain, (r1_tarski('#skF_2', k1_tarski('#skF_3')) | k1_tarski('#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_87, c_239])).
% 2.14/1.25  tff(c_254, plain, (r1_tarski('#skF_2', k1_tarski('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_40, c_249])).
% 2.14/1.25  tff(c_30, plain, (![B_41, A_40]: (k1_tarski(B_41)=A_40 | k1_xboole_0=A_40 | ~r1_tarski(A_40, k1_tarski(B_41)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.14/1.25  tff(c_268, plain, (k1_tarski('#skF_3')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_254, c_30])).
% 2.14/1.25  tff(c_275, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_40, c_268])).
% 2.14/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.25  
% 2.14/1.25  Inference rules
% 2.14/1.25  ----------------------
% 2.14/1.25  #Ref     : 0
% 2.14/1.25  #Sup     : 49
% 2.14/1.25  #Fact    : 0
% 2.14/1.25  #Define  : 0
% 2.14/1.25  #Split   : 2
% 2.14/1.25  #Chain   : 0
% 2.14/1.25  #Close   : 0
% 2.14/1.25  
% 2.14/1.25  Ordering : KBO
% 2.14/1.25  
% 2.14/1.25  Simplification rules
% 2.14/1.25  ----------------------
% 2.14/1.25  #Subsume      : 4
% 2.14/1.25  #Demod        : 8
% 2.14/1.25  #Tautology    : 26
% 2.14/1.25  #SimpNegUnit  : 5
% 2.14/1.25  #BackRed      : 0
% 2.14/1.25  
% 2.14/1.25  #Partial instantiations: 0
% 2.14/1.25  #Strategies tried      : 1
% 2.14/1.25  
% 2.14/1.25  Timing (in seconds)
% 2.14/1.25  ----------------------
% 2.14/1.25  Preprocessing        : 0.32
% 2.14/1.25  Parsing              : 0.16
% 2.14/1.25  CNF conversion       : 0.02
% 2.14/1.25  Main loop            : 0.19
% 2.14/1.25  Inferencing          : 0.07
% 2.14/1.25  Reduction            : 0.06
% 2.14/1.25  Demodulation         : 0.04
% 2.14/1.25  BG Simplification    : 0.02
% 2.14/1.25  Subsumption          : 0.04
% 2.14/1.25  Abstraction          : 0.01
% 2.14/1.25  MUC search           : 0.00
% 2.14/1.25  Cooper               : 0.00
% 2.14/1.25  Total                : 0.53
% 2.14/1.25  Index Insertion      : 0.00
% 2.14/1.25  Index Deletion       : 0.00
% 2.14/1.25  Index Matching       : 0.00
% 2.14/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
