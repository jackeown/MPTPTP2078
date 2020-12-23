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
% DateTime   : Thu Dec  3 09:42:46 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   31 (  32 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  32 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k4_xboole_0(B,A))
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_38,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_5'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_44,plain,(
    r1_tarski('#skF_6',k4_xboole_0('#skF_7','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_46,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,(
    k3_xboole_0('#skF_6',k4_xboole_0('#skF_7','#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_44,c_46])).

tff(c_55,plain,(
    ! [D_20,B_21,A_22] :
      ( r2_hidden(D_20,B_21)
      | ~ r2_hidden(D_20,k3_xboole_0(A_22,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_85,plain,(
    ! [D_32] :
      ( r2_hidden(D_32,k4_xboole_0('#skF_7','#skF_6'))
      | ~ r2_hidden(D_32,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_55])).

tff(c_22,plain,(
    ! [D_12,B_8,A_7] :
      ( ~ r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_94,plain,(
    ! [D_33] : ~ r2_hidden(D_33,'#skF_6') ),
    inference(resolution,[status(thm)],[c_85,c_22])).

tff(c_98,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_38,c_94])).

tff(c_102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_98])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.19  
% 1.84/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.19  %$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_3
% 1.84/1.19  
% 1.84/1.19  %Foreground sorts:
% 1.84/1.19  
% 1.84/1.19  
% 1.84/1.19  %Background operators:
% 1.84/1.19  
% 1.84/1.19  
% 1.84/1.19  %Foreground operators:
% 1.84/1.19  tff('#skF_5', type, '#skF_5': $i > $i).
% 1.84/1.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.84/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.19  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.84/1.19  tff('#skF_7', type, '#skF_7': $i).
% 1.84/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.19  tff('#skF_6', type, '#skF_6': $i).
% 1.84/1.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.19  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.19  
% 1.84/1.20  tff(f_61, negated_conjecture, ~(![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 1.84/1.20  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.84/1.20  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.84/1.20  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.84/1.20  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.84/1.20  tff(c_42, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.84/1.20  tff(c_38, plain, (![A_13]: (r2_hidden('#skF_5'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.84/1.20  tff(c_44, plain, (r1_tarski('#skF_6', k4_xboole_0('#skF_7', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.84/1.20  tff(c_46, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.84/1.20  tff(c_50, plain, (k3_xboole_0('#skF_6', k4_xboole_0('#skF_7', '#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_44, c_46])).
% 1.84/1.20  tff(c_55, plain, (![D_20, B_21, A_22]: (r2_hidden(D_20, B_21) | ~r2_hidden(D_20, k3_xboole_0(A_22, B_21)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.84/1.20  tff(c_85, plain, (![D_32]: (r2_hidden(D_32, k4_xboole_0('#skF_7', '#skF_6')) | ~r2_hidden(D_32, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_55])).
% 1.84/1.20  tff(c_22, plain, (![D_12, B_8, A_7]: (~r2_hidden(D_12, B_8) | ~r2_hidden(D_12, k4_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.84/1.20  tff(c_94, plain, (![D_33]: (~r2_hidden(D_33, '#skF_6'))), inference(resolution, [status(thm)], [c_85, c_22])).
% 1.84/1.20  tff(c_98, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_38, c_94])).
% 1.84/1.20  tff(c_102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_98])).
% 1.84/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.20  
% 1.84/1.20  Inference rules
% 1.84/1.20  ----------------------
% 1.84/1.20  #Ref     : 0
% 1.84/1.20  #Sup     : 12
% 1.84/1.20  #Fact    : 0
% 1.84/1.20  #Define  : 0
% 1.84/1.20  #Split   : 0
% 1.84/1.20  #Chain   : 0
% 1.84/1.20  #Close   : 0
% 1.84/1.20  
% 1.84/1.20  Ordering : KBO
% 1.84/1.20  
% 1.84/1.20  Simplification rules
% 1.84/1.20  ----------------------
% 1.84/1.20  #Subsume      : 1
% 1.84/1.20  #Demod        : 0
% 1.84/1.20  #Tautology    : 3
% 1.84/1.20  #SimpNegUnit  : 1
% 1.84/1.20  #BackRed      : 0
% 1.84/1.20  
% 1.84/1.20  #Partial instantiations: 0
% 1.84/1.20  #Strategies tried      : 1
% 1.84/1.20  
% 1.84/1.20  Timing (in seconds)
% 1.84/1.20  ----------------------
% 1.84/1.21  Preprocessing        : 0.31
% 1.84/1.21  Parsing              : 0.16
% 1.84/1.21  CNF conversion       : 0.02
% 1.84/1.21  Main loop            : 0.11
% 1.84/1.21  Inferencing          : 0.03
% 1.84/1.21  Reduction            : 0.03
% 1.84/1.21  Demodulation         : 0.02
% 1.84/1.21  BG Simplification    : 0.02
% 1.84/1.21  Subsumption          : 0.03
% 1.84/1.21  Abstraction          : 0.01
% 1.84/1.21  MUC search           : 0.00
% 1.84/1.21  Cooper               : 0.00
% 1.84/1.21  Total                : 0.45
% 1.84/1.21  Index Insertion      : 0.00
% 1.84/1.21  Index Deletion       : 0.00
% 1.84/1.21  Index Matching       : 0.00
% 1.84/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
