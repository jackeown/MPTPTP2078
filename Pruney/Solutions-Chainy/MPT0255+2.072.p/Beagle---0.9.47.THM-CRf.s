%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:48 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   41 (  56 expanded)
%              Number of leaves         :   27 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  71 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_65,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_167,plain,(
    ! [A_60,B_61] :
      ( ~ r2_hidden('#skF_1'(A_60,B_61),B_61)
      | r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_204,plain,(
    ! [A_63] : r1_tarski(A_63,A_63) ),
    inference(resolution,[status(thm)],[c_8,c_167])).

tff(c_48,plain,(
    ! [A_29,C_31,B_30] :
      ( r2_hidden(A_29,C_31)
      | ~ r1_tarski(k2_tarski(A_29,B_30),C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_221,plain,(
    ! [A_66,B_67] : r2_hidden(A_66,k2_tarski(A_66,B_67)) ),
    inference(resolution,[status(thm)],[c_204,c_48])).

tff(c_50,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_120,plain,(
    ! [D_45,A_46,B_47] :
      ( ~ r2_hidden(D_45,A_46)
      | r2_hidden(D_45,k2_xboole_0(A_46,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_132,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,k2_tarski('#skF_5','#skF_6'))
      | r2_hidden(D_45,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_120])).

tff(c_226,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_221,c_132])).

tff(c_36,plain,(
    ! [A_21] : r1_xboole_0(A_21,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_227,plain,(
    ! [A_68,B_69,C_70] :
      ( ~ r1_xboole_0(A_68,B_69)
      | ~ r2_hidden(C_70,B_69)
      | ~ r2_hidden(C_70,A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_231,plain,(
    ! [C_71,A_72] :
      ( ~ r2_hidden(C_71,k1_xboole_0)
      | ~ r2_hidden(C_71,A_72) ) ),
    inference(resolution,[status(thm)],[c_36,c_227])).

tff(c_247,plain,(
    ! [A_72] : ~ r2_hidden('#skF_5',A_72) ),
    inference(resolution,[status(thm)],[c_226,c_231])).

tff(c_255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_247,c_226])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:30:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.25  
% 2.19/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.19/1.25  
% 2.19/1.25  %Foreground sorts:
% 2.19/1.25  
% 2.19/1.25  
% 2.19/1.25  %Background operators:
% 2.19/1.25  
% 2.19/1.25  
% 2.19/1.25  %Foreground operators:
% 2.19/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.25  tff('#skF_7', type, '#skF_7': $i).
% 2.19/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.19/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.19/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.19/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.19/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.19/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.25  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.19/1.25  
% 2.19/1.26  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.19/1.26  tff(f_77, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.19/1.26  tff(f_81, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.19/1.26  tff(f_43, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.19/1.26  tff(f_65, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.19/1.26  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.19/1.26  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.19/1.26  tff(c_167, plain, (![A_60, B_61]: (~r2_hidden('#skF_1'(A_60, B_61), B_61) | r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.19/1.26  tff(c_204, plain, (![A_63]: (r1_tarski(A_63, A_63))), inference(resolution, [status(thm)], [c_8, c_167])).
% 2.19/1.26  tff(c_48, plain, (![A_29, C_31, B_30]: (r2_hidden(A_29, C_31) | ~r1_tarski(k2_tarski(A_29, B_30), C_31))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.19/1.26  tff(c_221, plain, (![A_66, B_67]: (r2_hidden(A_66, k2_tarski(A_66, B_67)))), inference(resolution, [status(thm)], [c_204, c_48])).
% 2.19/1.26  tff(c_50, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.19/1.26  tff(c_120, plain, (![D_45, A_46, B_47]: (~r2_hidden(D_45, A_46) | r2_hidden(D_45, k2_xboole_0(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.19/1.26  tff(c_132, plain, (![D_45]: (~r2_hidden(D_45, k2_tarski('#skF_5', '#skF_6')) | r2_hidden(D_45, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_120])).
% 2.19/1.26  tff(c_226, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_221, c_132])).
% 2.19/1.26  tff(c_36, plain, (![A_21]: (r1_xboole_0(A_21, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.19/1.26  tff(c_227, plain, (![A_68, B_69, C_70]: (~r1_xboole_0(A_68, B_69) | ~r2_hidden(C_70, B_69) | ~r2_hidden(C_70, A_68))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.19/1.26  tff(c_231, plain, (![C_71, A_72]: (~r2_hidden(C_71, k1_xboole_0) | ~r2_hidden(C_71, A_72))), inference(resolution, [status(thm)], [c_36, c_227])).
% 2.19/1.26  tff(c_247, plain, (![A_72]: (~r2_hidden('#skF_5', A_72))), inference(resolution, [status(thm)], [c_226, c_231])).
% 2.19/1.26  tff(c_255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_247, c_226])).
% 2.19/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.26  
% 2.19/1.26  Inference rules
% 2.19/1.26  ----------------------
% 2.19/1.26  #Ref     : 0
% 2.19/1.26  #Sup     : 48
% 2.19/1.26  #Fact    : 0
% 2.19/1.26  #Define  : 0
% 2.19/1.26  #Split   : 0
% 2.19/1.26  #Chain   : 0
% 2.19/1.26  #Close   : 0
% 2.19/1.26  
% 2.19/1.26  Ordering : KBO
% 2.19/1.26  
% 2.19/1.26  Simplification rules
% 2.19/1.26  ----------------------
% 2.19/1.26  #Subsume      : 3
% 2.19/1.26  #Demod        : 4
% 2.19/1.26  #Tautology    : 22
% 2.19/1.26  #SimpNegUnit  : 1
% 2.19/1.26  #BackRed      : 1
% 2.19/1.26  
% 2.19/1.26  #Partial instantiations: 0
% 2.19/1.26  #Strategies tried      : 1
% 2.19/1.26  
% 2.19/1.26  Timing (in seconds)
% 2.19/1.26  ----------------------
% 2.19/1.26  Preprocessing        : 0.32
% 2.19/1.26  Parsing              : 0.17
% 2.19/1.26  CNF conversion       : 0.02
% 2.19/1.26  Main loop            : 0.18
% 2.19/1.26  Inferencing          : 0.06
% 2.19/1.26  Reduction            : 0.06
% 2.19/1.26  Demodulation         : 0.05
% 2.19/1.26  BG Simplification    : 0.01
% 2.19/1.26  Subsumption          : 0.03
% 2.19/1.26  Abstraction          : 0.01
% 2.19/1.26  MUC search           : 0.00
% 2.19/1.26  Cooper               : 0.00
% 2.19/1.26  Total                : 0.52
% 2.19/1.26  Index Insertion      : 0.00
% 2.19/1.27  Index Deletion       : 0.00
% 2.19/1.27  Index Matching       : 0.00
% 2.19/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
