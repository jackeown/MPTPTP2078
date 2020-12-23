%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:24 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   23 (  25 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   26 (  36 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

tff(c_34,plain,(
    ! [A_17,B_18] :
      ( r2_hidden('#skF_3'(A_17,B_18),B_18)
      | r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_39,plain,(
    ! [A_17,A_1,B_2] :
      ( r2_hidden('#skF_3'(A_17,k4_xboole_0(A_1,B_2)),A_1)
      | r1_xboole_0(A_17,k4_xboole_0(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_34,c_6])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_40,plain,(
    ! [D_19,B_20,A_21] :
      ( ~ r2_hidden(D_19,B_20)
      | ~ r2_hidden(D_19,k4_xboole_0(A_21,B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,(
    ! [A_31,B_32,B_33] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_31,B_32),B_33),B_32)
      | r1_xboole_0(k4_xboole_0(A_31,B_32),B_33) ) ),
    inference(resolution,[status(thm)],[c_24,c_40])).

tff(c_85,plain,(
    ! [A_31,A_1,B_2] : r1_xboole_0(k4_xboole_0(A_31,A_1),k4_xboole_0(A_1,B_2)) ),
    inference(resolution,[status(thm)],[c_39,c_72])).

tff(c_26,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_4','#skF_5'),k4_xboole_0('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:54:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.18  
% 1.64/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.19  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 1.84/1.19  
% 1.84/1.19  %Foreground sorts:
% 1.84/1.19  
% 1.84/1.19  
% 1.84/1.19  %Background operators:
% 1.84/1.19  
% 1.84/1.19  
% 1.84/1.19  %Foreground operators:
% 1.84/1.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.84/1.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.84/1.19  tff('#skF_5', type, '#skF_5': $i).
% 1.84/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.84/1.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.19  
% 1.84/1.20  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.84/1.20  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.84/1.20  tff(f_56, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_xboole_1)).
% 1.84/1.20  tff(c_34, plain, (![A_17, B_18]: (r2_hidden('#skF_3'(A_17, B_18), B_18) | r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.84/1.20  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.84/1.20  tff(c_39, plain, (![A_17, A_1, B_2]: (r2_hidden('#skF_3'(A_17, k4_xboole_0(A_1, B_2)), A_1) | r1_xboole_0(A_17, k4_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_34, c_6])).
% 1.84/1.20  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.84/1.20  tff(c_40, plain, (![D_19, B_20, A_21]: (~r2_hidden(D_19, B_20) | ~r2_hidden(D_19, k4_xboole_0(A_21, B_20)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.84/1.20  tff(c_72, plain, (![A_31, B_32, B_33]: (~r2_hidden('#skF_3'(k4_xboole_0(A_31, B_32), B_33), B_32) | r1_xboole_0(k4_xboole_0(A_31, B_32), B_33))), inference(resolution, [status(thm)], [c_24, c_40])).
% 1.84/1.20  tff(c_85, plain, (![A_31, A_1, B_2]: (r1_xboole_0(k4_xboole_0(A_31, A_1), k4_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_39, c_72])).
% 1.84/1.20  tff(c_26, plain, (~r1_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), k4_xboole_0('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.84/1.20  tff(c_115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_26])).
% 1.84/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.20  
% 1.84/1.20  Inference rules
% 1.84/1.20  ----------------------
% 1.84/1.20  #Ref     : 0
% 1.84/1.20  #Sup     : 16
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
% 1.84/1.20  #Demod        : 1
% 1.84/1.20  #Tautology    : 2
% 1.84/1.20  #SimpNegUnit  : 0
% 1.84/1.20  #BackRed      : 1
% 1.84/1.20  
% 1.84/1.20  #Partial instantiations: 0
% 1.84/1.20  #Strategies tried      : 1
% 1.84/1.20  
% 1.84/1.20  Timing (in seconds)
% 1.84/1.20  ----------------------
% 1.89/1.20  Preprocessing        : 0.29
% 1.89/1.20  Parsing              : 0.16
% 1.89/1.20  CNF conversion       : 0.02
% 1.89/1.20  Main loop            : 0.13
% 1.89/1.20  Inferencing          : 0.05
% 1.89/1.20  Reduction            : 0.02
% 1.89/1.21  Demodulation         : 0.01
% 1.89/1.21  BG Simplification    : 0.01
% 1.89/1.21  Subsumption          : 0.03
% 1.89/1.21  Abstraction          : 0.01
% 1.89/1.21  MUC search           : 0.00
% 1.89/1.21  Cooper               : 0.00
% 1.89/1.21  Total                : 0.44
% 1.89/1.21  Index Insertion      : 0.00
% 1.89/1.21  Index Deletion       : 0.00
% 1.89/1.21  Index Matching       : 0.00
% 1.89/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
