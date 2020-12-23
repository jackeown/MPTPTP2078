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
% DateTime   : Thu Dec  3 09:44:35 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   27 (  28 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    4
%              Number of atoms          :   30 (  36 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_62,axiom,(
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

tff(f_65,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_xboole_1)).

tff(c_42,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_5'(A_13,B_14),A_13)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_58,plain,(
    ! [D_26,B_27,A_28] :
      ( r2_hidden(D_26,B_27)
      | ~ r2_hidden(D_26,k3_xboole_0(A_28,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_63,plain,(
    ! [A_28,B_27,B_14] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_28,B_27),B_14),B_27)
      | r1_xboole_0(k3_xboole_0(A_28,B_27),B_14) ) ),
    inference(resolution,[status(thm)],[c_42,c_58])).

tff(c_40,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_5'(A_13,B_14),B_14)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_80,plain,(
    ! [D_31,B_32,A_33] :
      ( ~ r2_hidden(D_31,B_32)
      | ~ r2_hidden(D_31,k4_xboole_0(A_33,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1217,plain,(
    ! [A_155,A_156,B_157] :
      ( ~ r2_hidden('#skF_5'(A_155,k4_xboole_0(A_156,B_157)),B_157)
      | r1_xboole_0(A_155,k4_xboole_0(A_156,B_157)) ) ),
    inference(resolution,[status(thm)],[c_40,c_80])).

tff(c_1242,plain,(
    ! [A_28,B_27,A_156] : r1_xboole_0(k3_xboole_0(A_28,B_27),k4_xboole_0(A_156,B_27)) ),
    inference(resolution,[status(thm)],[c_63,c_1217])).

tff(c_44,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_6','#skF_7'),k4_xboole_0('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n012.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 17:10:52 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.17/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.44  
% 2.97/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.44  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5
% 2.97/1.44  
% 2.97/1.44  %Foreground sorts:
% 2.97/1.44  
% 2.97/1.44  
% 2.97/1.44  %Background operators:
% 2.97/1.44  
% 2.97/1.44  
% 2.97/1.44  %Foreground operators:
% 2.97/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.97/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.97/1.44  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.97/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.97/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.97/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.97/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.97/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.97/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.97/1.44  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.97/1.44  
% 2.97/1.45  tff(f_62, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.97/1.45  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.97/1.45  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.97/1.45  tff(f_65, negated_conjecture, ~(![A, B]: r1_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_xboole_1)).
% 2.97/1.45  tff(c_42, plain, (![A_13, B_14]: (r2_hidden('#skF_5'(A_13, B_14), A_13) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.97/1.45  tff(c_58, plain, (![D_26, B_27, A_28]: (r2_hidden(D_26, B_27) | ~r2_hidden(D_26, k3_xboole_0(A_28, B_27)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.97/1.45  tff(c_63, plain, (![A_28, B_27, B_14]: (r2_hidden('#skF_5'(k3_xboole_0(A_28, B_27), B_14), B_27) | r1_xboole_0(k3_xboole_0(A_28, B_27), B_14))), inference(resolution, [status(thm)], [c_42, c_58])).
% 2.97/1.45  tff(c_40, plain, (![A_13, B_14]: (r2_hidden('#skF_5'(A_13, B_14), B_14) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.97/1.45  tff(c_80, plain, (![D_31, B_32, A_33]: (~r2_hidden(D_31, B_32) | ~r2_hidden(D_31, k4_xboole_0(A_33, B_32)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.97/1.45  tff(c_1217, plain, (![A_155, A_156, B_157]: (~r2_hidden('#skF_5'(A_155, k4_xboole_0(A_156, B_157)), B_157) | r1_xboole_0(A_155, k4_xboole_0(A_156, B_157)))), inference(resolution, [status(thm)], [c_40, c_80])).
% 2.97/1.45  tff(c_1242, plain, (![A_28, B_27, A_156]: (r1_xboole_0(k3_xboole_0(A_28, B_27), k4_xboole_0(A_156, B_27)))), inference(resolution, [status(thm)], [c_63, c_1217])).
% 2.97/1.45  tff(c_44, plain, (~r1_xboole_0(k3_xboole_0('#skF_6', '#skF_7'), k4_xboole_0('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.97/1.45  tff(c_1254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1242, c_44])).
% 2.97/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.45  
% 2.97/1.45  Inference rules
% 2.97/1.45  ----------------------
% 2.97/1.45  #Ref     : 0
% 2.97/1.45  #Sup     : 276
% 2.97/1.45  #Fact    : 0
% 2.97/1.45  #Define  : 0
% 2.97/1.45  #Split   : 0
% 2.97/1.45  #Chain   : 0
% 2.97/1.45  #Close   : 0
% 2.97/1.45  
% 2.97/1.45  Ordering : KBO
% 2.97/1.45  
% 2.97/1.45  Simplification rules
% 2.97/1.45  ----------------------
% 2.97/1.45  #Subsume      : 14
% 2.97/1.45  #Demod        : 11
% 2.97/1.45  #Tautology    : 18
% 2.97/1.45  #SimpNegUnit  : 0
% 2.97/1.45  #BackRed      : 1
% 2.97/1.45  
% 2.97/1.45  #Partial instantiations: 0
% 2.97/1.45  #Strategies tried      : 1
% 2.97/1.45  
% 2.97/1.45  Timing (in seconds)
% 2.97/1.45  ----------------------
% 3.40/1.46  Preprocessing        : 0.30
% 3.40/1.46  Parsing              : 0.16
% 3.40/1.46  CNF conversion       : 0.03
% 3.40/1.46  Main loop            : 0.49
% 3.40/1.46  Inferencing          : 0.19
% 3.40/1.46  Reduction            : 0.09
% 3.40/1.46  Demodulation         : 0.06
% 3.40/1.46  BG Simplification    : 0.03
% 3.40/1.46  Subsumption          : 0.13
% 3.40/1.46  Abstraction          : 0.03
% 3.40/1.46  MUC search           : 0.00
% 3.40/1.46  Cooper               : 0.00
% 3.40/1.46  Total                : 0.81
% 3.40/1.46  Index Insertion      : 0.00
% 3.40/1.46  Index Deletion       : 0.00
% 3.40/1.46  Index Matching       : 0.00
% 3.40/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
