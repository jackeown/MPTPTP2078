%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:57 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  45 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_52,axiom,(
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

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
          & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_42,plain,(
    ! [D_19,A_20,B_21] :
      ( r2_hidden(D_19,A_20)
      | ~ r2_hidden(D_19,k3_xboole_0(A_20,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1423,plain,(
    ! [A_150,A_151,B_152] :
      ( r2_hidden('#skF_3'(A_150,k3_xboole_0(A_151,B_152)),A_151)
      | r1_xboole_0(A_150,k3_xboole_0(A_151,B_152)) ) ),
    inference(resolution,[status(thm)],[c_22,c_42])).

tff(c_26,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_53,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ r1_xboole_0(A_22,B_23)
      | ~ r2_hidden(C_24,B_23)
      | ~ r2_hidden(C_24,A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_56,plain,(
    ! [C_24] :
      ( ~ r2_hidden(C_24,'#skF_5')
      | ~ r2_hidden(C_24,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_53])).

tff(c_1535,plain,(
    ! [A_158,B_159] :
      ( ~ r2_hidden('#skF_3'(A_158,k3_xboole_0('#skF_5',B_159)),'#skF_4')
      | r1_xboole_0(A_158,k3_xboole_0('#skF_5',B_159)) ) ),
    inference(resolution,[status(thm)],[c_1423,c_56])).

tff(c_1556,plain,(
    ! [B_159] : r1_xboole_0('#skF_4',k3_xboole_0('#skF_5',B_159)) ),
    inference(resolution,[status(thm)],[c_24,c_1535])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1556,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:23:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.63  
% 3.55/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.63  %$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.55/1.63  
% 3.55/1.63  %Foreground sorts:
% 3.55/1.63  
% 3.55/1.63  
% 3.55/1.63  %Background operators:
% 3.55/1.63  
% 3.55/1.63  
% 3.55/1.63  %Foreground operators:
% 3.55/1.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.55/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.55/1.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.55/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.55/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.55/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.55/1.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.55/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.55/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.55/1.63  
% 3.55/1.64  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.55/1.64  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.55/1.64  tff(f_59, negated_conjecture, ~(![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 3.55/1.64  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.55/1.64  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.55/1.64  tff(c_42, plain, (![D_19, A_20, B_21]: (r2_hidden(D_19, A_20) | ~r2_hidden(D_19, k3_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.55/1.64  tff(c_1423, plain, (![A_150, A_151, B_152]: (r2_hidden('#skF_3'(A_150, k3_xboole_0(A_151, B_152)), A_151) | r1_xboole_0(A_150, k3_xboole_0(A_151, B_152)))), inference(resolution, [status(thm)], [c_22, c_42])).
% 3.55/1.64  tff(c_26, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.55/1.64  tff(c_53, plain, (![A_22, B_23, C_24]: (~r1_xboole_0(A_22, B_23) | ~r2_hidden(C_24, B_23) | ~r2_hidden(C_24, A_22))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.55/1.64  tff(c_56, plain, (![C_24]: (~r2_hidden(C_24, '#skF_5') | ~r2_hidden(C_24, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_53])).
% 3.55/1.64  tff(c_1535, plain, (![A_158, B_159]: (~r2_hidden('#skF_3'(A_158, k3_xboole_0('#skF_5', B_159)), '#skF_4') | r1_xboole_0(A_158, k3_xboole_0('#skF_5', B_159)))), inference(resolution, [status(thm)], [c_1423, c_56])).
% 3.55/1.64  tff(c_1556, plain, (![B_159]: (r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', B_159)))), inference(resolution, [status(thm)], [c_24, c_1535])).
% 3.55/1.64  tff(c_28, plain, (~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.55/1.64  tff(c_1559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1556, c_28])).
% 3.55/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.64  
% 3.55/1.64  Inference rules
% 3.55/1.64  ----------------------
% 3.55/1.64  #Ref     : 0
% 3.55/1.64  #Sup     : 350
% 3.55/1.64  #Fact    : 0
% 3.55/1.64  #Define  : 0
% 3.55/1.64  #Split   : 0
% 3.55/1.64  #Chain   : 0
% 3.55/1.64  #Close   : 0
% 3.55/1.64  
% 3.55/1.64  Ordering : KBO
% 3.55/1.64  
% 3.55/1.64  Simplification rules
% 3.55/1.64  ----------------------
% 3.55/1.64  #Subsume      : 33
% 3.55/1.64  #Demod        : 16
% 3.55/1.64  #Tautology    : 19
% 3.55/1.64  #SimpNegUnit  : 0
% 3.55/1.64  #BackRed      : 1
% 3.55/1.64  
% 3.55/1.64  #Partial instantiations: 0
% 3.55/1.64  #Strategies tried      : 1
% 3.55/1.64  
% 3.55/1.64  Timing (in seconds)
% 3.55/1.64  ----------------------
% 3.55/1.64  Preprocessing        : 0.26
% 3.55/1.64  Parsing              : 0.14
% 3.55/1.64  CNF conversion       : 0.02
% 3.55/1.64  Main loop            : 0.57
% 3.55/1.64  Inferencing          : 0.19
% 3.55/1.64  Reduction            : 0.14
% 3.55/1.64  Demodulation         : 0.10
% 3.55/1.64  BG Simplification    : 0.03
% 3.55/1.64  Subsumption          : 0.17
% 3.55/1.64  Abstraction          : 0.03
% 3.55/1.65  MUC search           : 0.00
% 3.55/1.65  Cooper               : 0.00
% 3.55/1.65  Total                : 0.84
% 3.76/1.65  Index Insertion      : 0.00
% 3.76/1.65  Index Deletion       : 0.00
% 3.76/1.65  Index Matching       : 0.00
% 3.76/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
