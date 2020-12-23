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
% DateTime   : Thu Dec  3 09:44:00 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   25 (  30 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  49 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

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

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

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

tff(c_68,plain,(
    ! [D_26,A_27,B_28] :
      ( r2_hidden(D_26,k3_xboole_0(A_27,B_28))
      | ~ r2_hidden(D_26,B_28)
      | ~ r2_hidden(D_26,A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,(
    r1_xboole_0(k3_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
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
      | ~ r2_hidden(C_24,k3_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_26,c_53])).

tff(c_82,plain,(
    ! [D_29] :
      ( ~ r2_hidden(D_29,'#skF_5')
      | ~ r2_hidden(D_29,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_56])).

tff(c_102,plain,(
    ! [A_31] :
      ( ~ r2_hidden('#skF_3'(A_31,'#skF_5'),'#skF_4')
      | r1_xboole_0(A_31,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_82])).

tff(c_106,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_102])).

tff(c_110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_106])).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 17:51:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.12  
% 1.72/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.12  %$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 1.72/1.12  
% 1.72/1.12  %Foreground sorts:
% 1.72/1.12  
% 1.72/1.12  
% 1.72/1.12  %Background operators:
% 1.72/1.12  
% 1.72/1.12  
% 1.72/1.12  %Foreground operators:
% 1.72/1.12  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.72/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.12  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.72/1.12  tff('#skF_5', type, '#skF_5': $i).
% 1.72/1.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.72/1.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.72/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.12  tff('#skF_4', type, '#skF_4': $i).
% 1.72/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.72/1.12  
% 1.72/1.13  tff(f_59, negated_conjecture, ~(![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 1.72/1.13  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.72/1.13  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.72/1.13  tff(c_28, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.72/1.13  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.72/1.13  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.72/1.13  tff(c_68, plain, (![D_26, A_27, B_28]: (r2_hidden(D_26, k3_xboole_0(A_27, B_28)) | ~r2_hidden(D_26, B_28) | ~r2_hidden(D_26, A_27))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.72/1.13  tff(c_26, plain, (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.72/1.13  tff(c_53, plain, (![A_22, B_23, C_24]: (~r1_xboole_0(A_22, B_23) | ~r2_hidden(C_24, B_23) | ~r2_hidden(C_24, A_22))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.72/1.13  tff(c_56, plain, (![C_24]: (~r2_hidden(C_24, '#skF_5') | ~r2_hidden(C_24, k3_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_26, c_53])).
% 1.72/1.13  tff(c_82, plain, (![D_29]: (~r2_hidden(D_29, '#skF_5') | ~r2_hidden(D_29, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_56])).
% 1.72/1.13  tff(c_102, plain, (![A_31]: (~r2_hidden('#skF_3'(A_31, '#skF_5'), '#skF_4') | r1_xboole_0(A_31, '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_82])).
% 1.72/1.13  tff(c_106, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_102])).
% 1.72/1.13  tff(c_110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_28, c_106])).
% 1.72/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.13  
% 1.72/1.13  Inference rules
% 1.72/1.13  ----------------------
% 1.72/1.13  #Ref     : 0
% 1.72/1.13  #Sup     : 15
% 1.72/1.13  #Fact    : 0
% 1.72/1.13  #Define  : 0
% 1.72/1.13  #Split   : 0
% 1.72/1.13  #Chain   : 0
% 1.72/1.13  #Close   : 0
% 1.72/1.13  
% 1.72/1.13  Ordering : KBO
% 1.72/1.13  
% 1.72/1.13  Simplification rules
% 1.72/1.13  ----------------------
% 1.72/1.13  #Subsume      : 1
% 1.72/1.13  #Demod        : 0
% 1.72/1.13  #Tautology    : 2
% 1.72/1.13  #SimpNegUnit  : 1
% 1.72/1.13  #BackRed      : 0
% 1.72/1.13  
% 1.72/1.13  #Partial instantiations: 0
% 1.72/1.13  #Strategies tried      : 1
% 1.72/1.13  
% 1.72/1.13  Timing (in seconds)
% 1.72/1.13  ----------------------
% 1.72/1.13  Preprocessing        : 0.26
% 1.72/1.13  Parsing              : 0.14
% 1.72/1.13  CNF conversion       : 0.02
% 1.72/1.13  Main loop            : 0.12
% 1.72/1.13  Inferencing          : 0.05
% 1.72/1.13  Reduction            : 0.03
% 1.72/1.13  Demodulation         : 0.02
% 1.72/1.13  BG Simplification    : 0.01
% 1.72/1.13  Subsumption          : 0.03
% 1.72/1.14  Abstraction          : 0.01
% 1.72/1.14  MUC search           : 0.00
% 1.72/1.14  Cooper               : 0.00
% 1.72/1.14  Total                : 0.40
% 1.72/1.14  Index Insertion      : 0.00
% 1.72/1.14  Index Deletion       : 0.00
% 1.72/1.14  Index Matching       : 0.00
% 1.72/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
