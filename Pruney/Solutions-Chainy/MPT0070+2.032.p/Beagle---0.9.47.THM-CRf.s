%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:22 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  62 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_30,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

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

tff(c_34,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_35,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_39,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_35])).

tff(c_60,plain,(
    ! [D_25,B_26,A_27] :
      ( r2_hidden(D_25,B_26)
      | ~ r2_hidden(D_25,k3_xboole_0(A_27,B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,(
    ! [D_25] :
      ( r2_hidden(D_25,'#skF_5')
      | ~ r2_hidden(D_25,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_60])).

tff(c_32,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_90,plain,(
    ! [A_31,B_32,C_33] :
      ( ~ r1_xboole_0(A_31,B_32)
      | ~ r2_hidden(C_33,B_32)
      | ~ r2_hidden(C_33,A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_94,plain,(
    ! [C_34] :
      ( ~ r2_hidden(C_34,'#skF_6')
      | ~ r2_hidden(C_34,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_90])).

tff(c_109,plain,(
    ! [D_35] :
      ( ~ r2_hidden(D_35,'#skF_6')
      | ~ r2_hidden(D_35,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_71,c_94])).

tff(c_148,plain,(
    ! [A_41] :
      ( ~ r2_hidden('#skF_3'(A_41,'#skF_6'),'#skF_4')
      | r1_xboole_0(A_41,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_22,c_109])).

tff(c_152,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_148])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_30,c_152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:05:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.21  
% 1.85/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.21  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 1.85/1.21  
% 1.85/1.21  %Foreground sorts:
% 1.85/1.21  
% 1.85/1.21  
% 1.85/1.21  %Background operators:
% 1.85/1.21  
% 1.85/1.21  
% 1.85/1.21  %Foreground operators:
% 1.85/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.85/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.85/1.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.85/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.85/1.21  tff('#skF_6', type, '#skF_6': $i).
% 1.85/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.85/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.85/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.85/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.85/1.21  
% 1.85/1.22  tff(f_65, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.85/1.22  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.85/1.22  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.85/1.22  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.85/1.22  tff(c_30, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.85/1.22  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.85/1.22  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.85/1.22  tff(c_34, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.85/1.22  tff(c_35, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.85/1.22  tff(c_39, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_34, c_35])).
% 1.85/1.22  tff(c_60, plain, (![D_25, B_26, A_27]: (r2_hidden(D_25, B_26) | ~r2_hidden(D_25, k3_xboole_0(A_27, B_26)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.85/1.22  tff(c_71, plain, (![D_25]: (r2_hidden(D_25, '#skF_5') | ~r2_hidden(D_25, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_39, c_60])).
% 1.85/1.22  tff(c_32, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.85/1.22  tff(c_90, plain, (![A_31, B_32, C_33]: (~r1_xboole_0(A_31, B_32) | ~r2_hidden(C_33, B_32) | ~r2_hidden(C_33, A_31))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.85/1.22  tff(c_94, plain, (![C_34]: (~r2_hidden(C_34, '#skF_6') | ~r2_hidden(C_34, '#skF_5'))), inference(resolution, [status(thm)], [c_32, c_90])).
% 1.85/1.22  tff(c_109, plain, (![D_35]: (~r2_hidden(D_35, '#skF_6') | ~r2_hidden(D_35, '#skF_4'))), inference(resolution, [status(thm)], [c_71, c_94])).
% 1.85/1.22  tff(c_148, plain, (![A_41]: (~r2_hidden('#skF_3'(A_41, '#skF_6'), '#skF_4') | r1_xboole_0(A_41, '#skF_6'))), inference(resolution, [status(thm)], [c_22, c_109])).
% 1.85/1.22  tff(c_152, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_24, c_148])).
% 1.85/1.22  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_30, c_152])).
% 1.85/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.22  
% 1.85/1.22  Inference rules
% 1.85/1.22  ----------------------
% 1.85/1.22  #Ref     : 0
% 1.85/1.22  #Sup     : 26
% 1.85/1.22  #Fact    : 0
% 1.85/1.22  #Define  : 0
% 1.85/1.22  #Split   : 0
% 1.85/1.22  #Chain   : 0
% 1.85/1.22  #Close   : 0
% 1.85/1.22  
% 1.85/1.22  Ordering : KBO
% 1.85/1.22  
% 1.85/1.22  Simplification rules
% 1.85/1.22  ----------------------
% 1.85/1.22  #Subsume      : 1
% 1.85/1.22  #Demod        : 1
% 1.85/1.22  #Tautology    : 9
% 1.85/1.22  #SimpNegUnit  : 1
% 1.85/1.22  #BackRed      : 0
% 1.85/1.22  
% 1.85/1.22  #Partial instantiations: 0
% 1.85/1.22  #Strategies tried      : 1
% 1.85/1.22  
% 1.85/1.22  Timing (in seconds)
% 1.85/1.22  ----------------------
% 1.85/1.22  Preprocessing        : 0.29
% 1.85/1.22  Parsing              : 0.16
% 1.85/1.22  CNF conversion       : 0.02
% 1.85/1.22  Main loop            : 0.15
% 1.85/1.22  Inferencing          : 0.06
% 1.85/1.22  Reduction            : 0.04
% 1.85/1.22  Demodulation         : 0.03
% 1.85/1.22  BG Simplification    : 0.01
% 1.85/1.22  Subsumption          : 0.03
% 1.85/1.22  Abstraction          : 0.01
% 1.85/1.22  MUC search           : 0.00
% 1.85/1.22  Cooper               : 0.00
% 1.85/1.22  Total                : 0.47
% 1.85/1.22  Index Insertion      : 0.00
% 1.85/1.22  Index Deletion       : 0.00
% 1.85/1.22  Index Matching       : 0.00
% 1.85/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
