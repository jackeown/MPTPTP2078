%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:22 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   36 (  49 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 ( 107 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,k4_xboole_0(B,C))
       => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

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

tff(c_26,plain,(
    ~ r1_xboole_0('#skF_5',k4_xboole_0('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42,plain,(
    ! [D_19,A_20,B_21] :
      ( r2_hidden(D_19,A_20)
      | ~ r2_hidden(D_19,k4_xboole_0(A_20,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_51,plain,(
    ! [A_20,B_21,B_8] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_20,B_21),B_8),A_20)
      | r1_xboole_0(k4_xboole_0(A_20,B_21),B_8) ) ),
    inference(resolution,[status(thm)],[c_24,c_42])).

tff(c_68,plain,(
    ! [D_26,A_27,B_28] :
      ( r2_hidden(D_26,k4_xboole_0(A_27,B_28))
      | r2_hidden(D_26,B_28)
      | ~ r2_hidden(D_26,A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    r1_xboole_0('#skF_4',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_53,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ r1_xboole_0(A_22,B_23)
      | ~ r2_hidden(C_24,B_23)
      | ~ r2_hidden(C_24,A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_56,plain,(
    ! [C_24] :
      ( ~ r2_hidden(C_24,k4_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(C_24,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_53])).

tff(c_82,plain,(
    ! [D_29] :
      ( ~ r2_hidden(D_29,'#skF_4')
      | r2_hidden(D_29,'#skF_6')
      | ~ r2_hidden(D_29,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_56])).

tff(c_1072,plain,(
    ! [A_154] :
      ( ~ r2_hidden('#skF_3'(A_154,'#skF_5'),'#skF_4')
      | r2_hidden('#skF_3'(A_154,'#skF_5'),'#skF_6')
      | r1_xboole_0(A_154,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_82])).

tff(c_36,plain,(
    ! [A_17,B_18] :
      ( r2_hidden('#skF_3'(A_17,B_18),A_17)
      | r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41,plain,(
    ! [A_1,B_2,B_18] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_1,B_2),B_18),B_2)
      | r1_xboole_0(k4_xboole_0(A_1,B_2),B_18) ) ),
    inference(resolution,[status(thm)],[c_36,c_4])).

tff(c_1078,plain,(
    ! [A_155] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_155,'#skF_6'),'#skF_5'),'#skF_4')
      | r1_xboole_0(k4_xboole_0(A_155,'#skF_6'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1072,c_41])).

tff(c_1083,plain,(
    r1_xboole_0(k4_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_51,c_1078])).

tff(c_20,plain,(
    ! [A_7,B_8,C_11] :
      ( ~ r1_xboole_0(A_7,B_8)
      | ~ r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1100,plain,(
    ! [C_159] :
      ( ~ r2_hidden(C_159,'#skF_5')
      | ~ r2_hidden(C_159,k4_xboole_0('#skF_4','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1083,c_20])).

tff(c_1231,plain,(
    ! [A_165] :
      ( ~ r2_hidden('#skF_3'(A_165,k4_xboole_0('#skF_4','#skF_6')),'#skF_5')
      | r1_xboole_0(A_165,k4_xboole_0('#skF_4','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_22,c_1100])).

tff(c_1239,plain,(
    r1_xboole_0('#skF_5',k4_xboole_0('#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_24,c_1231])).

tff(c_1244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_1239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:33:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.52  
% 3.28/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.52  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.28/1.52  
% 3.28/1.52  %Foreground sorts:
% 3.28/1.52  
% 3.28/1.52  
% 3.28/1.52  %Background operators:
% 3.28/1.52  
% 3.28/1.52  
% 3.28/1.52  %Foreground operators:
% 3.28/1.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.28/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.28/1.52  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.28/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.28/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.28/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.28/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.28/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.28/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.52  
% 3.28/1.53  tff(f_58, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 3.28/1.53  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.28/1.53  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.28/1.53  tff(c_26, plain, (~r1_xboole_0('#skF_5', k4_xboole_0('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.28/1.53  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.28/1.53  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.28/1.53  tff(c_42, plain, (![D_19, A_20, B_21]: (r2_hidden(D_19, A_20) | ~r2_hidden(D_19, k4_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.28/1.53  tff(c_51, plain, (![A_20, B_21, B_8]: (r2_hidden('#skF_3'(k4_xboole_0(A_20, B_21), B_8), A_20) | r1_xboole_0(k4_xboole_0(A_20, B_21), B_8))), inference(resolution, [status(thm)], [c_24, c_42])).
% 3.28/1.53  tff(c_68, plain, (![D_26, A_27, B_28]: (r2_hidden(D_26, k4_xboole_0(A_27, B_28)) | r2_hidden(D_26, B_28) | ~r2_hidden(D_26, A_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.28/1.53  tff(c_28, plain, (r1_xboole_0('#skF_4', k4_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.28/1.53  tff(c_53, plain, (![A_22, B_23, C_24]: (~r1_xboole_0(A_22, B_23) | ~r2_hidden(C_24, B_23) | ~r2_hidden(C_24, A_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.28/1.53  tff(c_56, plain, (![C_24]: (~r2_hidden(C_24, k4_xboole_0('#skF_5', '#skF_6')) | ~r2_hidden(C_24, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_53])).
% 3.28/1.53  tff(c_82, plain, (![D_29]: (~r2_hidden(D_29, '#skF_4') | r2_hidden(D_29, '#skF_6') | ~r2_hidden(D_29, '#skF_5'))), inference(resolution, [status(thm)], [c_68, c_56])).
% 3.28/1.53  tff(c_1072, plain, (![A_154]: (~r2_hidden('#skF_3'(A_154, '#skF_5'), '#skF_4') | r2_hidden('#skF_3'(A_154, '#skF_5'), '#skF_6') | r1_xboole_0(A_154, '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_82])).
% 3.28/1.53  tff(c_36, plain, (![A_17, B_18]: (r2_hidden('#skF_3'(A_17, B_18), A_17) | r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.28/1.53  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.28/1.53  tff(c_41, plain, (![A_1, B_2, B_18]: (~r2_hidden('#skF_3'(k4_xboole_0(A_1, B_2), B_18), B_2) | r1_xboole_0(k4_xboole_0(A_1, B_2), B_18))), inference(resolution, [status(thm)], [c_36, c_4])).
% 3.28/1.53  tff(c_1078, plain, (![A_155]: (~r2_hidden('#skF_3'(k4_xboole_0(A_155, '#skF_6'), '#skF_5'), '#skF_4') | r1_xboole_0(k4_xboole_0(A_155, '#skF_6'), '#skF_5'))), inference(resolution, [status(thm)], [c_1072, c_41])).
% 3.28/1.53  tff(c_1083, plain, (r1_xboole_0(k4_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_51, c_1078])).
% 3.28/1.53  tff(c_20, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.28/1.53  tff(c_1100, plain, (![C_159]: (~r2_hidden(C_159, '#skF_5') | ~r2_hidden(C_159, k4_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_1083, c_20])).
% 3.28/1.53  tff(c_1231, plain, (![A_165]: (~r2_hidden('#skF_3'(A_165, k4_xboole_0('#skF_4', '#skF_6')), '#skF_5') | r1_xboole_0(A_165, k4_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_22, c_1100])).
% 3.28/1.53  tff(c_1239, plain, (r1_xboole_0('#skF_5', k4_xboole_0('#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_24, c_1231])).
% 3.28/1.53  tff(c_1244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_1239])).
% 3.28/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.53  
% 3.28/1.53  Inference rules
% 3.28/1.53  ----------------------
% 3.28/1.53  #Ref     : 0
% 3.28/1.53  #Sup     : 260
% 3.28/1.53  #Fact    : 0
% 3.28/1.53  #Define  : 0
% 3.28/1.53  #Split   : 0
% 3.28/1.53  #Chain   : 0
% 3.28/1.53  #Close   : 0
% 3.28/1.53  
% 3.28/1.53  Ordering : KBO
% 3.28/1.53  
% 3.28/1.53  Simplification rules
% 3.28/1.53  ----------------------
% 3.28/1.53  #Subsume      : 30
% 3.28/1.53  #Demod        : 14
% 3.28/1.53  #Tautology    : 21
% 3.28/1.53  #SimpNegUnit  : 1
% 3.28/1.53  #BackRed      : 0
% 3.28/1.53  
% 3.28/1.53  #Partial instantiations: 0
% 3.28/1.53  #Strategies tried      : 1
% 3.28/1.53  
% 3.28/1.53  Timing (in seconds)
% 3.28/1.53  ----------------------
% 3.47/1.53  Preprocessing        : 0.26
% 3.47/1.53  Parsing              : 0.14
% 3.47/1.53  CNF conversion       : 0.02
% 3.47/1.53  Main loop            : 0.49
% 3.47/1.53  Inferencing          : 0.18
% 3.47/1.53  Reduction            : 0.12
% 3.47/1.53  Demodulation         : 0.08
% 3.47/1.53  BG Simplification    : 0.03
% 3.47/1.53  Subsumption          : 0.13
% 3.47/1.53  Abstraction          : 0.03
% 3.47/1.53  MUC search           : 0.00
% 3.47/1.53  Cooper               : 0.00
% 3.47/1.53  Total                : 0.77
% 3.47/1.53  Index Insertion      : 0.00
% 3.47/1.53  Index Deletion       : 0.00
% 3.47/1.53  Index Matching       : 0.00
% 3.47/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
