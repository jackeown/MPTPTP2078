%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:33 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  58 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ~ ( r1_tarski(B,A)
            & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(A,B)
        & r2_hidden(C,k2_xboole_0(A,B))
        & ~ ( r2_hidden(C,A)
            & ~ r2_hidden(C,B) )
        & ~ ( r2_hidden(C,B)
            & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_38,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [C_41,B_42,A_43] :
      ( r2_hidden(C_41,B_42)
      | ~ r2_hidden(C_41,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_96,plain,(
    ! [A_1,B_42] :
      ( r2_hidden('#skF_1'(A_1),B_42)
      | ~ r1_tarski(A_1,B_42)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_84])).

tff(c_14,plain,(
    ! [D_15,B_11,A_10] :
      ( ~ r2_hidden(D_15,B_11)
      | r2_hidden(D_15,k2_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_256,plain,(
    ! [C_73,B_74,A_75] :
      ( ~ r2_hidden(C_73,B_74)
      | ~ r2_hidden(C_73,A_75)
      | ~ r2_hidden(C_73,k2_xboole_0(A_75,B_74))
      | ~ r1_xboole_0(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_326,plain,(
    ! [D_87,A_88,B_89] :
      ( ~ r2_hidden(D_87,A_88)
      | ~ r1_xboole_0(A_88,B_89)
      | ~ r2_hidden(D_87,B_89) ) ),
    inference(resolution,[status(thm)],[c_14,c_256])).

tff(c_370,plain,(
    ! [A_93,B_94] :
      ( ~ r1_xboole_0(A_93,B_94)
      | ~ r2_hidden('#skF_1'(A_93),B_94)
      | v1_xboole_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_4,c_326])).

tff(c_390,plain,(
    ! [A_96,B_97] :
      ( ~ r1_xboole_0(A_96,B_97)
      | ~ r1_tarski(A_96,B_97)
      | v1_xboole_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_96,c_370])).

tff(c_393,plain,
    ( ~ r1_tarski('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_390])).

tff(c_396,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_393])).

tff(c_398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_396])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.26  
% 2.10/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.26  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 2.10/1.26  
% 2.10/1.26  %Foreground sorts:
% 2.10/1.26  
% 2.10/1.26  
% 2.10/1.26  %Background operators:
% 2.10/1.26  
% 2.10/1.26  
% 2.10/1.26  %Foreground operators:
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.10/1.26  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.10/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.10/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.10/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.10/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.10/1.26  
% 2.10/1.27  tff(f_73, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.10/1.27  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.10/1.27  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.10/1.27  tff(f_47, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.10/1.27  tff(f_64, axiom, (![A, B, C]: ~(((r1_xboole_0(A, B) & r2_hidden(C, k2_xboole_0(A, B))) & ~(r2_hidden(C, A) & ~r2_hidden(C, B))) & ~(r2_hidden(C, B) & ~r2_hidden(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_xboole_0)).
% 2.10/1.27  tff(c_42, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.10/1.27  tff(c_40, plain, (r1_tarski('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.10/1.27  tff(c_38, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.10/1.27  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.27  tff(c_84, plain, (![C_41, B_42, A_43]: (r2_hidden(C_41, B_42) | ~r2_hidden(C_41, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.10/1.27  tff(c_96, plain, (![A_1, B_42]: (r2_hidden('#skF_1'(A_1), B_42) | ~r1_tarski(A_1, B_42) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_84])).
% 2.10/1.27  tff(c_14, plain, (![D_15, B_11, A_10]: (~r2_hidden(D_15, B_11) | r2_hidden(D_15, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.10/1.27  tff(c_256, plain, (![C_73, B_74, A_75]: (~r2_hidden(C_73, B_74) | ~r2_hidden(C_73, A_75) | ~r2_hidden(C_73, k2_xboole_0(A_75, B_74)) | ~r1_xboole_0(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.10/1.27  tff(c_326, plain, (![D_87, A_88, B_89]: (~r2_hidden(D_87, A_88) | ~r1_xboole_0(A_88, B_89) | ~r2_hidden(D_87, B_89))), inference(resolution, [status(thm)], [c_14, c_256])).
% 2.10/1.27  tff(c_370, plain, (![A_93, B_94]: (~r1_xboole_0(A_93, B_94) | ~r2_hidden('#skF_1'(A_93), B_94) | v1_xboole_0(A_93))), inference(resolution, [status(thm)], [c_4, c_326])).
% 2.10/1.27  tff(c_390, plain, (![A_96, B_97]: (~r1_xboole_0(A_96, B_97) | ~r1_tarski(A_96, B_97) | v1_xboole_0(A_96))), inference(resolution, [status(thm)], [c_96, c_370])).
% 2.10/1.27  tff(c_393, plain, (~r1_tarski('#skF_6', '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_38, c_390])).
% 2.10/1.27  tff(c_396, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_393])).
% 2.10/1.27  tff(c_398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_396])).
% 2.10/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.27  
% 2.10/1.27  Inference rules
% 2.10/1.27  ----------------------
% 2.10/1.27  #Ref     : 0
% 2.10/1.27  #Sup     : 80
% 2.10/1.27  #Fact    : 0
% 2.10/1.27  #Define  : 0
% 2.10/1.27  #Split   : 0
% 2.10/1.27  #Chain   : 0
% 2.10/1.27  #Close   : 0
% 2.10/1.27  
% 2.10/1.27  Ordering : KBO
% 2.10/1.27  
% 2.10/1.27  Simplification rules
% 2.10/1.27  ----------------------
% 2.10/1.27  #Subsume      : 9
% 2.10/1.27  #Demod        : 1
% 2.10/1.27  #Tautology    : 10
% 2.10/1.27  #SimpNegUnit  : 2
% 2.10/1.27  #BackRed      : 0
% 2.10/1.27  
% 2.10/1.27  #Partial instantiations: 0
% 2.10/1.27  #Strategies tried      : 1
% 2.10/1.27  
% 2.10/1.27  Timing (in seconds)
% 2.10/1.27  ----------------------
% 2.10/1.27  Preprocessing        : 0.27
% 2.10/1.27  Parsing              : 0.14
% 2.10/1.27  CNF conversion       : 0.02
% 2.10/1.27  Main loop            : 0.24
% 2.10/1.27  Inferencing          : 0.09
% 2.10/1.27  Reduction            : 0.06
% 2.10/1.27  Demodulation         : 0.03
% 2.10/1.27  BG Simplification    : 0.02
% 2.10/1.27  Subsumption          : 0.06
% 2.10/1.27  Abstraction          : 0.01
% 2.10/1.27  MUC search           : 0.00
% 2.10/1.27  Cooper               : 0.00
% 2.10/1.27  Total                : 0.53
% 2.10/1.27  Index Insertion      : 0.00
% 2.10/1.27  Index Deletion       : 0.00
% 2.10/1.27  Index Matching       : 0.00
% 2.10/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
