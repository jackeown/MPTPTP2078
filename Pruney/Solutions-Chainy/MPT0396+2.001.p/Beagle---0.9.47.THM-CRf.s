%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:30 EST 2020

% Result     : Theorem 27.91s
% Output     : CNFRefutation 27.91s
% Verified   : 
% Statistics : Number of formulae       :   39 (  47 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 (  82 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > #nlpp > k3_tarski > #skF_6 > #skF_3 > #skF_5 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(A,B)
       => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(c_34,plain,(
    ~ r1_tarski(k3_tarski('#skF_8'),k3_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    r1_setfam_1('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [A_6,C_21] :
      ( r2_hidden('#skF_5'(A_6,k3_tarski(A_6),C_21),A_6)
      | ~ r2_hidden(C_21,k3_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_26,plain,(
    ! [C_35,A_25,B_26] :
      ( r1_tarski(C_35,'#skF_7'(A_25,B_26,C_35))
      | ~ r2_hidden(C_35,A_25)
      | ~ r1_setfam_1(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_60,plain,(
    ! [C_50,A_51] :
      ( r2_hidden(C_50,'#skF_5'(A_51,k3_tarski(A_51),C_50))
      | ~ r2_hidden(C_50,k3_tarski(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_215,plain,(
    ! [C_87,B_88,A_89] :
      ( r2_hidden(C_87,B_88)
      | ~ r1_tarski('#skF_5'(A_89,k3_tarski(A_89),C_87),B_88)
      | ~ r2_hidden(C_87,k3_tarski(A_89)) ) ),
    inference(resolution,[status(thm)],[c_60,c_2])).

tff(c_41795,plain,(
    ! [C_1680,A_1681,B_1682,A_1683] :
      ( r2_hidden(C_1680,'#skF_7'(A_1681,B_1682,'#skF_5'(A_1683,k3_tarski(A_1683),C_1680)))
      | ~ r2_hidden(C_1680,k3_tarski(A_1683))
      | ~ r2_hidden('#skF_5'(A_1683,k3_tarski(A_1683),C_1680),A_1681)
      | ~ r1_setfam_1(A_1681,B_1682) ) ),
    inference(resolution,[status(thm)],[c_26,c_215])).

tff(c_111,plain,(
    ! [A_66,B_67,C_68] :
      ( r2_hidden('#skF_7'(A_66,B_67,C_68),B_67)
      | ~ r2_hidden(C_68,A_66)
      | ~ r1_setfam_1(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k3_tarski(A_6))
      | ~ r2_hidden(D_24,A_6)
      | ~ r2_hidden(C_21,D_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_116,plain,(
    ! [C_21,B_67,A_66,C_68] :
      ( r2_hidden(C_21,k3_tarski(B_67))
      | ~ r2_hidden(C_21,'#skF_7'(A_66,B_67,C_68))
      | ~ r2_hidden(C_68,A_66)
      | ~ r1_setfam_1(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_111,c_8])).

tff(c_49996,plain,(
    ! [C_1951,B_1952,A_1953,A_1954] :
      ( r2_hidden(C_1951,k3_tarski(B_1952))
      | ~ r2_hidden(C_1951,k3_tarski(A_1953))
      | ~ r2_hidden('#skF_5'(A_1953,k3_tarski(A_1953),C_1951),A_1954)
      | ~ r1_setfam_1(A_1954,B_1952) ) ),
    inference(resolution,[status(thm)],[c_41795,c_116])).

tff(c_50041,plain,(
    ! [C_1955,B_1956,A_1957] :
      ( r2_hidden(C_1955,k3_tarski(B_1956))
      | ~ r1_setfam_1(A_1957,B_1956)
      | ~ r2_hidden(C_1955,k3_tarski(A_1957)) ) ),
    inference(resolution,[status(thm)],[c_10,c_49996])).

tff(c_50591,plain,(
    ! [C_1958] :
      ( r2_hidden(C_1958,k3_tarski('#skF_9'))
      | ~ r2_hidden(C_1958,k3_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_36,c_50041])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_51566,plain,(
    ! [A_1966] :
      ( r1_tarski(A_1966,k3_tarski('#skF_9'))
      | ~ r2_hidden('#skF_1'(A_1966,k3_tarski('#skF_9')),k3_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_50591,c_4])).

tff(c_51618,plain,(
    r1_tarski(k3_tarski('#skF_8'),k3_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_6,c_51566])).

tff(c_51634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_51618])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:39:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.91/17.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.91/17.72  
% 27.91/17.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.91/17.72  %$ r2_hidden > r1_tarski > r1_setfam_1 > #nlpp > k3_tarski > #skF_6 > #skF_3 > #skF_5 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 27.91/17.72  
% 27.91/17.72  %Foreground sorts:
% 27.91/17.72  
% 27.91/17.72  
% 27.91/17.72  %Background operators:
% 27.91/17.72  
% 27.91/17.72  
% 27.91/17.72  %Foreground operators:
% 27.91/17.72  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 27.91/17.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.91/17.72  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 27.91/17.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 27.91/17.72  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 27.91/17.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.91/17.72  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 27.91/17.72  tff('#skF_9', type, '#skF_9': $i).
% 27.91/17.72  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 27.91/17.72  tff('#skF_8', type, '#skF_8': $i).
% 27.91/17.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.91/17.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 27.91/17.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.91/17.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 27.91/17.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 27.91/17.72  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 27.91/17.72  
% 27.91/17.73  tff(f_59, negated_conjecture, ~(![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_setfam_1)).
% 27.91/17.73  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 27.91/17.73  tff(f_42, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 27.91/17.73  tff(f_54, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 27.91/17.73  tff(c_34, plain, (~r1_tarski(k3_tarski('#skF_8'), k3_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 27.91/17.73  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 27.91/17.73  tff(c_36, plain, (r1_setfam_1('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_59])).
% 27.91/17.73  tff(c_10, plain, (![A_6, C_21]: (r2_hidden('#skF_5'(A_6, k3_tarski(A_6), C_21), A_6) | ~r2_hidden(C_21, k3_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 27.91/17.73  tff(c_26, plain, (![C_35, A_25, B_26]: (r1_tarski(C_35, '#skF_7'(A_25, B_26, C_35)) | ~r2_hidden(C_35, A_25) | ~r1_setfam_1(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_54])).
% 27.91/17.73  tff(c_60, plain, (![C_50, A_51]: (r2_hidden(C_50, '#skF_5'(A_51, k3_tarski(A_51), C_50)) | ~r2_hidden(C_50, k3_tarski(A_51)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 27.91/17.73  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 27.91/17.73  tff(c_215, plain, (![C_87, B_88, A_89]: (r2_hidden(C_87, B_88) | ~r1_tarski('#skF_5'(A_89, k3_tarski(A_89), C_87), B_88) | ~r2_hidden(C_87, k3_tarski(A_89)))), inference(resolution, [status(thm)], [c_60, c_2])).
% 27.91/17.73  tff(c_41795, plain, (![C_1680, A_1681, B_1682, A_1683]: (r2_hidden(C_1680, '#skF_7'(A_1681, B_1682, '#skF_5'(A_1683, k3_tarski(A_1683), C_1680))) | ~r2_hidden(C_1680, k3_tarski(A_1683)) | ~r2_hidden('#skF_5'(A_1683, k3_tarski(A_1683), C_1680), A_1681) | ~r1_setfam_1(A_1681, B_1682))), inference(resolution, [status(thm)], [c_26, c_215])).
% 27.91/17.73  tff(c_111, plain, (![A_66, B_67, C_68]: (r2_hidden('#skF_7'(A_66, B_67, C_68), B_67) | ~r2_hidden(C_68, A_66) | ~r1_setfam_1(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_54])).
% 27.91/17.73  tff(c_8, plain, (![C_21, A_6, D_24]: (r2_hidden(C_21, k3_tarski(A_6)) | ~r2_hidden(D_24, A_6) | ~r2_hidden(C_21, D_24))), inference(cnfTransformation, [status(thm)], [f_42])).
% 27.91/17.73  tff(c_116, plain, (![C_21, B_67, A_66, C_68]: (r2_hidden(C_21, k3_tarski(B_67)) | ~r2_hidden(C_21, '#skF_7'(A_66, B_67, C_68)) | ~r2_hidden(C_68, A_66) | ~r1_setfam_1(A_66, B_67))), inference(resolution, [status(thm)], [c_111, c_8])).
% 27.91/17.73  tff(c_49996, plain, (![C_1951, B_1952, A_1953, A_1954]: (r2_hidden(C_1951, k3_tarski(B_1952)) | ~r2_hidden(C_1951, k3_tarski(A_1953)) | ~r2_hidden('#skF_5'(A_1953, k3_tarski(A_1953), C_1951), A_1954) | ~r1_setfam_1(A_1954, B_1952))), inference(resolution, [status(thm)], [c_41795, c_116])).
% 27.91/17.73  tff(c_50041, plain, (![C_1955, B_1956, A_1957]: (r2_hidden(C_1955, k3_tarski(B_1956)) | ~r1_setfam_1(A_1957, B_1956) | ~r2_hidden(C_1955, k3_tarski(A_1957)))), inference(resolution, [status(thm)], [c_10, c_49996])).
% 27.91/17.73  tff(c_50591, plain, (![C_1958]: (r2_hidden(C_1958, k3_tarski('#skF_9')) | ~r2_hidden(C_1958, k3_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_36, c_50041])).
% 27.91/17.73  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 27.91/17.73  tff(c_51566, plain, (![A_1966]: (r1_tarski(A_1966, k3_tarski('#skF_9')) | ~r2_hidden('#skF_1'(A_1966, k3_tarski('#skF_9')), k3_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_50591, c_4])).
% 27.91/17.73  tff(c_51618, plain, (r1_tarski(k3_tarski('#skF_8'), k3_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_6, c_51566])).
% 27.91/17.73  tff(c_51634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_51618])).
% 27.91/17.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.91/17.73  
% 27.91/17.73  Inference rules
% 27.91/17.73  ----------------------
% 27.91/17.73  #Ref     : 0
% 27.91/17.73  #Sup     : 13725
% 27.91/17.73  #Fact    : 4
% 27.91/17.73  #Define  : 0
% 27.91/17.73  #Split   : 0
% 27.91/17.73  #Chain   : 0
% 27.91/17.73  #Close   : 0
% 27.91/17.73  
% 27.91/17.73  Ordering : KBO
% 27.91/17.73  
% 27.91/17.73  Simplification rules
% 27.91/17.73  ----------------------
% 27.91/17.73  #Subsume      : 653
% 27.91/17.73  #Demod        : 16
% 27.91/17.73  #Tautology    : 64
% 27.91/17.73  #SimpNegUnit  : 1
% 27.91/17.73  #BackRed      : 0
% 27.91/17.73  
% 27.91/17.73  #Partial instantiations: 0
% 27.91/17.73  #Strategies tried      : 1
% 27.91/17.73  
% 27.91/17.73  Timing (in seconds)
% 27.91/17.73  ----------------------
% 27.91/17.74  Preprocessing        : 0.28
% 27.91/17.74  Parsing              : 0.14
% 27.91/17.74  CNF conversion       : 0.03
% 27.91/17.74  Main loop            : 16.70
% 27.91/17.74  Inferencing          : 1.89
% 27.91/17.74  Reduction            : 1.70
% 27.91/17.74  Demodulation         : 1.05
% 27.91/17.74  BG Simplification    : 0.27
% 27.91/17.74  Subsumption          : 11.87
% 27.91/17.74  Abstraction          : 0.40
% 27.91/17.74  MUC search           : 0.00
% 27.91/17.74  Cooper               : 0.00
% 27.91/17.74  Total                : 17.00
% 27.91/17.74  Index Insertion      : 0.00
% 27.91/17.74  Index Deletion       : 0.00
% 27.91/17.74  Index Matching       : 0.00
% 27.91/17.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
