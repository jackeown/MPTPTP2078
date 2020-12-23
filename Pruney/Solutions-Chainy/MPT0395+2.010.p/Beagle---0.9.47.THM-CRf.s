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
% DateTime   : Thu Dec  3 09:57:29 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   31 (  36 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  52 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > #nlpp > k1_tarski > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_setfam_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_22,plain,(
    ~ r1_setfam_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_1'(A_8,B_9),A_8)
      | r1_setfam_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k1_tarski(A_6),B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_54,plain,(
    ! [A_30,C_31,B_32] :
      ( r1_tarski(A_30,C_31)
      | ~ r1_tarski(B_32,C_31)
      | ~ r1_tarski(A_30,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_64,plain,(
    ! [A_33] :
      ( r1_tarski(A_33,'#skF_4')
      | ~ r1_tarski(A_33,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_54])).

tff(c_76,plain,(
    ! [A_34] :
      ( r1_tarski(k1_tarski(A_34),'#skF_4')
      | ~ r2_hidden(A_34,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_64])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | ~ r1_tarski(k1_tarski(A_6),B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_87,plain,(
    ! [A_35] :
      ( r2_hidden(A_35,'#skF_4')
      | ~ r2_hidden(A_35,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_76,c_10])).

tff(c_92,plain,(
    ! [B_9] :
      ( r2_hidden('#skF_1'('#skF_3',B_9),'#skF_4')
      | r1_setfam_1('#skF_3',B_9) ) ),
    inference(resolution,[status(thm)],[c_20,c_87])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_94,plain,(
    ! [A_37,B_38,D_39] :
      ( ~ r1_tarski('#skF_1'(A_37,B_38),D_39)
      | ~ r2_hidden(D_39,B_38)
      | r1_setfam_1(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_100,plain,(
    ! [A_40,B_41] :
      ( ~ r2_hidden('#skF_1'(A_40,B_41),B_41)
      | r1_setfam_1(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_6,c_94])).

tff(c_104,plain,(
    r1_setfam_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_100])).

tff(c_112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_22,c_104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:31:24 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.53/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.15  
% 1.68/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.15  %$ r2_hidden > r1_tarski > r1_setfam_1 > #nlpp > k1_tarski > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 1.68/1.15  
% 1.68/1.15  %Foreground sorts:
% 1.68/1.15  
% 1.68/1.15  
% 1.68/1.15  %Background operators:
% 1.68/1.15  
% 1.68/1.15  
% 1.68/1.15  %Foreground operators:
% 1.68/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.15  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.68/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.68/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.68/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.68/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.68/1.15  
% 1.68/1.16  tff(f_58, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_setfam_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_setfam_1)).
% 1.68/1.16  tff(f_53, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.68/1.16  tff(f_41, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.68/1.16  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.68/1.16  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.68/1.16  tff(c_22, plain, (~r1_setfam_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.68/1.16  tff(c_20, plain, (![A_8, B_9]: (r2_hidden('#skF_1'(A_8, B_9), A_8) | r1_setfam_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.68/1.16  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(k1_tarski(A_6), B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.68/1.16  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.68/1.16  tff(c_54, plain, (![A_30, C_31, B_32]: (r1_tarski(A_30, C_31) | ~r1_tarski(B_32, C_31) | ~r1_tarski(A_30, B_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.68/1.16  tff(c_64, plain, (![A_33]: (r1_tarski(A_33, '#skF_4') | ~r1_tarski(A_33, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_54])).
% 1.68/1.16  tff(c_76, plain, (![A_34]: (r1_tarski(k1_tarski(A_34), '#skF_4') | ~r2_hidden(A_34, '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_64])).
% 1.68/1.16  tff(c_10, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | ~r1_tarski(k1_tarski(A_6), B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.68/1.16  tff(c_87, plain, (![A_35]: (r2_hidden(A_35, '#skF_4') | ~r2_hidden(A_35, '#skF_3'))), inference(resolution, [status(thm)], [c_76, c_10])).
% 1.68/1.16  tff(c_92, plain, (![B_9]: (r2_hidden('#skF_1'('#skF_3', B_9), '#skF_4') | r1_setfam_1('#skF_3', B_9))), inference(resolution, [status(thm)], [c_20, c_87])).
% 1.68/1.16  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.16  tff(c_94, plain, (![A_37, B_38, D_39]: (~r1_tarski('#skF_1'(A_37, B_38), D_39) | ~r2_hidden(D_39, B_38) | r1_setfam_1(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.68/1.16  tff(c_100, plain, (![A_40, B_41]: (~r2_hidden('#skF_1'(A_40, B_41), B_41) | r1_setfam_1(A_40, B_41))), inference(resolution, [status(thm)], [c_6, c_94])).
% 1.68/1.16  tff(c_104, plain, (r1_setfam_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_92, c_100])).
% 1.68/1.16  tff(c_112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_22, c_104])).
% 1.68/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.16  
% 1.68/1.16  Inference rules
% 1.68/1.16  ----------------------
% 1.68/1.16  #Ref     : 0
% 1.68/1.16  #Sup     : 17
% 1.68/1.16  #Fact    : 0
% 1.68/1.16  #Define  : 0
% 1.68/1.16  #Split   : 1
% 1.68/1.16  #Chain   : 0
% 1.68/1.16  #Close   : 0
% 1.68/1.16  
% 1.68/1.16  Ordering : KBO
% 1.68/1.16  
% 1.68/1.16  Simplification rules
% 1.68/1.16  ----------------------
% 1.68/1.16  #Subsume      : 0
% 1.68/1.16  #Demod        : 3
% 1.68/1.16  #Tautology    : 5
% 1.68/1.16  #SimpNegUnit  : 1
% 1.68/1.16  #BackRed      : 0
% 1.68/1.16  
% 1.68/1.16  #Partial instantiations: 0
% 1.68/1.16  #Strategies tried      : 1
% 1.68/1.16  
% 1.68/1.16  Timing (in seconds)
% 1.68/1.16  ----------------------
% 1.68/1.16  Preprocessing        : 0.25
% 1.68/1.17  Parsing              : 0.14
% 1.68/1.17  CNF conversion       : 0.02
% 1.68/1.17  Main loop            : 0.13
% 1.68/1.17  Inferencing          : 0.05
% 1.68/1.17  Reduction            : 0.03
% 1.68/1.17  Demodulation         : 0.02
% 1.68/1.17  BG Simplification    : 0.01
% 1.68/1.17  Subsumption          : 0.03
% 1.68/1.17  Abstraction          : 0.01
% 1.68/1.17  MUC search           : 0.00
% 1.68/1.17  Cooper               : 0.00
% 1.68/1.17  Total                : 0.40
% 1.68/1.17  Index Insertion      : 0.00
% 1.68/1.17  Index Deletion       : 0.00
% 1.68/1.17  Index Matching       : 0.00
% 1.68/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
