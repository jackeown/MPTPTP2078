%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:39 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   42 (  46 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  58 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(B,k1_tarski(A))
       => ! [C] :
            ( r2_hidden(C,B)
           => r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(c_38,plain,(
    ~ r1_tarski('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_42,plain,(
    r1_setfam_1('#skF_7',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    ! [A_35] : k3_tarski(k1_tarski(A_35)) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_78,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k3_tarski(A_48),k3_tarski(B_49))
      | ~ r1_setfam_1(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_84,plain,(
    ! [A_48,A_35] :
      ( r1_tarski(k3_tarski(A_48),A_35)
      | ~ r1_setfam_1(A_48,k1_tarski(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_78])).

tff(c_40,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_127,plain,(
    ! [C_65,A_66,D_67] :
      ( r2_hidden(C_65,k3_tarski(A_66))
      | ~ r2_hidden(D_67,A_66)
      | ~ r2_hidden(C_65,D_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_137,plain,(
    ! [C_68] :
      ( r2_hidden(C_68,k3_tarski('#skF_7'))
      | ~ r2_hidden(C_68,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_127])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_164,plain,(
    ! [C_71,B_72] :
      ( r2_hidden(C_71,B_72)
      | ~ r1_tarski(k3_tarski('#skF_7'),B_72)
      | ~ r2_hidden(C_71,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_137,c_2])).

tff(c_259,plain,(
    ! [C_84,A_85] :
      ( r2_hidden(C_84,A_85)
      | ~ r2_hidden(C_84,'#skF_8')
      | ~ r1_setfam_1('#skF_7',k1_tarski(A_85)) ) ),
    inference(resolution,[status(thm)],[c_84,c_164])).

tff(c_530,plain,(
    ! [B_133,A_134] :
      ( r2_hidden('#skF_1'('#skF_8',B_133),A_134)
      | ~ r1_setfam_1('#skF_7',k1_tarski(A_134))
      | r1_tarski('#skF_8',B_133) ) ),
    inference(resolution,[status(thm)],[c_6,c_259])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_583,plain,(
    ! [A_137] :
      ( ~ r1_setfam_1('#skF_7',k1_tarski(A_137))
      | r1_tarski('#skF_8',A_137) ) ),
    inference(resolution,[status(thm)],[c_530,c_4])).

tff(c_586,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_583])).

tff(c_590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_586])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.48  
% 2.86/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.48  %$ r2_hidden > r1_tarski > r1_setfam_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.86/1.48  
% 2.86/1.48  %Foreground sorts:
% 2.86/1.48  
% 2.86/1.48  
% 2.86/1.48  %Background operators:
% 2.86/1.48  
% 2.86/1.48  
% 2.86/1.48  %Foreground operators:
% 2.86/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.48  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.86/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.86/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.86/1.48  tff('#skF_7', type, '#skF_7': $i).
% 2.86/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.86/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.86/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.86/1.48  tff('#skF_6', type, '#skF_6': $i).
% 2.86/1.48  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.86/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.86/1.48  tff('#skF_8', type, '#skF_8': $i).
% 2.86/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.48  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.86/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.86/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.86/1.48  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.86/1.48  
% 2.86/1.49  tff(f_64, negated_conjecture, ~(![A, B]: (r1_setfam_1(B, k1_tarski(A)) => (![C]: (r2_hidden(C, B) => r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_setfam_1)).
% 2.86/1.49  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.86/1.49  tff(f_52, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.86/1.49  tff(f_56, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_setfam_1)).
% 2.86/1.49  tff(f_50, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 2.86/1.49  tff(c_38, plain, (~r1_tarski('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.86/1.49  tff(c_42, plain, (r1_setfam_1('#skF_7', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.86/1.49  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.86/1.49  tff(c_34, plain, (![A_35]: (k3_tarski(k1_tarski(A_35))=A_35)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.86/1.49  tff(c_78, plain, (![A_48, B_49]: (r1_tarski(k3_tarski(A_48), k3_tarski(B_49)) | ~r1_setfam_1(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.86/1.49  tff(c_84, plain, (![A_48, A_35]: (r1_tarski(k3_tarski(A_48), A_35) | ~r1_setfam_1(A_48, k1_tarski(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_78])).
% 2.86/1.49  tff(c_40, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.86/1.49  tff(c_127, plain, (![C_65, A_66, D_67]: (r2_hidden(C_65, k3_tarski(A_66)) | ~r2_hidden(D_67, A_66) | ~r2_hidden(C_65, D_67))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.86/1.49  tff(c_137, plain, (![C_68]: (r2_hidden(C_68, k3_tarski('#skF_7')) | ~r2_hidden(C_68, '#skF_8'))), inference(resolution, [status(thm)], [c_40, c_127])).
% 2.86/1.49  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.86/1.49  tff(c_164, plain, (![C_71, B_72]: (r2_hidden(C_71, B_72) | ~r1_tarski(k3_tarski('#skF_7'), B_72) | ~r2_hidden(C_71, '#skF_8'))), inference(resolution, [status(thm)], [c_137, c_2])).
% 2.86/1.49  tff(c_259, plain, (![C_84, A_85]: (r2_hidden(C_84, A_85) | ~r2_hidden(C_84, '#skF_8') | ~r1_setfam_1('#skF_7', k1_tarski(A_85)))), inference(resolution, [status(thm)], [c_84, c_164])).
% 2.86/1.49  tff(c_530, plain, (![B_133, A_134]: (r2_hidden('#skF_1'('#skF_8', B_133), A_134) | ~r1_setfam_1('#skF_7', k1_tarski(A_134)) | r1_tarski('#skF_8', B_133))), inference(resolution, [status(thm)], [c_6, c_259])).
% 2.86/1.49  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.86/1.49  tff(c_583, plain, (![A_137]: (~r1_setfam_1('#skF_7', k1_tarski(A_137)) | r1_tarski('#skF_8', A_137))), inference(resolution, [status(thm)], [c_530, c_4])).
% 2.86/1.49  tff(c_586, plain, (r1_tarski('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_583])).
% 2.86/1.49  tff(c_590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_586])).
% 2.86/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.49  
% 2.86/1.49  Inference rules
% 2.86/1.49  ----------------------
% 2.86/1.49  #Ref     : 0
% 2.86/1.49  #Sup     : 132
% 2.86/1.49  #Fact    : 0
% 2.86/1.49  #Define  : 0
% 2.86/1.49  #Split   : 6
% 2.86/1.49  #Chain   : 0
% 2.86/1.49  #Close   : 0
% 2.86/1.49  
% 2.86/1.49  Ordering : KBO
% 2.86/1.49  
% 2.86/1.49  Simplification rules
% 2.86/1.49  ----------------------
% 2.86/1.49  #Subsume      : 18
% 2.86/1.49  #Demod        : 5
% 2.86/1.49  #Tautology    : 12
% 2.86/1.49  #SimpNegUnit  : 1
% 2.86/1.49  #BackRed      : 0
% 2.86/1.49  
% 2.86/1.49  #Partial instantiations: 0
% 2.86/1.49  #Strategies tried      : 1
% 2.86/1.49  
% 2.86/1.49  Timing (in seconds)
% 2.86/1.49  ----------------------
% 2.86/1.49  Preprocessing        : 0.34
% 2.86/1.49  Parsing              : 0.17
% 2.86/1.49  CNF conversion       : 0.03
% 2.86/1.49  Main loop            : 0.34
% 2.86/1.49  Inferencing          : 0.12
% 2.86/1.49  Reduction            : 0.09
% 2.86/1.50  Demodulation         : 0.06
% 2.86/1.50  BG Simplification    : 0.02
% 2.86/1.50  Subsumption          : 0.09
% 2.86/1.50  Abstraction          : 0.02
% 2.86/1.50  MUC search           : 0.00
% 2.86/1.50  Cooper               : 0.00
% 2.86/1.50  Total                : 0.70
% 2.86/1.50  Index Insertion      : 0.00
% 2.86/1.50  Index Deletion       : 0.00
% 2.86/1.50  Index Matching       : 0.00
% 2.86/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
