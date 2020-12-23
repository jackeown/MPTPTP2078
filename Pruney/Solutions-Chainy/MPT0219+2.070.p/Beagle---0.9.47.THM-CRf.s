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
% DateTime   : Thu Dec  3 09:47:58 EST 2020

% Result     : Theorem 15.64s
% Output     : CNFRefutation 15.64s
% Verified   : 
% Statistics : Number of formulae       :   40 (  42 expanded)
%              Number of leaves         :   27 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  42 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_74,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_56,plain,(
    ! [C_34] : r2_hidden(C_34,k1_tarski(C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_76,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_10,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,k4_xboole_0(A_8,B_9))
      | r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_52,plain,(
    ! [A_28,B_29] : k5_xboole_0(A_28,k4_xboole_0(B_29,A_28)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_514,plain,(
    ! [A_107,B_108,C_109] :
      ( r2_hidden(A_107,B_108)
      | ~ r2_hidden(A_107,C_109)
      | r2_hidden(A_107,k5_xboole_0(B_108,C_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3923,plain,(
    ! [A_260,A_261,B_262] :
      ( r2_hidden(A_260,A_261)
      | ~ r2_hidden(A_260,k4_xboole_0(B_262,A_261))
      | r2_hidden(A_260,k2_xboole_0(A_261,B_262)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_514])).

tff(c_51442,plain,(
    ! [D_9632,B_9633,A_9634] :
      ( r2_hidden(D_9632,k2_xboole_0(B_9633,A_9634))
      | r2_hidden(D_9632,B_9633)
      | ~ r2_hidden(D_9632,A_9634) ) ),
    inference(resolution,[status(thm)],[c_10,c_3923])).

tff(c_51609,plain,(
    ! [D_9635] :
      ( r2_hidden(D_9635,k1_tarski('#skF_6'))
      | r2_hidden(D_9635,k1_tarski('#skF_6'))
      | ~ r2_hidden(D_9635,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_51442])).

tff(c_51829,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_56,c_51609])).

tff(c_54,plain,(
    ! [C_34,A_30] :
      ( C_34 = A_30
      | ~ r2_hidden(C_34,k1_tarski(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_51834,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_51829,c_54])).

tff(c_51839,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_51834])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.64/6.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.64/6.06  
% 15.64/6.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.64/6.06  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 15.64/6.06  
% 15.64/6.06  %Foreground sorts:
% 15.64/6.06  
% 15.64/6.06  
% 15.64/6.06  %Background operators:
% 15.64/6.06  
% 15.64/6.06  
% 15.64/6.06  %Foreground operators:
% 15.64/6.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.64/6.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.64/6.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 15.64/6.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.64/6.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.64/6.06  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 15.64/6.06  tff('#skF_7', type, '#skF_7': $i).
% 15.64/6.06  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.64/6.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.64/6.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 15.64/6.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.64/6.06  tff('#skF_6', type, '#skF_6': $i).
% 15.64/6.06  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.64/6.06  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 15.64/6.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.64/6.06  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 15.64/6.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.64/6.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.64/6.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.64/6.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.64/6.06  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 15.64/6.06  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 15.64/6.06  
% 15.64/6.07  tff(f_87, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 15.64/6.07  tff(f_74, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 15.64/6.07  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 15.64/6.07  tff(f_67, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 15.64/6.07  tff(f_55, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 15.64/6.07  tff(c_74, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_87])).
% 15.64/6.07  tff(c_56, plain, (![C_34]: (r2_hidden(C_34, k1_tarski(C_34)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 15.64/6.07  tff(c_76, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_87])).
% 15.64/6.07  tff(c_10, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, k4_xboole_0(A_8, B_9)) | r2_hidden(D_13, B_9) | ~r2_hidden(D_13, A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 15.64/6.07  tff(c_52, plain, (![A_28, B_29]: (k5_xboole_0(A_28, k4_xboole_0(B_29, A_28))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.64/6.07  tff(c_514, plain, (![A_107, B_108, C_109]: (r2_hidden(A_107, B_108) | ~r2_hidden(A_107, C_109) | r2_hidden(A_107, k5_xboole_0(B_108, C_109)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.64/6.07  tff(c_3923, plain, (![A_260, A_261, B_262]: (r2_hidden(A_260, A_261) | ~r2_hidden(A_260, k4_xboole_0(B_262, A_261)) | r2_hidden(A_260, k2_xboole_0(A_261, B_262)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_514])).
% 15.64/6.07  tff(c_51442, plain, (![D_9632, B_9633, A_9634]: (r2_hidden(D_9632, k2_xboole_0(B_9633, A_9634)) | r2_hidden(D_9632, B_9633) | ~r2_hidden(D_9632, A_9634))), inference(resolution, [status(thm)], [c_10, c_3923])).
% 15.64/6.07  tff(c_51609, plain, (![D_9635]: (r2_hidden(D_9635, k1_tarski('#skF_6')) | r2_hidden(D_9635, k1_tarski('#skF_6')) | ~r2_hidden(D_9635, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_76, c_51442])).
% 15.64/6.07  tff(c_51829, plain, (r2_hidden('#skF_7', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_56, c_51609])).
% 15.64/6.07  tff(c_54, plain, (![C_34, A_30]: (C_34=A_30 | ~r2_hidden(C_34, k1_tarski(A_30)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 15.64/6.07  tff(c_51834, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_51829, c_54])).
% 15.64/6.07  tff(c_51839, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_51834])).
% 15.64/6.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.64/6.07  
% 15.64/6.07  Inference rules
% 15.64/6.07  ----------------------
% 15.64/6.07  #Ref     : 0
% 15.64/6.07  #Sup     : 10926
% 15.64/6.07  #Fact    : 12
% 15.64/6.07  #Define  : 0
% 15.64/6.07  #Split   : 0
% 15.64/6.07  #Chain   : 0
% 15.64/6.07  #Close   : 0
% 15.64/6.07  
% 15.64/6.07  Ordering : KBO
% 15.64/6.07  
% 15.64/6.07  Simplification rules
% 15.64/6.07  ----------------------
% 15.64/6.07  #Subsume      : 3982
% 15.64/6.07  #Demod        : 5403
% 15.64/6.07  #Tautology    : 1937
% 15.64/6.07  #SimpNegUnit  : 290
% 15.64/6.07  #BackRed      : 62
% 15.64/6.07  
% 15.64/6.07  #Partial instantiations: 4318
% 15.64/6.07  #Strategies tried      : 1
% 15.64/6.07  
% 15.64/6.07  Timing (in seconds)
% 15.64/6.07  ----------------------
% 15.64/6.07  Preprocessing        : 0.34
% 15.64/6.07  Parsing              : 0.18
% 15.64/6.07  CNF conversion       : 0.02
% 15.64/6.07  Main loop            : 4.95
% 15.64/6.07  Inferencing          : 1.23
% 15.64/6.07  Reduction            : 1.94
% 15.64/6.07  Demodulation         : 1.57
% 15.64/6.07  BG Simplification    : 0.17
% 15.64/6.07  Subsumption          : 1.25
% 15.64/6.07  Abstraction          : 0.26
% 15.64/6.07  MUC search           : 0.00
% 15.64/6.07  Cooper               : 0.00
% 15.64/6.07  Total                : 5.31
% 15.64/6.07  Index Insertion      : 0.00
% 15.64/6.07  Index Deletion       : 0.00
% 15.64/6.07  Index Matching       : 0.00
% 15.64/6.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
