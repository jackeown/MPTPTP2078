%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:21 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   46 (  52 expanded)
%              Number of leaves         :   28 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  57 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_66,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_89,plain,(
    ! [A_43,B_44] : k1_enumset1(A_43,A_43,B_44) = k2_tarski(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_34,plain,(
    ! [E_20,A_14,B_15] : r2_hidden(E_20,k1_enumset1(A_14,B_15,E_20)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_101,plain,(
    ! [B_44,A_43] : r2_hidden(B_44,k2_tarski(A_43,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_34])).

tff(c_30,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_118,plain,(
    ! [B_50,A_51] :
      ( B_50 = A_51
      | ~ r1_tarski(B_50,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_137,plain,(
    ! [A_55] :
      ( k1_xboole_0 = A_55
      | ~ r1_tarski(A_55,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_118])).

tff(c_150,plain,(
    ! [B_13] : k4_xboole_0(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_137])).

tff(c_169,plain,(
    ! [D_57,B_58,A_59] :
      ( ~ r2_hidden(D_57,B_58)
      | ~ r2_hidden(D_57,k4_xboole_0(A_59,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_173,plain,(
    ! [D_60,B_61] :
      ( ~ r2_hidden(D_60,B_61)
      | ~ r2_hidden(D_60,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_169])).

tff(c_186,plain,(
    ! [B_44] : ~ r2_hidden(B_44,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_101,c_173])).

tff(c_68,plain,(
    k2_tarski('#skF_5','#skF_6') != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_70,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_211,plain,(
    ! [B_68,A_69] :
      ( k1_tarski(B_68) = A_69
      | k1_xboole_0 = A_69
      | ~ r1_tarski(A_69,k1_tarski(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_214,plain,
    ( k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7')
    | k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_211])).

tff(c_229,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_214])).

tff(c_242,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_101])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:38:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.20  
% 1.96/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.21  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 1.96/1.21  
% 1.96/1.21  %Foreground sorts:
% 1.96/1.21  
% 1.96/1.21  
% 1.96/1.21  %Background operators:
% 1.96/1.21  
% 1.96/1.21  
% 1.96/1.21  %Foreground operators:
% 1.96/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.96/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.96/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.21  tff('#skF_7', type, '#skF_7': $i).
% 1.96/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.96/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.96/1.21  tff('#skF_6', type, '#skF_6': $i).
% 1.96/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.96/1.21  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.96/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.96/1.21  
% 2.06/1.22  tff(f_66, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.06/1.22  tff(f_62, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.06/1.22  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.06/1.22  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.06/1.22  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.06/1.22  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.06/1.22  tff(f_79, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 2.06/1.22  tff(f_74, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.06/1.22  tff(c_89, plain, (![A_43, B_44]: (k1_enumset1(A_43, A_43, B_44)=k2_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.06/1.22  tff(c_34, plain, (![E_20, A_14, B_15]: (r2_hidden(E_20, k1_enumset1(A_14, B_15, E_20)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.06/1.22  tff(c_101, plain, (![B_44, A_43]: (r2_hidden(B_44, k2_tarski(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_34])).
% 2.06/1.22  tff(c_30, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.06/1.22  tff(c_28, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.06/1.22  tff(c_118, plain, (![B_50, A_51]: (B_50=A_51 | ~r1_tarski(B_50, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.06/1.22  tff(c_137, plain, (![A_55]: (k1_xboole_0=A_55 | ~r1_tarski(A_55, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_118])).
% 2.06/1.22  tff(c_150, plain, (![B_13]: (k4_xboole_0(k1_xboole_0, B_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_137])).
% 2.06/1.22  tff(c_169, plain, (![D_57, B_58, A_59]: (~r2_hidden(D_57, B_58) | ~r2_hidden(D_57, k4_xboole_0(A_59, B_58)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.22  tff(c_173, plain, (![D_60, B_61]: (~r2_hidden(D_60, B_61) | ~r2_hidden(D_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_150, c_169])).
% 2.06/1.22  tff(c_186, plain, (![B_44]: (~r2_hidden(B_44, k1_xboole_0))), inference(resolution, [status(thm)], [c_101, c_173])).
% 2.06/1.22  tff(c_68, plain, (k2_tarski('#skF_5', '#skF_6')!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.06/1.22  tff(c_70, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.06/1.22  tff(c_211, plain, (![B_68, A_69]: (k1_tarski(B_68)=A_69 | k1_xboole_0=A_69 | ~r1_tarski(A_69, k1_tarski(B_68)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.06/1.22  tff(c_214, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7') | k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_70, c_211])).
% 2.06/1.22  tff(c_229, plain, (k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_214])).
% 2.06/1.22  tff(c_242, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_229, c_101])).
% 2.06/1.22  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_242])).
% 2.06/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.22  
% 2.06/1.22  Inference rules
% 2.06/1.22  ----------------------
% 2.06/1.22  #Ref     : 0
% 2.06/1.22  #Sup     : 39
% 2.06/1.22  #Fact    : 0
% 2.06/1.22  #Define  : 0
% 2.06/1.22  #Split   : 0
% 2.06/1.22  #Chain   : 0
% 2.06/1.22  #Close   : 0
% 2.06/1.22  
% 2.06/1.22  Ordering : KBO
% 2.06/1.22  
% 2.06/1.22  Simplification rules
% 2.06/1.22  ----------------------
% 2.06/1.22  #Subsume      : 6
% 2.06/1.22  #Demod        : 11
% 2.06/1.22  #Tautology    : 24
% 2.06/1.22  #SimpNegUnit  : 3
% 2.06/1.22  #BackRed      : 3
% 2.06/1.22  
% 2.06/1.22  #Partial instantiations: 0
% 2.06/1.22  #Strategies tried      : 1
% 2.06/1.22  
% 2.06/1.22  Timing (in seconds)
% 2.06/1.22  ----------------------
% 2.06/1.22  Preprocessing        : 0.31
% 2.06/1.22  Parsing              : 0.15
% 2.06/1.22  CNF conversion       : 0.02
% 2.06/1.22  Main loop            : 0.16
% 2.06/1.22  Inferencing          : 0.05
% 2.06/1.22  Reduction            : 0.06
% 2.06/1.22  Demodulation         : 0.04
% 2.06/1.22  BG Simplification    : 0.01
% 2.06/1.22  Subsumption          : 0.04
% 2.06/1.22  Abstraction          : 0.01
% 2.06/1.22  MUC search           : 0.00
% 2.06/1.22  Cooper               : 0.00
% 2.06/1.22  Total                : 0.49
% 2.06/1.22  Index Insertion      : 0.00
% 2.06/1.22  Index Deletion       : 0.00
% 2.06/1.22  Index Matching       : 0.00
% 2.06/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
