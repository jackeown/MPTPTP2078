%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:34 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  43 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_6 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_43,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    r1_setfam_1('#skF_6',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ! [A_10,B_11,C_20] :
      ( r2_hidden('#skF_5'(A_10,B_11,C_20),B_11)
      | ~ r2_hidden(C_20,A_10)
      | ~ r1_setfam_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_255,plain,(
    ! [A_55,B_56,C_57] :
      ( r2_hidden('#skF_5'(A_55,B_56,C_57),B_56)
      | ~ r2_hidden(C_57,A_55)
      | ~ r1_setfam_1(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_45,plain,(
    ! [D_24,B_25,A_26] :
      ( ~ r2_hidden(D_24,B_25)
      | ~ r2_hidden(D_24,k4_xboole_0(A_26,B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_52,plain,(
    ! [D_24,A_9] :
      ( ~ r2_hidden(D_24,k1_xboole_0)
      | ~ r2_hidden(D_24,A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_45])).

tff(c_344,plain,(
    ! [A_66,C_67,A_68] :
      ( ~ r2_hidden('#skF_5'(A_66,k1_xboole_0,C_67),A_68)
      | ~ r2_hidden(C_67,A_66)
      | ~ r1_setfam_1(A_66,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_255,c_52])).

tff(c_361,plain,(
    ! [C_72,A_73] :
      ( ~ r2_hidden(C_72,A_73)
      | ~ r1_setfam_1(A_73,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_344])).

tff(c_386,plain,(
    ! [A_74] :
      ( ~ r1_setfam_1(A_74,k1_xboole_0)
      | k1_xboole_0 = A_74 ) ),
    inference(resolution,[status(thm)],[c_20,c_361])).

tff(c_393,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_34,c_386])).

tff(c_399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_393])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:25:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.30  
% 1.95/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.30  %$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_6 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 1.95/1.30  
% 1.95/1.30  %Foreground sorts:
% 1.95/1.30  
% 1.95/1.30  
% 1.95/1.30  %Background operators:
% 1.95/1.30  
% 1.95/1.30  
% 1.95/1.30  %Foreground operators:
% 1.95/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.95/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.30  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.95/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.95/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.30  tff('#skF_6', type, '#skF_6': $i).
% 1.95/1.30  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.95/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.95/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.30  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.95/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.95/1.30  
% 1.95/1.31  tff(f_62, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_setfam_1)).
% 1.95/1.31  tff(f_43, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.95/1.31  tff(f_57, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.95/1.31  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.95/1.31  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.95/1.31  tff(c_32, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.95/1.31  tff(c_34, plain, (r1_setfam_1('#skF_6', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.95/1.31  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.95/1.31  tff(c_26, plain, (![A_10, B_11, C_20]: (r2_hidden('#skF_5'(A_10, B_11, C_20), B_11) | ~r2_hidden(C_20, A_10) | ~r1_setfam_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.95/1.31  tff(c_255, plain, (![A_55, B_56, C_57]: (r2_hidden('#skF_5'(A_55, B_56, C_57), B_56) | ~r2_hidden(C_57, A_55) | ~r1_setfam_1(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.95/1.31  tff(c_22, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.95/1.31  tff(c_45, plain, (![D_24, B_25, A_26]: (~r2_hidden(D_24, B_25) | ~r2_hidden(D_24, k4_xboole_0(A_26, B_25)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.95/1.31  tff(c_52, plain, (![D_24, A_9]: (~r2_hidden(D_24, k1_xboole_0) | ~r2_hidden(D_24, A_9))), inference(superposition, [status(thm), theory('equality')], [c_22, c_45])).
% 1.95/1.31  tff(c_344, plain, (![A_66, C_67, A_68]: (~r2_hidden('#skF_5'(A_66, k1_xboole_0, C_67), A_68) | ~r2_hidden(C_67, A_66) | ~r1_setfam_1(A_66, k1_xboole_0))), inference(resolution, [status(thm)], [c_255, c_52])).
% 1.95/1.31  tff(c_361, plain, (![C_72, A_73]: (~r2_hidden(C_72, A_73) | ~r1_setfam_1(A_73, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_344])).
% 1.95/1.31  tff(c_386, plain, (![A_74]: (~r1_setfam_1(A_74, k1_xboole_0) | k1_xboole_0=A_74)), inference(resolution, [status(thm)], [c_20, c_361])).
% 1.95/1.31  tff(c_393, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_34, c_386])).
% 1.95/1.31  tff(c_399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_393])).
% 1.95/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.31  
% 1.95/1.31  Inference rules
% 1.95/1.31  ----------------------
% 1.95/1.31  #Ref     : 0
% 1.95/1.31  #Sup     : 77
% 1.95/1.31  #Fact    : 0
% 1.95/1.31  #Define  : 0
% 1.95/1.31  #Split   : 0
% 1.95/1.31  #Chain   : 0
% 1.95/1.31  #Close   : 0
% 1.95/1.31  
% 1.95/1.31  Ordering : KBO
% 1.95/1.31  
% 1.95/1.31  Simplification rules
% 1.95/1.31  ----------------------
% 1.95/1.31  #Subsume      : 7
% 1.95/1.31  #Demod        : 33
% 1.95/1.31  #Tautology    : 40
% 1.95/1.31  #SimpNegUnit  : 1
% 1.95/1.31  #BackRed      : 0
% 1.95/1.31  
% 1.95/1.31  #Partial instantiations: 0
% 1.95/1.31  #Strategies tried      : 1
% 1.95/1.31  
% 1.95/1.31  Timing (in seconds)
% 1.95/1.31  ----------------------
% 1.95/1.32  Preprocessing        : 0.29
% 1.95/1.32  Parsing              : 0.15
% 1.95/1.32  CNF conversion       : 0.02
% 1.95/1.32  Main loop            : 0.25
% 1.95/1.32  Inferencing          : 0.10
% 1.95/1.32  Reduction            : 0.07
% 1.95/1.32  Demodulation         : 0.05
% 1.95/1.32  BG Simplification    : 0.02
% 1.95/1.32  Subsumption          : 0.05
% 1.95/1.32  Abstraction          : 0.01
% 1.95/1.32  MUC search           : 0.00
% 1.95/1.32  Cooper               : 0.00
% 1.95/1.32  Total                : 0.56
% 1.95/1.32  Index Insertion      : 0.00
% 1.95/1.32  Index Deletion       : 0.00
% 1.95/1.32  Index Matching       : 0.00
% 1.95/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
