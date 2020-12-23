%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:59 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   42 (  49 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    5
%              Number of atoms          :   35 (  48 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k4_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_36,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_44,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_178,plain,(
    ! [C_73,A_74] :
      ( r2_hidden(k4_tarski(C_73,'#skF_5'(A_74,k1_relat_1(A_74),C_73)),A_74)
      | ~ r2_hidden(C_73,k1_relat_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,(
    ! [C_47,B_48] : ~ r2_hidden(C_47,k4_xboole_0(B_48,k1_tarski(C_47))) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_49,plain,(
    ! [C_47] : ~ r2_hidden(C_47,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_46])).

tff(c_197,plain,(
    ! [C_75] : ~ r2_hidden(C_75,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_178,c_49])).

tff(c_217,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_197])).

tff(c_226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_217])).

tff(c_227,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_308,plain,(
    ! [A_96,C_97] :
      ( r2_hidden(k4_tarski('#skF_9'(A_96,k2_relat_1(A_96),C_97),C_97),A_96)
      | ~ r2_hidden(C_97,k2_relat_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_234,plain,(
    ! [C_77,B_78] : ~ r2_hidden(C_77,k4_xboole_0(B_78,k1_tarski(C_77))) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_237,plain,(
    ! [C_77] : ~ r2_hidden(C_77,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_234])).

tff(c_327,plain,(
    ! [C_98] : ~ r2_hidden(C_98,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_308,c_237])).

tff(c_339,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_327])).

tff(c_345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:51:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.24  
% 1.99/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.24  %$ r2_hidden > k4_xboole_0 > k4_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_4
% 2.00/1.24  
% 2.00/1.24  %Foreground sorts:
% 2.00/1.24  
% 2.00/1.24  
% 2.00/1.24  %Background operators:
% 2.00/1.24  
% 2.00/1.24  
% 2.00/1.24  %Foreground operators:
% 2.00/1.24  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.00/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.00/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.00/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.00/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.00/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.00/1.24  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.00/1.24  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.00/1.24  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 2.00/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.00/1.24  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.00/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.24  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.00/1.24  
% 2.00/1.25  tff(f_62, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.00/1.25  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.00/1.25  tff(f_50, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.00/1.25  tff(f_35, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.00/1.25  tff(f_42, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.00/1.25  tff(f_58, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.00/1.25  tff(c_36, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.00/1.25  tff(c_44, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 2.00/1.25  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.00/1.25  tff(c_178, plain, (![C_73, A_74]: (r2_hidden(k4_tarski(C_73, '#skF_5'(A_74, k1_relat_1(A_74), C_73)), A_74) | ~r2_hidden(C_73, k1_relat_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.00/1.25  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.00/1.25  tff(c_46, plain, (![C_47, B_48]: (~r2_hidden(C_47, k4_xboole_0(B_48, k1_tarski(C_47))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.00/1.25  tff(c_49, plain, (![C_47]: (~r2_hidden(C_47, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_46])).
% 2.00/1.25  tff(c_197, plain, (![C_75]: (~r2_hidden(C_75, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_178, c_49])).
% 2.00/1.25  tff(c_217, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_197])).
% 2.00/1.25  tff(c_226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_217])).
% 2.00/1.25  tff(c_227, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.00/1.25  tff(c_308, plain, (![A_96, C_97]: (r2_hidden(k4_tarski('#skF_9'(A_96, k2_relat_1(A_96), C_97), C_97), A_96) | ~r2_hidden(C_97, k2_relat_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.00/1.25  tff(c_234, plain, (![C_77, B_78]: (~r2_hidden(C_77, k4_xboole_0(B_78, k1_tarski(C_77))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.00/1.25  tff(c_237, plain, (![C_77]: (~r2_hidden(C_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_234])).
% 2.00/1.25  tff(c_327, plain, (![C_98]: (~r2_hidden(C_98, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_308, c_237])).
% 2.00/1.25  tff(c_339, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_327])).
% 2.00/1.25  tff(c_345, plain, $false, inference(negUnitSimplification, [status(thm)], [c_227, c_339])).
% 2.00/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.25  
% 2.00/1.25  Inference rules
% 2.00/1.25  ----------------------
% 2.00/1.25  #Ref     : 0
% 2.00/1.25  #Sup     : 58
% 2.00/1.25  #Fact    : 0
% 2.00/1.25  #Define  : 0
% 2.00/1.25  #Split   : 1
% 2.00/1.25  #Chain   : 0
% 2.00/1.25  #Close   : 0
% 2.00/1.25  
% 2.00/1.25  Ordering : KBO
% 2.00/1.25  
% 2.00/1.25  Simplification rules
% 2.00/1.25  ----------------------
% 2.00/1.25  #Subsume      : 9
% 2.00/1.25  #Demod        : 12
% 2.00/1.25  #Tautology    : 20
% 2.00/1.25  #SimpNegUnit  : 9
% 2.00/1.25  #BackRed      : 1
% 2.00/1.25  
% 2.00/1.25  #Partial instantiations: 0
% 2.00/1.25  #Strategies tried      : 1
% 2.00/1.25  
% 2.00/1.25  Timing (in seconds)
% 2.00/1.25  ----------------------
% 2.00/1.25  Preprocessing        : 0.28
% 2.00/1.25  Parsing              : 0.15
% 2.00/1.25  CNF conversion       : 0.03
% 2.00/1.25  Main loop            : 0.20
% 2.00/1.25  Inferencing          : 0.08
% 2.00/1.25  Reduction            : 0.05
% 2.00/1.25  Demodulation         : 0.03
% 2.00/1.25  BG Simplification    : 0.01
% 2.00/1.25  Subsumption          : 0.03
% 2.00/1.26  Abstraction          : 0.01
% 2.00/1.26  MUC search           : 0.00
% 2.00/1.26  Cooper               : 0.00
% 2.00/1.26  Total                : 0.51
% 2.00/1.26  Index Insertion      : 0.00
% 2.00/1.26  Index Deletion       : 0.00
% 2.00/1.26  Index Matching       : 0.00
% 2.00/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
