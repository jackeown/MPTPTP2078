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
% DateTime   : Thu Dec  3 09:48:45 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   40 (  43 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  46 expanded)
%              Number of equality atoms :   14 (  19 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_60,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [C_14] : r2_hidden(C_14,k1_tarski(C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_38,plain,(
    ! [D_20,A_15] : r2_hidden(D_20,k2_tarski(A_15,D_20)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_109,plain,(
    ! [D_38,B_39,A_40] :
      ( ~ r2_hidden(D_38,B_39)
      | ~ r2_hidden(D_38,k4_xboole_0(A_40,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_116,plain,(
    ! [D_41,A_42] :
      ( ~ r2_hidden(D_41,A_42)
      | ~ r2_hidden(D_41,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_109])).

tff(c_123,plain,(
    ! [D_20] : ~ r2_hidden(D_20,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_116])).

tff(c_62,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_167,plain,(
    ! [D_55,A_56,B_57] :
      ( r2_hidden(D_55,k4_xboole_0(A_56,B_57))
      | r2_hidden(D_55,B_57)
      | ~ r2_hidden(D_55,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_176,plain,(
    ! [D_55] :
      ( r2_hidden(D_55,k1_xboole_0)
      | r2_hidden(D_55,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_55,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_167])).

tff(c_184,plain,(
    ! [D_58] :
      ( r2_hidden(D_58,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_58,k1_tarski('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_176])).

tff(c_189,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_26,c_184])).

tff(c_24,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_192,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_189,c_24])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_192])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:27:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.25  
% 1.94/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.25  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_8 > #skF_4
% 1.94/1.25  
% 1.94/1.25  %Foreground sorts:
% 1.94/1.25  
% 1.94/1.25  
% 1.94/1.25  %Background operators:
% 1.94/1.25  
% 1.94/1.25  
% 1.94/1.25  %Foreground operators:
% 1.94/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.94/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.25  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 1.94/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.94/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.94/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.25  tff('#skF_7', type, '#skF_7': $i).
% 1.94/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.94/1.25  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.94/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.94/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.25  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.94/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.94/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.94/1.25  tff('#skF_8', type, '#skF_8': $i).
% 1.94/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.94/1.25  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.94/1.25  
% 1.94/1.26  tff(f_66, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.94/1.26  tff(f_46, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.94/1.26  tff(f_55, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.94/1.26  tff(f_39, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.94/1.26  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.94/1.26  tff(c_60, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.94/1.26  tff(c_26, plain, (![C_14]: (r2_hidden(C_14, k1_tarski(C_14)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.94/1.26  tff(c_38, plain, (![D_20, A_15]: (r2_hidden(D_20, k2_tarski(A_15, D_20)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.94/1.26  tff(c_22, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.94/1.26  tff(c_109, plain, (![D_38, B_39, A_40]: (~r2_hidden(D_38, B_39) | ~r2_hidden(D_38, k4_xboole_0(A_40, B_39)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.26  tff(c_116, plain, (![D_41, A_42]: (~r2_hidden(D_41, A_42) | ~r2_hidden(D_41, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_109])).
% 1.94/1.26  tff(c_123, plain, (![D_20]: (~r2_hidden(D_20, k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_116])).
% 1.94/1.26  tff(c_62, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.94/1.26  tff(c_167, plain, (![D_55, A_56, B_57]: (r2_hidden(D_55, k4_xboole_0(A_56, B_57)) | r2_hidden(D_55, B_57) | ~r2_hidden(D_55, A_56))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.26  tff(c_176, plain, (![D_55]: (r2_hidden(D_55, k1_xboole_0) | r2_hidden(D_55, k1_tarski('#skF_8')) | ~r2_hidden(D_55, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_62, c_167])).
% 1.94/1.26  tff(c_184, plain, (![D_58]: (r2_hidden(D_58, k1_tarski('#skF_8')) | ~r2_hidden(D_58, k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_123, c_176])).
% 1.94/1.26  tff(c_189, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_26, c_184])).
% 1.94/1.26  tff(c_24, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.94/1.26  tff(c_192, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_189, c_24])).
% 1.94/1.26  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_192])).
% 1.94/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.26  
% 1.94/1.26  Inference rules
% 1.94/1.26  ----------------------
% 1.94/1.26  #Ref     : 0
% 1.94/1.26  #Sup     : 31
% 1.94/1.26  #Fact    : 0
% 1.94/1.26  #Define  : 0
% 1.94/1.26  #Split   : 0
% 1.94/1.26  #Chain   : 0
% 1.94/1.26  #Close   : 0
% 1.94/1.26  
% 1.94/1.26  Ordering : KBO
% 1.94/1.26  
% 1.94/1.26  Simplification rules
% 1.94/1.26  ----------------------
% 1.94/1.26  #Subsume      : 8
% 1.94/1.26  #Demod        : 2
% 1.94/1.26  #Tautology    : 19
% 1.94/1.26  #SimpNegUnit  : 4
% 1.94/1.26  #BackRed      : 0
% 1.94/1.26  
% 1.94/1.26  #Partial instantiations: 0
% 1.94/1.26  #Strategies tried      : 1
% 1.94/1.26  
% 1.94/1.26  Timing (in seconds)
% 1.94/1.26  ----------------------
% 1.94/1.27  Preprocessing        : 0.31
% 1.94/1.27  Parsing              : 0.15
% 1.94/1.27  CNF conversion       : 0.02
% 1.94/1.27  Main loop            : 0.14
% 1.94/1.27  Inferencing          : 0.04
% 1.94/1.27  Reduction            : 0.05
% 1.94/1.27  Demodulation         : 0.04
% 1.94/1.27  BG Simplification    : 0.01
% 1.94/1.27  Subsumption          : 0.03
% 1.94/1.27  Abstraction          : 0.01
% 1.94/1.27  MUC search           : 0.00
% 1.94/1.27  Cooper               : 0.00
% 1.94/1.27  Total                : 0.47
% 1.94/1.27  Index Insertion      : 0.00
% 1.94/1.27  Index Deletion       : 0.00
% 1.94/1.27  Index Matching       : 0.00
% 1.94/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
