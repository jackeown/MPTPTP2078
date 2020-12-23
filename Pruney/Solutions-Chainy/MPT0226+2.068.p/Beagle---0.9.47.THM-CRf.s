%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:46 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   43 (  55 expanded)
%              Number of leaves         :   26 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  63 expanded)
%              Number of equality atoms :   17 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_8 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_50,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_68,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_62,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_96,plain,(
    ! [D_32,A_33] : r2_hidden(D_32,k2_tarski(A_33,D_32)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_99,plain,(
    ! [A_23] : r2_hidden(A_23,k1_tarski(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_96])).

tff(c_42,plain,(
    ! [A_16] : k4_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_140,plain,(
    ! [D_49,B_50,A_51] :
      ( ~ r2_hidden(D_49,B_50)
      | ~ r2_hidden(D_49,k4_xboole_0(A_51,B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_151,plain,(
    ! [D_55,A_56] :
      ( ~ r2_hidden(D_55,A_56)
      | ~ r2_hidden(D_55,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_140])).

tff(c_164,plain,(
    ! [A_23] : ~ r2_hidden(A_23,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_99,c_151])).

tff(c_70,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_210,plain,(
    ! [D_69,A_70,B_71] :
      ( r2_hidden(D_69,k4_xboole_0(A_70,B_71))
      | r2_hidden(D_69,B_71)
      | ~ r2_hidden(D_69,A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_219,plain,(
    ! [D_69] :
      ( r2_hidden(D_69,k1_xboole_0)
      | r2_hidden(D_69,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_69,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_210])).

tff(c_227,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_72,k1_tarski('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_219])).

tff(c_232,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_99,c_227])).

tff(c_177,plain,(
    ! [D_61,B_62,A_63] :
      ( D_61 = B_62
      | D_61 = A_63
      | ~ r2_hidden(D_61,k2_tarski(A_63,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_186,plain,(
    ! [D_61,A_23] :
      ( D_61 = A_23
      | D_61 = A_23
      | ~ r2_hidden(D_61,k1_tarski(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_177])).

tff(c_235,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_232,c_186])).

tff(c_239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_68,c_235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.32  
% 2.18/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.32  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_8 > #skF_3
% 2.18/1.32  
% 2.18/1.32  %Foreground sorts:
% 2.18/1.32  
% 2.18/1.32  
% 2.18/1.32  %Background operators:
% 2.18/1.32  
% 2.18/1.32  
% 2.18/1.32  %Foreground operators:
% 2.18/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.18/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.32  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.18/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.32  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.18/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.18/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.18/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.32  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.18/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.18/1.32  tff('#skF_8', type, '#skF_8': $i).
% 2.18/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.18/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.32  
% 2.18/1.33  tff(f_70, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.18/1.33  tff(f_61, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.18/1.33  tff(f_59, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.18/1.33  tff(f_50, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.18/1.33  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.18/1.33  tff(c_68, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.18/1.33  tff(c_62, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.18/1.34  tff(c_96, plain, (![D_32, A_33]: (r2_hidden(D_32, k2_tarski(A_33, D_32)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.18/1.34  tff(c_99, plain, (![A_23]: (r2_hidden(A_23, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_96])).
% 2.18/1.34  tff(c_42, plain, (![A_16]: (k4_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.34  tff(c_140, plain, (![D_49, B_50, A_51]: (~r2_hidden(D_49, B_50) | ~r2_hidden(D_49, k4_xboole_0(A_51, B_50)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.18/1.34  tff(c_151, plain, (![D_55, A_56]: (~r2_hidden(D_55, A_56) | ~r2_hidden(D_55, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_140])).
% 2.18/1.34  tff(c_164, plain, (![A_23]: (~r2_hidden(A_23, k1_xboole_0))), inference(resolution, [status(thm)], [c_99, c_151])).
% 2.18/1.34  tff(c_70, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.18/1.34  tff(c_210, plain, (![D_69, A_70, B_71]: (r2_hidden(D_69, k4_xboole_0(A_70, B_71)) | r2_hidden(D_69, B_71) | ~r2_hidden(D_69, A_70))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.18/1.34  tff(c_219, plain, (![D_69]: (r2_hidden(D_69, k1_xboole_0) | r2_hidden(D_69, k1_tarski('#skF_8')) | ~r2_hidden(D_69, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_210])).
% 2.18/1.34  tff(c_227, plain, (![D_72]: (r2_hidden(D_72, k1_tarski('#skF_8')) | ~r2_hidden(D_72, k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_164, c_219])).
% 2.18/1.34  tff(c_232, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_99, c_227])).
% 2.18/1.34  tff(c_177, plain, (![D_61, B_62, A_63]: (D_61=B_62 | D_61=A_63 | ~r2_hidden(D_61, k2_tarski(A_63, B_62)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.18/1.34  tff(c_186, plain, (![D_61, A_23]: (D_61=A_23 | D_61=A_23 | ~r2_hidden(D_61, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_177])).
% 2.18/1.34  tff(c_235, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_232, c_186])).
% 2.18/1.34  tff(c_239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_68, c_235])).
% 2.18/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.34  
% 2.18/1.34  Inference rules
% 2.18/1.34  ----------------------
% 2.18/1.34  #Ref     : 0
% 2.18/1.34  #Sup     : 40
% 2.18/1.34  #Fact    : 0
% 2.18/1.34  #Define  : 0
% 2.18/1.34  #Split   : 0
% 2.18/1.34  #Chain   : 0
% 2.18/1.34  #Close   : 0
% 2.18/1.34  
% 2.18/1.34  Ordering : KBO
% 2.18/1.34  
% 2.18/1.34  Simplification rules
% 2.18/1.34  ----------------------
% 2.18/1.34  #Subsume      : 10
% 2.18/1.34  #Demod        : 1
% 2.18/1.34  #Tautology    : 24
% 2.18/1.34  #SimpNegUnit  : 4
% 2.18/1.34  #BackRed      : 0
% 2.18/1.34  
% 2.18/1.34  #Partial instantiations: 0
% 2.18/1.34  #Strategies tried      : 1
% 2.18/1.34  
% 2.18/1.34  Timing (in seconds)
% 2.18/1.34  ----------------------
% 2.18/1.34  Preprocessing        : 0.33
% 2.18/1.34  Parsing              : 0.17
% 2.18/1.34  CNF conversion       : 0.03
% 2.18/1.34  Main loop            : 0.19
% 2.18/1.34  Inferencing          : 0.06
% 2.18/1.34  Reduction            : 0.06
% 2.18/1.34  Demodulation         : 0.05
% 2.18/1.34  BG Simplification    : 0.02
% 2.18/1.34  Subsumption          : 0.04
% 2.18/1.34  Abstraction          : 0.01
% 2.18/1.34  MUC search           : 0.00
% 2.18/1.34  Cooper               : 0.00
% 2.18/1.34  Total                : 0.55
% 2.18/1.34  Index Insertion      : 0.00
% 2.18/1.34  Index Deletion       : 0.00
% 2.18/1.34  Index Matching       : 0.00
% 2.18/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
