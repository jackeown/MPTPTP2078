%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:25 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   43 (  51 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  65 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_60,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_62,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_81,plain,(
    ! [A_54,B_55] : k1_enumset1(A_54,A_54,B_55) = k2_tarski(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    ! [E_15,A_9,B_10] : r2_hidden(E_15,k1_enumset1(A_9,B_10,E_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_87,plain,(
    ! [B_55,A_54] : r2_hidden(B_55,k2_tarski(A_54,B_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_24])).

tff(c_64,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_149,plain,(
    ! [D_74,A_75,B_76] :
      ( r2_hidden(D_74,k3_xboole_0(A_75,B_76))
      | ~ r2_hidden(D_74,B_76)
      | ~ r2_hidden(D_74,A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_247,plain,(
    ! [D_98] :
      ( r2_hidden(D_98,k1_tarski('#skF_5'))
      | ~ r2_hidden(D_98,'#skF_7')
      | ~ r2_hidden(D_98,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_149])).

tff(c_258,plain,
    ( r2_hidden('#skF_6',k1_tarski('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_87,c_247])).

tff(c_265,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_258])).

tff(c_46,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_186,plain,(
    ! [E_83,C_84,B_85,A_86] :
      ( E_83 = C_84
      | E_83 = B_85
      | E_83 = A_86
      | ~ r2_hidden(E_83,k1_enumset1(A_86,B_85,C_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_205,plain,(
    ! [E_87,B_88,A_89] :
      ( E_87 = B_88
      | E_87 = A_89
      | E_87 = A_89
      | ~ r2_hidden(E_87,k2_tarski(A_89,B_88)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_186])).

tff(c_217,plain,(
    ! [E_87,A_16] :
      ( E_87 = A_16
      | E_87 = A_16
      | E_87 = A_16
      | ~ r2_hidden(E_87,k1_tarski(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_205])).

tff(c_285,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_265,c_217])).

tff(c_295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_60,c_60,c_285])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:37:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.35  
% 2.21/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.36  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.21/1.36  
% 2.21/1.36  %Foreground sorts:
% 2.21/1.36  
% 2.21/1.36  
% 2.21/1.36  %Background operators:
% 2.21/1.36  
% 2.21/1.36  
% 2.21/1.36  %Foreground operators:
% 2.21/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.21/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.21/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.21/1.36  tff('#skF_7', type, '#skF_7': $i).
% 2.21/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.21/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.21/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.21/1.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.21/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.36  
% 2.36/1.37  tff(f_74, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 2.36/1.37  tff(f_55, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.36/1.37  tff(f_51, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.36/1.37  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.36/1.37  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.36/1.37  tff(c_60, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.36/1.37  tff(c_62, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.36/1.37  tff(c_81, plain, (![A_54, B_55]: (k1_enumset1(A_54, A_54, B_55)=k2_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.36/1.37  tff(c_24, plain, (![E_15, A_9, B_10]: (r2_hidden(E_15, k1_enumset1(A_9, B_10, E_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.36/1.37  tff(c_87, plain, (![B_55, A_54]: (r2_hidden(B_55, k2_tarski(A_54, B_55)))), inference(superposition, [status(thm), theory('equality')], [c_81, c_24])).
% 2.36/1.37  tff(c_64, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.36/1.37  tff(c_149, plain, (![D_74, A_75, B_76]: (r2_hidden(D_74, k3_xboole_0(A_75, B_76)) | ~r2_hidden(D_74, B_76) | ~r2_hidden(D_74, A_75))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.36/1.37  tff(c_247, plain, (![D_98]: (r2_hidden(D_98, k1_tarski('#skF_5')) | ~r2_hidden(D_98, '#skF_7') | ~r2_hidden(D_98, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_64, c_149])).
% 2.36/1.37  tff(c_258, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5')) | ~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_87, c_247])).
% 2.36/1.37  tff(c_265, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_258])).
% 2.36/1.37  tff(c_46, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.36/1.37  tff(c_48, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.36/1.37  tff(c_186, plain, (![E_83, C_84, B_85, A_86]: (E_83=C_84 | E_83=B_85 | E_83=A_86 | ~r2_hidden(E_83, k1_enumset1(A_86, B_85, C_84)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.36/1.37  tff(c_205, plain, (![E_87, B_88, A_89]: (E_87=B_88 | E_87=A_89 | E_87=A_89 | ~r2_hidden(E_87, k2_tarski(A_89, B_88)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_186])).
% 2.36/1.37  tff(c_217, plain, (![E_87, A_16]: (E_87=A_16 | E_87=A_16 | E_87=A_16 | ~r2_hidden(E_87, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_205])).
% 2.36/1.37  tff(c_285, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_265, c_217])).
% 2.36/1.37  tff(c_295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_60, c_60, c_285])).
% 2.36/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.37  
% 2.36/1.37  Inference rules
% 2.36/1.37  ----------------------
% 2.36/1.37  #Ref     : 0
% 2.36/1.37  #Sup     : 53
% 2.36/1.37  #Fact    : 0
% 2.36/1.37  #Define  : 0
% 2.36/1.37  #Split   : 0
% 2.36/1.37  #Chain   : 0
% 2.36/1.37  #Close   : 0
% 2.36/1.37  
% 2.36/1.37  Ordering : KBO
% 2.36/1.37  
% 2.36/1.37  Simplification rules
% 2.36/1.37  ----------------------
% 2.36/1.37  #Subsume      : 0
% 2.36/1.37  #Demod        : 9
% 2.36/1.37  #Tautology    : 33
% 2.36/1.37  #SimpNegUnit  : 2
% 2.36/1.37  #BackRed      : 0
% 2.36/1.37  
% 2.36/1.37  #Partial instantiations: 0
% 2.36/1.37  #Strategies tried      : 1
% 2.36/1.37  
% 2.36/1.37  Timing (in seconds)
% 2.36/1.37  ----------------------
% 2.36/1.37  Preprocessing        : 0.33
% 2.36/1.37  Parsing              : 0.17
% 2.36/1.37  CNF conversion       : 0.03
% 2.36/1.37  Main loop            : 0.19
% 2.36/1.37  Inferencing          : 0.07
% 2.36/1.37  Reduction            : 0.06
% 2.36/1.37  Demodulation         : 0.05
% 2.36/1.37  BG Simplification    : 0.02
% 2.36/1.37  Subsumption          : 0.04
% 2.36/1.37  Abstraction          : 0.01
% 2.36/1.37  MUC search           : 0.00
% 2.36/1.37  Cooper               : 0.00
% 2.36/1.37  Total                : 0.55
% 2.36/1.37  Index Insertion      : 0.00
% 2.36/1.37  Index Deletion       : 0.00
% 2.36/1.37  Index Matching       : 0.00
% 2.36/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
