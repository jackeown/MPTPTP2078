%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:00 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   40 (  42 expanded)
%              Number of leaves         :   25 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  32 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_61,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_58,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_52,plain,(
    ! [A_34,B_35] : k1_enumset1(A_34,A_34,B_35) = k2_tarski(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_50,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_140,plain,(
    ! [A_69,B_70,C_71] : k2_xboole_0(k2_tarski(A_69,B_70),k1_tarski(C_71)) = k1_enumset1(A_69,B_70,C_71) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_149,plain,(
    ! [A_33,C_71] : k2_xboole_0(k1_tarski(A_33),k1_tarski(C_71)) = k1_enumset1(A_33,A_33,C_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_140])).

tff(c_153,plain,(
    ! [A_72,C_73] : k2_xboole_0(k1_tarski(A_72),k1_tarski(C_73)) = k2_tarski(A_72,C_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_149])).

tff(c_60,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_159,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_60])).

tff(c_84,plain,(
    ! [A_56,B_57] : k1_enumset1(A_56,A_56,B_57) = k2_tarski(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [E_11,A_5,B_6] : r2_hidden(E_11,k1_enumset1(A_5,B_6,E_11)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_90,plain,(
    ! [B_57,A_56] : r2_hidden(B_57,k2_tarski(A_56,B_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_8])).

tff(c_177,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_90])).

tff(c_30,plain,(
    ! [C_16,A_12] :
      ( C_16 = A_12
      | ~ r2_hidden(C_16,k1_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_185,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_177,c_30])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:43:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.22  
% 1.95/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.22  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 1.95/1.22  
% 1.95/1.22  %Foreground sorts:
% 1.95/1.22  
% 1.95/1.22  
% 1.95/1.22  %Background operators:
% 1.95/1.22  
% 1.95/1.22  
% 1.95/1.22  %Foreground operators:
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.95/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.95/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.95/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.95/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.95/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.95/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.95/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.95/1.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 1.95/1.22  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.95/1.22  
% 2.04/1.23  tff(f_72, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.04/1.23  tff(f_63, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.04/1.23  tff(f_61, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.04/1.23  tff(f_55, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 2.04/1.23  tff(f_44, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.04/1.23  tff(f_51, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.04/1.23  tff(c_58, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.04/1.23  tff(c_52, plain, (![A_34, B_35]: (k1_enumset1(A_34, A_34, B_35)=k2_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.04/1.23  tff(c_50, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.04/1.23  tff(c_140, plain, (![A_69, B_70, C_71]: (k2_xboole_0(k2_tarski(A_69, B_70), k1_tarski(C_71))=k1_enumset1(A_69, B_70, C_71))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.04/1.23  tff(c_149, plain, (![A_33, C_71]: (k2_xboole_0(k1_tarski(A_33), k1_tarski(C_71))=k1_enumset1(A_33, A_33, C_71))), inference(superposition, [status(thm), theory('equality')], [c_50, c_140])).
% 2.04/1.23  tff(c_153, plain, (![A_72, C_73]: (k2_xboole_0(k1_tarski(A_72), k1_tarski(C_73))=k2_tarski(A_72, C_73))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_149])).
% 2.04/1.23  tff(c_60, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.04/1.23  tff(c_159, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_153, c_60])).
% 2.04/1.23  tff(c_84, plain, (![A_56, B_57]: (k1_enumset1(A_56, A_56, B_57)=k2_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.04/1.23  tff(c_8, plain, (![E_11, A_5, B_6]: (r2_hidden(E_11, k1_enumset1(A_5, B_6, E_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.04/1.23  tff(c_90, plain, (![B_57, A_56]: (r2_hidden(B_57, k2_tarski(A_56, B_57)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_8])).
% 2.04/1.23  tff(c_177, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_159, c_90])).
% 2.04/1.23  tff(c_30, plain, (![C_16, A_12]: (C_16=A_12 | ~r2_hidden(C_16, k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.04/1.23  tff(c_185, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_177, c_30])).
% 2.04/1.23  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_185])).
% 2.04/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.23  
% 2.04/1.23  Inference rules
% 2.04/1.23  ----------------------
% 2.04/1.23  #Ref     : 0
% 2.04/1.23  #Sup     : 31
% 2.04/1.23  #Fact    : 0
% 2.04/1.23  #Define  : 0
% 2.04/1.23  #Split   : 0
% 2.04/1.23  #Chain   : 0
% 2.04/1.23  #Close   : 0
% 2.04/1.23  
% 2.04/1.23  Ordering : KBO
% 2.04/1.23  
% 2.04/1.23  Simplification rules
% 2.04/1.23  ----------------------
% 2.04/1.23  #Subsume      : 0
% 2.04/1.23  #Demod        : 6
% 2.04/1.23  #Tautology    : 23
% 2.04/1.23  #SimpNegUnit  : 1
% 2.04/1.23  #BackRed      : 0
% 2.04/1.23  
% 2.04/1.23  #Partial instantiations: 0
% 2.04/1.23  #Strategies tried      : 1
% 2.04/1.23  
% 2.04/1.23  Timing (in seconds)
% 2.04/1.23  ----------------------
% 2.04/1.24  Preprocessing        : 0.30
% 2.04/1.24  Parsing              : 0.15
% 2.04/1.24  CNF conversion       : 0.02
% 2.04/1.24  Main loop            : 0.13
% 2.04/1.24  Inferencing          : 0.04
% 2.04/1.24  Reduction            : 0.05
% 2.04/1.24  Demodulation         : 0.04
% 2.04/1.24  BG Simplification    : 0.01
% 2.04/1.24  Subsumption          : 0.03
% 2.04/1.24  Abstraction          : 0.01
% 2.04/1.24  MUC search           : 0.00
% 2.04/1.24  Cooper               : 0.00
% 2.04/1.24  Total                : 0.46
% 2.04/1.24  Index Insertion      : 0.00
% 2.04/1.24  Index Deletion       : 0.00
% 2.04/1.24  Index Matching       : 0.00
% 2.04/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
