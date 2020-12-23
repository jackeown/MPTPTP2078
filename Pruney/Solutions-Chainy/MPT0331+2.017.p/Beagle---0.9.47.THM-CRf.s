%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:47 EST 2020

% Result     : Theorem 4.81s
% Output     : CNFRefutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :   39 (  44 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   41 (  50 expanded)
%              Number of equality atoms :   22 (  27 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_30,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_159,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_177,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_159])).

tff(c_180,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_177])).

tff(c_797,plain,(
    ! [A_63,B_64,C_65] :
      ( k4_xboole_0(k2_tarski(A_63,B_64),C_65) = k2_tarski(A_63,B_64)
      | r2_hidden(B_64,C_65)
      | r2_hidden(A_63,C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_845,plain,(
    ! [A_63,B_64,C_65] :
      ( k4_xboole_0(k2_tarski(A_63,B_64),k2_tarski(A_63,B_64)) = k3_xboole_0(k2_tarski(A_63,B_64),C_65)
      | r2_hidden(B_64,C_65)
      | r2_hidden(A_63,C_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_797,c_10])).

tff(c_3333,plain,(
    ! [A_109,B_110,C_111] :
      ( k3_xboole_0(k2_tarski(A_109,B_110),C_111) = k1_xboole_0
      | r2_hidden(B_110,C_111)
      | r2_hidden(A_109,C_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_845])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_239,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k3_xboole_0(A_37,B_38)) = k4_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_263,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_239])).

tff(c_3390,plain,(
    ! [C_111,A_109,B_110] :
      ( k4_xboole_0(C_111,k2_tarski(A_109,B_110)) = k4_xboole_0(C_111,k1_xboole_0)
      | r2_hidden(B_110,C_111)
      | r2_hidden(A_109,C_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3333,c_263])).

tff(c_7538,plain,(
    ! [C_164,A_165,B_166] :
      ( k4_xboole_0(C_164,k2_tarski(A_165,B_166)) = C_164
      | r2_hidden(B_166,C_164)
      | r2_hidden(A_165,C_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3390])).

tff(c_26,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_7671,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7538,c_26])).

tff(c_7732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_7671])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 14:10:40 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.81/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/2.04  
% 4.81/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/2.05  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.81/2.05  
% 4.81/2.05  %Foreground sorts:
% 4.81/2.05  
% 4.81/2.05  
% 4.81/2.05  %Background operators:
% 4.81/2.05  
% 4.81/2.05  
% 4.81/2.05  %Foreground operators:
% 4.81/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.81/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.81/2.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.81/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.81/2.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.81/2.05  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.81/2.05  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.81/2.05  tff('#skF_2', type, '#skF_2': $i).
% 4.81/2.05  tff('#skF_3', type, '#skF_3': $i).
% 4.81/2.05  tff('#skF_1', type, '#skF_1': $i).
% 4.81/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.81/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.81/2.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.81/2.05  
% 4.81/2.05  tff(f_62, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 4.81/2.05  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.81/2.05  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.81/2.05  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.81/2.05  tff(f_51, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 4.81/2.05  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.81/2.05  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.81/2.05  tff(c_30, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.81/2.05  tff(c_28, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.81/2.05  tff(c_6, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.81/2.05  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.81/2.05  tff(c_159, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.81/2.05  tff(c_177, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_159])).
% 4.81/2.05  tff(c_180, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_177])).
% 4.81/2.05  tff(c_797, plain, (![A_63, B_64, C_65]: (k4_xboole_0(k2_tarski(A_63, B_64), C_65)=k2_tarski(A_63, B_64) | r2_hidden(B_64, C_65) | r2_hidden(A_63, C_65))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.81/2.05  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.81/2.05  tff(c_845, plain, (![A_63, B_64, C_65]: (k4_xboole_0(k2_tarski(A_63, B_64), k2_tarski(A_63, B_64))=k3_xboole_0(k2_tarski(A_63, B_64), C_65) | r2_hidden(B_64, C_65) | r2_hidden(A_63, C_65))), inference(superposition, [status(thm), theory('equality')], [c_797, c_10])).
% 4.81/2.05  tff(c_3333, plain, (![A_109, B_110, C_111]: (k3_xboole_0(k2_tarski(A_109, B_110), C_111)=k1_xboole_0 | r2_hidden(B_110, C_111) | r2_hidden(A_109, C_111))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_845])).
% 4.81/2.05  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.81/2.05  tff(c_239, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k3_xboole_0(A_37, B_38))=k4_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.81/2.05  tff(c_263, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_239])).
% 4.81/2.05  tff(c_3390, plain, (![C_111, A_109, B_110]: (k4_xboole_0(C_111, k2_tarski(A_109, B_110))=k4_xboole_0(C_111, k1_xboole_0) | r2_hidden(B_110, C_111) | r2_hidden(A_109, C_111))), inference(superposition, [status(thm), theory('equality')], [c_3333, c_263])).
% 4.81/2.05  tff(c_7538, plain, (![C_164, A_165, B_166]: (k4_xboole_0(C_164, k2_tarski(A_165, B_166))=C_164 | r2_hidden(B_166, C_164) | r2_hidden(A_165, C_164))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3390])).
% 4.81/2.05  tff(c_26, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.81/2.05  tff(c_7671, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7538, c_26])).
% 4.81/2.05  tff(c_7732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_7671])).
% 4.81/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/2.05  
% 4.81/2.05  Inference rules
% 4.81/2.05  ----------------------
% 4.81/2.05  #Ref     : 0
% 4.81/2.05  #Sup     : 1858
% 4.81/2.05  #Fact    : 4
% 4.81/2.06  #Define  : 0
% 4.81/2.06  #Split   : 0
% 4.81/2.06  #Chain   : 0
% 4.81/2.06  #Close   : 0
% 4.81/2.06  
% 4.81/2.06  Ordering : KBO
% 4.81/2.06  
% 4.81/2.06  Simplification rules
% 4.81/2.06  ----------------------
% 4.81/2.06  #Subsume      : 185
% 4.81/2.06  #Demod        : 2953
% 4.81/2.06  #Tautology    : 1493
% 4.81/2.06  #SimpNegUnit  : 23
% 4.81/2.06  #BackRed      : 0
% 4.81/2.06  
% 4.81/2.06  #Partial instantiations: 0
% 4.81/2.06  #Strategies tried      : 1
% 4.81/2.06  
% 4.81/2.06  Timing (in seconds)
% 4.81/2.06  ----------------------
% 4.81/2.06  Preprocessing        : 0.29
% 4.81/2.06  Parsing              : 0.15
% 4.81/2.06  CNF conversion       : 0.02
% 4.81/2.06  Main loop            : 1.00
% 4.81/2.06  Inferencing          : 0.29
% 4.81/2.06  Reduction            : 0.53
% 4.81/2.06  Demodulation         : 0.45
% 4.81/2.06  BG Simplification    : 0.03
% 4.81/2.06  Subsumption          : 0.11
% 4.81/2.06  Abstraction          : 0.06
% 4.81/2.06  MUC search           : 0.00
% 4.81/2.06  Cooper               : 0.00
% 4.81/2.06  Total                : 1.31
% 4.81/2.06  Index Insertion      : 0.00
% 4.81/2.06  Index Deletion       : 0.00
% 4.81/2.06  Index Matching       : 0.00
% 4.81/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
