%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:58 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   45 (  47 expanded)
%              Number of leaves         :   29 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  43 expanded)
%              Number of equality atoms :   27 (  31 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_80,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_78,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_429,plain,(
    ! [A_114,B_115,C_116] : k2_xboole_0(k2_tarski(A_114,B_115),k1_tarski(C_116)) = k1_enumset1(A_114,B_115,C_116) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_82,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_214,plain,(
    ! [A_97,B_98] :
      ( k3_xboole_0(A_97,B_98) = A_97
      | ~ r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_218,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_214])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_171,plain,(
    ! [A_93,B_94] : k2_xboole_0(A_93,k3_xboole_0(A_93,B_94)) = A_93 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_180,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_171])).

tff(c_363,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_180])).

tff(c_435,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_363])).

tff(c_12,plain,(
    ! [E_15,A_9,B_10] : r2_hidden(E_15,k1_enumset1(A_9,B_10,E_15)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_475,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_12])).

tff(c_34,plain,(
    ! [D_21,B_17,A_16] :
      ( D_21 = B_17
      | D_21 = A_16
      | ~ r2_hidden(D_21,k2_tarski(A_16,B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_489,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_475,c_34])).

tff(c_493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_78,c_489])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:52:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.35  
% 2.36/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.36  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 2.36/1.36  
% 2.36/1.36  %Foreground sorts:
% 2.36/1.36  
% 2.36/1.36  
% 2.36/1.36  %Background operators:
% 2.36/1.36  
% 2.36/1.36  
% 2.36/1.36  %Foreground operators:
% 2.36/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.36/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.36/1.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.36/1.36  tff('#skF_7', type, '#skF_7': $i).
% 2.36/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.36/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.36/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.36/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.36/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.36/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.36/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.36/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.36/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.36/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.36/1.36  
% 2.36/1.37  tff(f_95, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.36/1.37  tff(f_63, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.36/1.37  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.36/1.37  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.36/1.37  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.36/1.37  tff(f_50, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.36/1.37  tff(f_59, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.36/1.37  tff(c_80, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.36/1.37  tff(c_78, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.36/1.37  tff(c_429, plain, (![A_114, B_115, C_116]: (k2_xboole_0(k2_tarski(A_114, B_115), k1_tarski(C_116))=k1_enumset1(A_114, B_115, C_116))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.36/1.37  tff(c_82, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.36/1.37  tff(c_214, plain, (![A_97, B_98]: (k3_xboole_0(A_97, B_98)=A_97 | ~r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.36/1.37  tff(c_218, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_82, c_214])).
% 2.36/1.37  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.36/1.37  tff(c_171, plain, (![A_93, B_94]: (k2_xboole_0(A_93, k3_xboole_0(A_93, B_94))=A_93)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.37  tff(c_180, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(B_4, A_3))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_171])).
% 2.36/1.37  tff(c_363, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_218, c_180])).
% 2.36/1.37  tff(c_435, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_429, c_363])).
% 2.36/1.37  tff(c_12, plain, (![E_15, A_9, B_10]: (r2_hidden(E_15, k1_enumset1(A_9, B_10, E_15)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.36/1.37  tff(c_475, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_435, c_12])).
% 2.36/1.37  tff(c_34, plain, (![D_21, B_17, A_16]: (D_21=B_17 | D_21=A_16 | ~r2_hidden(D_21, k2_tarski(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.36/1.37  tff(c_489, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_475, c_34])).
% 2.36/1.37  tff(c_493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_78, c_489])).
% 2.36/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.37  
% 2.36/1.37  Inference rules
% 2.36/1.37  ----------------------
% 2.36/1.37  #Ref     : 0
% 2.36/1.37  #Sup     : 104
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
% 2.36/1.37  #Demod        : 33
% 2.36/1.37  #Tautology    : 83
% 2.36/1.37  #SimpNegUnit  : 1
% 2.36/1.37  #BackRed      : 0
% 2.36/1.37  
% 2.36/1.37  #Partial instantiations: 0
% 2.36/1.37  #Strategies tried      : 1
% 2.36/1.37  
% 2.36/1.37  Timing (in seconds)
% 2.36/1.37  ----------------------
% 2.62/1.37  Preprocessing        : 0.33
% 2.62/1.37  Parsing              : 0.16
% 2.62/1.37  CNF conversion       : 0.03
% 2.62/1.37  Main loop            : 0.23
% 2.62/1.37  Inferencing          : 0.07
% 2.62/1.37  Reduction            : 0.09
% 2.62/1.37  Demodulation         : 0.07
% 2.62/1.37  BG Simplification    : 0.02
% 2.62/1.37  Subsumption          : 0.04
% 2.62/1.37  Abstraction          : 0.01
% 2.62/1.37  MUC search           : 0.00
% 2.62/1.37  Cooper               : 0.00
% 2.62/1.37  Total                : 0.59
% 2.62/1.37  Index Insertion      : 0.00
% 2.62/1.37  Index Deletion       : 0.00
% 2.62/1.37  Index Matching       : 0.00
% 2.62/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
