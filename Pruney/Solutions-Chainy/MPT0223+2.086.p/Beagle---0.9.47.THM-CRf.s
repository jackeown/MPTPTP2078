%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:27 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   35 (  46 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  58 expanded)
%              Number of equality atoms :   14 (  27 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_26,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_42,plain,(
    ! [D_18,B_19] : r2_hidden(D_18,k2_tarski(D_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_45,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_42])).

tff(c_30,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(k1_tarski(A_15),B_16)
      | r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_72,plain,(
    ! [A_27,B_28,C_29] :
      ( ~ r1_xboole_0(A_27,B_28)
      | ~ r2_hidden(C_29,k3_xboole_0(A_27,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_75,plain,(
    ! [C_29] :
      ( ~ r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5'))
      | ~ r2_hidden(C_29,k1_tarski('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_72])).

tff(c_76,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_80,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_28,c_76])).

tff(c_81,plain,(
    ! [D_30,B_31,A_32] :
      ( D_30 = B_31
      | D_30 = A_32
      | ~ r2_hidden(D_30,k2_tarski(A_32,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_95,plain,(
    ! [D_33,A_34] :
      ( D_33 = A_34
      | D_33 = A_34
      | ~ r2_hidden(D_33,k1_tarski(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_81])).

tff(c_98,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_80,c_95])).

tff(c_105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_30,c_98])).

tff(c_108,plain,(
    ! [C_35] : ~ r2_hidden(C_35,k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_113,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_45,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:11:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.29  
% 1.87/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.29  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.87/1.29  
% 1.87/1.29  %Foreground sorts:
% 1.87/1.29  
% 1.87/1.29  
% 1.87/1.29  %Background operators:
% 1.87/1.29  
% 1.87/1.29  
% 1.87/1.29  %Foreground operators:
% 1.87/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.87/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.87/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.29  tff('#skF_5', type, '#skF_5': $i).
% 1.87/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.87/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.87/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.29  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.87/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.87/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.87/1.29  
% 1.87/1.30  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.87/1.30  tff(f_50, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.87/1.30  tff(f_62, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 1.87/1.30  tff(f_57, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.87/1.30  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.87/1.30  tff(c_26, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.87/1.30  tff(c_42, plain, (![D_18, B_19]: (r2_hidden(D_18, k2_tarski(D_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.30  tff(c_45, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_42])).
% 1.87/1.30  tff(c_30, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.87/1.30  tff(c_28, plain, (![A_15, B_16]: (r1_xboole_0(k1_tarski(A_15), B_16) | r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.87/1.30  tff(c_32, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.87/1.30  tff(c_72, plain, (![A_27, B_28, C_29]: (~r1_xboole_0(A_27, B_28) | ~r2_hidden(C_29, k3_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.87/1.30  tff(c_75, plain, (![C_29]: (~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')) | ~r2_hidden(C_29, k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_32, c_72])).
% 1.87/1.30  tff(c_76, plain, (~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_75])).
% 1.87/1.30  tff(c_80, plain, (r2_hidden('#skF_4', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_76])).
% 1.87/1.30  tff(c_81, plain, (![D_30, B_31, A_32]: (D_30=B_31 | D_30=A_32 | ~r2_hidden(D_30, k2_tarski(A_32, B_31)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.30  tff(c_95, plain, (![D_33, A_34]: (D_33=A_34 | D_33=A_34 | ~r2_hidden(D_33, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_81])).
% 1.87/1.30  tff(c_98, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_80, c_95])).
% 1.87/1.30  tff(c_105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_30, c_98])).
% 1.87/1.30  tff(c_108, plain, (![C_35]: (~r2_hidden(C_35, k1_tarski('#skF_4')))), inference(splitRight, [status(thm)], [c_75])).
% 1.87/1.30  tff(c_113, plain, $false, inference(resolution, [status(thm)], [c_45, c_108])).
% 1.87/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.30  
% 1.87/1.30  Inference rules
% 1.87/1.30  ----------------------
% 1.87/1.30  #Ref     : 0
% 1.87/1.30  #Sup     : 18
% 1.87/1.30  #Fact    : 0
% 1.87/1.30  #Define  : 0
% 1.87/1.30  #Split   : 1
% 1.87/1.30  #Chain   : 0
% 1.87/1.30  #Close   : 0
% 1.87/1.30  
% 1.87/1.30  Ordering : KBO
% 1.87/1.30  
% 1.87/1.30  Simplification rules
% 1.87/1.30  ----------------------
% 1.87/1.30  #Subsume      : 0
% 1.87/1.30  #Demod        : 1
% 1.87/1.30  #Tautology    : 9
% 1.87/1.30  #SimpNegUnit  : 1
% 1.87/1.30  #BackRed      : 0
% 1.87/1.30  
% 1.87/1.30  #Partial instantiations: 0
% 1.87/1.30  #Strategies tried      : 1
% 1.87/1.30  
% 1.87/1.30  Timing (in seconds)
% 1.87/1.30  ----------------------
% 1.87/1.31  Preprocessing        : 0.33
% 1.87/1.31  Parsing              : 0.17
% 1.87/1.31  CNF conversion       : 0.02
% 1.87/1.31  Main loop            : 0.11
% 1.87/1.31  Inferencing          : 0.04
% 1.87/1.31  Reduction            : 0.03
% 1.87/1.31  Demodulation         : 0.03
% 1.87/1.31  BG Simplification    : 0.01
% 1.87/1.31  Subsumption          : 0.02
% 1.87/1.31  Abstraction          : 0.01
% 1.87/1.31  MUC search           : 0.00
% 1.87/1.31  Cooper               : 0.00
% 1.87/1.31  Total                : 0.46
% 1.87/1.31  Index Insertion      : 0.00
% 1.87/1.31  Index Deletion       : 0.00
% 1.87/1.31  Index Matching       : 0.00
% 1.87/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
