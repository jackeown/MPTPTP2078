%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:01 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   47 (  53 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :   37 (  44 expanded)
%              Number of equality atoms :   30 (  37 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_50,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_44,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_46,plain,(
    ! [A_23,B_24,C_25] : k2_enumset1(A_23,A_23,B_24,C_25) = k1_enumset1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_48,plain,(
    ! [A_26,B_27,C_28,D_29] : k3_enumset1(A_26,A_26,B_27,C_28,D_29) = k2_enumset1(A_26,B_27,C_28,D_29) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_477,plain,(
    ! [D_912,B_913,A_915,E_914,C_911] : k2_xboole_0(k2_enumset1(A_915,B_913,C_911,D_912),k1_tarski(E_914)) = k3_enumset1(A_915,B_913,C_911,D_912,E_914) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_523,plain,(
    ! [A_23,B_24,C_25,E_914] : k3_enumset1(A_23,A_23,B_24,C_25,E_914) = k2_xboole_0(k1_enumset1(A_23,B_24,C_25),k1_tarski(E_914)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_477])).

tff(c_527,plain,(
    ! [A_949,B_950,C_951,E_952] : k2_xboole_0(k1_enumset1(A_949,B_950,C_951),k1_tarski(E_952)) = k2_enumset1(A_949,B_950,C_951,E_952) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_523])).

tff(c_573,plain,(
    ! [A_21,B_22,E_952] : k2_xboole_0(k2_tarski(A_21,B_22),k1_tarski(E_952)) = k2_enumset1(A_21,A_21,B_22,E_952) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_527])).

tff(c_577,plain,(
    ! [A_986,B_987,E_988] : k2_xboole_0(k2_tarski(A_986,B_987),k1_tarski(E_988)) = k1_enumset1(A_986,B_987,E_988) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_573])).

tff(c_623,plain,(
    ! [A_20,E_988] : k2_xboole_0(k1_tarski(A_20),k1_tarski(E_988)) = k1_enumset1(A_20,A_20,E_988) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_577])).

tff(c_627,plain,(
    ! [A_1022,E_1023] : k2_xboole_0(k1_tarski(A_1022),k1_tarski(E_1023)) = k2_tarski(A_1022,E_1023) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_623])).

tff(c_52,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_633,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_52])).

tff(c_72,plain,(
    ! [A_43,B_44] : k1_enumset1(A_43,A_43,B_44) = k2_tarski(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [E_9,A_3,B_4] : r2_hidden(E_9,k1_enumset1(A_3,B_4,E_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_78,plain,(
    ! [B_44,A_43] : r2_hidden(B_44,k2_tarski(A_43,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_6])).

tff(c_725,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_78])).

tff(c_28,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_748,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_725,c_28])).

tff(c_780,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_748])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.39  
% 2.33/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.39  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 2.33/1.39  
% 2.33/1.39  %Foreground sorts:
% 2.33/1.39  
% 2.33/1.39  
% 2.33/1.39  %Background operators:
% 2.33/1.39  
% 2.33/1.39  
% 2.33/1.39  %Foreground operators:
% 2.33/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.33/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.33/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.33/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.33/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.33/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.33/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.33/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.33/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.33/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.33/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.33/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.33/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.33/1.39  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.33/1.39  
% 2.33/1.40  tff(f_64, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.33/1.40  tff(f_55, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.33/1.40  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.33/1.40  tff(f_57, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.33/1.40  tff(f_59, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.33/1.40  tff(f_51, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 2.33/1.40  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.33/1.40  tff(f_49, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.33/1.40  tff(c_50, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.33/1.40  tff(c_44, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.33/1.40  tff(c_42, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.33/1.40  tff(c_46, plain, (![A_23, B_24, C_25]: (k2_enumset1(A_23, A_23, B_24, C_25)=k1_enumset1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.33/1.40  tff(c_48, plain, (![A_26, B_27, C_28, D_29]: (k3_enumset1(A_26, A_26, B_27, C_28, D_29)=k2_enumset1(A_26, B_27, C_28, D_29))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.33/1.40  tff(c_477, plain, (![D_912, B_913, A_915, E_914, C_911]: (k2_xboole_0(k2_enumset1(A_915, B_913, C_911, D_912), k1_tarski(E_914))=k3_enumset1(A_915, B_913, C_911, D_912, E_914))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.33/1.40  tff(c_523, plain, (![A_23, B_24, C_25, E_914]: (k3_enumset1(A_23, A_23, B_24, C_25, E_914)=k2_xboole_0(k1_enumset1(A_23, B_24, C_25), k1_tarski(E_914)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_477])).
% 2.33/1.40  tff(c_527, plain, (![A_949, B_950, C_951, E_952]: (k2_xboole_0(k1_enumset1(A_949, B_950, C_951), k1_tarski(E_952))=k2_enumset1(A_949, B_950, C_951, E_952))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_523])).
% 2.33/1.40  tff(c_573, plain, (![A_21, B_22, E_952]: (k2_xboole_0(k2_tarski(A_21, B_22), k1_tarski(E_952))=k2_enumset1(A_21, A_21, B_22, E_952))), inference(superposition, [status(thm), theory('equality')], [c_44, c_527])).
% 2.33/1.40  tff(c_577, plain, (![A_986, B_987, E_988]: (k2_xboole_0(k2_tarski(A_986, B_987), k1_tarski(E_988))=k1_enumset1(A_986, B_987, E_988))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_573])).
% 2.33/1.40  tff(c_623, plain, (![A_20, E_988]: (k2_xboole_0(k1_tarski(A_20), k1_tarski(E_988))=k1_enumset1(A_20, A_20, E_988))), inference(superposition, [status(thm), theory('equality')], [c_42, c_577])).
% 2.33/1.40  tff(c_627, plain, (![A_1022, E_1023]: (k2_xboole_0(k1_tarski(A_1022), k1_tarski(E_1023))=k2_tarski(A_1022, E_1023))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_623])).
% 2.33/1.40  tff(c_52, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.33/1.40  tff(c_633, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_627, c_52])).
% 2.33/1.40  tff(c_72, plain, (![A_43, B_44]: (k1_enumset1(A_43, A_43, B_44)=k2_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.33/1.40  tff(c_6, plain, (![E_9, A_3, B_4]: (r2_hidden(E_9, k1_enumset1(A_3, B_4, E_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.33/1.40  tff(c_78, plain, (![B_44, A_43]: (r2_hidden(B_44, k2_tarski(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_6])).
% 2.33/1.40  tff(c_725, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_633, c_78])).
% 2.33/1.40  tff(c_28, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.33/1.40  tff(c_748, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_725, c_28])).
% 2.33/1.40  tff(c_780, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_748])).
% 2.33/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.40  
% 2.33/1.40  Inference rules
% 2.33/1.40  ----------------------
% 2.33/1.40  #Ref     : 0
% 2.33/1.40  #Sup     : 79
% 2.33/1.40  #Fact    : 0
% 2.33/1.40  #Define  : 0
% 2.33/1.40  #Split   : 1
% 2.33/1.40  #Chain   : 0
% 2.33/1.40  #Close   : 0
% 2.33/1.40  
% 2.33/1.40  Ordering : KBO
% 2.33/1.40  
% 2.33/1.40  Simplification rules
% 2.33/1.40  ----------------------
% 2.33/1.40  #Subsume      : 2
% 2.33/1.40  #Demod        : 8
% 2.33/1.40  #Tautology    : 34
% 2.33/1.40  #SimpNegUnit  : 1
% 2.33/1.40  #BackRed      : 0
% 2.33/1.40  
% 2.33/1.40  #Partial instantiations: 420
% 2.33/1.40  #Strategies tried      : 1
% 2.33/1.40  
% 2.33/1.40  Timing (in seconds)
% 2.33/1.40  ----------------------
% 2.33/1.41  Preprocessing        : 0.32
% 2.33/1.41  Parsing              : 0.17
% 2.33/1.41  CNF conversion       : 0.02
% 2.33/1.41  Main loop            : 0.28
% 2.33/1.41  Inferencing          : 0.15
% 2.33/1.41  Reduction            : 0.06
% 2.33/1.41  Demodulation         : 0.04
% 2.33/1.41  BG Simplification    : 0.02
% 2.33/1.41  Subsumption          : 0.04
% 2.33/1.41  Abstraction          : 0.01
% 2.33/1.41  MUC search           : 0.00
% 2.33/1.41  Cooper               : 0.00
% 2.33/1.41  Total                : 0.63
% 2.33/1.41  Index Insertion      : 0.00
% 2.33/1.41  Index Deletion       : 0.00
% 2.33/1.41  Index Matching       : 0.00
% 2.33/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
