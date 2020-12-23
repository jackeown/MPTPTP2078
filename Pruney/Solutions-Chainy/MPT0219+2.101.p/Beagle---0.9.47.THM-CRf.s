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
% DateTime   : Thu Dec  3 09:48:02 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   44 (  54 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   40 (  57 expanded)
%              Number of equality atoms :   33 (  49 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_38,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_86,plain,(
    ! [A_39,B_40] : k2_xboole_0(k1_tarski(A_39),k1_tarski(B_40)) = k2_tarski(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_92,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_40])).

tff(c_53,plain,(
    ! [A_32,B_33] : k1_enumset1(A_32,A_32,B_33) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [E_9,A_3,B_4] : r2_hidden(E_9,k1_enumset1(A_3,B_4,E_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_59,plain,(
    ! [B_33,A_32] : r2_hidden(B_33,k2_tarski(A_32,B_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_6])).

tff(c_107,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_59])).

tff(c_32,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    ! [A_10,B_11] : k2_xboole_0(k1_tarski(A_10),k1_tarski(B_11)) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_131,plain,(
    ! [A_46,B_47,C_48,D_49] : k2_xboole_0(k1_tarski(A_46),k1_enumset1(B_47,C_48,D_49)) = k2_enumset1(A_46,B_47,C_48,D_49) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_143,plain,(
    ! [A_50,A_51,B_52] : k2_xboole_0(k1_tarski(A_50),k2_tarski(A_51,B_52)) = k2_enumset1(A_50,A_51,A_51,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_131])).

tff(c_169,plain,(
    ! [A_50,A_16] : k2_xboole_0(k1_tarski(A_50),k1_tarski(A_16)) = k2_enumset1(A_50,A_16,A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_143])).

tff(c_197,plain,(
    ! [A_54,A_55] : k2_enumset1(A_54,A_55,A_55,A_55) = k2_tarski(A_54,A_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_169])).

tff(c_36,plain,(
    ! [A_19,B_20,C_21] : k2_enumset1(A_19,A_19,B_20,C_21) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_207,plain,(
    ! [A_55] : k1_enumset1(A_55,A_55,A_55) = k2_tarski(A_55,A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_36])).

tff(c_221,plain,(
    ! [A_55] : k1_enumset1(A_55,A_55,A_55) = k1_tarski(A_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_207])).

tff(c_296,plain,(
    ! [E_59,C_60,B_61,A_62] :
      ( E_59 = C_60
      | E_59 = B_61
      | E_59 = A_62
      | ~ r2_hidden(E_59,k1_enumset1(A_62,B_61,C_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_387,plain,(
    ! [E_70,A_71] :
      ( E_70 = A_71
      | E_70 = A_71
      | E_70 = A_71
      | ~ r2_hidden(E_70,k1_tarski(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_296])).

tff(c_390,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_107,c_387])).

tff(c_397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_38,c_390])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.39  
% 2.27/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.40  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.27/1.40  
% 2.27/1.40  %Foreground sorts:
% 2.27/1.40  
% 2.27/1.40  
% 2.27/1.40  %Background operators:
% 2.27/1.40  
% 2.27/1.40  
% 2.27/1.40  %Foreground operators:
% 2.27/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.27/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.27/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.27/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.27/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.27/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.27/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.27/1.40  
% 2.27/1.41  tff(f_57, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.27/1.41  tff(f_44, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.27/1.41  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.27/1.41  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.27/1.41  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.27/1.41  tff(f_46, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 2.27/1.41  tff(f_52, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.27/1.41  tff(c_38, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.27/1.41  tff(c_86, plain, (![A_39, B_40]: (k2_xboole_0(k1_tarski(A_39), k1_tarski(B_40))=k2_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.27/1.41  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.27/1.41  tff(c_92, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_86, c_40])).
% 2.27/1.41  tff(c_53, plain, (![A_32, B_33]: (k1_enumset1(A_32, A_32, B_33)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.27/1.41  tff(c_6, plain, (![E_9, A_3, B_4]: (r2_hidden(E_9, k1_enumset1(A_3, B_4, E_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.27/1.41  tff(c_59, plain, (![B_33, A_32]: (r2_hidden(B_33, k2_tarski(A_32, B_33)))), inference(superposition, [status(thm), theory('equality')], [c_53, c_6])).
% 2.27/1.41  tff(c_107, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_59])).
% 2.27/1.41  tff(c_32, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.27/1.41  tff(c_28, plain, (![A_10, B_11]: (k2_xboole_0(k1_tarski(A_10), k1_tarski(B_11))=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.27/1.41  tff(c_34, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.27/1.41  tff(c_131, plain, (![A_46, B_47, C_48, D_49]: (k2_xboole_0(k1_tarski(A_46), k1_enumset1(B_47, C_48, D_49))=k2_enumset1(A_46, B_47, C_48, D_49))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.27/1.41  tff(c_143, plain, (![A_50, A_51, B_52]: (k2_xboole_0(k1_tarski(A_50), k2_tarski(A_51, B_52))=k2_enumset1(A_50, A_51, A_51, B_52))), inference(superposition, [status(thm), theory('equality')], [c_34, c_131])).
% 2.27/1.41  tff(c_169, plain, (![A_50, A_16]: (k2_xboole_0(k1_tarski(A_50), k1_tarski(A_16))=k2_enumset1(A_50, A_16, A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_32, c_143])).
% 2.27/1.41  tff(c_197, plain, (![A_54, A_55]: (k2_enumset1(A_54, A_55, A_55, A_55)=k2_tarski(A_54, A_55))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_169])).
% 2.27/1.41  tff(c_36, plain, (![A_19, B_20, C_21]: (k2_enumset1(A_19, A_19, B_20, C_21)=k1_enumset1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.27/1.41  tff(c_207, plain, (![A_55]: (k1_enumset1(A_55, A_55, A_55)=k2_tarski(A_55, A_55))), inference(superposition, [status(thm), theory('equality')], [c_197, c_36])).
% 2.27/1.41  tff(c_221, plain, (![A_55]: (k1_enumset1(A_55, A_55, A_55)=k1_tarski(A_55))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_207])).
% 2.27/1.41  tff(c_296, plain, (![E_59, C_60, B_61, A_62]: (E_59=C_60 | E_59=B_61 | E_59=A_62 | ~r2_hidden(E_59, k1_enumset1(A_62, B_61, C_60)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.27/1.41  tff(c_387, plain, (![E_70, A_71]: (E_70=A_71 | E_70=A_71 | E_70=A_71 | ~r2_hidden(E_70, k1_tarski(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_221, c_296])).
% 2.27/1.41  tff(c_390, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_107, c_387])).
% 2.27/1.41  tff(c_397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_38, c_390])).
% 2.27/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.41  
% 2.27/1.41  Inference rules
% 2.27/1.41  ----------------------
% 2.27/1.41  #Ref     : 0
% 2.27/1.41  #Sup     : 83
% 2.27/1.41  #Fact    : 0
% 2.27/1.41  #Define  : 0
% 2.27/1.41  #Split   : 0
% 2.27/1.41  #Chain   : 0
% 2.27/1.41  #Close   : 0
% 2.27/1.41  
% 2.27/1.41  Ordering : KBO
% 2.27/1.41  
% 2.27/1.41  Simplification rules
% 2.27/1.41  ----------------------
% 2.27/1.41  #Subsume      : 0
% 2.27/1.41  #Demod        : 49
% 2.27/1.41  #Tautology    : 67
% 2.27/1.41  #SimpNegUnit  : 1
% 2.27/1.41  #BackRed      : 0
% 2.27/1.41  
% 2.27/1.41  #Partial instantiations: 0
% 2.27/1.41  #Strategies tried      : 1
% 2.27/1.41  
% 2.27/1.41  Timing (in seconds)
% 2.27/1.41  ----------------------
% 2.27/1.41  Preprocessing        : 0.39
% 2.27/1.41  Parsing              : 0.17
% 2.27/1.41  CNF conversion       : 0.03
% 2.27/1.41  Main loop            : 0.22
% 2.27/1.41  Inferencing          : 0.08
% 2.27/1.41  Reduction            : 0.08
% 2.27/1.41  Demodulation         : 0.06
% 2.27/1.41  BG Simplification    : 0.02
% 2.27/1.41  Subsumption          : 0.04
% 2.27/1.41  Abstraction          : 0.01
% 2.27/1.41  MUC search           : 0.00
% 2.27/1.41  Cooper               : 0.00
% 2.27/1.41  Total                : 0.65
% 2.27/1.41  Index Insertion      : 0.00
% 2.27/1.41  Index Deletion       : 0.00
% 2.27/1.41  Index Matching       : 0.00
% 2.27/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
