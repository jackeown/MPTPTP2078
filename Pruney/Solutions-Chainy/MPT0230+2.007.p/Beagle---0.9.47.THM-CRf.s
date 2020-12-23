%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:58 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   48 (  61 expanded)
%              Number of leaves         :   26 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  63 expanded)
%              Number of equality atoms :   35 (  50 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_61,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_58,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_60,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_177,plain,(
    ! [A_60,B_61,C_62] : k2_xboole_0(k2_tarski(A_60,B_61),k1_tarski(C_62)) = k1_enumset1(A_60,B_61,C_62) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_367,plain,(
    ! [C_83,A_84,B_85] : k2_xboole_0(k1_tarski(C_83),k2_tarski(A_84,B_85)) = k1_enumset1(A_84,B_85,C_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_177])).

tff(c_62,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_118,plain,(
    ! [A_48,B_49] :
      ( k2_xboole_0(A_48,B_49) = B_49
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k2_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_118])).

tff(c_373,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_122])).

tff(c_8,plain,(
    ! [E_11,A_5,B_6] : r2_hidden(E_11,k1_enumset1(A_5,B_6,E_11)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_420,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_8])).

tff(c_52,plain,(
    ! [A_22,B_23] : k1_enumset1(A_22,A_22,B_23) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_50,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_198,plain,(
    ! [A_21,C_62] : k2_xboole_0(k1_tarski(A_21),k1_tarski(C_62)) = k1_enumset1(A_21,A_21,C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_177])).

tff(c_202,plain,(
    ! [A_63,C_64] : k2_xboole_0(k1_tarski(A_63),k1_tarski(C_64)) = k2_tarski(A_63,C_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_198])).

tff(c_232,plain,(
    ! [C_69,A_70] : k2_xboole_0(k1_tarski(C_69),k1_tarski(A_70)) = k2_tarski(A_70,C_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_2])).

tff(c_201,plain,(
    ! [A_21,C_62] : k2_xboole_0(k1_tarski(A_21),k1_tarski(C_62)) = k2_tarski(A_21,C_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_198])).

tff(c_263,plain,(
    ! [C_71,A_72] : k2_tarski(C_71,A_72) = k2_tarski(A_72,C_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_201])).

tff(c_30,plain,(
    ! [D_17,B_13,A_12] :
      ( D_17 = B_13
      | D_17 = A_12
      | ~ r2_hidden(D_17,k2_tarski(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_287,plain,(
    ! [D_17,A_72,C_71] :
      ( D_17 = A_72
      | D_17 = C_71
      | ~ r2_hidden(D_17,k2_tarski(A_72,C_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_30])).

tff(c_428,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_420,c_287])).

tff(c_435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_60,c_428])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.33  
% 2.37/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.33  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 2.37/1.33  
% 2.37/1.33  %Foreground sorts:
% 2.37/1.33  
% 2.37/1.33  
% 2.37/1.33  %Background operators:
% 2.37/1.33  
% 2.37/1.33  
% 2.37/1.33  %Foreground operators:
% 2.37/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.37/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.37/1.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.37/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.37/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.37/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.37/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.37/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.37/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.37/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.37/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.37/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.37/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.37/1.33  
% 2.37/1.34  tff(f_75, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.37/1.34  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.37/1.34  tff(f_57, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.37/1.34  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.37/1.34  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.37/1.34  tff(f_61, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.37/1.34  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.37/1.34  tff(f_55, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.37/1.34  tff(c_58, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.37/1.34  tff(c_60, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.37/1.34  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.37/1.34  tff(c_177, plain, (![A_60, B_61, C_62]: (k2_xboole_0(k2_tarski(A_60, B_61), k1_tarski(C_62))=k1_enumset1(A_60, B_61, C_62))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.37/1.34  tff(c_367, plain, (![C_83, A_84, B_85]: (k2_xboole_0(k1_tarski(C_83), k2_tarski(A_84, B_85))=k1_enumset1(A_84, B_85, C_83))), inference(superposition, [status(thm), theory('equality')], [c_2, c_177])).
% 2.37/1.34  tff(c_62, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.37/1.34  tff(c_118, plain, (![A_48, B_49]: (k2_xboole_0(A_48, B_49)=B_49 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.37/1.34  tff(c_122, plain, (k2_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k2_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_62, c_118])).
% 2.37/1.34  tff(c_373, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_367, c_122])).
% 2.37/1.34  tff(c_8, plain, (![E_11, A_5, B_6]: (r2_hidden(E_11, k1_enumset1(A_5, B_6, E_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.37/1.34  tff(c_420, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_373, c_8])).
% 2.37/1.34  tff(c_52, plain, (![A_22, B_23]: (k1_enumset1(A_22, A_22, B_23)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.37/1.34  tff(c_50, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.37/1.34  tff(c_198, plain, (![A_21, C_62]: (k2_xboole_0(k1_tarski(A_21), k1_tarski(C_62))=k1_enumset1(A_21, A_21, C_62))), inference(superposition, [status(thm), theory('equality')], [c_50, c_177])).
% 2.37/1.34  tff(c_202, plain, (![A_63, C_64]: (k2_xboole_0(k1_tarski(A_63), k1_tarski(C_64))=k2_tarski(A_63, C_64))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_198])).
% 2.37/1.34  tff(c_232, plain, (![C_69, A_70]: (k2_xboole_0(k1_tarski(C_69), k1_tarski(A_70))=k2_tarski(A_70, C_69))), inference(superposition, [status(thm), theory('equality')], [c_202, c_2])).
% 2.37/1.34  tff(c_201, plain, (![A_21, C_62]: (k2_xboole_0(k1_tarski(A_21), k1_tarski(C_62))=k2_tarski(A_21, C_62))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_198])).
% 2.37/1.34  tff(c_263, plain, (![C_71, A_72]: (k2_tarski(C_71, A_72)=k2_tarski(A_72, C_71))), inference(superposition, [status(thm), theory('equality')], [c_232, c_201])).
% 2.37/1.34  tff(c_30, plain, (![D_17, B_13, A_12]: (D_17=B_13 | D_17=A_12 | ~r2_hidden(D_17, k2_tarski(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.37/1.34  tff(c_287, plain, (![D_17, A_72, C_71]: (D_17=A_72 | D_17=C_71 | ~r2_hidden(D_17, k2_tarski(A_72, C_71)))), inference(superposition, [status(thm), theory('equality')], [c_263, c_30])).
% 2.37/1.34  tff(c_428, plain, ('#skF_5'='#skF_6' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_420, c_287])).
% 2.37/1.34  tff(c_435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_60, c_428])).
% 2.37/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.34  
% 2.37/1.34  Inference rules
% 2.37/1.34  ----------------------
% 2.37/1.34  #Ref     : 0
% 2.37/1.34  #Sup     : 93
% 2.37/1.34  #Fact    : 0
% 2.37/1.34  #Define  : 0
% 2.37/1.34  #Split   : 0
% 2.37/1.34  #Chain   : 0
% 2.37/1.34  #Close   : 0
% 2.37/1.34  
% 2.37/1.34  Ordering : KBO
% 2.37/1.34  
% 2.37/1.34  Simplification rules
% 2.37/1.34  ----------------------
% 2.37/1.35  #Subsume      : 8
% 2.37/1.35  #Demod        : 24
% 2.37/1.35  #Tautology    : 65
% 2.37/1.35  #SimpNegUnit  : 1
% 2.37/1.35  #BackRed      : 0
% 2.37/1.35  
% 2.37/1.35  #Partial instantiations: 0
% 2.37/1.35  #Strategies tried      : 1
% 2.37/1.35  
% 2.37/1.35  Timing (in seconds)
% 2.37/1.35  ----------------------
% 2.37/1.35  Preprocessing        : 0.33
% 2.37/1.35  Parsing              : 0.17
% 2.37/1.35  CNF conversion       : 0.02
% 2.37/1.35  Main loop            : 0.23
% 2.37/1.35  Inferencing          : 0.08
% 2.37/1.35  Reduction            : 0.08
% 2.37/1.35  Demodulation         : 0.06
% 2.37/1.35  BG Simplification    : 0.02
% 2.37/1.35  Subsumption          : 0.04
% 2.37/1.35  Abstraction          : 0.01
% 2.37/1.35  MUC search           : 0.00
% 2.37/1.35  Cooper               : 0.00
% 2.37/1.35  Total                : 0.59
% 2.37/1.35  Index Insertion      : 0.00
% 2.37/1.35  Index Deletion       : 0.00
% 2.37/1.35  Index Matching       : 0.00
% 2.37/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
