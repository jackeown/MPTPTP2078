%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:08 EST 2020

% Result     : Theorem 4.42s
% Output     : CNFRefutation 4.42s
% Verified   : 
% Statistics : Number of formulae       :   54 (  56 expanded)
%              Number of leaves         :   34 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  49 expanded)
%              Number of equality atoms :   33 (  37 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_75,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_82,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_80,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_68,plain,(
    ! [A_37,B_38,C_39] : k2_enumset1(A_37,A_37,B_38,C_39) = k1_enumset1(A_37,B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_66,plain,(
    ! [A_35,B_36] : k1_enumset1(A_35,A_35,B_36) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1237,plain,(
    ! [A_144,B_145,C_146,D_147] : k2_xboole_0(k1_enumset1(A_144,B_145,C_146),k1_tarski(D_147)) = k2_enumset1(A_144,B_145,C_146,D_147) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1312,plain,(
    ! [A_35,B_36,D_147] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(D_147)) = k2_enumset1(A_35,A_35,B_36,D_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1237])).

tff(c_2636,plain,(
    ! [A_282,B_283,D_284] : k2_xboole_0(k2_tarski(A_282,B_283),k1_tarski(D_284)) = k1_enumset1(A_282,B_283,D_284) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1312])).

tff(c_12,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_84,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_126,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(A_85,B_86) = k1_xboole_0
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_133,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_126])).

tff(c_345,plain,(
    ! [A_103,B_104] : k5_xboole_0(A_103,k4_xboole_0(B_104,A_103)) = k2_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_354,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k5_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_345])).

tff(c_360,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_354])).

tff(c_2673,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2636,c_360])).

tff(c_20,plain,(
    ! [E_20,A_14,B_15] : r2_hidden(E_20,k1_enumset1(A_14,B_15,E_20)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2765,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2673,c_20])).

tff(c_42,plain,(
    ! [D_26,B_22,A_21] :
      ( D_26 = B_22
      | D_26 = A_21
      | ~ r2_hidden(D_26,k2_tarski(A_21,B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2790,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2765,c_42])).

tff(c_2794,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_80,c_2790])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.42/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.85  
% 4.42/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.86  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 4.42/1.86  
% 4.42/1.86  %Foreground sorts:
% 4.42/1.86  
% 4.42/1.86  
% 4.42/1.86  %Background operators:
% 4.42/1.86  
% 4.42/1.86  
% 4.42/1.86  %Foreground operators:
% 4.42/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.42/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.42/1.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.42/1.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.42/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.42/1.86  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.42/1.86  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.42/1.86  tff('#skF_7', type, '#skF_7': $i).
% 4.42/1.86  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.42/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.42/1.86  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.42/1.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.42/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.42/1.86  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.42/1.86  tff('#skF_6', type, '#skF_6': $i).
% 4.42/1.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.42/1.86  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.42/1.86  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.42/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.42/1.86  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.42/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.42/1.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.42/1.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.42/1.86  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.42/1.86  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.42/1.86  
% 4.42/1.87  tff(f_97, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 4.42/1.87  tff(f_77, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.42/1.87  tff(f_75, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.42/1.87  tff(f_71, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 4.42/1.87  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.42/1.87  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.42/1.87  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.42/1.88  tff(f_58, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.42/1.88  tff(f_67, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 4.42/1.88  tff(c_82, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.42/1.88  tff(c_80, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.42/1.88  tff(c_68, plain, (![A_37, B_38, C_39]: (k2_enumset1(A_37, A_37, B_38, C_39)=k1_enumset1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.42/1.88  tff(c_66, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.42/1.88  tff(c_1237, plain, (![A_144, B_145, C_146, D_147]: (k2_xboole_0(k1_enumset1(A_144, B_145, C_146), k1_tarski(D_147))=k2_enumset1(A_144, B_145, C_146, D_147))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.42/1.88  tff(c_1312, plain, (![A_35, B_36, D_147]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(D_147))=k2_enumset1(A_35, A_35, B_36, D_147))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1237])).
% 4.42/1.88  tff(c_2636, plain, (![A_282, B_283, D_284]: (k2_xboole_0(k2_tarski(A_282, B_283), k1_tarski(D_284))=k1_enumset1(A_282, B_283, D_284))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1312])).
% 4.42/1.88  tff(c_12, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.42/1.88  tff(c_84, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.42/1.88  tff(c_126, plain, (![A_85, B_86]: (k4_xboole_0(A_85, B_86)=k1_xboole_0 | ~r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.42/1.88  tff(c_133, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_xboole_0), inference(resolution, [status(thm)], [c_84, c_126])).
% 4.42/1.88  tff(c_345, plain, (![A_103, B_104]: (k5_xboole_0(A_103, k4_xboole_0(B_104, A_103))=k2_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.42/1.88  tff(c_354, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k5_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_133, c_345])).
% 4.42/1.88  tff(c_360, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k2_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_354])).
% 4.42/1.88  tff(c_2673, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2636, c_360])).
% 4.42/1.88  tff(c_20, plain, (![E_20, A_14, B_15]: (r2_hidden(E_20, k1_enumset1(A_14, B_15, E_20)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.42/1.88  tff(c_2765, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2673, c_20])).
% 4.42/1.88  tff(c_42, plain, (![D_26, B_22, A_21]: (D_26=B_22 | D_26=A_21 | ~r2_hidden(D_26, k2_tarski(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.42/1.88  tff(c_2790, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_2765, c_42])).
% 4.42/1.88  tff(c_2794, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_80, c_2790])).
% 4.42/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.88  
% 4.42/1.88  Inference rules
% 4.42/1.88  ----------------------
% 4.42/1.88  #Ref     : 0
% 4.42/1.88  #Sup     : 685
% 4.42/1.88  #Fact    : 0
% 4.42/1.88  #Define  : 0
% 4.42/1.88  #Split   : 0
% 4.42/1.88  #Chain   : 0
% 4.42/1.88  #Close   : 0
% 4.42/1.88  
% 4.42/1.88  Ordering : KBO
% 4.42/1.88  
% 4.42/1.88  Simplification rules
% 4.42/1.88  ----------------------
% 4.42/1.88  #Subsume      : 53
% 4.42/1.88  #Demod        : 461
% 4.42/1.88  #Tautology    : 469
% 4.42/1.88  #SimpNegUnit  : 1
% 4.42/1.88  #BackRed      : 0
% 4.42/1.88  
% 4.42/1.88  #Partial instantiations: 0
% 4.42/1.88  #Strategies tried      : 1
% 4.42/1.88  
% 4.42/1.88  Timing (in seconds)
% 4.42/1.88  ----------------------
% 4.42/1.88  Preprocessing        : 0.37
% 4.42/1.88  Parsing              : 0.19
% 4.42/1.88  CNF conversion       : 0.03
% 4.42/1.88  Main loop            : 0.68
% 4.42/1.88  Inferencing          : 0.22
% 4.42/1.88  Reduction            : 0.28
% 4.42/1.88  Demodulation         : 0.23
% 4.42/1.88  BG Simplification    : 0.03
% 4.42/1.88  Subsumption          : 0.10
% 4.42/1.88  Abstraction          : 0.03
% 4.42/1.88  MUC search           : 0.00
% 4.42/1.88  Cooper               : 0.00
% 4.42/1.88  Total                : 1.09
% 4.42/1.88  Index Insertion      : 0.00
% 4.42/1.88  Index Deletion       : 0.00
% 4.42/1.88  Index Matching       : 0.00
% 4.42/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
