%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:01 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   57 (  59 expanded)
%              Number of leaves         :   33 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   49 (  55 expanded)
%              Number of equality atoms :   39 (  43 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_69,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_76,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_74,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_62,plain,(
    ! [A_35,B_36,C_37] : k2_enumset1(A_35,A_35,B_36,C_37) = k1_enumset1(A_35,B_36,C_37) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_60,plain,(
    ! [A_33,B_34] : k1_enumset1(A_33,A_33,B_34) = k2_tarski(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1025,plain,(
    ! [A_127,B_128,C_129,D_130] : k2_xboole_0(k1_enumset1(A_127,B_128,C_129),k1_tarski(D_130)) = k2_enumset1(A_127,B_128,C_129,D_130) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1067,plain,(
    ! [A_33,B_34,D_130] : k2_xboole_0(k2_tarski(A_33,B_34),k1_tarski(D_130)) = k2_enumset1(A_33,A_33,B_34,D_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1025])).

tff(c_1339,plain,(
    ! [A_140,B_141,D_142] : k2_xboole_0(k2_tarski(A_140,B_141),k1_tarski(D_142)) = k1_enumset1(A_140,B_141,D_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1067])).

tff(c_78,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_152,plain,(
    ! [A_83,B_84] :
      ( k3_xboole_0(A_83,B_84) = A_83
      | ~ r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_156,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_152])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_655,plain,(
    ! [A_112,B_113,C_114] : k2_xboole_0(k3_xboole_0(A_112,B_113),k3_xboole_0(A_112,C_114)) = k3_xboole_0(A_112,k2_xboole_0(B_113,C_114)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_691,plain,(
    ! [A_3,C_114] : k3_xboole_0(A_3,k2_xboole_0(A_3,C_114)) = k2_xboole_0(A_3,k3_xboole_0(A_3,C_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_655])).

tff(c_698,plain,(
    ! [A_115,C_116] : k2_xboole_0(A_115,k3_xboole_0(A_115,C_116)) = A_115 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_691])).

tff(c_750,plain,(
    ! [A_118,B_119] : k2_xboole_0(A_118,k3_xboole_0(B_119,A_118)) = A_118 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_698])).

tff(c_778,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_750])).

tff(c_1355,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1339,c_778])).

tff(c_14,plain,(
    ! [E_18,A_12,B_13] : r2_hidden(E_18,k1_enumset1(A_12,B_13,E_18)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1387,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1355,c_14])).

tff(c_36,plain,(
    ! [D_24,B_20,A_19] :
      ( D_24 = B_20
      | D_24 = A_19
      | ~ r2_hidden(D_24,k2_tarski(A_19,B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1417,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1387,c_36])).

tff(c_1421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_74,c_1417])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.58  
% 3.32/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.58  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 3.32/1.58  
% 3.32/1.58  %Foreground sorts:
% 3.32/1.58  
% 3.32/1.58  
% 3.32/1.58  %Background operators:
% 3.32/1.58  
% 3.32/1.58  
% 3.32/1.58  %Foreground operators:
% 3.32/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.32/1.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.32/1.58  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.32/1.58  tff('#skF_7', type, '#skF_7': $i).
% 3.32/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.32/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.32/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.32/1.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.32/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.32/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.32/1.58  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.58  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.32/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.32/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.32/1.58  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.58  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.32/1.58  
% 3.32/1.59  tff(f_91, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 3.32/1.59  tff(f_71, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.32/1.59  tff(f_69, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.32/1.59  tff(f_65, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 3.32/1.59  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.32/1.59  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.32/1.59  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.32/1.59  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.32/1.59  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 3.32/1.59  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.32/1.59  tff(f_61, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.32/1.59  tff(c_76, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.32/1.59  tff(c_74, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.32/1.59  tff(c_62, plain, (![A_35, B_36, C_37]: (k2_enumset1(A_35, A_35, B_36, C_37)=k1_enumset1(A_35, B_36, C_37))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.32/1.59  tff(c_60, plain, (![A_33, B_34]: (k1_enumset1(A_33, A_33, B_34)=k2_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.32/1.59  tff(c_1025, plain, (![A_127, B_128, C_129, D_130]: (k2_xboole_0(k1_enumset1(A_127, B_128, C_129), k1_tarski(D_130))=k2_enumset1(A_127, B_128, C_129, D_130))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.32/1.59  tff(c_1067, plain, (![A_33, B_34, D_130]: (k2_xboole_0(k2_tarski(A_33, B_34), k1_tarski(D_130))=k2_enumset1(A_33, A_33, B_34, D_130))), inference(superposition, [status(thm), theory('equality')], [c_60, c_1025])).
% 3.32/1.59  tff(c_1339, plain, (![A_140, B_141, D_142]: (k2_xboole_0(k2_tarski(A_140, B_141), k1_tarski(D_142))=k1_enumset1(A_140, B_141, D_142))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1067])).
% 3.32/1.59  tff(c_78, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.32/1.59  tff(c_152, plain, (![A_83, B_84]: (k3_xboole_0(A_83, B_84)=A_83 | ~r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.32/1.59  tff(c_156, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_78, c_152])).
% 3.32/1.59  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.32/1.59  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.59  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.32/1.59  tff(c_655, plain, (![A_112, B_113, C_114]: (k2_xboole_0(k3_xboole_0(A_112, B_113), k3_xboole_0(A_112, C_114))=k3_xboole_0(A_112, k2_xboole_0(B_113, C_114)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.32/1.59  tff(c_691, plain, (![A_3, C_114]: (k3_xboole_0(A_3, k2_xboole_0(A_3, C_114))=k2_xboole_0(A_3, k3_xboole_0(A_3, C_114)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_655])).
% 3.32/1.59  tff(c_698, plain, (![A_115, C_116]: (k2_xboole_0(A_115, k3_xboole_0(A_115, C_116))=A_115)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_691])).
% 3.32/1.59  tff(c_750, plain, (![A_118, B_119]: (k2_xboole_0(A_118, k3_xboole_0(B_119, A_118))=A_118)), inference(superposition, [status(thm), theory('equality')], [c_2, c_698])).
% 3.32/1.59  tff(c_778, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_156, c_750])).
% 3.32/1.59  tff(c_1355, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1339, c_778])).
% 3.32/1.59  tff(c_14, plain, (![E_18, A_12, B_13]: (r2_hidden(E_18, k1_enumset1(A_12, B_13, E_18)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.32/1.59  tff(c_1387, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1355, c_14])).
% 3.32/1.59  tff(c_36, plain, (![D_24, B_20, A_19]: (D_24=B_20 | D_24=A_19 | ~r2_hidden(D_24, k2_tarski(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.32/1.59  tff(c_1417, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1387, c_36])).
% 3.32/1.59  tff(c_1421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_74, c_1417])).
% 3.32/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.59  
% 3.32/1.59  Inference rules
% 3.32/1.59  ----------------------
% 3.32/1.59  #Ref     : 0
% 3.32/1.59  #Sup     : 347
% 3.32/1.59  #Fact    : 0
% 3.32/1.59  #Define  : 0
% 3.32/1.59  #Split   : 0
% 3.32/1.59  #Chain   : 0
% 3.32/1.59  #Close   : 0
% 3.32/1.59  
% 3.32/1.59  Ordering : KBO
% 3.32/1.59  
% 3.32/1.59  Simplification rules
% 3.32/1.59  ----------------------
% 3.32/1.59  #Subsume      : 53
% 3.32/1.59  #Demod        : 174
% 3.32/1.59  #Tautology    : 215
% 3.32/1.59  #SimpNegUnit  : 1
% 3.32/1.59  #BackRed      : 0
% 3.32/1.59  
% 3.32/1.59  #Partial instantiations: 0
% 3.32/1.59  #Strategies tried      : 1
% 3.32/1.59  
% 3.32/1.59  Timing (in seconds)
% 3.32/1.59  ----------------------
% 3.32/1.60  Preprocessing        : 0.36
% 3.32/1.60  Parsing              : 0.18
% 3.32/1.60  CNF conversion       : 0.03
% 3.32/1.60  Main loop            : 0.41
% 3.32/1.60  Inferencing          : 0.13
% 3.32/1.60  Reduction            : 0.17
% 3.32/1.60  Demodulation         : 0.14
% 3.32/1.60  BG Simplification    : 0.03
% 3.32/1.60  Subsumption          : 0.07
% 3.32/1.60  Abstraction          : 0.02
% 3.32/1.60  MUC search           : 0.00
% 3.32/1.60  Cooper               : 0.00
% 3.32/1.60  Total                : 0.79
% 3.32/1.60  Index Insertion      : 0.00
% 3.32/1.60  Index Deletion       : 0.00
% 3.32/1.60  Index Matching       : 0.00
% 3.32/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
