%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:34 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   66 (  89 expanded)
%              Number of leaves         :   33 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 (  80 expanded)
%              Number of equality atoms :   44 (  65 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_42,plain,(
    ! [A_25] : k2_tarski(A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_102,plain,(
    ! [D_41,A_42] : r2_hidden(D_41,k2_tarski(A_42,D_41)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_105,plain,(
    ! [A_25] : r2_hidden(A_25,k1_tarski(A_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_102])).

tff(c_16,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_349,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_366,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_349])).

tff(c_371,plain,(
    ! [A_68] : k4_xboole_0(A_68,k1_xboole_0) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_366])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_248,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,B_57) = k1_xboole_0
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_256,plain,(
    ! [A_8,B_9] : k4_xboole_0(k4_xboole_0(A_8,B_9),A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_248])).

tff(c_381,plain,(
    ! [A_68] : k4_xboole_0(A_68,A_68) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_256])).

tff(c_540,plain,(
    ! [A_76,B_77] :
      ( ~ r2_hidden(A_76,B_77)
      | k4_xboole_0(k1_tarski(A_76),B_77) != k1_tarski(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_544,plain,(
    ! [A_76] :
      ( ~ r2_hidden(A_76,k1_tarski(A_76))
      | k1_tarski(A_76) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_540])).

tff(c_550,plain,(
    ! [A_76] : k1_tarski(A_76) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_544])).

tff(c_480,plain,(
    ! [A_74] : k4_xboole_0(A_74,A_74) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_256])).

tff(c_22,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_488,plain,(
    ! [A_74] : k5_xboole_0(A_74,k1_xboole_0) = k2_xboole_0(A_74,A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_22])).

tff(c_513,plain,(
    ! [A_74] : k2_xboole_0(A_74,A_74) = A_74 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_488])).

tff(c_54,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_112,plain,(
    ! [B_46,A_47] : k5_xboole_0(B_46,A_47) = k5_xboole_0(A_47,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_128,plain,(
    ! [A_47] : k5_xboole_0(k1_xboole_0,A_47) = A_47 ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_16])).

tff(c_20,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_770,plain,(
    ! [A_96,B_97,C_98] : k5_xboole_0(k5_xboole_0(A_96,B_97),C_98) = k5_xboole_0(A_96,k5_xboole_0(B_97,C_98)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_845,plain,(
    ! [A_16,C_98] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_98)) = k5_xboole_0(k1_xboole_0,C_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_770])).

tff(c_859,plain,(
    ! [A_99,C_100] : k5_xboole_0(A_99,k5_xboole_0(A_99,C_100)) = C_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_845])).

tff(c_1343,plain,(
    ! [A_119,B_120] : k5_xboole_0(A_119,k2_xboole_0(A_119,B_120)) = k4_xboole_0(B_120,A_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_859])).

tff(c_1398,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k4_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1343])).

tff(c_1409,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1398])).

tff(c_14,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1857,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1409,c_14])).

tff(c_1865,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_54,c_1857])).

tff(c_1867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_550,c_1865])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:31:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.50  
% 3.13/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.50  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 3.13/1.50  
% 3.13/1.50  %Foreground sorts:
% 3.13/1.50  
% 3.13/1.50  
% 3.13/1.50  %Background operators:
% 3.13/1.50  
% 3.13/1.50  
% 3.13/1.50  %Foreground operators:
% 3.13/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.13/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.13/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.13/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.13/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.13/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.13/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.13/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.13/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.13/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.13/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.13/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.13/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.13/1.50  
% 3.13/1.51  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.13/1.51  tff(f_56, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.13/1.51  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.13/1.51  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.13/1.51  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.13/1.51  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.13/1.51  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.13/1.51  tff(f_67, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 3.13/1.51  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.13/1.51  tff(f_73, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.13/1.51  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.13/1.51  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.13/1.51  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.13/1.51  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.13/1.51  tff(c_42, plain, (![A_25]: (k2_tarski(A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.13/1.51  tff(c_102, plain, (![D_41, A_42]: (r2_hidden(D_41, k2_tarski(A_42, D_41)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.13/1.51  tff(c_105, plain, (![A_25]: (r2_hidden(A_25, k1_tarski(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_102])).
% 3.13/1.51  tff(c_16, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.13/1.51  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.13/1.51  tff(c_349, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.13/1.51  tff(c_366, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_349])).
% 3.13/1.51  tff(c_371, plain, (![A_68]: (k4_xboole_0(A_68, k1_xboole_0)=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_366])).
% 3.13/1.51  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.13/1.51  tff(c_248, plain, (![A_56, B_57]: (k4_xboole_0(A_56, B_57)=k1_xboole_0 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.13/1.51  tff(c_256, plain, (![A_8, B_9]: (k4_xboole_0(k4_xboole_0(A_8, B_9), A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_248])).
% 3.13/1.51  tff(c_381, plain, (![A_68]: (k4_xboole_0(A_68, A_68)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_371, c_256])).
% 3.13/1.51  tff(c_540, plain, (![A_76, B_77]: (~r2_hidden(A_76, B_77) | k4_xboole_0(k1_tarski(A_76), B_77)!=k1_tarski(A_76))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.13/1.51  tff(c_544, plain, (![A_76]: (~r2_hidden(A_76, k1_tarski(A_76)) | k1_tarski(A_76)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_381, c_540])).
% 3.13/1.51  tff(c_550, plain, (![A_76]: (k1_tarski(A_76)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_105, c_544])).
% 3.13/1.51  tff(c_480, plain, (![A_74]: (k4_xboole_0(A_74, A_74)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_371, c_256])).
% 3.13/1.51  tff(c_22, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.13/1.51  tff(c_488, plain, (![A_74]: (k5_xboole_0(A_74, k1_xboole_0)=k2_xboole_0(A_74, A_74))), inference(superposition, [status(thm), theory('equality')], [c_480, c_22])).
% 3.13/1.51  tff(c_513, plain, (![A_74]: (k2_xboole_0(A_74, A_74)=A_74)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_488])).
% 3.13/1.51  tff(c_54, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.13/1.51  tff(c_112, plain, (![B_46, A_47]: (k5_xboole_0(B_46, A_47)=k5_xboole_0(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.13/1.51  tff(c_128, plain, (![A_47]: (k5_xboole_0(k1_xboole_0, A_47)=A_47)), inference(superposition, [status(thm), theory('equality')], [c_112, c_16])).
% 3.13/1.51  tff(c_20, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.13/1.51  tff(c_770, plain, (![A_96, B_97, C_98]: (k5_xboole_0(k5_xboole_0(A_96, B_97), C_98)=k5_xboole_0(A_96, k5_xboole_0(B_97, C_98)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.13/1.51  tff(c_845, plain, (![A_16, C_98]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_98))=k5_xboole_0(k1_xboole_0, C_98))), inference(superposition, [status(thm), theory('equality')], [c_20, c_770])).
% 3.13/1.51  tff(c_859, plain, (![A_99, C_100]: (k5_xboole_0(A_99, k5_xboole_0(A_99, C_100))=C_100)), inference(demodulation, [status(thm), theory('equality')], [c_128, c_845])).
% 3.13/1.51  tff(c_1343, plain, (![A_119, B_120]: (k5_xboole_0(A_119, k2_xboole_0(A_119, B_120))=k4_xboole_0(B_120, A_119))), inference(superposition, [status(thm), theory('equality')], [c_22, c_859])).
% 3.13/1.51  tff(c_1398, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k4_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1343])).
% 3.13/1.51  tff(c_1409, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1398])).
% 3.13/1.51  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.13/1.51  tff(c_1857, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1409, c_14])).
% 3.13/1.51  tff(c_1865, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_513, c_54, c_1857])).
% 3.13/1.51  tff(c_1867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_550, c_1865])).
% 3.13/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.51  
% 3.13/1.51  Inference rules
% 3.13/1.51  ----------------------
% 3.13/1.51  #Ref     : 0
% 3.13/1.51  #Sup     : 365
% 3.13/1.51  #Fact    : 2
% 3.13/1.51  #Define  : 0
% 3.13/1.51  #Split   : 0
% 3.13/1.51  #Chain   : 0
% 3.13/1.51  #Close   : 0
% 3.13/1.51  
% 3.13/1.51  Ordering : KBO
% 3.13/1.51  
% 3.13/1.51  Simplification rules
% 3.13/1.51  ----------------------
% 3.13/1.51  #Subsume      : 8
% 3.13/1.51  #Demod        : 176
% 3.13/1.51  #Tautology    : 253
% 3.13/1.51  #SimpNegUnit  : 8
% 3.13/1.51  #BackRed      : 1
% 3.13/1.51  
% 3.13/1.51  #Partial instantiations: 714
% 3.13/1.51  #Strategies tried      : 1
% 3.13/1.51  
% 3.13/1.51  Timing (in seconds)
% 3.13/1.51  ----------------------
% 3.13/1.52  Preprocessing        : 0.31
% 3.13/1.52  Parsing              : 0.16
% 3.13/1.52  CNF conversion       : 0.02
% 3.13/1.52  Main loop            : 0.45
% 3.13/1.52  Inferencing          : 0.20
% 3.13/1.52  Reduction            : 0.15
% 3.13/1.52  Demodulation         : 0.12
% 3.13/1.52  BG Simplification    : 0.02
% 3.13/1.52  Subsumption          : 0.05
% 3.13/1.52  Abstraction          : 0.02
% 3.13/1.52  MUC search           : 0.00
% 3.13/1.52  Cooper               : 0.00
% 3.13/1.52  Total                : 0.79
% 3.13/1.52  Index Insertion      : 0.00
% 3.13/1.52  Index Deletion       : 0.00
% 3.13/1.52  Index Matching       : 0.00
% 3.13/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
