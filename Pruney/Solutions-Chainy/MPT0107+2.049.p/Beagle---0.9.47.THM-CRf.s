%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:59 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 125 expanded)
%              Number of leaves         :   20 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :   45 ( 115 expanded)
%              Number of equality atoms :   44 ( 114 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_6,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k3_xboole_0(A_4,B_5)) = k4_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_56,plain,(
    ! [B_20,A_21] : k5_xboole_0(B_20,A_21) = k5_xboole_0(A_21,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,(
    ! [A_21] : k5_xboole_0(k1_xboole_0,A_21) = A_21 ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_10])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_500,plain,(
    ! [A_40,B_41,C_42] : k5_xboole_0(k5_xboole_0(A_40,B_41),C_42) = k5_xboole_0(A_40,k5_xboole_0(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_588,plain,(
    ! [A_12,C_42] : k5_xboole_0(A_12,k5_xboole_0(A_12,C_42)) = k5_xboole_0(k1_xboole_0,C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_500])).

tff(c_602,plain,(
    ! [A_43,C_44] : k5_xboole_0(A_43,k5_xboole_0(A_43,C_44)) = C_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_588])).

tff(c_654,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_602])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_231,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k3_xboole_0(A_29,B_30)) = k4_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_237,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,k3_xboole_0(A_29,B_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_8])).

tff(c_245,plain,(
    ! [A_29,B_30] : k3_xboole_0(A_29,k3_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_237])).

tff(c_281,plain,(
    ! [A_33,B_34] : k5_xboole_0(k5_xboole_0(A_33,B_34),k3_xboole_0(A_33,B_34)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1666,plain,(
    ! [A_68,B_69] : k5_xboole_0(k3_xboole_0(A_68,B_69),k5_xboole_0(A_68,B_69)) = k2_xboole_0(A_68,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_2])).

tff(c_1747,plain,(
    ! [A_29,B_30] : k5_xboole_0(k3_xboole_0(A_29,B_30),k5_xboole_0(A_29,k3_xboole_0(A_29,B_30))) = k2_xboole_0(A_29,k3_xboole_0(A_29,B_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_1666])).

tff(c_1776,plain,(
    ! [A_70,B_71] : k2_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = A_70 ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_1747])).

tff(c_18,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_644,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k4_xboole_0(B_16,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_602])).

tff(c_1791,plain,(
    ! [A_70,B_71] : k4_xboole_0(k3_xboole_0(A_70,B_71),A_70) = k5_xboole_0(A_70,A_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_1776,c_644])).

tff(c_1825,plain,(
    ! [A_72,B_73] : k4_xboole_0(k3_xboole_0(A_72,B_73),A_72) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1791])).

tff(c_1839,plain,(
    ! [A_72,B_73] : k4_xboole_0(k3_xboole_0(A_72,B_73),k1_xboole_0) = k3_xboole_0(k3_xboole_0(A_72,B_73),A_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_1825,c_8])).

tff(c_1886,plain,(
    ! [A_74,B_75] : k3_xboole_0(k3_xboole_0(A_74,B_75),A_74) = k3_xboole_0(A_74,B_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1839])).

tff(c_293,plain,(
    ! [A_33,B_34] : k5_xboole_0(k3_xboole_0(A_33,B_34),k5_xboole_0(A_33,B_34)) = k2_xboole_0(A_33,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_2])).

tff(c_1901,plain,(
    ! [A_74,B_75] : k5_xboole_0(k3_xboole_0(A_74,B_75),k5_xboole_0(k3_xboole_0(A_74,B_75),A_74)) = k2_xboole_0(k3_xboole_0(A_74,B_75),A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_1886,c_293])).

tff(c_1953,plain,(
    ! [A_76,B_77] : k2_xboole_0(k3_xboole_0(A_76,B_77),A_76) = A_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_2,c_1901])).

tff(c_740,plain,(
    ! [A_47,B_48] : k5_xboole_0(A_47,k5_xboole_0(B_48,A_47)) = B_48 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_602])).

tff(c_897,plain,(
    ! [B_51,A_52] : k5_xboole_0(k5_xboole_0(B_51,A_52),B_51) = A_52 ),
    inference(superposition,[status(thm),theory(equality)],[c_740,c_654])).

tff(c_953,plain,(
    ! [A_15,B_16] : k5_xboole_0(k2_xboole_0(A_15,B_16),A_15) = k4_xboole_0(B_16,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_897])).

tff(c_1959,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k4_xboole_0(A_76,k3_xboole_0(A_76,B_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1953,c_953])).

tff(c_1996,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k4_xboole_0(A_76,B_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1959])).

tff(c_20,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1996,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:20:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.83/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.70  
% 3.83/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.70  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.83/1.70  
% 3.83/1.70  %Foreground sorts:
% 3.83/1.70  
% 3.83/1.70  
% 3.83/1.70  %Background operators:
% 3.83/1.70  
% 3.83/1.70  
% 3.83/1.70  %Foreground operators:
% 3.83/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.83/1.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.83/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.83/1.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.83/1.70  tff('#skF_2', type, '#skF_2': $i).
% 3.83/1.70  tff('#skF_1', type, '#skF_1': $i).
% 3.83/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.83/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.83/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.83/1.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.83/1.70  
% 3.83/1.71  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.83/1.71  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.83/1.71  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.83/1.71  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.83/1.71  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.83/1.71  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.83/1.71  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.83/1.71  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.83/1.71  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.83/1.71  tff(f_46, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.83/1.71  tff(c_6, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k3_xboole_0(A_4, B_5))=k4_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.83/1.71  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.83/1.71  tff(c_56, plain, (![B_20, A_21]: (k5_xboole_0(B_20, A_21)=k5_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.83/1.71  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.83/1.71  tff(c_72, plain, (![A_21]: (k5_xboole_0(k1_xboole_0, A_21)=A_21)), inference(superposition, [status(thm), theory('equality')], [c_56, c_10])).
% 3.83/1.71  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.83/1.71  tff(c_500, plain, (![A_40, B_41, C_42]: (k5_xboole_0(k5_xboole_0(A_40, B_41), C_42)=k5_xboole_0(A_40, k5_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.83/1.71  tff(c_588, plain, (![A_12, C_42]: (k5_xboole_0(A_12, k5_xboole_0(A_12, C_42))=k5_xboole_0(k1_xboole_0, C_42))), inference(superposition, [status(thm), theory('equality')], [c_14, c_500])).
% 3.83/1.71  tff(c_602, plain, (![A_43, C_44]: (k5_xboole_0(A_43, k5_xboole_0(A_43, C_44))=C_44)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_588])).
% 3.83/1.71  tff(c_654, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_602])).
% 3.83/1.71  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.83/1.71  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.83/1.71  tff(c_231, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k3_xboole_0(A_29, B_30))=k4_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.83/1.71  tff(c_237, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, k3_xboole_0(A_29, B_30)))), inference(superposition, [status(thm), theory('equality')], [c_231, c_8])).
% 3.83/1.71  tff(c_245, plain, (![A_29, B_30]: (k3_xboole_0(A_29, k3_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_237])).
% 3.83/1.71  tff(c_281, plain, (![A_33, B_34]: (k5_xboole_0(k5_xboole_0(A_33, B_34), k3_xboole_0(A_33, B_34))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.83/1.71  tff(c_1666, plain, (![A_68, B_69]: (k5_xboole_0(k3_xboole_0(A_68, B_69), k5_xboole_0(A_68, B_69))=k2_xboole_0(A_68, B_69))), inference(superposition, [status(thm), theory('equality')], [c_281, c_2])).
% 3.83/1.71  tff(c_1747, plain, (![A_29, B_30]: (k5_xboole_0(k3_xboole_0(A_29, B_30), k5_xboole_0(A_29, k3_xboole_0(A_29, B_30)))=k2_xboole_0(A_29, k3_xboole_0(A_29, B_30)))), inference(superposition, [status(thm), theory('equality')], [c_245, c_1666])).
% 3.83/1.71  tff(c_1776, plain, (![A_70, B_71]: (k2_xboole_0(A_70, k3_xboole_0(A_70, B_71))=A_70)), inference(demodulation, [status(thm), theory('equality')], [c_654, c_1747])).
% 3.83/1.71  tff(c_18, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.83/1.71  tff(c_644, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k4_xboole_0(B_16, A_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_602])).
% 3.83/1.71  tff(c_1791, plain, (![A_70, B_71]: (k4_xboole_0(k3_xboole_0(A_70, B_71), A_70)=k5_xboole_0(A_70, A_70))), inference(superposition, [status(thm), theory('equality')], [c_1776, c_644])).
% 3.83/1.71  tff(c_1825, plain, (![A_72, B_73]: (k4_xboole_0(k3_xboole_0(A_72, B_73), A_72)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1791])).
% 3.83/1.71  tff(c_1839, plain, (![A_72, B_73]: (k4_xboole_0(k3_xboole_0(A_72, B_73), k1_xboole_0)=k3_xboole_0(k3_xboole_0(A_72, B_73), A_72))), inference(superposition, [status(thm), theory('equality')], [c_1825, c_8])).
% 3.83/1.71  tff(c_1886, plain, (![A_74, B_75]: (k3_xboole_0(k3_xboole_0(A_74, B_75), A_74)=k3_xboole_0(A_74, B_75))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1839])).
% 3.83/1.71  tff(c_293, plain, (![A_33, B_34]: (k5_xboole_0(k3_xboole_0(A_33, B_34), k5_xboole_0(A_33, B_34))=k2_xboole_0(A_33, B_34))), inference(superposition, [status(thm), theory('equality')], [c_281, c_2])).
% 3.83/1.71  tff(c_1901, plain, (![A_74, B_75]: (k5_xboole_0(k3_xboole_0(A_74, B_75), k5_xboole_0(k3_xboole_0(A_74, B_75), A_74))=k2_xboole_0(k3_xboole_0(A_74, B_75), A_74))), inference(superposition, [status(thm), theory('equality')], [c_1886, c_293])).
% 3.83/1.71  tff(c_1953, plain, (![A_76, B_77]: (k2_xboole_0(k3_xboole_0(A_76, B_77), A_76)=A_76)), inference(demodulation, [status(thm), theory('equality')], [c_654, c_2, c_1901])).
% 3.83/1.71  tff(c_740, plain, (![A_47, B_48]: (k5_xboole_0(A_47, k5_xboole_0(B_48, A_47))=B_48)), inference(superposition, [status(thm), theory('equality')], [c_2, c_602])).
% 3.83/1.71  tff(c_897, plain, (![B_51, A_52]: (k5_xboole_0(k5_xboole_0(B_51, A_52), B_51)=A_52)), inference(superposition, [status(thm), theory('equality')], [c_740, c_654])).
% 3.83/1.71  tff(c_953, plain, (![A_15, B_16]: (k5_xboole_0(k2_xboole_0(A_15, B_16), A_15)=k4_xboole_0(B_16, A_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_897])).
% 3.83/1.71  tff(c_1959, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k4_xboole_0(A_76, k3_xboole_0(A_76, B_77)))), inference(superposition, [status(thm), theory('equality')], [c_1953, c_953])).
% 3.83/1.71  tff(c_1996, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k4_xboole_0(A_76, B_77))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1959])).
% 3.83/1.71  tff(c_20, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.83/1.71  tff(c_3370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1996, c_20])).
% 3.83/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.71  
% 3.83/1.71  Inference rules
% 3.83/1.71  ----------------------
% 3.83/1.71  #Ref     : 0
% 3.83/1.71  #Sup     : 846
% 3.83/1.71  #Fact    : 0
% 3.83/1.71  #Define  : 0
% 3.83/1.71  #Split   : 0
% 3.83/1.71  #Chain   : 0
% 3.83/1.71  #Close   : 0
% 3.83/1.71  
% 3.83/1.71  Ordering : KBO
% 3.83/1.71  
% 3.83/1.71  Simplification rules
% 3.83/1.71  ----------------------
% 3.83/1.71  #Subsume      : 37
% 3.83/1.71  #Demod        : 810
% 3.83/1.71  #Tautology    : 511
% 3.83/1.71  #SimpNegUnit  : 0
% 3.83/1.71  #BackRed      : 4
% 3.83/1.71  
% 3.83/1.71  #Partial instantiations: 0
% 3.83/1.71  #Strategies tried      : 1
% 3.83/1.71  
% 3.83/1.71  Timing (in seconds)
% 3.83/1.71  ----------------------
% 3.83/1.72  Preprocessing        : 0.26
% 3.83/1.72  Parsing              : 0.14
% 3.83/1.72  CNF conversion       : 0.02
% 3.83/1.72  Main loop            : 0.70
% 3.83/1.72  Inferencing          : 0.21
% 3.83/1.72  Reduction            : 0.35
% 3.83/1.72  Demodulation         : 0.30
% 3.83/1.72  BG Simplification    : 0.03
% 3.83/1.72  Subsumption          : 0.08
% 3.83/1.72  Abstraction          : 0.04
% 3.83/1.72  MUC search           : 0.00
% 3.83/1.72  Cooper               : 0.00
% 3.83/1.72  Total                : 0.99
% 3.83/1.72  Index Insertion      : 0.00
% 3.83/1.72  Index Deletion       : 0.00
% 3.83/1.72  Index Matching       : 0.00
% 3.83/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
