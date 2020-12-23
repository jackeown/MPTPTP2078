%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:53 EST 2020

% Result     : Theorem 5.50s
% Output     : CNFRefutation 5.50s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 164 expanded)
%              Number of leaves         :   24 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :   48 ( 151 expanded)
%              Number of equality atoms :   47 ( 150 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_84,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_100,plain,(
    ! [A_31] : k2_xboole_0(k1_xboole_0,A_31) = A_31 ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_26])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    ! [A_23,B_24] : k2_xboole_0(k3_xboole_0(A_23,B_24),k4_xboole_0(A_23,B_24)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_214,plain,(
    ! [A_40,B_41] : k2_xboole_0(A_40,k4_xboole_0(B_41,A_40)) = k2_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_221,plain,(
    ! [B_41] : k4_xboole_0(B_41,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_100])).

tff(c_236,plain,(
    ! [B_41] : k4_xboole_0(B_41,k1_xboole_0) = B_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_221])).

tff(c_262,plain,(
    ! [A_45,B_46] : k5_xboole_0(A_45,k4_xboole_0(B_46,A_45)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_271,plain,(
    ! [B_41] : k5_xboole_0(k1_xboole_0,B_41) = k2_xboole_0(k1_xboole_0,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_262])).

tff(c_280,plain,(
    ! [B_41] : k5_xboole_0(k1_xboole_0,B_41) = B_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_271])).

tff(c_461,plain,(
    ! [A_56,B_57] : k2_xboole_0(k4_xboole_0(A_56,B_57),k4_xboole_0(B_57,A_56)) = k5_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_485,plain,(
    ! [B_41] : k2_xboole_0(k4_xboole_0(k1_xboole_0,B_41),B_41) = k5_xboole_0(k1_xboole_0,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_461])).

tff(c_529,plain,(
    ! [B_59] : k2_xboole_0(k4_xboole_0(k1_xboole_0,B_59),B_59) = B_59 ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_485])).

tff(c_557,plain,(
    ! [B_22] : k2_xboole_0(k3_xboole_0(k1_xboole_0,B_22),k4_xboole_0(k1_xboole_0,B_22)) = k4_xboole_0(k1_xboole_0,B_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_529])).

tff(c_579,plain,(
    ! [B_22] : k4_xboole_0(k1_xboole_0,B_22) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_557])).

tff(c_583,plain,(
    ! [B_60] : k4_xboole_0(k1_xboole_0,B_60) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_557])).

tff(c_757,plain,(
    ! [B_64] : k3_xboole_0(k1_xboole_0,B_64) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_583,c_34])).

tff(c_776,plain,(
    ! [B_64] : k3_xboole_0(B_64,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_757,c_4])).

tff(c_241,plain,(
    ! [B_42] : k4_xboole_0(B_42,k1_xboole_0) = B_42 ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_221])).

tff(c_253,plain,(
    ! [B_42] : k4_xboole_0(B_42,B_42) = k3_xboole_0(B_42,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_34])).

tff(c_870,plain,(
    ! [B_69] : k4_xboole_0(B_69,B_69) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_253])).

tff(c_30,plain,(
    ! [A_16,B_17,C_18] : k4_xboole_0(k4_xboole_0(A_16,B_17),C_18) = k4_xboole_0(A_16,k2_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_878,plain,(
    ! [B_69,C_18] : k4_xboole_0(B_69,k2_xboole_0(B_69,C_18)) = k4_xboole_0(k1_xboole_0,C_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_870,c_30])).

tff(c_1222,plain,(
    ! [B_92,C_93] : k4_xboole_0(B_92,k2_xboole_0(B_92,C_93)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_878])).

tff(c_1427,plain,(
    ! [A_99,B_100] : k4_xboole_0(k3_xboole_0(A_99,B_100),A_99) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1222])).

tff(c_1484,plain,(
    ! [B_4,A_3] : k4_xboole_0(k3_xboole_0(B_4,A_3),A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1427])).

tff(c_169,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k3_xboole_0(A_33,B_34)) = k4_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_178,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = k4_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_169])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2658,plain,(
    ! [B_131,A_132] : k2_xboole_0(k4_xboole_0(B_131,A_132),k4_xboole_0(A_132,B_131)) = k5_xboole_0(A_132,B_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_461])).

tff(c_2695,plain,(
    ! [B_4,A_3] : k2_xboole_0(k4_xboole_0(k3_xboole_0(B_4,A_3),A_3),k4_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,k3_xboole_0(B_4,A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_2658])).

tff(c_2781,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = k4_xboole_0(A_3,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1484,c_2695])).

tff(c_40,plain,(
    k5_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_4')) != k4_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_41,plain,(
    k5_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_3')) != k4_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_40])).

tff(c_8482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2781,c_41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.50/2.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.50/2.26  
% 5.50/2.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.50/2.26  %$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 5.50/2.26  
% 5.50/2.26  %Foreground sorts:
% 5.50/2.26  
% 5.50/2.26  
% 5.50/2.26  %Background operators:
% 5.50/2.26  
% 5.50/2.26  
% 5.50/2.26  %Foreground operators:
% 5.50/2.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.50/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.50/2.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.50/2.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.50/2.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.50/2.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.50/2.26  tff('#skF_3', type, '#skF_3': $i).
% 5.50/2.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.50/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.50/2.26  tff('#skF_4', type, '#skF_4': $i).
% 5.50/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.50/2.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.50/2.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.50/2.26  
% 5.50/2.28  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.50/2.28  tff(f_43, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.50/2.28  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.50/2.28  tff(f_53, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.50/2.28  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.50/2.28  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.50/2.28  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.50/2.28  tff(f_41, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 5.50/2.28  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.50/2.28  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.50/2.28  tff(f_58, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.50/2.28  tff(c_84, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.50/2.28  tff(c_26, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.50/2.28  tff(c_100, plain, (![A_31]: (k2_xboole_0(k1_xboole_0, A_31)=A_31)), inference(superposition, [status(thm), theory('equality')], [c_84, c_26])).
% 5.50/2.28  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.50/2.28  tff(c_36, plain, (![A_23, B_24]: (k2_xboole_0(k3_xboole_0(A_23, B_24), k4_xboole_0(A_23, B_24))=A_23)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.50/2.28  tff(c_34, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.50/2.28  tff(c_214, plain, (![A_40, B_41]: (k2_xboole_0(A_40, k4_xboole_0(B_41, A_40))=k2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.50/2.28  tff(c_221, plain, (![B_41]: (k4_xboole_0(B_41, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_41))), inference(superposition, [status(thm), theory('equality')], [c_214, c_100])).
% 5.50/2.28  tff(c_236, plain, (![B_41]: (k4_xboole_0(B_41, k1_xboole_0)=B_41)), inference(demodulation, [status(thm), theory('equality')], [c_100, c_221])).
% 5.50/2.28  tff(c_262, plain, (![A_45, B_46]: (k5_xboole_0(A_45, k4_xboole_0(B_46, A_45))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.50/2.28  tff(c_271, plain, (![B_41]: (k5_xboole_0(k1_xboole_0, B_41)=k2_xboole_0(k1_xboole_0, B_41))), inference(superposition, [status(thm), theory('equality')], [c_236, c_262])).
% 5.50/2.28  tff(c_280, plain, (![B_41]: (k5_xboole_0(k1_xboole_0, B_41)=B_41)), inference(demodulation, [status(thm), theory('equality')], [c_100, c_271])).
% 5.50/2.28  tff(c_461, plain, (![A_56, B_57]: (k2_xboole_0(k4_xboole_0(A_56, B_57), k4_xboole_0(B_57, A_56))=k5_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.50/2.28  tff(c_485, plain, (![B_41]: (k2_xboole_0(k4_xboole_0(k1_xboole_0, B_41), B_41)=k5_xboole_0(k1_xboole_0, B_41))), inference(superposition, [status(thm), theory('equality')], [c_236, c_461])).
% 5.50/2.28  tff(c_529, plain, (![B_59]: (k2_xboole_0(k4_xboole_0(k1_xboole_0, B_59), B_59)=B_59)), inference(demodulation, [status(thm), theory('equality')], [c_280, c_485])).
% 5.50/2.28  tff(c_557, plain, (![B_22]: (k2_xboole_0(k3_xboole_0(k1_xboole_0, B_22), k4_xboole_0(k1_xboole_0, B_22))=k4_xboole_0(k1_xboole_0, B_22))), inference(superposition, [status(thm), theory('equality')], [c_34, c_529])).
% 5.50/2.28  tff(c_579, plain, (![B_22]: (k4_xboole_0(k1_xboole_0, B_22)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_557])).
% 5.50/2.28  tff(c_583, plain, (![B_60]: (k4_xboole_0(k1_xboole_0, B_60)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_557])).
% 5.50/2.28  tff(c_757, plain, (![B_64]: (k3_xboole_0(k1_xboole_0, B_64)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_583, c_34])).
% 5.50/2.28  tff(c_776, plain, (![B_64]: (k3_xboole_0(B_64, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_757, c_4])).
% 5.50/2.28  tff(c_241, plain, (![B_42]: (k4_xboole_0(B_42, k1_xboole_0)=B_42)), inference(demodulation, [status(thm), theory('equality')], [c_100, c_221])).
% 5.50/2.28  tff(c_253, plain, (![B_42]: (k4_xboole_0(B_42, B_42)=k3_xboole_0(B_42, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_241, c_34])).
% 5.50/2.28  tff(c_870, plain, (![B_69]: (k4_xboole_0(B_69, B_69)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_776, c_253])).
% 5.50/2.28  tff(c_30, plain, (![A_16, B_17, C_18]: (k4_xboole_0(k4_xboole_0(A_16, B_17), C_18)=k4_xboole_0(A_16, k2_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.50/2.28  tff(c_878, plain, (![B_69, C_18]: (k4_xboole_0(B_69, k2_xboole_0(B_69, C_18))=k4_xboole_0(k1_xboole_0, C_18))), inference(superposition, [status(thm), theory('equality')], [c_870, c_30])).
% 5.50/2.28  tff(c_1222, plain, (![B_92, C_93]: (k4_xboole_0(B_92, k2_xboole_0(B_92, C_93))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_579, c_878])).
% 5.50/2.28  tff(c_1427, plain, (![A_99, B_100]: (k4_xboole_0(k3_xboole_0(A_99, B_100), A_99)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_1222])).
% 5.50/2.28  tff(c_1484, plain, (![B_4, A_3]: (k4_xboole_0(k3_xboole_0(B_4, A_3), A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1427])).
% 5.50/2.28  tff(c_169, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k3_xboole_0(A_33, B_34))=k4_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.50/2.28  tff(c_178, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k3_xboole_0(B_4, A_3))=k4_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_169])).
% 5.50/2.28  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.50/2.28  tff(c_2658, plain, (![B_131, A_132]: (k2_xboole_0(k4_xboole_0(B_131, A_132), k4_xboole_0(A_132, B_131))=k5_xboole_0(A_132, B_131))), inference(superposition, [status(thm), theory('equality')], [c_2, c_461])).
% 5.50/2.28  tff(c_2695, plain, (![B_4, A_3]: (k2_xboole_0(k4_xboole_0(k3_xboole_0(B_4, A_3), A_3), k4_xboole_0(A_3, B_4))=k5_xboole_0(A_3, k3_xboole_0(B_4, A_3)))), inference(superposition, [status(thm), theory('equality')], [c_178, c_2658])).
% 5.50/2.28  tff(c_2781, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(B_4, A_3))=k4_xboole_0(A_3, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1484, c_2695])).
% 5.50/2.28  tff(c_40, plain, (k5_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_4'))!=k4_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.50/2.28  tff(c_41, plain, (k5_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_3'))!=k4_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_40])).
% 5.50/2.28  tff(c_8482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2781, c_41])).
% 5.50/2.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.50/2.28  
% 5.50/2.28  Inference rules
% 5.50/2.28  ----------------------
% 5.50/2.28  #Ref     : 0
% 5.50/2.28  #Sup     : 2112
% 5.50/2.28  #Fact    : 0
% 5.50/2.28  #Define  : 0
% 5.50/2.28  #Split   : 0
% 5.50/2.28  #Chain   : 0
% 5.50/2.28  #Close   : 0
% 5.50/2.28  
% 5.50/2.28  Ordering : KBO
% 5.50/2.28  
% 5.50/2.28  Simplification rules
% 5.50/2.28  ----------------------
% 5.50/2.28  #Subsume      : 116
% 5.50/2.28  #Demod        : 1995
% 5.50/2.28  #Tautology    : 1387
% 5.50/2.28  #SimpNegUnit  : 0
% 5.50/2.28  #BackRed      : 6
% 5.50/2.28  
% 5.50/2.28  #Partial instantiations: 0
% 5.50/2.28  #Strategies tried      : 1
% 5.50/2.28  
% 5.50/2.28  Timing (in seconds)
% 5.50/2.28  ----------------------
% 5.50/2.28  Preprocessing        : 0.31
% 5.50/2.28  Parsing              : 0.17
% 5.50/2.28  CNF conversion       : 0.02
% 5.50/2.28  Main loop            : 1.12
% 5.50/2.28  Inferencing          : 0.31
% 5.50/2.28  Reduction            : 0.54
% 5.50/2.28  Demodulation         : 0.46
% 5.50/2.28  BG Simplification    : 0.04
% 5.50/2.28  Subsumption          : 0.16
% 5.50/2.28  Abstraction          : 0.05
% 5.50/2.28  MUC search           : 0.00
% 5.50/2.28  Cooper               : 0.00
% 5.50/2.28  Total                : 1.46
% 5.50/2.28  Index Insertion      : 0.00
% 5.50/2.28  Index Deletion       : 0.00
% 5.50/2.28  Index Matching       : 0.00
% 5.50/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
