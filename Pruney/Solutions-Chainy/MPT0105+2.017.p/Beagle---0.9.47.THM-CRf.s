%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:49 EST 2020

% Result     : Theorem 4.81s
% Output     : CNFRefutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :   40 (  49 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   30 (  39 expanded)
%              Number of equality atoms :   29 (  38 expanded)
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

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_93,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_108,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,k3_xboole_0(A_5,B_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_93])).

tff(c_113,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_108])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k5_xboole_0(k5_xboole_0(A_10,B_11),C_12) = k5_xboole_0(A_10,k5_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_439,plain,(
    ! [A_38,B_39] : k5_xboole_0(k5_xboole_0(A_38,B_39),k3_xboole_0(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1673,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k5_xboole_0(B_66,k3_xboole_0(A_65,B_66))) = k2_xboole_0(A_65,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_439])).

tff(c_1737,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k5_xboole_0(k3_xboole_0(A_5,B_6),k3_xboole_0(A_5,B_6))) = k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_1673])).

tff(c_1765,plain,(
    ! [A_67,B_68] : k2_xboole_0(A_67,k3_xboole_0(A_67,B_68)) = A_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14,c_1737])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(k2_xboole_0(A_3,B_4),k3_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1771,plain,(
    ! [A_67,B_68] : k4_xboole_0(A_67,k3_xboole_0(A_67,k3_xboole_0(A_67,B_68))) = k5_xboole_0(A_67,k3_xboole_0(A_67,B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1765,c_4])).

tff(c_1794,plain,(
    ! [A_67,B_68] : k5_xboole_0(A_67,k3_xboole_0(A_67,B_68)) = k4_xboole_0(A_67,B_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_1771])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1919,plain,(
    ! [B_74,A_75] : k5_xboole_0(k5_xboole_0(B_74,A_75),k3_xboole_0(A_75,B_74)) = k2_xboole_0(B_74,A_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_439])).

tff(c_2021,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k5_xboole_0(B_11,k3_xboole_0(B_11,A_10))) = k2_xboole_0(A_10,B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1919])).

tff(c_5014,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1794,c_2021])).

tff(c_18,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_5017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5014,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:18:10 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.81/1.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.95  
% 4.81/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.95  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 4.81/1.95  
% 4.81/1.95  %Foreground sorts:
% 4.81/1.95  
% 4.81/1.95  
% 4.81/1.95  %Background operators:
% 4.81/1.95  
% 4.81/1.95  
% 4.81/1.95  %Foreground operators:
% 4.81/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.81/1.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.81/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.81/1.95  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.81/1.95  tff('#skF_2', type, '#skF_2': $i).
% 4.81/1.95  tff('#skF_1', type, '#skF_1': $i).
% 4.81/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.81/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.81/1.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.81/1.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.81/1.95  
% 4.81/1.96  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.81/1.96  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.81/1.96  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.81/1.96  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.81/1.96  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.81/1.96  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.81/1.96  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 4.81/1.96  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.81/1.96  tff(f_44, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.81/1.96  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.81/1.96  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.81/1.96  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.81/1.96  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.81/1.96  tff(c_93, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.81/1.96  tff(c_108, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, k3_xboole_0(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_93])).
% 4.81/1.96  tff(c_113, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_108])).
% 4.81/1.96  tff(c_12, plain, (![A_10, B_11, C_12]: (k5_xboole_0(k5_xboole_0(A_10, B_11), C_12)=k5_xboole_0(A_10, k5_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.81/1.96  tff(c_439, plain, (![A_38, B_39]: (k5_xboole_0(k5_xboole_0(A_38, B_39), k3_xboole_0(A_38, B_39))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.81/1.96  tff(c_1673, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k5_xboole_0(B_66, k3_xboole_0(A_65, B_66)))=k2_xboole_0(A_65, B_66))), inference(superposition, [status(thm), theory('equality')], [c_12, c_439])).
% 4.81/1.96  tff(c_1737, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k5_xboole_0(k3_xboole_0(A_5, B_6), k3_xboole_0(A_5, B_6)))=k2_xboole_0(A_5, k3_xboole_0(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_1673])).
% 4.81/1.96  tff(c_1765, plain, (![A_67, B_68]: (k2_xboole_0(A_67, k3_xboole_0(A_67, B_68))=A_67)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14, c_1737])).
% 4.81/1.96  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(k2_xboole_0(A_3, B_4), k3_xboole_0(A_3, B_4))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.81/1.96  tff(c_1771, plain, (![A_67, B_68]: (k4_xboole_0(A_67, k3_xboole_0(A_67, k3_xboole_0(A_67, B_68)))=k5_xboole_0(A_67, k3_xboole_0(A_67, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_1765, c_4])).
% 4.81/1.96  tff(c_1794, plain, (![A_67, B_68]: (k5_xboole_0(A_67, k3_xboole_0(A_67, B_68))=k4_xboole_0(A_67, B_68))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_1771])).
% 4.81/1.96  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.81/1.96  tff(c_1919, plain, (![B_74, A_75]: (k5_xboole_0(k5_xboole_0(B_74, A_75), k3_xboole_0(A_75, B_74))=k2_xboole_0(B_74, A_75))), inference(superposition, [status(thm), theory('equality')], [c_2, c_439])).
% 4.81/1.96  tff(c_2021, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k5_xboole_0(B_11, k3_xboole_0(B_11, A_10)))=k2_xboole_0(A_10, B_11))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1919])).
% 4.81/1.96  tff(c_5014, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_1794, c_2021])).
% 4.81/1.96  tff(c_18, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.81/1.96  tff(c_5017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5014, c_18])).
% 4.81/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.96  
% 4.81/1.96  Inference rules
% 4.81/1.96  ----------------------
% 4.81/1.96  #Ref     : 0
% 4.81/1.96  #Sup     : 1208
% 4.81/1.96  #Fact    : 0
% 4.81/1.96  #Define  : 0
% 4.81/1.96  #Split   : 0
% 4.81/1.96  #Chain   : 0
% 4.81/1.96  #Close   : 0
% 4.81/1.96  
% 4.81/1.96  Ordering : KBO
% 4.81/1.96  
% 4.81/1.96  Simplification rules
% 4.81/1.96  ----------------------
% 4.81/1.96  #Subsume      : 23
% 4.81/1.96  #Demod        : 1423
% 4.81/1.96  #Tautology    : 691
% 4.81/1.96  #SimpNegUnit  : 0
% 4.81/1.96  #BackRed      : 24
% 4.81/1.96  
% 4.81/1.96  #Partial instantiations: 0
% 4.81/1.96  #Strategies tried      : 1
% 4.81/1.96  
% 4.81/1.96  Timing (in seconds)
% 4.81/1.96  ----------------------
% 4.81/1.96  Preprocessing        : 0.27
% 4.81/1.96  Parsing              : 0.15
% 4.81/1.96  CNF conversion       : 0.01
% 4.81/1.96  Main loop            : 0.91
% 4.81/1.96  Inferencing          : 0.28
% 4.81/1.96  Reduction            : 0.43
% 4.81/1.96  Demodulation         : 0.37
% 4.81/1.96  BG Simplification    : 0.03
% 4.81/1.96  Subsumption          : 0.11
% 4.81/1.96  Abstraction          : 0.05
% 4.81/1.96  MUC search           : 0.00
% 4.81/1.96  Cooper               : 0.00
% 4.81/1.96  Total                : 1.20
% 4.81/1.96  Index Insertion      : 0.00
% 4.81/1.96  Index Deletion       : 0.00
% 4.81/1.96  Index Matching       : 0.00
% 4.81/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
