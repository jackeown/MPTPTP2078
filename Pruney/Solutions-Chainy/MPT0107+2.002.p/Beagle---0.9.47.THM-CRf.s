%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:53 EST 2020

% Result     : Theorem 5.33s
% Output     : CNFRefutation 5.33s
% Verified   : 
% Statistics : Number of formulae       :   54 (  66 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   43 (  57 expanded)
%              Number of equality atoms :   38 (  48 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_34,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_42,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_50,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_6,A_5] : k5_xboole_0(B_6,A_5) = k5_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_283,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_292,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,k4_xboole_0(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_283])).

tff(c_883,plain,(
    ! [A_59,B_60] : k3_xboole_0(A_59,k4_xboole_0(A_59,B_60)) = k4_xboole_0(A_59,B_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_292])).

tff(c_12,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_901,plain,(
    ! [A_59,B_60] : k2_xboole_0(A_59,k4_xboole_0(A_59,B_60)) = A_59 ),
    inference(superposition,[status(thm),theory(equality)],[c_883,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_41,plain,(
    ! [A_22] :
      ( k1_xboole_0 = A_22
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_45,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10,c_41])).

tff(c_18,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_53,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_1') = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_18])).

tff(c_24,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_47,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_24])).

tff(c_26,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_374,plain,(
    ! [A_44,B_45,C_46] : k5_xboole_0(k5_xboole_0(A_44,B_45),C_46) = k5_xboole_0(A_44,k5_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3077,plain,(
    ! [A_100,B_101,C_102] : k5_xboole_0(A_100,k5_xboole_0(k4_xboole_0(B_101,A_100),C_102)) = k5_xboole_0(k2_xboole_0(A_100,B_101),C_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_374])).

tff(c_3231,plain,(
    ! [A_100,B_101] : k5_xboole_0(k2_xboole_0(A_100,B_101),k4_xboole_0(B_101,A_100)) = k5_xboole_0(A_100,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_3077])).

tff(c_3768,plain,(
    ! [A_110,B_111] : k5_xboole_0(k2_xboole_0(A_110,B_111),k4_xboole_0(B_111,A_110)) = A_110 ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_3231])).

tff(c_3843,plain,(
    ! [A_11,B_12] : k5_xboole_0(k2_xboole_0(k4_xboole_0(A_11,B_12),A_11),k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3768])).

tff(c_4803,plain,(
    ! [A_121,B_122] : k5_xboole_0(A_121,k3_xboole_0(A_121,B_122)) = k4_xboole_0(A_121,B_122) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_901,c_6,c_2,c_3843])).

tff(c_4894,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = k4_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_4803])).

tff(c_28,plain,(
    k5_xboole_0('#skF_2',k3_xboole_0('#skF_2','#skF_3')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_29,plain,(
    k5_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_28])).

tff(c_6088,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4894,c_29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:05:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.33/2.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.12  
% 5.33/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.12  %$ v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.33/2.12  
% 5.33/2.12  %Foreground sorts:
% 5.33/2.12  
% 5.33/2.12  
% 5.33/2.12  %Background operators:
% 5.33/2.12  
% 5.33/2.12  
% 5.33/2.12  %Foreground operators:
% 5.33/2.12  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 5.33/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.33/2.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.33/2.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.33/2.12  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.33/2.12  tff('#skF_2', type, '#skF_2': $i).
% 5.33/2.12  tff('#skF_3', type, '#skF_3': $i).
% 5.33/2.12  tff('#skF_1', type, '#skF_1': $i).
% 5.33/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.33/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.33/2.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.33/2.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.33/2.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.33/2.12  
% 5.33/2.14  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.33/2.14  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.33/2.14  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.33/2.14  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.33/2.14  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 5.33/2.14  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.33/2.14  tff(f_34, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 5.33/2.14  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 5.33/2.14  tff(f_42, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.33/2.14  tff(f_50, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.33/2.14  tff(f_52, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.33/2.14  tff(f_48, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.33/2.14  tff(f_55, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.33/2.14  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.33/2.14  tff(c_6, plain, (![B_6, A_5]: (k5_xboole_0(B_6, A_5)=k5_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.33/2.14  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.33/2.14  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.33/2.14  tff(c_283, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.33/2.14  tff(c_292, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k3_xboole_0(A_11, k4_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_283])).
% 5.33/2.14  tff(c_883, plain, (![A_59, B_60]: (k3_xboole_0(A_59, k4_xboole_0(A_59, B_60))=k4_xboole_0(A_59, B_60))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_292])).
% 5.33/2.14  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k3_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.33/2.14  tff(c_901, plain, (![A_59, B_60]: (k2_xboole_0(A_59, k4_xboole_0(A_59, B_60))=A_59)), inference(superposition, [status(thm), theory('equality')], [c_883, c_12])).
% 5.33/2.14  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.33/2.14  tff(c_10, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.33/2.14  tff(c_41, plain, (![A_22]: (k1_xboole_0=A_22 | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.33/2.14  tff(c_45, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_10, c_41])).
% 5.33/2.14  tff(c_18, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.33/2.14  tff(c_53, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_1')=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_45, c_18])).
% 5.33/2.14  tff(c_24, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.33/2.14  tff(c_47, plain, (![A_18]: (k5_xboole_0(A_18, A_18)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_24])).
% 5.33/2.14  tff(c_26, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.33/2.14  tff(c_374, plain, (![A_44, B_45, C_46]: (k5_xboole_0(k5_xboole_0(A_44, B_45), C_46)=k5_xboole_0(A_44, k5_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.33/2.14  tff(c_3077, plain, (![A_100, B_101, C_102]: (k5_xboole_0(A_100, k5_xboole_0(k4_xboole_0(B_101, A_100), C_102))=k5_xboole_0(k2_xboole_0(A_100, B_101), C_102))), inference(superposition, [status(thm), theory('equality')], [c_26, c_374])).
% 5.33/2.14  tff(c_3231, plain, (![A_100, B_101]: (k5_xboole_0(k2_xboole_0(A_100, B_101), k4_xboole_0(B_101, A_100))=k5_xboole_0(A_100, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_47, c_3077])).
% 5.33/2.14  tff(c_3768, plain, (![A_110, B_111]: (k5_xboole_0(k2_xboole_0(A_110, B_111), k4_xboole_0(B_111, A_110))=A_110)), inference(demodulation, [status(thm), theory('equality')], [c_53, c_3231])).
% 5.33/2.14  tff(c_3843, plain, (![A_11, B_12]: (k5_xboole_0(k2_xboole_0(k4_xboole_0(A_11, B_12), A_11), k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3768])).
% 5.33/2.14  tff(c_4803, plain, (![A_121, B_122]: (k5_xboole_0(A_121, k3_xboole_0(A_121, B_122))=k4_xboole_0(A_121, B_122))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_901, c_6, c_2, c_3843])).
% 5.33/2.14  tff(c_4894, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(B_4, A_3))=k4_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_4803])).
% 5.33/2.14  tff(c_28, plain, (k5_xboole_0('#skF_2', k3_xboole_0('#skF_2', '#skF_3'))!=k4_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.33/2.14  tff(c_29, plain, (k5_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2'))!=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_28])).
% 5.33/2.14  tff(c_6088, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4894, c_29])).
% 5.33/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.14  
% 5.33/2.14  Inference rules
% 5.33/2.14  ----------------------
% 5.33/2.14  #Ref     : 0
% 5.33/2.14  #Sup     : 1517
% 5.33/2.14  #Fact    : 0
% 5.33/2.14  #Define  : 0
% 5.33/2.14  #Split   : 0
% 5.33/2.14  #Chain   : 0
% 5.33/2.14  #Close   : 0
% 5.33/2.14  
% 5.33/2.14  Ordering : KBO
% 5.33/2.14  
% 5.33/2.14  Simplification rules
% 5.33/2.14  ----------------------
% 5.33/2.14  #Subsume      : 72
% 5.33/2.14  #Demod        : 1345
% 5.33/2.14  #Tautology    : 866
% 5.33/2.14  #SimpNegUnit  : 0
% 5.33/2.14  #BackRed      : 7
% 5.33/2.14  
% 5.33/2.14  #Partial instantiations: 0
% 5.33/2.14  #Strategies tried      : 1
% 5.33/2.14  
% 5.33/2.14  Timing (in seconds)
% 5.33/2.14  ----------------------
% 5.50/2.14  Preprocessing        : 0.31
% 5.50/2.14  Parsing              : 0.16
% 5.50/2.14  CNF conversion       : 0.02
% 5.50/2.14  Main loop            : 1.01
% 5.50/2.14  Inferencing          : 0.28
% 5.50/2.14  Reduction            : 0.53
% 5.50/2.14  Demodulation         : 0.47
% 5.50/2.14  BG Simplification    : 0.04
% 5.50/2.14  Subsumption          : 0.11
% 5.50/2.14  Abstraction          : 0.05
% 5.50/2.14  MUC search           : 0.00
% 5.50/2.14  Cooper               : 0.00
% 5.50/2.14  Total                : 1.35
% 5.50/2.14  Index Insertion      : 0.00
% 5.50/2.14  Index Deletion       : 0.00
% 5.50/2.14  Index Matching       : 0.00
% 5.50/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
