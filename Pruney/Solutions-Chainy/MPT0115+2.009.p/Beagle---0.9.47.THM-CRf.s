%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:26 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   50 (  77 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :   42 (  75 expanded)
%              Number of equality atoms :   22 (  44 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_53,plain,(
    ! [A_6,B_7] : k3_xboole_0(k3_xboole_0(A_6,B_7),A_6) = k3_xboole_0(A_6,B_7) ),
    inference(resolution,[status(thm)],[c_6,c_46])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_54,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_46])).

tff(c_373,plain,(
    ! [A_48,B_49,C_50] : k3_xboole_0(k3_xboole_0(A_48,B_49),C_50) = k3_xboole_0(A_48,k3_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42,plain,(
    ! [A_25,B_26] : r1_tarski(k3_xboole_0(A_25,B_26),A_25) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ! [A_29] : r1_tarski(k1_xboole_0,A_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_42])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_59,plain,(
    ! [A_29] : k3_xboole_0(k1_xboole_0,A_29) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_10])).

tff(c_98,plain,(
    ! [A_31,B_32] : k5_xboole_0(A_31,k3_xboole_0(A_31,B_32)) = k4_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_107,plain,(
    ! [A_29] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_98])).

tff(c_119,plain,(
    ! [A_29] : k4_xboole_0(k1_xboole_0,A_29) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_107])).

tff(c_151,plain,(
    ! [A_35,B_36] : k5_xboole_0(A_35,k4_xboole_0(B_36,A_35)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_160,plain,(
    ! [A_29] : k5_xboole_0(A_29,k1_xboole_0) = k2_xboole_0(A_29,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_151])).

tff(c_166,plain,(
    ! [A_29] : k2_xboole_0(A_29,k1_xboole_0) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_160])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_xboole_0(k3_xboole_0(A_8,B_9),k3_xboole_0(A_8,C_10)) = k3_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] : r1_tarski(k2_xboole_0(k3_xboole_0(A_14,B_15),k3_xboole_0(A_14,C_16)),k2_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_325,plain,(
    ! [A_43,B_44,C_45] : r1_tarski(k3_xboole_0(A_43,k2_xboole_0(B_44,C_45)),k2_xboole_0(B_44,C_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_335,plain,(
    ! [A_43,A_29] : r1_tarski(k3_xboole_0(A_43,A_29),k2_xboole_0(A_29,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_325])).

tff(c_344,plain,(
    ! [A_43,A_29] : r1_tarski(k3_xboole_0(A_43,A_29),A_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_335])).

tff(c_447,plain,(
    ! [A_51,B_52,C_53] : r1_tarski(k3_xboole_0(A_51,k3_xboole_0(B_52,C_53)),C_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_344])).

tff(c_486,plain,(
    ! [A_54] : r1_tarski(k3_xboole_0(A_54,'#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_447])).

tff(c_497,plain,(
    ! [B_7] : r1_tarski(k3_xboole_0('#skF_1',B_7),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_486])).

tff(c_22,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_556,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:45:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.31  
% 2.06/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.31  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.06/1.31  
% 2.06/1.31  %Foreground sorts:
% 2.06/1.31  
% 2.06/1.31  
% 2.06/1.31  %Background operators:
% 2.06/1.31  
% 2.06/1.31  
% 2.06/1.31  %Foreground operators:
% 2.06/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.06/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.06/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.31  
% 2.06/1.32  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.06/1.32  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.06/1.32  tff(f_52, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.06/1.32  tff(f_29, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.06/1.32  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.06/1.32  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.06/1.32  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.06/1.32  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.06/1.32  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 2.06/1.32  tff(f_41, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.06/1.32  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.32  tff(c_46, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.06/1.32  tff(c_53, plain, (![A_6, B_7]: (k3_xboole_0(k3_xboole_0(A_6, B_7), A_6)=k3_xboole_0(A_6, B_7))), inference(resolution, [status(thm)], [c_6, c_46])).
% 2.06/1.32  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.06/1.32  tff(c_54, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_24, c_46])).
% 2.06/1.32  tff(c_373, plain, (![A_48, B_49, C_50]: (k3_xboole_0(k3_xboole_0(A_48, B_49), C_50)=k3_xboole_0(A_48, k3_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.06/1.32  tff(c_18, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.06/1.32  tff(c_12, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.32  tff(c_42, plain, (![A_25, B_26]: (r1_tarski(k3_xboole_0(A_25, B_26), A_25))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.32  tff(c_55, plain, (![A_29]: (r1_tarski(k1_xboole_0, A_29))), inference(superposition, [status(thm), theory('equality')], [c_12, c_42])).
% 2.06/1.32  tff(c_10, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.06/1.32  tff(c_59, plain, (![A_29]: (k3_xboole_0(k1_xboole_0, A_29)=k1_xboole_0)), inference(resolution, [status(thm)], [c_55, c_10])).
% 2.06/1.32  tff(c_98, plain, (![A_31, B_32]: (k5_xboole_0(A_31, k3_xboole_0(A_31, B_32))=k4_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.32  tff(c_107, plain, (![A_29]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_29))), inference(superposition, [status(thm), theory('equality')], [c_59, c_98])).
% 2.06/1.32  tff(c_119, plain, (![A_29]: (k4_xboole_0(k1_xboole_0, A_29)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_107])).
% 2.06/1.32  tff(c_151, plain, (![A_35, B_36]: (k5_xboole_0(A_35, k4_xboole_0(B_36, A_35))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.06/1.32  tff(c_160, plain, (![A_29]: (k5_xboole_0(A_29, k1_xboole_0)=k2_xboole_0(A_29, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_119, c_151])).
% 2.06/1.32  tff(c_166, plain, (![A_29]: (k2_xboole_0(A_29, k1_xboole_0)=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_160])).
% 2.06/1.32  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_xboole_0(k3_xboole_0(A_8, B_9), k3_xboole_0(A_8, C_10))=k3_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.32  tff(c_14, plain, (![A_14, B_15, C_16]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_14, B_15), k3_xboole_0(A_14, C_16)), k2_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.06/1.32  tff(c_325, plain, (![A_43, B_44, C_45]: (r1_tarski(k3_xboole_0(A_43, k2_xboole_0(B_44, C_45)), k2_xboole_0(B_44, C_45)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 2.06/1.32  tff(c_335, plain, (![A_43, A_29]: (r1_tarski(k3_xboole_0(A_43, A_29), k2_xboole_0(A_29, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_166, c_325])).
% 2.06/1.32  tff(c_344, plain, (![A_43, A_29]: (r1_tarski(k3_xboole_0(A_43, A_29), A_29))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_335])).
% 2.06/1.32  tff(c_447, plain, (![A_51, B_52, C_53]: (r1_tarski(k3_xboole_0(A_51, k3_xboole_0(B_52, C_53)), C_53))), inference(superposition, [status(thm), theory('equality')], [c_373, c_344])).
% 2.06/1.32  tff(c_486, plain, (![A_54]: (r1_tarski(k3_xboole_0(A_54, '#skF_1'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_447])).
% 2.06/1.32  tff(c_497, plain, (![B_7]: (r1_tarski(k3_xboole_0('#skF_1', B_7), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_53, c_486])).
% 2.06/1.32  tff(c_22, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.06/1.32  tff(c_556, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_497, c_22])).
% 2.06/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.32  
% 2.06/1.32  Inference rules
% 2.06/1.32  ----------------------
% 2.06/1.32  #Ref     : 0
% 2.06/1.32  #Sup     : 135
% 2.06/1.32  #Fact    : 0
% 2.06/1.32  #Define  : 0
% 2.06/1.32  #Split   : 0
% 2.06/1.32  #Chain   : 0
% 2.06/1.32  #Close   : 0
% 2.06/1.32  
% 2.06/1.32  Ordering : KBO
% 2.06/1.32  
% 2.06/1.32  Simplification rules
% 2.06/1.32  ----------------------
% 2.06/1.32  #Subsume      : 0
% 2.06/1.32  #Demod        : 100
% 2.06/1.32  #Tautology    : 94
% 2.06/1.32  #SimpNegUnit  : 0
% 2.06/1.32  #BackRed      : 2
% 2.06/1.32  
% 2.06/1.32  #Partial instantiations: 0
% 2.06/1.32  #Strategies tried      : 1
% 2.06/1.32  
% 2.06/1.32  Timing (in seconds)
% 2.06/1.32  ----------------------
% 2.06/1.32  Preprocessing        : 0.28
% 2.06/1.32  Parsing              : 0.15
% 2.06/1.32  CNF conversion       : 0.02
% 2.06/1.32  Main loop            : 0.24
% 2.06/1.32  Inferencing          : 0.09
% 2.06/1.32  Reduction            : 0.09
% 2.06/1.32  Demodulation         : 0.07
% 2.35/1.32  BG Simplification    : 0.01
% 2.35/1.32  Subsumption          : 0.03
% 2.35/1.32  Abstraction          : 0.02
% 2.35/1.32  MUC search           : 0.00
% 2.35/1.32  Cooper               : 0.00
% 2.35/1.32  Total                : 0.55
% 2.35/1.32  Index Insertion      : 0.00
% 2.35/1.32  Index Deletion       : 0.00
% 2.35/1.32  Index Matching       : 0.00
% 2.35/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
