%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:49 EST 2020

% Result     : Theorem 8.68s
% Output     : CNFRefutation 8.72s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 119 expanded)
%              Number of leaves         :   23 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :   54 ( 113 expanded)
%              Number of equality atoms :   49 ( 108 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_100,plain,(
    ! [A_40,B_41] : k4_xboole_0(A_40,k4_xboole_0(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_118,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_100])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_115,plain,(
    ! [A_13,B_14] : k3_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_100])).

tff(c_121,plain,(
    ! [A_13,B_14] : k3_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_115])).

tff(c_156,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k3_xboole_0(A_45,B_46)) = k4_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_171,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_156])).

tff(c_182,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_16,c_171])).

tff(c_184,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_118])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [A_36,B_37] :
      ( k2_xboole_0(A_36,B_37) = B_37
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1161,plain,(
    ! [A_79,B_80] :
      ( k2_xboole_0(A_79,B_80) = B_80
      | k4_xboole_0(A_79,B_80) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_90])).

tff(c_1199,plain,(
    ! [A_81] : k2_xboole_0(A_81,A_81) = A_81 ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_1161])).

tff(c_8,plain,(
    ! [A_5,B_6] : k4_xboole_0(k2_xboole_0(A_5,B_6),k3_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1209,plain,(
    ! [A_81] : k4_xboole_0(A_81,k3_xboole_0(A_81,A_81)) = k5_xboole_0(A_81,A_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_1199,c_8])).

tff(c_1229,plain,(
    ! [A_81] : k5_xboole_0(A_81,A_81) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_18,c_1209])).

tff(c_20,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_162,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,k3_xboole_0(A_45,B_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_20])).

tff(c_179,plain,(
    ! [A_45,B_46] : k3_xboole_0(A_45,k3_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_162])).

tff(c_341,plain,(
    ! [A_54,B_55] : k5_xboole_0(k5_xboole_0(A_54,B_55),k3_xboole_0(A_54,B_55)) = k2_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_23,B_24,C_25] : k5_xboole_0(k5_xboole_0(A_23,B_24),C_25) = k5_xboole_0(A_23,k5_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1456,plain,(
    ! [A_87,B_88] : k5_xboole_0(A_87,k5_xboole_0(B_88,k3_xboole_0(A_87,B_88))) = k2_xboole_0(A_87,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_26])).

tff(c_1493,plain,(
    ! [A_45,B_46] : k5_xboole_0(A_45,k5_xboole_0(k3_xboole_0(A_45,B_46),k3_xboole_0(A_45,B_46))) = k2_xboole_0(A_45,k3_xboole_0(A_45,B_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_1456])).

tff(c_1534,plain,(
    ! [A_89,B_90] : k2_xboole_0(A_89,k3_xboole_0(A_89,B_90)) = A_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1229,c_1493])).

tff(c_1584,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1534])).

tff(c_535,plain,(
    ! [A_61,B_62] : k3_xboole_0(A_61,k3_xboole_0(A_61,B_62)) = k3_xboole_0(A_61,B_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_162])).

tff(c_1678,plain,(
    ! [B_93,A_94] : k3_xboole_0(B_93,k3_xboole_0(A_94,B_93)) = k3_xboole_0(B_93,A_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_535])).

tff(c_1709,plain,(
    ! [B_93,A_94] : k4_xboole_0(k2_xboole_0(B_93,k3_xboole_0(A_94,B_93)),k3_xboole_0(B_93,A_94)) = k5_xboole_0(B_93,k3_xboole_0(A_94,B_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1678,c_8])).

tff(c_1769,plain,(
    ! [B_93,A_94] : k5_xboole_0(B_93,k3_xboole_0(A_94,B_93)) = k4_xboole_0(B_93,A_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1584,c_1709])).

tff(c_353,plain,(
    ! [A_54,B_55] : k5_xboole_0(A_54,k5_xboole_0(B_55,k3_xboole_0(A_54,B_55))) = k2_xboole_0(A_54,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_26])).

tff(c_15087,plain,(
    ! [A_54,B_55] : k5_xboole_0(A_54,k4_xboole_0(B_55,A_54)) = k2_xboole_0(A_54,B_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1769,c_353])).

tff(c_30,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22698,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15087,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:11:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.68/3.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.72/3.43  
% 8.72/3.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.72/3.43  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 8.72/3.43  
% 8.72/3.43  %Foreground sorts:
% 8.72/3.43  
% 8.72/3.43  
% 8.72/3.43  %Background operators:
% 8.72/3.43  
% 8.72/3.43  
% 8.72/3.43  %Foreground operators:
% 8.72/3.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.72/3.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.72/3.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.72/3.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.72/3.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.72/3.43  tff('#skF_2', type, '#skF_2': $i).
% 8.72/3.43  tff('#skF_1', type, '#skF_1': $i).
% 8.72/3.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.72/3.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.72/3.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.72/3.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.72/3.43  
% 8.72/3.45  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.72/3.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.72/3.45  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 8.72/3.45  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.72/3.45  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.72/3.45  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 8.72/3.45  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.72/3.45  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.72/3.45  tff(f_33, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 8.72/3.45  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 8.72/3.45  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.72/3.45  tff(f_58, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.72/3.45  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.72/3.45  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.72/3.45  tff(c_24, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.72/3.45  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.72/3.45  tff(c_100, plain, (![A_40, B_41]: (k4_xboole_0(A_40, k4_xboole_0(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.72/3.45  tff(c_118, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_100])).
% 8.72/3.45  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.72/3.45  tff(c_115, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k4_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_100])).
% 8.72/3.45  tff(c_121, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k2_xboole_0(A_13, B_14))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_115])).
% 8.72/3.45  tff(c_156, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k3_xboole_0(A_45, B_46))=k4_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.72/3.45  tff(c_171, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k4_xboole_0(A_13, A_13))), inference(superposition, [status(thm), theory('equality')], [c_121, c_156])).
% 8.72/3.45  tff(c_182, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_118, c_16, c_171])).
% 8.72/3.45  tff(c_184, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_182, c_118])).
% 8.72/3.45  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.72/3.45  tff(c_90, plain, (![A_36, B_37]: (k2_xboole_0(A_36, B_37)=B_37 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.72/3.45  tff(c_1161, plain, (![A_79, B_80]: (k2_xboole_0(A_79, B_80)=B_80 | k4_xboole_0(A_79, B_80)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_90])).
% 8.72/3.45  tff(c_1199, plain, (![A_81]: (k2_xboole_0(A_81, A_81)=A_81)), inference(superposition, [status(thm), theory('equality')], [c_184, c_1161])).
% 8.72/3.45  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(k2_xboole_0(A_5, B_6), k3_xboole_0(A_5, B_6))=k5_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.72/3.45  tff(c_1209, plain, (![A_81]: (k4_xboole_0(A_81, k3_xboole_0(A_81, A_81))=k5_xboole_0(A_81, A_81))), inference(superposition, [status(thm), theory('equality')], [c_1199, c_8])).
% 8.72/3.45  tff(c_1229, plain, (![A_81]: (k5_xboole_0(A_81, A_81)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_184, c_18, c_1209])).
% 8.72/3.45  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.72/3.45  tff(c_162, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, k3_xboole_0(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_156, c_20])).
% 8.72/3.45  tff(c_179, plain, (![A_45, B_46]: (k3_xboole_0(A_45, k3_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_162])).
% 8.72/3.45  tff(c_341, plain, (![A_54, B_55]: (k5_xboole_0(k5_xboole_0(A_54, B_55), k3_xboole_0(A_54, B_55))=k2_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.72/3.45  tff(c_26, plain, (![A_23, B_24, C_25]: (k5_xboole_0(k5_xboole_0(A_23, B_24), C_25)=k5_xboole_0(A_23, k5_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.72/3.45  tff(c_1456, plain, (![A_87, B_88]: (k5_xboole_0(A_87, k5_xboole_0(B_88, k3_xboole_0(A_87, B_88)))=k2_xboole_0(A_87, B_88))), inference(superposition, [status(thm), theory('equality')], [c_341, c_26])).
% 8.72/3.45  tff(c_1493, plain, (![A_45, B_46]: (k5_xboole_0(A_45, k5_xboole_0(k3_xboole_0(A_45, B_46), k3_xboole_0(A_45, B_46)))=k2_xboole_0(A_45, k3_xboole_0(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_179, c_1456])).
% 8.72/3.45  tff(c_1534, plain, (![A_89, B_90]: (k2_xboole_0(A_89, k3_xboole_0(A_89, B_90))=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1229, c_1493])).
% 8.72/3.45  tff(c_1584, plain, (![B_2, A_1]: (k2_xboole_0(B_2, k3_xboole_0(A_1, B_2))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1534])).
% 8.72/3.45  tff(c_535, plain, (![A_61, B_62]: (k3_xboole_0(A_61, k3_xboole_0(A_61, B_62))=k3_xboole_0(A_61, B_62))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_162])).
% 8.72/3.45  tff(c_1678, plain, (![B_93, A_94]: (k3_xboole_0(B_93, k3_xboole_0(A_94, B_93))=k3_xboole_0(B_93, A_94))), inference(superposition, [status(thm), theory('equality')], [c_2, c_535])).
% 8.72/3.45  tff(c_1709, plain, (![B_93, A_94]: (k4_xboole_0(k2_xboole_0(B_93, k3_xboole_0(A_94, B_93)), k3_xboole_0(B_93, A_94))=k5_xboole_0(B_93, k3_xboole_0(A_94, B_93)))), inference(superposition, [status(thm), theory('equality')], [c_1678, c_8])).
% 8.72/3.45  tff(c_1769, plain, (![B_93, A_94]: (k5_xboole_0(B_93, k3_xboole_0(A_94, B_93))=k4_xboole_0(B_93, A_94))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1584, c_1709])).
% 8.72/3.45  tff(c_353, plain, (![A_54, B_55]: (k5_xboole_0(A_54, k5_xboole_0(B_55, k3_xboole_0(A_54, B_55)))=k2_xboole_0(A_54, B_55))), inference(superposition, [status(thm), theory('equality')], [c_341, c_26])).
% 8.72/3.45  tff(c_15087, plain, (![A_54, B_55]: (k5_xboole_0(A_54, k4_xboole_0(B_55, A_54))=k2_xboole_0(A_54, B_55))), inference(demodulation, [status(thm), theory('equality')], [c_1769, c_353])).
% 8.72/3.45  tff(c_30, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.72/3.45  tff(c_22698, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15087, c_30])).
% 8.72/3.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.72/3.45  
% 8.72/3.45  Inference rules
% 8.72/3.45  ----------------------
% 8.72/3.45  #Ref     : 0
% 8.72/3.45  #Sup     : 5705
% 8.72/3.45  #Fact    : 0
% 8.72/3.45  #Define  : 0
% 8.72/3.45  #Split   : 0
% 8.72/3.45  #Chain   : 0
% 8.72/3.45  #Close   : 0
% 8.72/3.45  
% 8.72/3.45  Ordering : KBO
% 8.72/3.45  
% 8.72/3.45  Simplification rules
% 8.72/3.45  ----------------------
% 8.72/3.45  #Subsume      : 7
% 8.72/3.45  #Demod        : 6054
% 8.79/3.45  #Tautology    : 3857
% 8.79/3.45  #SimpNegUnit  : 0
% 8.79/3.45  #BackRed      : 8
% 8.79/3.45  
% 8.79/3.45  #Partial instantiations: 0
% 8.79/3.45  #Strategies tried      : 1
% 8.79/3.45  
% 8.79/3.45  Timing (in seconds)
% 8.79/3.45  ----------------------
% 8.79/3.45  Preprocessing        : 0.30
% 8.79/3.45  Parsing              : 0.17
% 8.79/3.45  CNF conversion       : 0.02
% 8.79/3.45  Main loop            : 2.32
% 8.79/3.45  Inferencing          : 0.52
% 8.79/3.45  Reduction            : 1.29
% 8.79/3.45  Demodulation         : 1.15
% 8.79/3.45  BG Simplification    : 0.07
% 8.79/3.45  Subsumption          : 0.33
% 8.79/3.45  Abstraction          : 0.11
% 8.79/3.45  MUC search           : 0.00
% 8.79/3.45  Cooper               : 0.00
% 8.79/3.45  Total                : 2.65
% 8.79/3.45  Index Insertion      : 0.00
% 8.79/3.45  Index Deletion       : 0.00
% 8.79/3.45  Index Matching       : 0.00
% 8.79/3.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
