%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:28 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :   49 (  84 expanded)
%              Number of leaves         :   17 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   47 (  97 expanded)
%              Number of equality atoms :   23 (  43 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_829,plain,(
    ! [A_58,B_59] : k3_xboole_0(k3_xboole_0(A_58,B_59),A_58) = k3_xboole_0(A_58,B_59) ),
    inference(resolution,[status(thm)],[c_6,c_66])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_248,plain,(
    ! [A_35,B_36] : k5_xboole_0(A_35,k3_xboole_0(A_35,B_36)) = k4_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_266,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_248])).

tff(c_850,plain,(
    ! [A_58,B_59] : k5_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,k3_xboole_0(A_58,B_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_829,c_266])).

tff(c_955,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_850])).

tff(c_373,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_376,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,k4_xboole_0(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_12])).

tff(c_2299,plain,(
    ! [A_83,B_84] : k3_xboole_0(A_83,k4_xboole_0(A_83,B_84)) = k4_xboole_0(A_83,B_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_955,c_376])).

tff(c_2411,plain,(
    ! [A_83,B_84] : r1_tarski(k4_xboole_0(A_83,B_84),A_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_2299,c_6])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_78,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_66])).

tff(c_85,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_6])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_93,plain,(
    k3_xboole_0('#skF_1','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_85,c_10])).

tff(c_106,plain,(
    ! [A_22,B_23,C_24] :
      ( r1_tarski(A_22,B_23)
      | ~ r1_tarski(A_22,k3_xboole_0(B_23,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_130,plain,(
    ! [B_25,C_26,B_27] : r1_tarski(k3_xboole_0(k3_xboole_0(B_25,C_26),B_27),B_25) ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_196,plain,(
    ! [B_31,A_32,B_33] : r1_tarski(k3_xboole_0(k3_xboole_0(B_31,A_32),B_33),A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_130])).

tff(c_229,plain,(
    ! [B_34] : r1_tarski(k3_xboole_0('#skF_1',B_34),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_196])).

tff(c_292,plain,(
    ! [B_38] : k3_xboole_0(k3_xboole_0('#skF_1',B_38),'#skF_2') = k3_xboole_0('#skF_1',B_38) ),
    inference(resolution,[status(thm)],[c_229,c_10])).

tff(c_637,plain,(
    ! [B_55] : k3_xboole_0('#skF_2',k3_xboole_0('#skF_1',B_55)) = k3_xboole_0('#skF_1',B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_2])).

tff(c_685,plain,(
    k3_xboole_0('#skF_2','#skF_1') = k3_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_637])).

tff(c_709,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_685])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( r1_tarski(A_7,B_8)
      | ~ r1_tarski(A_7,k3_xboole_0(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_775,plain,(
    ! [A_56] :
      ( r1_tarski(A_56,'#skF_2')
      | ~ r1_tarski(A_56,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_709,c_8])).

tff(c_14,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_783,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_775,c_14])).

tff(c_2448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2411,c_783])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:53:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.60  
% 3.43/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.61  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 3.43/1.61  
% 3.43/1.61  %Foreground sorts:
% 3.43/1.61  
% 3.43/1.61  
% 3.43/1.61  %Background operators:
% 3.43/1.61  
% 3.43/1.61  
% 3.43/1.61  %Foreground operators:
% 3.43/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.43/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.43/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.43/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.43/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.43/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.43/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.43/1.61  
% 3.43/1.62  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.43/1.62  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.43/1.62  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.43/1.62  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.43/1.62  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.43/1.62  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 3.43/1.62  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.43/1.62  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.43/1.62  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.43/1.62  tff(c_66, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.43/1.62  tff(c_829, plain, (![A_58, B_59]: (k3_xboole_0(k3_xboole_0(A_58, B_59), A_58)=k3_xboole_0(A_58, B_59))), inference(resolution, [status(thm)], [c_6, c_66])).
% 3.43/1.62  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.43/1.62  tff(c_248, plain, (![A_35, B_36]: (k5_xboole_0(A_35, k3_xboole_0(A_35, B_36))=k4_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.43/1.62  tff(c_266, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_248])).
% 3.43/1.62  tff(c_850, plain, (![A_58, B_59]: (k5_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, k3_xboole_0(A_58, B_59)))), inference(superposition, [status(thm), theory('equality')], [c_829, c_266])).
% 3.43/1.62  tff(c_955, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_850])).
% 3.43/1.62  tff(c_373, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.43/1.62  tff(c_12, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.43/1.62  tff(c_376, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k3_xboole_0(A_39, B_40))=k3_xboole_0(A_39, k4_xboole_0(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_373, c_12])).
% 3.43/1.62  tff(c_2299, plain, (![A_83, B_84]: (k3_xboole_0(A_83, k4_xboole_0(A_83, B_84))=k4_xboole_0(A_83, B_84))), inference(demodulation, [status(thm), theory('equality')], [c_955, c_376])).
% 3.43/1.62  tff(c_2411, plain, (![A_83, B_84]: (r1_tarski(k4_xboole_0(A_83, B_84), A_83))), inference(superposition, [status(thm), theory('equality')], [c_2299, c_6])).
% 3.43/1.62  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.43/1.62  tff(c_78, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_16, c_66])).
% 3.43/1.62  tff(c_85, plain, (r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_78, c_6])).
% 3.43/1.62  tff(c_10, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.43/1.62  tff(c_93, plain, (k3_xboole_0('#skF_1', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_85, c_10])).
% 3.43/1.62  tff(c_106, plain, (![A_22, B_23, C_24]: (r1_tarski(A_22, B_23) | ~r1_tarski(A_22, k3_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.43/1.62  tff(c_130, plain, (![B_25, C_26, B_27]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_25, C_26), B_27), B_25))), inference(resolution, [status(thm)], [c_6, c_106])).
% 3.43/1.62  tff(c_196, plain, (![B_31, A_32, B_33]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_31, A_32), B_33), A_32))), inference(superposition, [status(thm), theory('equality')], [c_2, c_130])).
% 3.43/1.62  tff(c_229, plain, (![B_34]: (r1_tarski(k3_xboole_0('#skF_1', B_34), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_196])).
% 3.43/1.62  tff(c_292, plain, (![B_38]: (k3_xboole_0(k3_xboole_0('#skF_1', B_38), '#skF_2')=k3_xboole_0('#skF_1', B_38))), inference(resolution, [status(thm)], [c_229, c_10])).
% 3.43/1.62  tff(c_637, plain, (![B_55]: (k3_xboole_0('#skF_2', k3_xboole_0('#skF_1', B_55))=k3_xboole_0('#skF_1', B_55))), inference(superposition, [status(thm), theory('equality')], [c_292, c_2])).
% 3.43/1.62  tff(c_685, plain, (k3_xboole_0('#skF_2', '#skF_1')=k3_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_93, c_637])).
% 3.43/1.62  tff(c_709, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_685])).
% 3.43/1.62  tff(c_8, plain, (![A_7, B_8, C_9]: (r1_tarski(A_7, B_8) | ~r1_tarski(A_7, k3_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.43/1.62  tff(c_775, plain, (![A_56]: (r1_tarski(A_56, '#skF_2') | ~r1_tarski(A_56, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_709, c_8])).
% 3.43/1.62  tff(c_14, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.43/1.62  tff(c_783, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_775, c_14])).
% 3.43/1.62  tff(c_2448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2411, c_783])).
% 3.43/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.62  
% 3.43/1.62  Inference rules
% 3.43/1.62  ----------------------
% 3.43/1.62  #Ref     : 0
% 3.43/1.62  #Sup     : 603
% 3.43/1.62  #Fact    : 0
% 3.43/1.62  #Define  : 0
% 3.43/1.62  #Split   : 0
% 3.43/1.62  #Chain   : 0
% 3.43/1.62  #Close   : 0
% 3.43/1.62  
% 3.43/1.62  Ordering : KBO
% 3.43/1.62  
% 3.43/1.62  Simplification rules
% 3.43/1.62  ----------------------
% 3.43/1.62  #Subsume      : 14
% 3.43/1.62  #Demod        : 461
% 3.43/1.62  #Tautology    : 388
% 3.43/1.62  #SimpNegUnit  : 0
% 3.43/1.62  #BackRed      : 3
% 3.43/1.62  
% 3.43/1.62  #Partial instantiations: 0
% 3.43/1.62  #Strategies tried      : 1
% 3.43/1.62  
% 3.43/1.62  Timing (in seconds)
% 3.43/1.62  ----------------------
% 3.43/1.62  Preprocessing        : 0.26
% 3.43/1.62  Parsing              : 0.15
% 3.43/1.62  CNF conversion       : 0.01
% 3.43/1.62  Main loop            : 0.55
% 3.43/1.62  Inferencing          : 0.17
% 3.43/1.62  Reduction            : 0.24
% 3.43/1.62  Demodulation         : 0.20
% 3.43/1.62  BG Simplification    : 0.02
% 3.43/1.62  Subsumption          : 0.08
% 3.43/1.62  Abstraction          : 0.03
% 3.43/1.62  MUC search           : 0.00
% 3.43/1.62  Cooper               : 0.00
% 3.43/1.62  Total                : 0.83
% 3.43/1.62  Index Insertion      : 0.00
% 3.43/1.62  Index Deletion       : 0.00
% 3.43/1.62  Index Matching       : 0.00
% 3.43/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
