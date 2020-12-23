%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:29 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 143 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :   50 ( 167 expanded)
%              Number of equality atoms :   36 ( 104 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B) )
       => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(k5_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,k2_xboole_0(B,C)),k4_xboole_0(B,k2_xboole_0(A,C))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_xboole_1)).

tff(c_185,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | k4_xboole_0(A_32,B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_197,plain,(
    k4_xboole_0(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_185,c_24])).

tff(c_14,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_105,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_115,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_105])).

tff(c_234,plain,(
    ! [A_35,B_36] : k5_xboole_0(A_35,k4_xboole_0(B_36,A_35)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_249,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k2_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_234])).

tff(c_16,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_143,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = A_29
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_156,plain,(
    ! [A_31] : k3_xboole_0(k1_xboole_0,A_31) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_143])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_161,plain,(
    ! [A_31] : k3_xboole_0(A_31,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_4])).

tff(c_303,plain,(
    ! [A_39,B_40] : k5_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = k4_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_320,plain,(
    ! [A_31] : k5_xboole_0(A_31,k1_xboole_0) = k4_xboole_0(A_31,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_303])).

tff(c_340,plain,(
    ! [A_31] : k2_xboole_0(A_31,k1_xboole_0) = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_16,c_320])).

tff(c_28,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_117,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_105])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_116,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_105])).

tff(c_359,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_249])).

tff(c_246,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_234])).

tff(c_256,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_246])).

tff(c_585,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_256])).

tff(c_243,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_234])).

tff(c_255,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_243])).

tff(c_383,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_255])).

tff(c_661,plain,(
    ! [A_51,B_52,C_53] : k2_xboole_0(k4_xboole_0(A_51,k2_xboole_0(B_52,C_53)),k4_xboole_0(B_52,k2_xboole_0(A_51,C_53))) = k4_xboole_0(k5_xboole_0(A_51,B_52),C_53) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1271,plain,(
    ! [B_65] : k2_xboole_0(k4_xboole_0('#skF_1',k2_xboole_0(B_65,'#skF_2')),k4_xboole_0(B_65,'#skF_2')) = k4_xboole_0(k5_xboole_0('#skF_1',B_65),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_661])).

tff(c_1314,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_3','#skF_2')) = k4_xboole_0(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_1271])).

tff(c_1359,plain,(
    k4_xboole_0(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_117,c_2,c_116,c_1314])).

tff(c_1361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_1359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.44  
% 2.94/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.44  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.94/1.44  
% 2.94/1.44  %Foreground sorts:
% 2.94/1.44  
% 2.94/1.44  
% 2.94/1.44  %Background operators:
% 2.94/1.44  
% 2.94/1.44  
% 2.94/1.44  %Foreground operators:
% 2.94/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.94/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.94/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.94/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.94/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.94/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.94/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.94/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.94/1.44  
% 2.94/1.46  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.94/1.46  tff(f_56, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 2.94/1.46  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.94/1.46  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.94/1.46  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.94/1.46  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.94/1.46  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.94/1.46  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.94/1.46  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.94/1.46  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(k5_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, k2_xboole_0(B, C)), k4_xboole_0(B, k2_xboole_0(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_xboole_1)).
% 2.94/1.46  tff(c_185, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | k4_xboole_0(A_32, B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.94/1.46  tff(c_24, plain, (~r1_tarski(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.94/1.46  tff(c_197, plain, (k4_xboole_0(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_185, c_24])).
% 2.94/1.46  tff(c_14, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.94/1.46  tff(c_105, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.94/1.46  tff(c_115, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_105])).
% 2.94/1.46  tff(c_234, plain, (![A_35, B_36]: (k5_xboole_0(A_35, k4_xboole_0(B_36, A_35))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.94/1.46  tff(c_249, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k2_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_115, c_234])).
% 2.94/1.46  tff(c_16, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.94/1.46  tff(c_143, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=A_29 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.94/1.46  tff(c_156, plain, (![A_31]: (k3_xboole_0(k1_xboole_0, A_31)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_143])).
% 2.94/1.46  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.94/1.46  tff(c_161, plain, (![A_31]: (k3_xboole_0(A_31, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_156, c_4])).
% 2.94/1.46  tff(c_303, plain, (![A_39, B_40]: (k5_xboole_0(A_39, k3_xboole_0(A_39, B_40))=k4_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.94/1.46  tff(c_320, plain, (![A_31]: (k5_xboole_0(A_31, k1_xboole_0)=k4_xboole_0(A_31, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_161, c_303])).
% 2.94/1.46  tff(c_340, plain, (![A_31]: (k2_xboole_0(A_31, k1_xboole_0)=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_249, c_16, c_320])).
% 2.94/1.46  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.94/1.46  tff(c_117, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_105])).
% 2.94/1.46  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.94/1.46  tff(c_26, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.94/1.46  tff(c_116, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_105])).
% 2.94/1.46  tff(c_359, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_340, c_249])).
% 2.94/1.46  tff(c_246, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_116, c_234])).
% 2.94/1.46  tff(c_256, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_246])).
% 2.94/1.46  tff(c_585, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_359, c_256])).
% 2.94/1.46  tff(c_243, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_117, c_234])).
% 2.94/1.46  tff(c_255, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_243])).
% 2.94/1.46  tff(c_383, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_359, c_255])).
% 2.94/1.46  tff(c_661, plain, (![A_51, B_52, C_53]: (k2_xboole_0(k4_xboole_0(A_51, k2_xboole_0(B_52, C_53)), k4_xboole_0(B_52, k2_xboole_0(A_51, C_53)))=k4_xboole_0(k5_xboole_0(A_51, B_52), C_53))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.94/1.46  tff(c_1271, plain, (![B_65]: (k2_xboole_0(k4_xboole_0('#skF_1', k2_xboole_0(B_65, '#skF_2')), k4_xboole_0(B_65, '#skF_2'))=k4_xboole_0(k5_xboole_0('#skF_1', B_65), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_383, c_661])).
% 2.94/1.46  tff(c_1314, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_585, c_1271])).
% 2.94/1.46  tff(c_1359, plain, (k4_xboole_0(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_340, c_117, c_2, c_116, c_1314])).
% 2.94/1.46  tff(c_1361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197, c_1359])).
% 2.94/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.46  
% 2.94/1.46  Inference rules
% 2.94/1.46  ----------------------
% 2.94/1.46  #Ref     : 0
% 2.94/1.46  #Sup     : 341
% 2.94/1.46  #Fact    : 0
% 2.94/1.46  #Define  : 0
% 2.94/1.46  #Split   : 0
% 2.94/1.46  #Chain   : 0
% 2.94/1.46  #Close   : 0
% 2.94/1.46  
% 2.94/1.46  Ordering : KBO
% 2.94/1.46  
% 2.94/1.46  Simplification rules
% 2.94/1.46  ----------------------
% 2.94/1.46  #Subsume      : 2
% 2.94/1.46  #Demod        : 242
% 2.94/1.46  #Tautology    : 233
% 2.94/1.46  #SimpNegUnit  : 1
% 2.94/1.46  #BackRed      : 4
% 2.94/1.46  
% 2.94/1.46  #Partial instantiations: 0
% 2.94/1.46  #Strategies tried      : 1
% 2.94/1.46  
% 2.94/1.46  Timing (in seconds)
% 2.94/1.46  ----------------------
% 2.94/1.46  Preprocessing        : 0.27
% 2.94/1.46  Parsing              : 0.15
% 2.94/1.46  CNF conversion       : 0.02
% 2.94/1.46  Main loop            : 0.41
% 2.94/1.46  Inferencing          : 0.14
% 3.10/1.46  Reduction            : 0.16
% 3.10/1.46  Demodulation         : 0.13
% 3.10/1.46  BG Simplification    : 0.02
% 3.10/1.46  Subsumption          : 0.06
% 3.10/1.46  Abstraction          : 0.02
% 3.10/1.46  MUC search           : 0.00
% 3.10/1.46  Cooper               : 0.00
% 3.10/1.46  Total                : 0.70
% 3.10/1.46  Index Insertion      : 0.00
% 3.10/1.46  Index Deletion       : 0.00
% 3.10/1.46  Index Matching       : 0.00
% 3.10/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
