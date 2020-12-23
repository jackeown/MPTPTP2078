%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:19 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 106 expanded)
%              Number of leaves         :   22 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :   60 ( 116 expanded)
%              Number of equality atoms :   41 (  73 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_307,plain,(
    ! [A_38,B_39] :
      ( r1_xboole_0(A_38,B_39)
      | k3_xboole_0(A_38,B_39) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_315,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_307,c_24])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_344,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_193,plain,(
    ! [A_32,B_33] :
      ( k2_xboole_0(A_32,B_33) = B_33
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_246,plain,(
    ! [A_35,B_36] : k2_xboole_0(k4_xboole_0(A_35,B_36),A_35) = A_35 ),
    inference(resolution,[status(thm)],[c_14,c_193])).

tff(c_12,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_259,plain,(
    ! [B_36] : k4_xboole_0(k1_xboole_0,B_36) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_12])).

tff(c_383,plain,(
    ! [B_44] : k3_xboole_0(k1_xboole_0,B_44) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_259])).

tff(c_397,plain,(
    ! [B_4] : k3_xboole_0(B_4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_383])).

tff(c_18,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_379,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_344])).

tff(c_555,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_379])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_270,plain,(
    ! [A_1,B_36] : k2_xboole_0(A_1,k4_xboole_0(A_1,B_36)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_246])).

tff(c_26,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_172,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_176,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_172])).

tff(c_180,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_4])).

tff(c_22,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1080,plain,(
    ! [A_70,B_71] : k4_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k3_xboole_0(A_70,k4_xboole_0(A_70,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_344])).

tff(c_1135,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_1080])).

tff(c_1158,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1135])).

tff(c_483,plain,(
    ! [A_48,B_49] : r1_tarski(k3_xboole_0(A_48,B_49),A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_14])).

tff(c_525,plain,(
    ! [A_51,B_52] : r1_tarski(k3_xboole_0(A_51,B_52),B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_483])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_547,plain,(
    ! [A_51,B_52] : k2_xboole_0(k3_xboole_0(A_51,B_52),B_52) = B_52 ),
    inference(resolution,[status(thm)],[c_525,c_10])).

tff(c_1289,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1158,c_547])).

tff(c_1306,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_1289])).

tff(c_28,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_205,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_193])).

tff(c_601,plain,(
    ! [A_54,B_55,C_56] : k4_xboole_0(k4_xboole_0(A_54,B_55),C_56) = k4_xboole_0(A_54,k2_xboole_0(B_55,C_56)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_895,plain,(
    ! [A_64,B_65,C_66] : r1_tarski(k4_xboole_0(A_64,k2_xboole_0(B_65,C_66)),k4_xboole_0(A_64,B_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_14])).

tff(c_978,plain,(
    ! [A_67] : r1_tarski(k4_xboole_0(A_67,'#skF_2'),k4_xboole_0(A_67,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_895])).

tff(c_1006,plain,(
    ! [A_67] : k2_xboole_0(k4_xboole_0(A_67,'#skF_2'),k4_xboole_0(A_67,'#skF_1')) = k4_xboole_0(A_67,'#skF_1') ),
    inference(resolution,[status(thm)],[c_978,c_10])).

tff(c_1316,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_1')) = k4_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1306,c_1006])).

tff(c_1343,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_1316])).

tff(c_1370,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k3_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1343,c_22])).

tff(c_1386,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_4,c_1370])).

tff(c_1388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_1386])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:33:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.44  
% 2.78/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.44  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.78/1.44  
% 2.78/1.44  %Foreground sorts:
% 2.78/1.44  
% 2.78/1.44  
% 2.78/1.44  %Background operators:
% 2.78/1.44  
% 2.78/1.44  
% 2.78/1.44  %Foreground operators:
% 2.78/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.78/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.78/1.44  
% 3.00/1.45  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.00/1.45  tff(f_56, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.00/1.45  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.00/1.45  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.00/1.45  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.00/1.45  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.00/1.45  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.00/1.45  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.00/1.45  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.00/1.45  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.00/1.45  tff(c_307, plain, (![A_38, B_39]: (r1_xboole_0(A_38, B_39) | k3_xboole_0(A_38, B_39)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.00/1.45  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.00/1.45  tff(c_315, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_307, c_24])).
% 3.00/1.45  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.00/1.45  tff(c_344, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.00/1.45  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.00/1.45  tff(c_193, plain, (![A_32, B_33]: (k2_xboole_0(A_32, B_33)=B_33 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.00/1.45  tff(c_246, plain, (![A_35, B_36]: (k2_xboole_0(k4_xboole_0(A_35, B_36), A_35)=A_35)), inference(resolution, [status(thm)], [c_14, c_193])).
% 3.00/1.45  tff(c_12, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.00/1.45  tff(c_259, plain, (![B_36]: (k4_xboole_0(k1_xboole_0, B_36)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_246, c_12])).
% 3.00/1.45  tff(c_383, plain, (![B_44]: (k3_xboole_0(k1_xboole_0, B_44)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_344, c_259])).
% 3.00/1.45  tff(c_397, plain, (![B_4]: (k3_xboole_0(B_4, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_383])).
% 3.00/1.45  tff(c_18, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.00/1.45  tff(c_379, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_344])).
% 3.00/1.45  tff(c_555, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_397, c_379])).
% 3.00/1.45  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.00/1.45  tff(c_270, plain, (![A_1, B_36]: (k2_xboole_0(A_1, k4_xboole_0(A_1, B_36))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_246])).
% 3.00/1.45  tff(c_26, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.00/1.45  tff(c_172, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.00/1.45  tff(c_176, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_172])).
% 3.00/1.45  tff(c_180, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_176, c_4])).
% 3.00/1.45  tff(c_22, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.00/1.45  tff(c_1080, plain, (![A_70, B_71]: (k4_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k3_xboole_0(A_70, k4_xboole_0(A_70, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_344])).
% 3.00/1.45  tff(c_1135, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_180, c_1080])).
% 3.00/1.45  tff(c_1158, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1135])).
% 3.00/1.45  tff(c_483, plain, (![A_48, B_49]: (r1_tarski(k3_xboole_0(A_48, B_49), A_48))), inference(superposition, [status(thm), theory('equality')], [c_344, c_14])).
% 3.00/1.45  tff(c_525, plain, (![A_51, B_52]: (r1_tarski(k3_xboole_0(A_51, B_52), B_52))), inference(superposition, [status(thm), theory('equality')], [c_4, c_483])).
% 3.00/1.45  tff(c_10, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.00/1.45  tff(c_547, plain, (![A_51, B_52]: (k2_xboole_0(k3_xboole_0(A_51, B_52), B_52)=B_52)), inference(resolution, [status(thm)], [c_525, c_10])).
% 3.00/1.45  tff(c_1289, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1158, c_547])).
% 3.00/1.45  tff(c_1306, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_270, c_1289])).
% 3.00/1.45  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.00/1.45  tff(c_205, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_28, c_193])).
% 3.00/1.45  tff(c_601, plain, (![A_54, B_55, C_56]: (k4_xboole_0(k4_xboole_0(A_54, B_55), C_56)=k4_xboole_0(A_54, k2_xboole_0(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.00/1.45  tff(c_895, plain, (![A_64, B_65, C_66]: (r1_tarski(k4_xboole_0(A_64, k2_xboole_0(B_65, C_66)), k4_xboole_0(A_64, B_65)))), inference(superposition, [status(thm), theory('equality')], [c_601, c_14])).
% 3.00/1.45  tff(c_978, plain, (![A_67]: (r1_tarski(k4_xboole_0(A_67, '#skF_2'), k4_xboole_0(A_67, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_205, c_895])).
% 3.00/1.45  tff(c_1006, plain, (![A_67]: (k2_xboole_0(k4_xboole_0(A_67, '#skF_2'), k4_xboole_0(A_67, '#skF_1'))=k4_xboole_0(A_67, '#skF_1'))), inference(resolution, [status(thm)], [c_978, c_10])).
% 3.00/1.45  tff(c_1316, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_1'))=k4_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1306, c_1006])).
% 3.00/1.45  tff(c_1343, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_270, c_1316])).
% 3.00/1.45  tff(c_1370, plain, (k4_xboole_0('#skF_3', '#skF_3')=k3_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1343, c_22])).
% 3.00/1.45  tff(c_1386, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_555, c_4, c_1370])).
% 3.00/1.45  tff(c_1388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_315, c_1386])).
% 3.00/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.45  
% 3.00/1.45  Inference rules
% 3.00/1.45  ----------------------
% 3.00/1.45  #Ref     : 0
% 3.00/1.45  #Sup     : 333
% 3.00/1.45  #Fact    : 0
% 3.00/1.45  #Define  : 0
% 3.00/1.45  #Split   : 0
% 3.00/1.45  #Chain   : 0
% 3.00/1.45  #Close   : 0
% 3.00/1.45  
% 3.00/1.45  Ordering : KBO
% 3.00/1.45  
% 3.00/1.45  Simplification rules
% 3.00/1.45  ----------------------
% 3.00/1.45  #Subsume      : 0
% 3.00/1.45  #Demod        : 223
% 3.00/1.45  #Tautology    : 248
% 3.00/1.45  #SimpNegUnit  : 1
% 3.00/1.45  #BackRed      : 2
% 3.00/1.45  
% 3.00/1.46  #Partial instantiations: 0
% 3.00/1.46  #Strategies tried      : 1
% 3.00/1.46  
% 3.00/1.46  Timing (in seconds)
% 3.00/1.46  ----------------------
% 3.00/1.46  Preprocessing        : 0.26
% 3.00/1.46  Parsing              : 0.15
% 3.00/1.46  CNF conversion       : 0.02
% 3.00/1.46  Main loop            : 0.39
% 3.00/1.46  Inferencing          : 0.14
% 3.00/1.46  Reduction            : 0.15
% 3.00/1.46  Demodulation         : 0.12
% 3.00/1.46  BG Simplification    : 0.02
% 3.00/1.46  Subsumption          : 0.05
% 3.00/1.46  Abstraction          : 0.02
% 3.00/1.46  MUC search           : 0.00
% 3.00/1.46  Cooper               : 0.00
% 3.00/1.46  Total                : 0.68
% 3.00/1.46  Index Insertion      : 0.00
% 3.00/1.46  Index Deletion       : 0.00
% 3.00/1.46  Index Matching       : 0.00
% 3.00/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
