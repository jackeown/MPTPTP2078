%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:18 EST 2020

% Result     : Theorem 5.12s
% Output     : CNFRefutation 5.12s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 100 expanded)
%              Number of leaves         :   22 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :   49 ( 120 expanded)
%              Number of equality atoms :   32 (  63 expanded)
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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_197,plain,(
    ! [A_31,B_32] :
      ( r1_xboole_0(A_31,B_32)
      | k3_xboole_0(A_31,B_32) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_208,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_197,c_26])).

tff(c_28,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_87,plain,(
    ! [B_24,A_25] :
      ( r1_xboole_0(B_24,A_25)
      | ~ r1_xboole_0(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_90,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_87])).

tff(c_168,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_175,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_90,c_168])).

tff(c_18,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_40,plain,(
    ! [B_22,A_23] : k2_xboole_0(B_22,A_23) = k2_xboole_0(A_23,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_78,plain,(
    ! [A_13] : k2_xboole_0(k1_xboole_0,A_13) = A_13 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_40])).

tff(c_236,plain,(
    ! [A_39,B_40] : k2_xboole_0(k3_xboole_0(A_39,B_40),k4_xboole_0(A_39,B_40)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_248,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_236])).

tff(c_326,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_248])).

tff(c_22,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_370,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_22])).

tff(c_376,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_370])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_227,plain,(
    ! [A_37,B_38] :
      ( k2_xboole_0(A_37,B_38) = B_38
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_235,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_227])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_413,plain,(
    ! [A_43,B_44,C_45] : k4_xboole_0(k4_xboole_0(A_43,B_44),C_45) = k4_xboole_0(A_43,k2_xboole_0(B_44,C_45)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1720,plain,(
    ! [C_65] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_2',C_65)) = k4_xboole_0('#skF_3',C_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_413])).

tff(c_3737,plain,(
    ! [B_95] : k4_xboole_0('#skF_3',k2_xboole_0(B_95,'#skF_2')) = k4_xboole_0('#skF_3',B_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1720])).

tff(c_3808,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k4_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_3737])).

tff(c_3836,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_3808])).

tff(c_3864,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k3_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3836,c_22])).

tff(c_3875,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_4,c_3864])).

tff(c_3877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_3875])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:46:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.12/2.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.12/2.12  
% 5.12/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.12/2.12  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.12/2.12  
% 5.12/2.12  %Foreground sorts:
% 5.12/2.12  
% 5.12/2.12  
% 5.12/2.12  %Background operators:
% 5.12/2.12  
% 5.12/2.12  
% 5.12/2.12  %Foreground operators:
% 5.12/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.12/2.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.12/2.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.12/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.12/2.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.12/2.12  tff('#skF_2', type, '#skF_2': $i).
% 5.12/2.12  tff('#skF_3', type, '#skF_3': $i).
% 5.12/2.12  tff('#skF_1', type, '#skF_1': $i).
% 5.12/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.12/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.12/2.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.12/2.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.12/2.12  
% 5.12/2.13  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.12/2.13  tff(f_60, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 5.12/2.13  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.12/2.13  tff(f_47, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.12/2.13  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.12/2.13  tff(f_53, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.12/2.13  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.12/2.13  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.12/2.13  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.12/2.13  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.12/2.13  tff(c_197, plain, (![A_31, B_32]: (r1_xboole_0(A_31, B_32) | k3_xboole_0(A_31, B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.12/2.13  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.12/2.13  tff(c_208, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_197, c_26])).
% 5.12/2.13  tff(c_28, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.12/2.13  tff(c_87, plain, (![B_24, A_25]: (r1_xboole_0(B_24, A_25) | ~r1_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.12/2.13  tff(c_90, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_87])).
% 5.12/2.13  tff(c_168, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.12/2.13  tff(c_175, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_90, c_168])).
% 5.12/2.13  tff(c_18, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.12/2.13  tff(c_40, plain, (![B_22, A_23]: (k2_xboole_0(B_22, A_23)=k2_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.12/2.13  tff(c_78, plain, (![A_13]: (k2_xboole_0(k1_xboole_0, A_13)=A_13)), inference(superposition, [status(thm), theory('equality')], [c_18, c_40])).
% 5.12/2.13  tff(c_236, plain, (![A_39, B_40]: (k2_xboole_0(k3_xboole_0(A_39, B_40), k4_xboole_0(A_39, B_40))=A_39)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.12/2.13  tff(c_248, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_175, c_236])).
% 5.12/2.13  tff(c_326, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_78, c_248])).
% 5.12/2.13  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.12/2.13  tff(c_370, plain, (k4_xboole_0('#skF_3', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_326, c_22])).
% 5.12/2.13  tff(c_376, plain, (k4_xboole_0('#skF_3', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_175, c_370])).
% 5.12/2.13  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.12/2.13  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.12/2.13  tff(c_227, plain, (![A_37, B_38]: (k2_xboole_0(A_37, B_38)=B_38 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.12/2.13  tff(c_235, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_30, c_227])).
% 5.12/2.13  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.12/2.13  tff(c_413, plain, (![A_43, B_44, C_45]: (k4_xboole_0(k4_xboole_0(A_43, B_44), C_45)=k4_xboole_0(A_43, k2_xboole_0(B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.12/2.13  tff(c_1720, plain, (![C_65]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_2', C_65))=k4_xboole_0('#skF_3', C_65))), inference(superposition, [status(thm), theory('equality')], [c_326, c_413])).
% 5.12/2.13  tff(c_3737, plain, (![B_95]: (k4_xboole_0('#skF_3', k2_xboole_0(B_95, '#skF_2'))=k4_xboole_0('#skF_3', B_95))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1720])).
% 5.12/2.13  tff(c_3808, plain, (k4_xboole_0('#skF_3', '#skF_2')=k4_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_235, c_3737])).
% 5.12/2.13  tff(c_3836, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_326, c_3808])).
% 5.12/2.13  tff(c_3864, plain, (k4_xboole_0('#skF_3', '#skF_3')=k3_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3836, c_22])).
% 5.12/2.13  tff(c_3875, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_376, c_4, c_3864])).
% 5.12/2.13  tff(c_3877, plain, $false, inference(negUnitSimplification, [status(thm)], [c_208, c_3875])).
% 5.12/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.12/2.13  
% 5.12/2.13  Inference rules
% 5.12/2.13  ----------------------
% 5.12/2.13  #Ref     : 0
% 5.12/2.13  #Sup     : 1012
% 5.12/2.13  #Fact    : 0
% 5.12/2.13  #Define  : 0
% 5.12/2.13  #Split   : 2
% 5.12/2.13  #Chain   : 0
% 5.12/2.13  #Close   : 0
% 5.12/2.13  
% 5.12/2.13  Ordering : KBO
% 5.12/2.13  
% 5.12/2.13  Simplification rules
% 5.12/2.13  ----------------------
% 5.12/2.13  #Subsume      : 11
% 5.12/2.13  #Demod        : 1162
% 5.12/2.13  #Tautology    : 572
% 5.12/2.13  #SimpNegUnit  : 4
% 5.12/2.13  #BackRed      : 10
% 5.12/2.13  
% 5.12/2.13  #Partial instantiations: 0
% 5.12/2.13  #Strategies tried      : 1
% 5.12/2.13  
% 5.12/2.13  Timing (in seconds)
% 5.12/2.13  ----------------------
% 5.12/2.13  Preprocessing        : 0.32
% 5.12/2.13  Parsing              : 0.17
% 5.12/2.13  CNF conversion       : 0.02
% 5.12/2.13  Main loop            : 0.93
% 5.12/2.13  Inferencing          : 0.27
% 5.12/2.13  Reduction            : 0.44
% 5.12/2.13  Demodulation         : 0.37
% 5.12/2.13  BG Simplification    : 0.03
% 5.12/2.13  Subsumption          : 0.13
% 5.12/2.13  Abstraction          : 0.04
% 5.12/2.13  MUC search           : 0.00
% 5.12/2.13  Cooper               : 0.00
% 5.12/2.13  Total                : 1.28
% 5.12/2.13  Index Insertion      : 0.00
% 5.12/2.13  Index Deletion       : 0.00
% 5.12/2.13  Index Matching       : 0.00
% 5.12/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
