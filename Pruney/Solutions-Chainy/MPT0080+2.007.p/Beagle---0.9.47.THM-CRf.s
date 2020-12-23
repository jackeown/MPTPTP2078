%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:50 EST 2020

% Result     : Theorem 4.43s
% Output     : CNFRefutation 4.65s
% Verified   : 
% Statistics : Number of formulae       :   60 (  84 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 (  93 expanded)
%              Number of equality atoms :   39 (  59 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_192,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | k4_xboole_0(A_31,B_32) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_196,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_192,c_24])).

tff(c_44,plain,(
    ! [B_23,A_24] : k2_xboole_0(B_23,A_24) = k2_xboole_0(A_24,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_97,plain,(
    ! [A_25] : k2_xboole_0(k1_xboole_0,A_25) = A_25 ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_16])).

tff(c_22,plain,(
    ! [A_17,B_18] : r1_tarski(A_17,k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_109,plain,(
    ! [A_25] : r1_tarski(k1_xboole_0,A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_22])).

tff(c_274,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_295,plain,(
    ! [A_25] : k4_xboole_0(k1_xboole_0,A_25) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109,c_274])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_197,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_xboole_0(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_201,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_197])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_29,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_296,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_29,c_274])).

tff(c_18,plain,(
    ! [A_12,B_13,C_14] : k4_xboole_0(k4_xboole_0(A_12,B_13),C_14) = k4_xboole_0(A_12,k2_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_453,plain,(
    ! [A_50,B_51,C_52] : k4_xboole_0(k4_xboole_0(A_50,B_51),C_52) = k4_xboole_0(A_50,k2_xboole_0(B_51,C_52)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_497,plain,(
    ! [A_50,B_51,B_16] : k4_xboole_0(A_50,k2_xboole_0(B_51,k4_xboole_0(k4_xboole_0(A_50,B_51),B_16))) = k3_xboole_0(k4_xboole_0(A_50,B_51),B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_453])).

tff(c_3153,plain,(
    ! [A_107,B_108,B_109] : k4_xboole_0(A_107,k2_xboole_0(B_108,k4_xboole_0(A_107,k2_xboole_0(B_108,B_109)))) = k3_xboole_0(k4_xboole_0(A_107,B_108),B_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_497])).

tff(c_3306,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',k1_xboole_0)) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_3153])).

tff(c_3374,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_16,c_3306])).

tff(c_2487,plain,(
    ! [A_94,B_95,C_96] : k4_xboole_0(A_94,k2_xboole_0(k4_xboole_0(A_94,B_95),C_96)) = k4_xboole_0(k3_xboole_0(A_94,B_95),C_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_453])).

tff(c_62,plain,(
    ! [B_23,A_24] : r1_tarski(B_23,k2_xboole_0(A_24,B_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_22])).

tff(c_294,plain,(
    ! [B_23,A_24] : k4_xboole_0(B_23,k2_xboole_0(A_24,B_23)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_274])).

tff(c_2511,plain,(
    ! [C_96,B_95] : k4_xboole_0(k3_xboole_0(C_96,B_95),C_96) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2487,c_294])).

tff(c_4318,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3374,c_2511])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_211,plain,(
    ! [A_37,B_38] :
      ( k2_xboole_0(A_37,B_38) = B_38
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_230,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_211])).

tff(c_4370,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_4318,c_230])).

tff(c_493,plain,(
    ! [A_15,B_16,C_52] : k4_xboole_0(A_15,k2_xboole_0(k4_xboole_0(A_15,B_16),C_52)) = k4_xboole_0(k3_xboole_0(A_15,B_16),C_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_453])).

tff(c_4828,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4370,c_493])).

tff(c_4899,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_201,c_4828])).

tff(c_4901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_4899])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.43/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.90  
% 4.43/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.90  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.43/1.90  
% 4.43/1.90  %Foreground sorts:
% 4.43/1.90  
% 4.43/1.90  
% 4.43/1.90  %Background operators:
% 4.43/1.90  
% 4.43/1.90  
% 4.43/1.90  %Foreground operators:
% 4.43/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.43/1.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.43/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.43/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.43/1.90  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.43/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.43/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.43/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.43/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.43/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.43/1.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.43/1.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.43/1.90  
% 4.65/1.91  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.65/1.91  tff(f_56, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 4.65/1.91  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.65/1.91  tff(f_43, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.65/1.91  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.65/1.91  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.65/1.91  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.65/1.91  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.65/1.91  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.65/1.91  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.65/1.91  tff(c_192, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | k4_xboole_0(A_31, B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.65/1.91  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.65/1.91  tff(c_196, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_192, c_24])).
% 4.65/1.91  tff(c_44, plain, (![B_23, A_24]: (k2_xboole_0(B_23, A_24)=k2_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.65/1.91  tff(c_16, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.65/1.91  tff(c_97, plain, (![A_25]: (k2_xboole_0(k1_xboole_0, A_25)=A_25)), inference(superposition, [status(thm), theory('equality')], [c_44, c_16])).
% 4.65/1.91  tff(c_22, plain, (![A_17, B_18]: (r1_tarski(A_17, k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.65/1.91  tff(c_109, plain, (![A_25]: (r1_tarski(k1_xboole_0, A_25))), inference(superposition, [status(thm), theory('equality')], [c_97, c_22])).
% 4.65/1.91  tff(c_274, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k1_xboole_0 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.65/1.91  tff(c_295, plain, (![A_25]: (k4_xboole_0(k1_xboole_0, A_25)=k1_xboole_0)), inference(resolution, [status(thm)], [c_109, c_274])).
% 4.65/1.91  tff(c_26, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.65/1.91  tff(c_197, plain, (![A_33, B_34]: (k3_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.65/1.91  tff(c_201, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_197])).
% 4.65/1.91  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.65/1.91  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.65/1.91  tff(c_28, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.65/1.91  tff(c_29, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 4.65/1.91  tff(c_296, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_29, c_274])).
% 4.65/1.91  tff(c_18, plain, (![A_12, B_13, C_14]: (k4_xboole_0(k4_xboole_0(A_12, B_13), C_14)=k4_xboole_0(A_12, k2_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.65/1.91  tff(c_20, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.65/1.91  tff(c_453, plain, (![A_50, B_51, C_52]: (k4_xboole_0(k4_xboole_0(A_50, B_51), C_52)=k4_xboole_0(A_50, k2_xboole_0(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.65/1.91  tff(c_497, plain, (![A_50, B_51, B_16]: (k4_xboole_0(A_50, k2_xboole_0(B_51, k4_xboole_0(k4_xboole_0(A_50, B_51), B_16)))=k3_xboole_0(k4_xboole_0(A_50, B_51), B_16))), inference(superposition, [status(thm), theory('equality')], [c_20, c_453])).
% 4.65/1.91  tff(c_3153, plain, (![A_107, B_108, B_109]: (k4_xboole_0(A_107, k2_xboole_0(B_108, k4_xboole_0(A_107, k2_xboole_0(B_108, B_109))))=k3_xboole_0(k4_xboole_0(A_107, B_108), B_109))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_497])).
% 4.65/1.91  tff(c_3306, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', k1_xboole_0))=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_296, c_3153])).
% 4.65/1.91  tff(c_3374, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_16, c_3306])).
% 4.65/1.91  tff(c_2487, plain, (![A_94, B_95, C_96]: (k4_xboole_0(A_94, k2_xboole_0(k4_xboole_0(A_94, B_95), C_96))=k4_xboole_0(k3_xboole_0(A_94, B_95), C_96))), inference(superposition, [status(thm), theory('equality')], [c_20, c_453])).
% 4.65/1.91  tff(c_62, plain, (![B_23, A_24]: (r1_tarski(B_23, k2_xboole_0(A_24, B_23)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_22])).
% 4.65/1.91  tff(c_294, plain, (![B_23, A_24]: (k4_xboole_0(B_23, k2_xboole_0(A_24, B_23))=k1_xboole_0)), inference(resolution, [status(thm)], [c_62, c_274])).
% 4.65/1.91  tff(c_2511, plain, (![C_96, B_95]: (k4_xboole_0(k3_xboole_0(C_96, B_95), C_96)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2487, c_294])).
% 4.65/1.91  tff(c_4318, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3374, c_2511])).
% 4.65/1.91  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.65/1.91  tff(c_211, plain, (![A_37, B_38]: (k2_xboole_0(A_37, B_38)=B_38 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.65/1.91  tff(c_230, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_211])).
% 4.65/1.91  tff(c_4370, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_4318, c_230])).
% 4.65/1.91  tff(c_493, plain, (![A_15, B_16, C_52]: (k4_xboole_0(A_15, k2_xboole_0(k4_xboole_0(A_15, B_16), C_52))=k4_xboole_0(k3_xboole_0(A_15, B_16), C_52))), inference(superposition, [status(thm), theory('equality')], [c_20, c_453])).
% 4.65/1.91  tff(c_4828, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4370, c_493])).
% 4.65/1.91  tff(c_4899, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_295, c_201, c_4828])).
% 4.65/1.91  tff(c_4901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_196, c_4899])).
% 4.65/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.65/1.91  
% 4.65/1.91  Inference rules
% 4.65/1.91  ----------------------
% 4.65/1.91  #Ref     : 0
% 4.65/1.91  #Sup     : 1208
% 4.65/1.91  #Fact    : 0
% 4.65/1.91  #Define  : 0
% 4.65/1.91  #Split   : 0
% 4.65/1.91  #Chain   : 0
% 4.65/1.91  #Close   : 0
% 4.65/1.91  
% 4.65/1.91  Ordering : KBO
% 4.65/1.91  
% 4.65/1.91  Simplification rules
% 4.65/1.91  ----------------------
% 4.65/1.91  #Subsume      : 23
% 4.65/1.91  #Demod        : 1145
% 4.65/1.91  #Tautology    : 753
% 4.65/1.91  #SimpNegUnit  : 1
% 4.65/1.91  #BackRed      : 0
% 4.65/1.91  
% 4.65/1.91  #Partial instantiations: 0
% 4.65/1.91  #Strategies tried      : 1
% 4.65/1.91  
% 4.65/1.91  Timing (in seconds)
% 4.65/1.91  ----------------------
% 4.65/1.92  Preprocessing        : 0.26
% 4.65/1.92  Parsing              : 0.15
% 4.65/1.92  CNF conversion       : 0.02
% 4.65/1.92  Main loop            : 0.85
% 4.65/1.92  Inferencing          : 0.24
% 4.65/1.92  Reduction            : 0.42
% 4.65/1.92  Demodulation         : 0.36
% 4.65/1.92  BG Simplification    : 0.03
% 4.65/1.92  Subsumption          : 0.12
% 4.65/1.92  Abstraction          : 0.04
% 4.65/1.92  MUC search           : 0.00
% 4.65/1.92  Cooper               : 0.00
% 4.65/1.92  Total                : 1.15
% 4.65/1.92  Index Insertion      : 0.00
% 4.65/1.92  Index Deletion       : 0.00
% 4.65/1.92  Index Matching       : 0.00
% 4.65/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
