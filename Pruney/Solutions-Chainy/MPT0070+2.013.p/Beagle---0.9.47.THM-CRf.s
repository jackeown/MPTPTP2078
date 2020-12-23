%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:19 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :   57 (  70 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :   52 (  70 expanded)
%              Number of equality atoms :   40 (  51 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_233,plain,(
    ! [A_30,B_31] :
      ( r1_xboole_0(A_30,B_31)
      | k3_xboole_0(A_30,B_31) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_237,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_233,c_24])).

tff(c_28,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_223,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_227,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_223])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_382,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_414,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_382])).

tff(c_421,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_414])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_238,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_246,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_238])).

tff(c_269,plain,(
    ! [A_34,B_35] : k2_xboole_0(k3_xboole_0(A_34,B_35),k4_xboole_0(A_34,B_35)) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_281,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2','#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_269])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_135,plain,(
    ! [B_25,A_26] : k2_xboole_0(B_25,A_26) = k2_xboole_0(A_26,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_170,plain,(
    ! [A_7] : k2_xboole_0(k1_xboole_0,A_7) = A_7 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_135])).

tff(c_308,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_170])).

tff(c_583,plain,(
    ! [A_44,B_45,C_46] : k4_xboole_0(k4_xboole_0(A_44,B_45),C_46) = k4_xboole_0(A_44,k2_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1581,plain,(
    ! [C_67] : k4_xboole_0('#skF_2',k2_xboole_0('#skF_3',C_67)) = k4_xboole_0('#skF_2',C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_583])).

tff(c_2969,plain,(
    ! [A_89] : k4_xboole_0('#skF_2',k2_xboole_0(A_89,'#skF_3')) = k4_xboole_0('#skF_2',A_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1581])).

tff(c_599,plain,(
    ! [A_44,B_45,C_46] : k4_xboole_0(k4_xboole_0(A_44,B_45),k4_xboole_0(A_44,k2_xboole_0(B_45,C_46))) = k3_xboole_0(k4_xboole_0(A_44,B_45),C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_583,c_20])).

tff(c_2978,plain,(
    ! [A_89] : k4_xboole_0(k4_xboole_0('#skF_2',A_89),k4_xboole_0('#skF_2',A_89)) = k3_xboole_0(k4_xboole_0('#skF_2',A_89),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2969,c_599])).

tff(c_3198,plain,(
    ! [A_91] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_2',A_91)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_4,c_2978])).

tff(c_3273,plain,(
    ! [B_92] : k3_xboole_0('#skF_3',k3_xboole_0('#skF_2',B_92)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3198])).

tff(c_3347,plain,(
    ! [B_93] : k3_xboole_0('#skF_3',k3_xboole_0(B_93,'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3273])).

tff(c_3385,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_3347])).

tff(c_3433,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3385,c_4])).

tff(c_3450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_3433])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:06:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.92/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.73  
% 3.92/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.73  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.92/1.73  
% 3.92/1.73  %Foreground sorts:
% 3.92/1.73  
% 3.92/1.73  
% 3.92/1.73  %Background operators:
% 3.92/1.73  
% 3.92/1.73  
% 3.92/1.73  %Foreground operators:
% 3.92/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.92/1.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.92/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.92/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.92/1.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.92/1.73  tff('#skF_2', type, '#skF_2': $i).
% 3.92/1.73  tff('#skF_3', type, '#skF_3': $i).
% 3.92/1.73  tff('#skF_1', type, '#skF_1': $i).
% 3.92/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.92/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.92/1.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.92/1.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.92/1.73  
% 3.92/1.74  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.92/1.74  tff(f_56, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.92/1.74  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.92/1.74  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.92/1.74  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.92/1.74  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.92/1.74  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.92/1.74  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.92/1.74  tff(f_49, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.92/1.74  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.92/1.74  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.92/1.74  tff(c_233, plain, (![A_30, B_31]: (r1_xboole_0(A_30, B_31) | k3_xboole_0(A_30, B_31)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.92/1.74  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.92/1.74  tff(c_237, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_233, c_24])).
% 3.92/1.74  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.92/1.74  tff(c_223, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.92/1.74  tff(c_227, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_28, c_223])).
% 3.92/1.74  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.92/1.74  tff(c_20, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.92/1.74  tff(c_14, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.92/1.74  tff(c_16, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.92/1.74  tff(c_382, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.92/1.74  tff(c_414, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_382])).
% 3.92/1.74  tff(c_421, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_414])).
% 3.92/1.74  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.92/1.74  tff(c_26, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.92/1.74  tff(c_238, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.92/1.74  tff(c_246, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_238])).
% 3.92/1.74  tff(c_269, plain, (![A_34, B_35]: (k2_xboole_0(k3_xboole_0(A_34, B_35), k4_xboole_0(A_34, B_35))=A_34)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.92/1.74  tff(c_281, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', '#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_246, c_269])).
% 3.92/1.74  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.92/1.74  tff(c_135, plain, (![B_25, A_26]: (k2_xboole_0(B_25, A_26)=k2_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.92/1.74  tff(c_170, plain, (![A_7]: (k2_xboole_0(k1_xboole_0, A_7)=A_7)), inference(superposition, [status(thm), theory('equality')], [c_10, c_135])).
% 3.92/1.74  tff(c_308, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_281, c_170])).
% 3.92/1.74  tff(c_583, plain, (![A_44, B_45, C_46]: (k4_xboole_0(k4_xboole_0(A_44, B_45), C_46)=k4_xboole_0(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.92/1.74  tff(c_1581, plain, (![C_67]: (k4_xboole_0('#skF_2', k2_xboole_0('#skF_3', C_67))=k4_xboole_0('#skF_2', C_67))), inference(superposition, [status(thm), theory('equality')], [c_308, c_583])).
% 3.92/1.74  tff(c_2969, plain, (![A_89]: (k4_xboole_0('#skF_2', k2_xboole_0(A_89, '#skF_3'))=k4_xboole_0('#skF_2', A_89))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1581])).
% 3.92/1.74  tff(c_599, plain, (![A_44, B_45, C_46]: (k4_xboole_0(k4_xboole_0(A_44, B_45), k4_xboole_0(A_44, k2_xboole_0(B_45, C_46)))=k3_xboole_0(k4_xboole_0(A_44, B_45), C_46))), inference(superposition, [status(thm), theory('equality')], [c_583, c_20])).
% 3.92/1.74  tff(c_2978, plain, (![A_89]: (k4_xboole_0(k4_xboole_0('#skF_2', A_89), k4_xboole_0('#skF_2', A_89))=k3_xboole_0(k4_xboole_0('#skF_2', A_89), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2969, c_599])).
% 3.92/1.74  tff(c_3198, plain, (![A_91]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_2', A_91))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_421, c_4, c_2978])).
% 3.92/1.74  tff(c_3273, plain, (![B_92]: (k3_xboole_0('#skF_3', k3_xboole_0('#skF_2', B_92))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_3198])).
% 3.92/1.74  tff(c_3347, plain, (![B_93]: (k3_xboole_0('#skF_3', k3_xboole_0(B_93, '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_3273])).
% 3.92/1.74  tff(c_3385, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_227, c_3347])).
% 3.92/1.74  tff(c_3433, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3385, c_4])).
% 3.92/1.74  tff(c_3450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_237, c_3433])).
% 3.92/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.74  
% 3.92/1.74  Inference rules
% 3.92/1.74  ----------------------
% 3.92/1.74  #Ref     : 0
% 3.92/1.74  #Sup     : 864
% 3.92/1.74  #Fact    : 0
% 3.92/1.74  #Define  : 0
% 3.92/1.74  #Split   : 0
% 3.92/1.74  #Chain   : 0
% 3.92/1.74  #Close   : 0
% 3.92/1.74  
% 3.92/1.74  Ordering : KBO
% 3.92/1.74  
% 3.92/1.74  Simplification rules
% 3.92/1.74  ----------------------
% 3.92/1.74  #Subsume      : 0
% 3.92/1.74  #Demod        : 877
% 3.92/1.74  #Tautology    : 589
% 3.92/1.74  #SimpNegUnit  : 1
% 3.92/1.74  #BackRed      : 4
% 3.92/1.74  
% 3.92/1.74  #Partial instantiations: 0
% 3.92/1.74  #Strategies tried      : 1
% 3.92/1.74  
% 3.92/1.74  Timing (in seconds)
% 3.92/1.74  ----------------------
% 3.92/1.74  Preprocessing        : 0.28
% 3.92/1.74  Parsing              : 0.16
% 3.92/1.74  CNF conversion       : 0.02
% 3.92/1.74  Main loop            : 0.71
% 3.92/1.74  Inferencing          : 0.21
% 3.92/1.74  Reduction            : 0.33
% 3.92/1.74  Demodulation         : 0.28
% 3.92/1.74  BG Simplification    : 0.03
% 3.92/1.74  Subsumption          : 0.10
% 3.92/1.74  Abstraction          : 0.03
% 3.92/1.74  MUC search           : 0.00
% 3.92/1.74  Cooper               : 0.00
% 3.92/1.74  Total                : 1.02
% 3.92/1.74  Index Insertion      : 0.00
% 3.92/1.74  Index Deletion       : 0.00
% 3.92/1.74  Index Matching       : 0.00
% 3.92/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
