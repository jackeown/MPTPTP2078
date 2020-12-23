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
% DateTime   : Thu Dec  3 09:43:43 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :   57 (  95 expanded)
%              Number of leaves         :   23 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 ( 105 expanded)
%              Number of equality atoms :   39 (  78 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_30,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_338,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = k1_xboole_0
      | ~ r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_345,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_338])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_475,plain,(
    ! [A_52,B_53] : k2_xboole_0(k3_xboole_0(A_52,B_53),k4_xboole_0(A_52,B_53)) = A_52 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1541,plain,(
    ! [B_79,A_80] : k2_xboole_0(k3_xboole_0(B_79,A_80),k4_xboole_0(A_80,B_79)) = A_80 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_475])).

tff(c_1624,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2','#skF_4')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_1541])).

tff(c_158,plain,(
    ! [B_32,A_33] : k2_xboole_0(B_32,A_33) = k2_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_180,plain,(
    ! [A_33] : k2_xboole_0(k1_xboole_0,A_33) = A_33 ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_14])).

tff(c_1687,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1624,c_180])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_37,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_28,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_314,plain,(
    ! [B_40,A_41] : r1_tarski(B_40,k2_xboole_0(A_41,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_28])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_416,plain,(
    ! [B_48,A_49] : k4_xboole_0(B_48,k2_xboole_0(A_49,B_48)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_314,c_12])).

tff(c_444,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_416])).

tff(c_1096,plain,(
    ! [A_70,B_71,C_72] : k4_xboole_0(k4_xboole_0(A_70,B_71),C_72) = k4_xboole_0(A_70,k2_xboole_0(B_71,C_72)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3990,plain,(
    ! [C_110,A_111,B_112] : k2_xboole_0(C_110,k4_xboole_0(A_111,k2_xboole_0(B_112,C_110))) = k2_xboole_0(C_110,k4_xboole_0(A_111,B_112)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1096,c_18])).

tff(c_4130,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_4')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_3990])).

tff(c_4200,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1687,c_14,c_4130])).

tff(c_34,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_346,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_338])).

tff(c_511,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_1')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_475])).

tff(c_802,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_180])).

tff(c_333,plain,(
    ! [B_40,A_41] : k4_xboole_0(B_40,k2_xboole_0(A_41,B_40)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_314,c_12])).

tff(c_4333,plain,(
    ! [A_113] : k2_xboole_0('#skF_2',k4_xboole_0(A_113,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0('#skF_2',k4_xboole_0(A_113,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_3990])).

tff(c_4425,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_1')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_4333])).

tff(c_4460,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4200,c_2,c_802,c_14,c_4425])).

tff(c_4462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_4460])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:50:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.79  
% 4.45/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.80  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.45/1.80  
% 4.45/1.80  %Foreground sorts:
% 4.45/1.80  
% 4.45/1.80  
% 4.45/1.80  %Background operators:
% 4.45/1.80  
% 4.45/1.80  
% 4.45/1.80  %Foreground operators:
% 4.45/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.45/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.45/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.45/1.80  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.45/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.45/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.45/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.45/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.45/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.45/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.45/1.80  
% 4.45/1.81  tff(f_62, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 4.45/1.81  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.45/1.81  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.45/1.81  tff(f_51, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.45/1.81  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.45/1.81  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.45/1.81  tff(f_53, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.45/1.81  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.45/1.81  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.45/1.81  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.45/1.81  tff(c_30, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.45/1.81  tff(c_32, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.45/1.81  tff(c_338, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=k1_xboole_0 | ~r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.45/1.81  tff(c_345, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_338])).
% 4.45/1.81  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.45/1.81  tff(c_475, plain, (![A_52, B_53]: (k2_xboole_0(k3_xboole_0(A_52, B_53), k4_xboole_0(A_52, B_53))=A_52)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.45/1.81  tff(c_1541, plain, (![B_79, A_80]: (k2_xboole_0(k3_xboole_0(B_79, A_80), k4_xboole_0(A_80, B_79))=A_80)), inference(superposition, [status(thm), theory('equality')], [c_4, c_475])).
% 4.45/1.81  tff(c_1624, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', '#skF_4'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_345, c_1541])).
% 4.45/1.81  tff(c_158, plain, (![B_32, A_33]: (k2_xboole_0(B_32, A_33)=k2_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.45/1.81  tff(c_14, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.45/1.81  tff(c_180, plain, (![A_33]: (k2_xboole_0(k1_xboole_0, A_33)=A_33)), inference(superposition, [status(thm), theory('equality')], [c_158, c_14])).
% 4.45/1.81  tff(c_1687, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1624, c_180])).
% 4.45/1.81  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.45/1.81  tff(c_36, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.45/1.81  tff(c_37, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 4.45/1.81  tff(c_28, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.45/1.81  tff(c_314, plain, (![B_40, A_41]: (r1_tarski(B_40, k2_xboole_0(A_41, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_158, c_28])).
% 4.45/1.81  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.45/1.81  tff(c_416, plain, (![B_48, A_49]: (k4_xboole_0(B_48, k2_xboole_0(A_49, B_48))=k1_xboole_0)), inference(resolution, [status(thm)], [c_314, c_12])).
% 4.45/1.81  tff(c_444, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_37, c_416])).
% 4.45/1.81  tff(c_1096, plain, (![A_70, B_71, C_72]: (k4_xboole_0(k4_xboole_0(A_70, B_71), C_72)=k4_xboole_0(A_70, k2_xboole_0(B_71, C_72)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.45/1.81  tff(c_18, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.45/1.81  tff(c_3990, plain, (![C_110, A_111, B_112]: (k2_xboole_0(C_110, k4_xboole_0(A_111, k2_xboole_0(B_112, C_110)))=k2_xboole_0(C_110, k4_xboole_0(A_111, B_112)))), inference(superposition, [status(thm), theory('equality')], [c_1096, c_18])).
% 4.45/1.81  tff(c_4130, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_4'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_444, c_3990])).
% 4.45/1.81  tff(c_4200, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1687, c_14, c_4130])).
% 4.45/1.81  tff(c_34, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.45/1.81  tff(c_346, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_338])).
% 4.45/1.81  tff(c_511, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_1'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_346, c_475])).
% 4.45/1.81  tff(c_802, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_511, c_180])).
% 4.45/1.81  tff(c_333, plain, (![B_40, A_41]: (k4_xboole_0(B_40, k2_xboole_0(A_41, B_40))=k1_xboole_0)), inference(resolution, [status(thm)], [c_314, c_12])).
% 4.45/1.81  tff(c_4333, plain, (![A_113]: (k2_xboole_0('#skF_2', k4_xboole_0(A_113, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0('#skF_2', k4_xboole_0(A_113, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_37, c_3990])).
% 4.45/1.81  tff(c_4425, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_1'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_333, c_4333])).
% 4.45/1.81  tff(c_4460, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4200, c_2, c_802, c_14, c_4425])).
% 4.45/1.81  tff(c_4462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_4460])).
% 4.45/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.81  
% 4.45/1.81  Inference rules
% 4.45/1.81  ----------------------
% 4.45/1.81  #Ref     : 0
% 4.45/1.81  #Sup     : 1131
% 4.45/1.81  #Fact    : 0
% 4.45/1.81  #Define  : 0
% 4.45/1.81  #Split   : 0
% 4.45/1.81  #Chain   : 0
% 4.45/1.81  #Close   : 0
% 4.45/1.81  
% 4.45/1.81  Ordering : KBO
% 4.45/1.81  
% 4.45/1.81  Simplification rules
% 4.45/1.81  ----------------------
% 4.45/1.81  #Subsume      : 0
% 4.45/1.81  #Demod        : 1203
% 4.45/1.81  #Tautology    : 852
% 4.45/1.81  #SimpNegUnit  : 1
% 4.45/1.81  #BackRed      : 5
% 4.45/1.81  
% 4.45/1.81  #Partial instantiations: 0
% 4.45/1.81  #Strategies tried      : 1
% 4.45/1.81  
% 4.45/1.81  Timing (in seconds)
% 4.45/1.81  ----------------------
% 4.45/1.81  Preprocessing        : 0.28
% 4.45/1.81  Parsing              : 0.15
% 4.45/1.81  CNF conversion       : 0.02
% 4.45/1.81  Main loop            : 0.77
% 4.45/1.81  Inferencing          : 0.23
% 4.45/1.81  Reduction            : 0.38
% 4.45/1.81  Demodulation         : 0.32
% 4.45/1.81  BG Simplification    : 0.02
% 4.45/1.81  Subsumption          : 0.10
% 4.45/1.81  Abstraction          : 0.03
% 4.45/1.81  MUC search           : 0.00
% 4.45/1.81  Cooper               : 0.00
% 4.45/1.81  Total                : 1.08
% 4.45/1.81  Index Insertion      : 0.00
% 4.45/1.81  Index Deletion       : 0.00
% 4.45/1.81  Index Matching       : 0.00
% 4.45/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
