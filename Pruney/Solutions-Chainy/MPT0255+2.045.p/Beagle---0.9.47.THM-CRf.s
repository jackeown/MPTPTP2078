%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:45 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   52 (  98 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   45 ( 100 expanded)
%              Number of equality atoms :   36 (  80 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_16,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_77,plain,(
    ! [B_32,A_33] : k2_xboole_0(B_32,A_33) = k2_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_95,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_34])).

tff(c_20,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_146,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,B_37) = k1_xboole_0
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_150,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_146])).

tff(c_309,plain,(
    ! [A_61,B_62,C_63] : k4_xboole_0(k4_xboole_0(A_61,B_62),C_63) = k4_xboole_0(A_61,k2_xboole_0(B_62,C_63)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_335,plain,(
    ! [B_4,C_63] : k4_xboole_0(B_4,k2_xboole_0(B_4,C_63)) = k4_xboole_0(k1_xboole_0,C_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_309])).

tff(c_449,plain,(
    ! [B_66,C_67] : k4_xboole_0(B_66,k2_xboole_0(B_66,C_67)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_335])).

tff(c_485,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_449])).

tff(c_506,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_485])).

tff(c_249,plain,(
    ! [A_52,B_53] : k2_xboole_0(k1_tarski(A_52),k1_tarski(B_53)) = k2_tarski(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_32,plain,(
    ! [A_24,B_25] : k2_xboole_0(k1_tarski(A_24),B_25) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_266,plain,(
    ! [A_52,B_53] : k2_tarski(A_52,B_53) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_32])).

tff(c_512,plain,(
    ! [A_52,B_53] : k2_tarski(A_52,B_53) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_266])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_181,plain,(
    ! [A_41,B_42] :
      ( k2_xboole_0(A_41,B_42) = B_42
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_296,plain,(
    ! [A_59,B_60] :
      ( k2_xboole_0(A_59,B_60) = B_60
      | k4_xboole_0(A_59,B_60) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_181])).

tff(c_356,plain,(
    ! [A_64] : k2_xboole_0(k1_xboole_0,A_64) = A_64 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_296])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_370,plain,(
    ! [A_64] : k2_xboole_0(A_64,k1_xboole_0) = A_64 ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_2])).

tff(c_699,plain,(
    ! [A_77] : k2_xboole_0(A_77,'#skF_3') = A_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_370])).

tff(c_519,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_34])).

tff(c_709,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_699,c_519])).

tff(c_745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_512,c_709])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.29  
% 2.17/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.29  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.17/1.29  
% 2.17/1.29  %Foreground sorts:
% 2.17/1.29  
% 2.17/1.29  
% 2.17/1.29  %Background operators:
% 2.17/1.29  
% 2.17/1.29  
% 2.17/1.29  %Foreground operators:
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.17/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.29  
% 2.17/1.30  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.17/1.30  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.17/1.30  tff(f_64, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.17/1.30  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.17/1.30  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.17/1.30  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.17/1.30  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.17/1.30  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.17/1.30  tff(f_60, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.17/1.30  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.17/1.30  tff(c_16, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.17/1.30  tff(c_77, plain, (![B_32, A_33]: (k2_xboole_0(B_32, A_33)=k2_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.17/1.30  tff(c_34, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.17/1.30  tff(c_95, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_77, c_34])).
% 2.17/1.30  tff(c_20, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.17/1.30  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.30  tff(c_146, plain, (![A_36, B_37]: (k4_xboole_0(A_36, B_37)=k1_xboole_0 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.17/1.30  tff(c_150, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_146])).
% 2.17/1.30  tff(c_309, plain, (![A_61, B_62, C_63]: (k4_xboole_0(k4_xboole_0(A_61, B_62), C_63)=k4_xboole_0(A_61, k2_xboole_0(B_62, C_63)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.30  tff(c_335, plain, (![B_4, C_63]: (k4_xboole_0(B_4, k2_xboole_0(B_4, C_63))=k4_xboole_0(k1_xboole_0, C_63))), inference(superposition, [status(thm), theory('equality')], [c_150, c_309])).
% 2.17/1.30  tff(c_449, plain, (![B_66, C_67]: (k4_xboole_0(B_66, k2_xboole_0(B_66, C_67))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_335])).
% 2.17/1.30  tff(c_485, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_95, c_449])).
% 2.17/1.30  tff(c_506, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_485])).
% 2.17/1.30  tff(c_249, plain, (![A_52, B_53]: (k2_xboole_0(k1_tarski(A_52), k1_tarski(B_53))=k2_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.17/1.30  tff(c_32, plain, (![A_24, B_25]: (k2_xboole_0(k1_tarski(A_24), B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.17/1.30  tff(c_266, plain, (![A_52, B_53]: (k2_tarski(A_52, B_53)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_249, c_32])).
% 2.17/1.30  tff(c_512, plain, (![A_52, B_53]: (k2_tarski(A_52, B_53)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_506, c_266])).
% 2.17/1.30  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.17/1.30  tff(c_181, plain, (![A_41, B_42]: (k2_xboole_0(A_41, B_42)=B_42 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.17/1.30  tff(c_296, plain, (![A_59, B_60]: (k2_xboole_0(A_59, B_60)=B_60 | k4_xboole_0(A_59, B_60)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_181])).
% 2.17/1.30  tff(c_356, plain, (![A_64]: (k2_xboole_0(k1_xboole_0, A_64)=A_64)), inference(superposition, [status(thm), theory('equality')], [c_20, c_296])).
% 2.17/1.30  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.17/1.30  tff(c_370, plain, (![A_64]: (k2_xboole_0(A_64, k1_xboole_0)=A_64)), inference(superposition, [status(thm), theory('equality')], [c_356, c_2])).
% 2.17/1.30  tff(c_699, plain, (![A_77]: (k2_xboole_0(A_77, '#skF_3')=A_77)), inference(demodulation, [status(thm), theory('equality')], [c_506, c_370])).
% 2.17/1.30  tff(c_519, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_506, c_34])).
% 2.17/1.30  tff(c_709, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_699, c_519])).
% 2.17/1.30  tff(c_745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_512, c_709])).
% 2.17/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.30  
% 2.17/1.30  Inference rules
% 2.17/1.30  ----------------------
% 2.17/1.30  #Ref     : 0
% 2.17/1.30  #Sup     : 173
% 2.17/1.30  #Fact    : 0
% 2.17/1.30  #Define  : 0
% 2.17/1.30  #Split   : 0
% 2.17/1.30  #Chain   : 0
% 2.17/1.30  #Close   : 0
% 2.17/1.30  
% 2.17/1.30  Ordering : KBO
% 2.17/1.30  
% 2.17/1.30  Simplification rules
% 2.17/1.30  ----------------------
% 2.17/1.30  #Subsume      : 9
% 2.17/1.30  #Demod        : 55
% 2.17/1.30  #Tautology    : 107
% 2.17/1.30  #SimpNegUnit  : 1
% 2.17/1.30  #BackRed      : 15
% 2.17/1.30  
% 2.17/1.30  #Partial instantiations: 0
% 2.17/1.30  #Strategies tried      : 1
% 2.17/1.30  
% 2.17/1.30  Timing (in seconds)
% 2.17/1.30  ----------------------
% 2.17/1.30  Preprocessing        : 0.30
% 2.17/1.30  Parsing              : 0.16
% 2.17/1.30  CNF conversion       : 0.02
% 2.17/1.30  Main loop            : 0.25
% 2.17/1.30  Inferencing          : 0.09
% 2.17/1.30  Reduction            : 0.09
% 2.17/1.30  Demodulation         : 0.07
% 2.17/1.30  BG Simplification    : 0.01
% 2.17/1.30  Subsumption          : 0.04
% 2.17/1.30  Abstraction          : 0.01
% 2.17/1.30  MUC search           : 0.00
% 2.17/1.30  Cooper               : 0.00
% 2.17/1.30  Total                : 0.57
% 2.17/1.31  Index Insertion      : 0.00
% 2.17/1.31  Index Deletion       : 0.00
% 2.17/1.31  Index Matching       : 0.00
% 2.17/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
