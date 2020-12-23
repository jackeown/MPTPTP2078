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
% DateTime   : Thu Dec  3 09:43:53 EST 2020

% Result     : Theorem 4.59s
% Output     : CNFRefutation 4.85s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 116 expanded)
%              Number of leaves         :   21 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   53 ( 126 expanded)
%              Number of equality atoms :   36 (  83 expanded)
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

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_95,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | k4_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_99,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_22])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_100,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_100])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_37,plain,(
    ! [A_19,B_20] : r1_tarski(A_19,k2_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_40,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_37])).

tff(c_109,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_128,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_109])).

tff(c_190,plain,(
    ! [A_39,B_40] : k2_xboole_0(A_39,k4_xboole_0(B_40,A_39)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_220,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = k2_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_190])).

tff(c_228,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_220])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_142,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k2_xboole_0(A_35,B_36)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_109])).

tff(c_152,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_142])).

tff(c_487,plain,(
    ! [A_49,B_50,C_51] : k4_xboole_0(k4_xboole_0(A_49,B_50),C_51) = k4_xboole_0(A_49,k2_xboole_0(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1745,plain,(
    ! [C_80,A_81,B_82] : k2_xboole_0(C_80,k4_xboole_0(A_81,k2_xboole_0(B_82,C_80))) = k2_xboole_0(C_80,k4_xboole_0(A_81,B_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_14])).

tff(c_1863,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,k4_xboole_0(B_2,A_1)) = k2_xboole_0(B_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_1745])).

tff(c_1908,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,k4_xboole_0(B_2,A_1)) = B_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_1863])).

tff(c_389,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_402,plain,(
    ! [A_45,B_46] : k2_xboole_0(k4_xboole_0(A_45,B_46),k3_xboole_0(A_45,B_46)) = k2_xboole_0(k4_xboole_0(A_45,B_46),A_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_14])).

tff(c_429,plain,(
    ! [A_45,B_46] : k2_xboole_0(k4_xboole_0(A_45,B_46),k3_xboole_0(A_45,B_46)) = k2_xboole_0(A_45,k4_xboole_0(A_45,B_46)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_402])).

tff(c_2571,plain,(
    ! [A_93,B_94] : k2_xboole_0(k4_xboole_0(A_93,B_94),k3_xboole_0(A_93,B_94)) = A_93 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1908,c_429])).

tff(c_2709,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_3'),k1_xboole_0) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_2571])).

tff(c_2877,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2709,c_228])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_27,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_26])).

tff(c_127,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_27,c_109])).

tff(c_1866,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_1745])).

tff(c_1909,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_1866])).

tff(c_2229,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1909,c_152])).

tff(c_2922,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2877,c_2229])).

tff(c_2928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_2922])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.59/2.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.85/2.27  
% 4.85/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.85/2.27  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.85/2.27  
% 4.85/2.27  %Foreground sorts:
% 4.85/2.27  
% 4.85/2.27  
% 4.85/2.27  %Background operators:
% 4.85/2.27  
% 4.85/2.27  
% 4.85/2.27  %Foreground operators:
% 4.85/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.85/2.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.85/2.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.85/2.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.85/2.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.85/2.27  tff('#skF_2', type, '#skF_2': $i).
% 4.85/2.27  tff('#skF_3', type, '#skF_3': $i).
% 4.85/2.27  tff('#skF_1', type, '#skF_1': $i).
% 4.85/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.85/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.85/2.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.85/2.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.85/2.27  
% 4.85/2.29  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.85/2.29  tff(f_52, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 4.85/2.29  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.85/2.29  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.85/2.29  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.85/2.29  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.85/2.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.85/2.29  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.85/2.29  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.85/2.29  tff(c_95, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | k4_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.85/2.29  tff(c_22, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.85/2.29  tff(c_99, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_95, c_22])).
% 4.85/2.29  tff(c_24, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.85/2.29  tff(c_100, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.85/2.29  tff(c_104, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_100])).
% 4.85/2.29  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.85/2.29  tff(c_37, plain, (![A_19, B_20]: (r1_tarski(A_19, k2_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.85/2.29  tff(c_40, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_37])).
% 4.85/2.29  tff(c_109, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.85/2.29  tff(c_128, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_109])).
% 4.85/2.29  tff(c_190, plain, (![A_39, B_40]: (k2_xboole_0(A_39, k4_xboole_0(B_40, A_39))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.85/2.29  tff(c_220, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=k2_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_128, c_190])).
% 4.85/2.29  tff(c_228, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_220])).
% 4.85/2.29  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.85/2.29  tff(c_20, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.85/2.29  tff(c_142, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k2_xboole_0(A_35, B_36))=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_109])).
% 4.85/2.29  tff(c_152, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_142])).
% 4.85/2.29  tff(c_487, plain, (![A_49, B_50, C_51]: (k4_xboole_0(k4_xboole_0(A_49, B_50), C_51)=k4_xboole_0(A_49, k2_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.85/2.29  tff(c_14, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.85/2.29  tff(c_1745, plain, (![C_80, A_81, B_82]: (k2_xboole_0(C_80, k4_xboole_0(A_81, k2_xboole_0(B_82, C_80)))=k2_xboole_0(C_80, k4_xboole_0(A_81, B_82)))), inference(superposition, [status(thm), theory('equality')], [c_487, c_14])).
% 4.85/2.29  tff(c_1863, plain, (![B_2, A_1]: (k2_xboole_0(B_2, k4_xboole_0(B_2, A_1))=k2_xboole_0(B_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_152, c_1745])).
% 4.85/2.29  tff(c_1908, plain, (![B_2, A_1]: (k2_xboole_0(B_2, k4_xboole_0(B_2, A_1))=B_2)), inference(demodulation, [status(thm), theory('equality')], [c_228, c_1863])).
% 4.85/2.29  tff(c_389, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.85/2.29  tff(c_402, plain, (![A_45, B_46]: (k2_xboole_0(k4_xboole_0(A_45, B_46), k3_xboole_0(A_45, B_46))=k2_xboole_0(k4_xboole_0(A_45, B_46), A_45))), inference(superposition, [status(thm), theory('equality')], [c_389, c_14])).
% 4.85/2.29  tff(c_429, plain, (![A_45, B_46]: (k2_xboole_0(k4_xboole_0(A_45, B_46), k3_xboole_0(A_45, B_46))=k2_xboole_0(A_45, k4_xboole_0(A_45, B_46)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_402])).
% 4.85/2.29  tff(c_2571, plain, (![A_93, B_94]: (k2_xboole_0(k4_xboole_0(A_93, B_94), k3_xboole_0(A_93, B_94))=A_93)), inference(demodulation, [status(thm), theory('equality')], [c_1908, c_429])).
% 4.85/2.29  tff(c_2709, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), k1_xboole_0)='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_104, c_2571])).
% 4.85/2.29  tff(c_2877, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2709, c_228])).
% 4.85/2.29  tff(c_26, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.85/2.29  tff(c_27, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_26])).
% 4.85/2.29  tff(c_127, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_27, c_109])).
% 4.85/2.29  tff(c_1866, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_127, c_1745])).
% 4.85/2.29  tff(c_1909, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_228, c_1866])).
% 4.85/2.29  tff(c_2229, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1909, c_152])).
% 4.85/2.29  tff(c_2922, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2877, c_2229])).
% 4.85/2.29  tff(c_2928, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_2922])).
% 4.85/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.85/2.29  
% 4.85/2.29  Inference rules
% 4.85/2.29  ----------------------
% 4.85/2.29  #Ref     : 0
% 4.85/2.29  #Sup     : 731
% 4.85/2.29  #Fact    : 0
% 4.85/2.29  #Define  : 0
% 4.85/2.29  #Split   : 0
% 4.85/2.29  #Chain   : 0
% 4.85/2.29  #Close   : 0
% 4.85/2.29  
% 4.85/2.29  Ordering : KBO
% 4.85/2.29  
% 4.85/2.29  Simplification rules
% 4.85/2.29  ----------------------
% 4.85/2.30  #Subsume      : 0
% 4.85/2.30  #Demod        : 613
% 4.85/2.30  #Tautology    : 525
% 4.85/2.30  #SimpNegUnit  : 1
% 4.85/2.30  #BackRed      : 5
% 4.85/2.30  
% 4.85/2.30  #Partial instantiations: 0
% 4.85/2.30  #Strategies tried      : 1
% 4.85/2.30  
% 4.85/2.30  Timing (in seconds)
% 4.85/2.30  ----------------------
% 4.95/2.30  Preprocessing        : 0.43
% 4.95/2.30  Parsing              : 0.24
% 4.95/2.30  CNF conversion       : 0.03
% 4.95/2.30  Main loop            : 0.96
% 4.95/2.30  Inferencing          : 0.29
% 4.95/2.30  Reduction            : 0.44
% 4.95/2.30  Demodulation         : 0.37
% 4.95/2.30  BG Simplification    : 0.03
% 4.95/2.30  Subsumption          : 0.13
% 4.95/2.30  Abstraction          : 0.04
% 4.95/2.30  MUC search           : 0.00
% 4.95/2.30  Cooper               : 0.00
% 4.95/2.30  Total                : 1.44
% 4.95/2.30  Index Insertion      : 0.00
% 4.95/2.30  Index Deletion       : 0.00
% 4.95/2.30  Index Matching       : 0.00
% 4.95/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
