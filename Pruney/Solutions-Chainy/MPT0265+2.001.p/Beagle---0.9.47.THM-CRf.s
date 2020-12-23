%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:25 EST 2020

% Result     : Theorem 8.91s
% Output     : CNFRefutation 8.91s
% Verified   : 
% Statistics : Number of formulae       :   50 (  77 expanded)
%              Number of leaves         :   19 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 137 expanded)
%              Number of equality atoms :   42 (  75 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,B)
       => ( ( r2_hidden(C,B)
            & A != C )
          | k3_xboole_0(k2_tarski(A,C),B) = k1_tarski(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( A != B
     => k4_xboole_0(k2_tarski(A,B),k1_tarski(B)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_26,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_15058,plain,(
    ! [B_1109,A_1110] :
      ( k3_xboole_0(B_1109,k1_tarski(A_1110)) = k1_tarski(A_1110)
      | ~ r2_hidden(A_1110,B_1109) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_29,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_144,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(k2_tarski(A_24,B_25),k1_tarski(B_25)) = k1_tarski(A_24)
      | B_25 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_159,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(k2_tarski(A_5,B_6),k1_tarski(A_5)) = k1_tarski(B_6)
      | B_6 = A_5 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_144])).

tff(c_2097,plain,(
    ! [B_390,C_391,A_392] :
      ( ~ r2_hidden(B_390,C_391)
      | k4_xboole_0(k2_tarski(A_392,B_390),C_391) = k1_tarski(A_392)
      | r2_hidden(A_392,C_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5473,plain,(
    ! [A_919,B_920,C_921] :
      ( k4_xboole_0(k2_tarski(A_919,B_920),k1_tarski(A_919)) = k3_xboole_0(k2_tarski(A_919,B_920),C_921)
      | ~ r2_hidden(B_920,C_921)
      | r2_hidden(A_919,C_921) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2097,c_4])).

tff(c_9314,plain,(
    ! [A_1001,B_1002,C_1003] :
      ( k3_xboole_0(k2_tarski(A_1001,B_1002),C_1003) = k1_tarski(B_1002)
      | ~ r2_hidden(B_1002,C_1003)
      | r2_hidden(A_1001,C_1003)
      | B_1002 = A_1001 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_5473])).

tff(c_14437,plain,(
    ! [B_1094,A_1095,C_1096] :
      ( k3_xboole_0(k2_tarski(B_1094,A_1095),C_1096) = k1_tarski(B_1094)
      | ~ r2_hidden(B_1094,C_1096)
      | r2_hidden(A_1095,C_1096)
      | B_1094 = A_1095 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_9314])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14665,plain,(
    ! [C_1097,B_1098,A_1099] :
      ( k3_xboole_0(C_1097,k2_tarski(B_1098,A_1099)) = k1_tarski(B_1098)
      | ~ r2_hidden(B_1098,C_1097)
      | r2_hidden(A_1099,C_1097)
      | B_1098 = A_1099 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14437,c_2])).

tff(c_22,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    k3_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_14817,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | r2_hidden('#skF_3','#skF_2')
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_14665,c_28])).

tff(c_14922,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_14817])).

tff(c_14923,plain,(
    '#skF_3' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_14922])).

tff(c_4796,plain,(
    ! [B_894,C_895,A_896] :
      ( ~ r2_hidden(B_894,C_895)
      | k4_xboole_0(k2_tarski(B_894,A_896),C_895) = k1_tarski(A_896)
      | r2_hidden(A_896,C_895) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2097])).

tff(c_14,plain,(
    ! [A_10,C_12,B_11] :
      ( ~ r2_hidden(A_10,C_12)
      | k4_xboole_0(k2_tarski(A_10,B_11),C_12) != k1_tarski(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6203,plain,(
    ! [B_941,C_942,A_943] :
      ( ~ r2_hidden(B_941,C_942)
      | k1_tarski(B_941) != k1_tarski(A_943)
      | ~ r2_hidden(B_941,C_942)
      | r2_hidden(A_943,C_942) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4796,c_14])).

tff(c_6215,plain,(
    ! [A_943] :
      ( k1_tarski(A_943) != k1_tarski('#skF_1')
      | ~ r2_hidden('#skF_1','#skF_2')
      | r2_hidden(A_943,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_6203])).

tff(c_6226,plain,(
    ! [A_944] :
      ( k1_tarski(A_944) != k1_tarski('#skF_1')
      | r2_hidden(A_944,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6215])).

tff(c_6233,plain,(
    k1_tarski('#skF_3') != k1_tarski('#skF_1') ),
    inference(resolution,[status(thm)],[c_6226,c_29])).

tff(c_14939,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14923,c_6233])).

tff(c_14940,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_15022,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14940,c_28])).

tff(c_15064,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_15058,c_15022])).

tff(c_15086,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_15064])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:07:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.91/3.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.91/3.03  
% 8.91/3.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.91/3.03  %$ r2_hidden > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 8.91/3.03  
% 8.91/3.03  %Foreground sorts:
% 8.91/3.03  
% 8.91/3.03  
% 8.91/3.03  %Background operators:
% 8.91/3.03  
% 8.91/3.03  
% 8.91/3.03  %Foreground operators:
% 8.91/3.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.91/3.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.91/3.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.91/3.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.91/3.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.91/3.03  tff('#skF_2', type, '#skF_2': $i).
% 8.91/3.03  tff('#skF_3', type, '#skF_3': $i).
% 8.91/3.03  tff('#skF_1', type, '#skF_1': $i).
% 8.91/3.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.91/3.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.91/3.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.91/3.03  
% 8.91/3.04  tff(f_61, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, B) => ((r2_hidden(C, B) & ~(A = C)) | (k3_xboole_0(k2_tarski(A, C), B) = k1_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_zfmisc_1)).
% 8.91/3.04  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 8.91/3.04  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 8.91/3.04  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.91/3.04  tff(f_51, axiom, (![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 8.91/3.04  tff(f_46, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 8.91/3.04  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.91/3.04  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.91/3.04  tff(c_26, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.91/3.04  tff(c_15058, plain, (![B_1109, A_1110]: (k3_xboole_0(B_1109, k1_tarski(A_1110))=k1_tarski(A_1110) | ~r2_hidden(A_1110, B_1109))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.91/3.04  tff(c_8, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.91/3.04  tff(c_24, plain, ('#skF_3'='#skF_1' | ~r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.91/3.04  tff(c_29, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_24])).
% 8.91/3.04  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.91/3.04  tff(c_144, plain, (![A_24, B_25]: (k4_xboole_0(k2_tarski(A_24, B_25), k1_tarski(B_25))=k1_tarski(A_24) | B_25=A_24)), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.91/3.04  tff(c_159, plain, (![A_5, B_6]: (k4_xboole_0(k2_tarski(A_5, B_6), k1_tarski(A_5))=k1_tarski(B_6) | B_6=A_5)), inference(superposition, [status(thm), theory('equality')], [c_6, c_144])).
% 8.91/3.04  tff(c_2097, plain, (![B_390, C_391, A_392]: (~r2_hidden(B_390, C_391) | k4_xboole_0(k2_tarski(A_392, B_390), C_391)=k1_tarski(A_392) | r2_hidden(A_392, C_391))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.91/3.04  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.91/3.04  tff(c_5473, plain, (![A_919, B_920, C_921]: (k4_xboole_0(k2_tarski(A_919, B_920), k1_tarski(A_919))=k3_xboole_0(k2_tarski(A_919, B_920), C_921) | ~r2_hidden(B_920, C_921) | r2_hidden(A_919, C_921))), inference(superposition, [status(thm), theory('equality')], [c_2097, c_4])).
% 8.91/3.04  tff(c_9314, plain, (![A_1001, B_1002, C_1003]: (k3_xboole_0(k2_tarski(A_1001, B_1002), C_1003)=k1_tarski(B_1002) | ~r2_hidden(B_1002, C_1003) | r2_hidden(A_1001, C_1003) | B_1002=A_1001)), inference(superposition, [status(thm), theory('equality')], [c_159, c_5473])).
% 8.91/3.04  tff(c_14437, plain, (![B_1094, A_1095, C_1096]: (k3_xboole_0(k2_tarski(B_1094, A_1095), C_1096)=k1_tarski(B_1094) | ~r2_hidden(B_1094, C_1096) | r2_hidden(A_1095, C_1096) | B_1094=A_1095)), inference(superposition, [status(thm), theory('equality')], [c_6, c_9314])).
% 8.91/3.04  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.91/3.04  tff(c_14665, plain, (![C_1097, B_1098, A_1099]: (k3_xboole_0(C_1097, k2_tarski(B_1098, A_1099))=k1_tarski(B_1098) | ~r2_hidden(B_1098, C_1097) | r2_hidden(A_1099, C_1097) | B_1098=A_1099)), inference(superposition, [status(thm), theory('equality')], [c_14437, c_2])).
% 8.91/3.04  tff(c_22, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.91/3.04  tff(c_28, plain, (k3_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 8.91/3.04  tff(c_14817, plain, (~r2_hidden('#skF_1', '#skF_2') | r2_hidden('#skF_3', '#skF_2') | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_14665, c_28])).
% 8.91/3.04  tff(c_14922, plain, (r2_hidden('#skF_3', '#skF_2') | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_14817])).
% 8.91/3.04  tff(c_14923, plain, ('#skF_3'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_29, c_14922])).
% 8.91/3.04  tff(c_4796, plain, (![B_894, C_895, A_896]: (~r2_hidden(B_894, C_895) | k4_xboole_0(k2_tarski(B_894, A_896), C_895)=k1_tarski(A_896) | r2_hidden(A_896, C_895))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2097])).
% 8.91/3.04  tff(c_14, plain, (![A_10, C_12, B_11]: (~r2_hidden(A_10, C_12) | k4_xboole_0(k2_tarski(A_10, B_11), C_12)!=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.91/3.04  tff(c_6203, plain, (![B_941, C_942, A_943]: (~r2_hidden(B_941, C_942) | k1_tarski(B_941)!=k1_tarski(A_943) | ~r2_hidden(B_941, C_942) | r2_hidden(A_943, C_942))), inference(superposition, [status(thm), theory('equality')], [c_4796, c_14])).
% 8.91/3.04  tff(c_6215, plain, (![A_943]: (k1_tarski(A_943)!=k1_tarski('#skF_1') | ~r2_hidden('#skF_1', '#skF_2') | r2_hidden(A_943, '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_6203])).
% 8.91/3.04  tff(c_6226, plain, (![A_944]: (k1_tarski(A_944)!=k1_tarski('#skF_1') | r2_hidden(A_944, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_6215])).
% 8.91/3.04  tff(c_6233, plain, (k1_tarski('#skF_3')!=k1_tarski('#skF_1')), inference(resolution, [status(thm)], [c_6226, c_29])).
% 8.91/3.04  tff(c_14939, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14923, c_6233])).
% 8.91/3.04  tff(c_14940, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_24])).
% 8.91/3.04  tff(c_15022, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14940, c_28])).
% 8.91/3.04  tff(c_15064, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_15058, c_15022])).
% 8.91/3.04  tff(c_15086, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_15064])).
% 8.91/3.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.91/3.04  
% 8.91/3.04  Inference rules
% 8.91/3.04  ----------------------
% 8.91/3.04  #Ref     : 15
% 8.91/3.04  #Sup     : 3278
% 8.91/3.04  #Fact    : 2
% 8.91/3.04  #Define  : 0
% 8.91/3.04  #Split   : 13
% 8.91/3.04  #Chain   : 0
% 8.91/3.04  #Close   : 0
% 8.91/3.04  
% 8.91/3.04  Ordering : KBO
% 8.91/3.04  
% 8.91/3.04  Simplification rules
% 8.91/3.04  ----------------------
% 8.91/3.04  #Subsume      : 992
% 8.91/3.04  #Demod        : 1396
% 8.91/3.04  #Tautology    : 961
% 8.91/3.04  #SimpNegUnit  : 43
% 8.91/3.04  #BackRed      : 9
% 8.91/3.04  
% 8.91/3.04  #Partial instantiations: 770
% 8.91/3.04  #Strategies tried      : 1
% 8.91/3.04  
% 8.91/3.04  Timing (in seconds)
% 8.91/3.04  ----------------------
% 8.91/3.04  Preprocessing        : 0.29
% 8.91/3.04  Parsing              : 0.15
% 8.91/3.04  CNF conversion       : 0.02
% 8.91/3.04  Main loop            : 1.99
% 8.91/3.04  Inferencing          : 0.62
% 8.91/3.04  Reduction            : 0.70
% 8.91/3.04  Demodulation         : 0.54
% 8.91/3.04  BG Simplification    : 0.08
% 8.91/3.04  Subsumption          : 0.46
% 8.91/3.04  Abstraction          : 0.12
% 8.91/3.04  MUC search           : 0.00
% 8.91/3.05  Cooper               : 0.00
% 8.91/3.05  Total                : 2.31
% 8.91/3.05  Index Insertion      : 0.00
% 8.91/3.05  Index Deletion       : 0.00
% 8.91/3.05  Index Matching       : 0.00
% 8.91/3.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
