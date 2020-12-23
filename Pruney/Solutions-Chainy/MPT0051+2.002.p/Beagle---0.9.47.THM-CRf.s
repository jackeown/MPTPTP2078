%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:49 EST 2020

% Result     : Theorem 30.49s
% Output     : CNFRefutation 30.55s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 122 expanded)
%              Number of leaves         :   16 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :   58 ( 145 expanded)
%              Number of equality atoms :   30 (  80 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k4_xboole_0(A,B),C)
       => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_17,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_16,plain,(
    r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_67,plain,(
    ! [A_21,B_22] :
      ( k2_xboole_0(A_21,B_22) = B_22
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_79,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_16,c_67])).

tff(c_19,plain,(
    ! [B_17,A_18] : k2_xboole_0(B_17,A_18) = k2_xboole_0(A_18,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    ! [A_18,B_17] : r1_tarski(A_18,k2_xboole_0(B_17,A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_19,c_12])).

tff(c_84,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_34])).

tff(c_8,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_268,plain,(
    ! [A_30,B_31,C_32] : k4_xboole_0(k4_xboole_0(A_30,B_31),C_32) = k4_xboole_0(A_30,k2_xboole_0(B_31,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2028,plain,(
    ! [C_65,A_66,B_67] : k2_xboole_0(C_65,k4_xboole_0(A_66,k2_xboole_0(B_67,C_65))) = k2_xboole_0(C_65,k4_xboole_0(A_66,B_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_8])).

tff(c_2155,plain,(
    ! [A_66] : k2_xboole_0('#skF_3',k4_xboole_0(A_66,k4_xboole_0('#skF_1','#skF_2'))) = k2_xboole_0('#skF_3',k4_xboole_0(A_66,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_2028])).

tff(c_2193,plain,(
    ! [A_66] : k2_xboole_0('#skF_3',k4_xboole_0(A_66,k4_xboole_0('#skF_1','#skF_2'))) = k2_xboole_0('#skF_3',A_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2155])).

tff(c_78,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k2_xboole_0(A_13,B_14) ),
    inference(resolution,[status(thm)],[c_12,c_67])).

tff(c_2197,plain,(
    ! [A_68] : k2_xboole_0('#skF_3',k4_xboole_0(A_68,k4_xboole_0('#skF_1','#skF_2'))) = k2_xboole_0('#skF_3',A_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2155])).

tff(c_650,plain,(
    ! [A_45,B_46] : k2_xboole_0(A_45,k2_xboole_0(B_46,A_45)) = k2_xboole_0(B_46,A_45) ),
    inference(resolution,[status(thm)],[c_34,c_67])).

tff(c_733,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_650])).

tff(c_2221,plain,(
    ! [A_68] : k2_xboole_0(k4_xboole_0(A_68,k4_xboole_0('#skF_1','#skF_2')),'#skF_3') = k2_xboole_0('#skF_3',k2_xboole_0('#skF_3',A_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2197,c_733])).

tff(c_54271,plain,(
    ! [A_459] : k2_xboole_0(k4_xboole_0(A_459,k4_xboole_0('#skF_1','#skF_2')),'#skF_3') = k2_xboole_0('#skF_3',A_459) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2221])).

tff(c_151,plain,(
    ! [A_25,C_26,B_27] :
      ( r1_tarski(A_25,k2_xboole_0(C_26,B_27))
      | ~ r1_tarski(A_25,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1544,plain,(
    ! [A_60,C_61,B_62] :
      ( k2_xboole_0(A_60,k2_xboole_0(C_61,B_62)) = k2_xboole_0(C_61,B_62)
      | ~ r1_tarski(A_60,B_62) ) ),
    inference(resolution,[status(thm)],[c_151,c_6])).

tff(c_172,plain,(
    ! [A_25,B_2,A_1] :
      ( r1_tarski(A_25,k2_xboole_0(B_2,A_1))
      | ~ r1_tarski(A_25,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_151])).

tff(c_8018,plain,(
    ! [A_123,C_124,B_125,A_126] :
      ( r1_tarski(A_123,k2_xboole_0(C_124,B_125))
      | ~ r1_tarski(A_123,A_126)
      | ~ r1_tarski(A_126,B_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1544,c_172])).

tff(c_8124,plain,(
    ! [C_127,B_128] :
      ( r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k2_xboole_0(C_127,B_128))
      | ~ r1_tarski('#skF_3',B_128) ) ),
    inference(resolution,[status(thm)],[c_16,c_8018])).

tff(c_8230,plain,(
    ! [C_127,B_128] :
      ( k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k2_xboole_0(C_127,B_128)) = k2_xboole_0(C_127,B_128)
      | ~ r1_tarski('#skF_3',B_128) ) ),
    inference(resolution,[status(thm)],[c_8124,c_6])).

tff(c_54499,plain,(
    ! [A_459] :
      ( k2_xboole_0(k4_xboole_0(A_459,k4_xboole_0('#skF_1','#skF_2')),'#skF_3') = k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_3',A_459))
      | ~ r1_tarski('#skF_3','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54271,c_8230])).

tff(c_62699,plain,(
    ! [A_495] : k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_3',A_495)) = k2_xboole_0('#skF_3',A_495) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2193,c_2,c_54499])).

tff(c_84131,plain,(
    ! [B_608] : k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k2_xboole_0(B_608,'#skF_3')) = k2_xboole_0('#skF_3',B_608) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_62699])).

tff(c_2133,plain,(
    ! [A_13,B_14,A_66] : k2_xboole_0(k2_xboole_0(A_13,B_14),k4_xboole_0(A_66,k2_xboole_0(A_13,B_14))) = k2_xboole_0(k2_xboole_0(A_13,B_14),k4_xboole_0(A_66,A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_2028])).

tff(c_8259,plain,(
    ! [A_129,B_130,A_131] : k2_xboole_0(k2_xboole_0(A_129,B_130),k4_xboole_0(A_131,A_129)) = k2_xboole_0(k2_xboole_0(A_129,B_130),A_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2133])).

tff(c_8420,plain,(
    ! [A_131,A_129,B_130] : k2_xboole_0(k4_xboole_0(A_131,A_129),k2_xboole_0(A_129,B_130)) = k2_xboole_0(k2_xboole_0(A_129,B_130),A_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_8259,c_2])).

tff(c_84169,plain,(
    k2_xboole_0(k2_xboole_0('#skF_2','#skF_3'),'#skF_1') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_84131,c_8420])).

tff(c_84955,plain,(
    k2_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k2_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_84169])).

tff(c_86487,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_84955,c_12])).

tff(c_86657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17,c_86487])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 30.49/21.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.49/21.52  
% 30.49/21.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.49/21.52  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 30.49/21.52  
% 30.49/21.52  %Foreground sorts:
% 30.49/21.52  
% 30.49/21.52  
% 30.49/21.52  %Background operators:
% 30.49/21.52  
% 30.49/21.52  
% 30.49/21.52  %Foreground operators:
% 30.49/21.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.49/21.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 30.49/21.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 30.49/21.52  tff('#skF_2', type, '#skF_2': $i).
% 30.49/21.52  tff('#skF_3', type, '#skF_3': $i).
% 30.49/21.52  tff('#skF_1', type, '#skF_1': $i).
% 30.49/21.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.49/21.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.49/21.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 30.49/21.52  
% 30.55/21.53  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 30.55/21.53  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 30.55/21.53  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 30.55/21.53  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 30.55/21.53  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 30.55/21.53  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 30.55/21.53  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 30.55/21.53  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 30.55/21.53  tff(c_14, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 30.55/21.53  tff(c_17, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 30.55/21.53  tff(c_16, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 30.55/21.53  tff(c_67, plain, (![A_21, B_22]: (k2_xboole_0(A_21, B_22)=B_22 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 30.55/21.53  tff(c_79, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_16, c_67])).
% 30.55/21.53  tff(c_19, plain, (![B_17, A_18]: (k2_xboole_0(B_17, A_18)=k2_xboole_0(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_27])).
% 30.55/21.53  tff(c_12, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 30.55/21.53  tff(c_34, plain, (![A_18, B_17]: (r1_tarski(A_18, k2_xboole_0(B_17, A_18)))), inference(superposition, [status(thm), theory('equality')], [c_19, c_12])).
% 30.55/21.53  tff(c_84, plain, (r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_79, c_34])).
% 30.55/21.53  tff(c_8, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 30.55/21.53  tff(c_268, plain, (![A_30, B_31, C_32]: (k4_xboole_0(k4_xboole_0(A_30, B_31), C_32)=k4_xboole_0(A_30, k2_xboole_0(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 30.55/21.53  tff(c_2028, plain, (![C_65, A_66, B_67]: (k2_xboole_0(C_65, k4_xboole_0(A_66, k2_xboole_0(B_67, C_65)))=k2_xboole_0(C_65, k4_xboole_0(A_66, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_268, c_8])).
% 30.55/21.53  tff(c_2155, plain, (![A_66]: (k2_xboole_0('#skF_3', k4_xboole_0(A_66, k4_xboole_0('#skF_1', '#skF_2')))=k2_xboole_0('#skF_3', k4_xboole_0(A_66, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_79, c_2028])).
% 30.55/21.53  tff(c_2193, plain, (![A_66]: (k2_xboole_0('#skF_3', k4_xboole_0(A_66, k4_xboole_0('#skF_1', '#skF_2')))=k2_xboole_0('#skF_3', A_66))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2155])).
% 30.55/21.53  tff(c_78, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k2_xboole_0(A_13, B_14))), inference(resolution, [status(thm)], [c_12, c_67])).
% 30.55/21.53  tff(c_2197, plain, (![A_68]: (k2_xboole_0('#skF_3', k4_xboole_0(A_68, k4_xboole_0('#skF_1', '#skF_2')))=k2_xboole_0('#skF_3', A_68))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2155])).
% 30.55/21.53  tff(c_650, plain, (![A_45, B_46]: (k2_xboole_0(A_45, k2_xboole_0(B_46, A_45))=k2_xboole_0(B_46, A_45))), inference(resolution, [status(thm)], [c_34, c_67])).
% 30.55/21.53  tff(c_733, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_650])).
% 30.55/21.53  tff(c_2221, plain, (![A_68]: (k2_xboole_0(k4_xboole_0(A_68, k4_xboole_0('#skF_1', '#skF_2')), '#skF_3')=k2_xboole_0('#skF_3', k2_xboole_0('#skF_3', A_68)))), inference(superposition, [status(thm), theory('equality')], [c_2197, c_733])).
% 30.55/21.53  tff(c_54271, plain, (![A_459]: (k2_xboole_0(k4_xboole_0(A_459, k4_xboole_0('#skF_1', '#skF_2')), '#skF_3')=k2_xboole_0('#skF_3', A_459))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2221])).
% 30.55/21.53  tff(c_151, plain, (![A_25, C_26, B_27]: (r1_tarski(A_25, k2_xboole_0(C_26, B_27)) | ~r1_tarski(A_25, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 30.55/21.53  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 30.55/21.53  tff(c_1544, plain, (![A_60, C_61, B_62]: (k2_xboole_0(A_60, k2_xboole_0(C_61, B_62))=k2_xboole_0(C_61, B_62) | ~r1_tarski(A_60, B_62))), inference(resolution, [status(thm)], [c_151, c_6])).
% 30.55/21.53  tff(c_172, plain, (![A_25, B_2, A_1]: (r1_tarski(A_25, k2_xboole_0(B_2, A_1)) | ~r1_tarski(A_25, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_151])).
% 30.55/21.53  tff(c_8018, plain, (![A_123, C_124, B_125, A_126]: (r1_tarski(A_123, k2_xboole_0(C_124, B_125)) | ~r1_tarski(A_123, A_126) | ~r1_tarski(A_126, B_125))), inference(superposition, [status(thm), theory('equality')], [c_1544, c_172])).
% 30.55/21.53  tff(c_8124, plain, (![C_127, B_128]: (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k2_xboole_0(C_127, B_128)) | ~r1_tarski('#skF_3', B_128))), inference(resolution, [status(thm)], [c_16, c_8018])).
% 30.55/21.53  tff(c_8230, plain, (![C_127, B_128]: (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k2_xboole_0(C_127, B_128))=k2_xboole_0(C_127, B_128) | ~r1_tarski('#skF_3', B_128))), inference(resolution, [status(thm)], [c_8124, c_6])).
% 30.55/21.53  tff(c_54499, plain, (![A_459]: (k2_xboole_0(k4_xboole_0(A_459, k4_xboole_0('#skF_1', '#skF_2')), '#skF_3')=k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_3', A_459)) | ~r1_tarski('#skF_3', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_54271, c_8230])).
% 30.55/21.53  tff(c_62699, plain, (![A_495]: (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_3', A_495))=k2_xboole_0('#skF_3', A_495))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2193, c_2, c_54499])).
% 30.55/21.53  tff(c_84131, plain, (![B_608]: (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k2_xboole_0(B_608, '#skF_3'))=k2_xboole_0('#skF_3', B_608))), inference(superposition, [status(thm), theory('equality')], [c_2, c_62699])).
% 30.55/21.53  tff(c_2133, plain, (![A_13, B_14, A_66]: (k2_xboole_0(k2_xboole_0(A_13, B_14), k4_xboole_0(A_66, k2_xboole_0(A_13, B_14)))=k2_xboole_0(k2_xboole_0(A_13, B_14), k4_xboole_0(A_66, A_13)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_2028])).
% 30.55/21.53  tff(c_8259, plain, (![A_129, B_130, A_131]: (k2_xboole_0(k2_xboole_0(A_129, B_130), k4_xboole_0(A_131, A_129))=k2_xboole_0(k2_xboole_0(A_129, B_130), A_131))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2133])).
% 30.55/21.53  tff(c_8420, plain, (![A_131, A_129, B_130]: (k2_xboole_0(k4_xboole_0(A_131, A_129), k2_xboole_0(A_129, B_130))=k2_xboole_0(k2_xboole_0(A_129, B_130), A_131))), inference(superposition, [status(thm), theory('equality')], [c_8259, c_2])).
% 30.55/21.53  tff(c_84169, plain, (k2_xboole_0(k2_xboole_0('#skF_2', '#skF_3'), '#skF_1')=k2_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_84131, c_8420])).
% 30.55/21.53  tff(c_84955, plain, (k2_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k2_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_84169])).
% 30.55/21.53  tff(c_86487, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_84955, c_12])).
% 30.55/21.53  tff(c_86657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17, c_86487])).
% 30.55/21.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.55/21.53  
% 30.55/21.53  Inference rules
% 30.55/21.53  ----------------------
% 30.55/21.53  #Ref     : 0
% 30.55/21.53  #Sup     : 23065
% 30.55/21.53  #Fact    : 0
% 30.55/21.53  #Define  : 0
% 30.55/21.53  #Split   : 3
% 30.55/21.53  #Chain   : 0
% 30.55/21.53  #Close   : 0
% 30.55/21.53  
% 30.55/21.53  Ordering : KBO
% 30.55/21.53  
% 30.55/21.53  Simplification rules
% 30.55/21.53  ----------------------
% 30.55/21.53  #Subsume      : 2633
% 30.55/21.53  #Demod        : 22619
% 30.55/21.53  #Tautology    : 7564
% 30.55/21.53  #SimpNegUnit  : 1
% 30.55/21.53  #BackRed      : 3
% 30.55/21.53  
% 30.55/21.53  #Partial instantiations: 0
% 30.55/21.53  #Strategies tried      : 1
% 30.55/21.53  
% 30.55/21.53  Timing (in seconds)
% 30.55/21.53  ----------------------
% 30.55/21.54  Preprocessing        : 0.28
% 30.55/21.54  Parsing              : 0.15
% 30.55/21.54  CNF conversion       : 0.02
% 30.55/21.54  Main loop            : 20.44
% 30.55/21.54  Inferencing          : 1.85
% 30.55/21.54  Reduction            : 13.26
% 30.55/21.54  Demodulation         : 12.46
% 30.55/21.54  BG Simplification    : 0.32
% 30.55/21.54  Subsumption          : 4.30
% 30.55/21.54  Abstraction          : 0.50
% 30.55/21.54  MUC search           : 0.00
% 30.55/21.54  Cooper               : 0.00
% 30.55/21.54  Total                : 20.75
% 30.55/21.54  Index Insertion      : 0.00
% 30.55/21.54  Index Deletion       : 0.00
% 30.55/21.54  Index Matching       : 0.00
% 30.55/21.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
