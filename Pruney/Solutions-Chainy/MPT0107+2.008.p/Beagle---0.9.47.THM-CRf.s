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
% DateTime   : Thu Dec  3 09:44:53 EST 2020

% Result     : Theorem 12.20s
% Output     : CNFRefutation 12.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 110 expanded)
%              Number of leaves         :   21 (  45 expanded)
%              Depth                    :   16
%              Number of atoms          :   58 ( 120 expanded)
%              Number of equality atoms :   34 (  75 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_14,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_145,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = k4_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    ! [A_27,B_28] : k5_xboole_0(A_27,k4_xboole_0(B_28,A_27)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_154,plain,(
    ! [A_48,B_49] : k5_xboole_0(k3_xboole_0(A_48,B_49),k4_xboole_0(A_48,B_49)) = k2_xboole_0(k3_xboole_0(A_48,B_49),A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_28])).

tff(c_162,plain,(
    ! [A_48,B_49] : k5_xboole_0(k3_xboole_0(A_48,B_49),k4_xboole_0(A_48,B_49)) = k2_xboole_0(A_48,k3_xboole_0(A_48,B_49)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_154])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_190,plain,(
    ! [A_52,B_53] :
      ( k2_xboole_0(A_52,k4_xboole_0(B_53,A_52)) = B_53
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_199,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(k3_xboole_0(A_13,B_14),k4_xboole_0(A_13,B_14)) = A_13
      | ~ r1_tarski(k3_xboole_0(A_13,B_14),A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_190])).

tff(c_206,plain,(
    ! [A_13,B_14] : k2_xboole_0(k3_xboole_0(A_13,B_14),k4_xboole_0(A_13,B_14)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_199])).

tff(c_444,plain,(
    ! [A_70,B_71] : k4_xboole_0(k2_xboole_0(A_70,B_71),k3_xboole_0(A_70,B_71)) = k5_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_486,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),k3_xboole_0(B_2,A_1)) = k5_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_444])).

tff(c_16,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_109,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k4_xboole_0(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_118,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,k4_xboole_0(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_109])).

tff(c_848,plain,(
    ! [A_86,B_87] : k3_xboole_0(A_86,k4_xboole_0(A_86,B_87)) = k4_xboole_0(A_86,B_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_118])).

tff(c_917,plain,(
    ! [A_88,B_89] : r1_tarski(k4_xboole_0(A_88,B_89),A_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_848,c_8])).

tff(c_951,plain,(
    ! [B_92,A_93] : r1_tarski(k5_xboole_0(B_92,A_93),k2_xboole_0(A_93,B_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_917])).

tff(c_137,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_xboole_0(A_45,k4_xboole_0(C_46,B_47))
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = A_17
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_144,plain,(
    ! [A_45,C_46,B_47] :
      ( k4_xboole_0(A_45,k4_xboole_0(C_46,B_47)) = A_45
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(resolution,[status(thm)],[c_137,c_18])).

tff(c_929,plain,(
    ! [A_45,B_47] :
      ( r1_tarski(A_45,A_45)
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_917])).

tff(c_1172,plain,(
    ! [B_100,A_101] : r1_tarski(k5_xboole_0(B_100,A_101),k5_xboole_0(B_100,A_101)) ),
    inference(resolution,[status(thm)],[c_951,c_929])).

tff(c_1219,plain,(
    ! [A_27,B_28] : r1_tarski(k5_xboole_0(A_27,k4_xboole_0(B_28,A_27)),k2_xboole_0(A_27,B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1172])).

tff(c_1463,plain,(
    ! [A_106,B_107] : r1_tarski(k2_xboole_0(A_106,B_107),k2_xboole_0(A_106,B_107)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1219])).

tff(c_1471,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(k3_xboole_0(A_13,B_14),k4_xboole_0(A_13,B_14))) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_1463])).

tff(c_1496,plain,(
    ! [A_13] : r1_tarski(A_13,A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_1471])).

tff(c_228,plain,(
    ! [A_56,C_57,B_58] :
      ( k4_xboole_0(A_56,k4_xboole_0(C_57,B_58)) = A_56
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(resolution,[status(thm)],[c_137,c_18])).

tff(c_14588,plain,(
    ! [A_252,A_253,B_254] :
      ( k4_xboole_0(A_252,k3_xboole_0(A_253,B_254)) = A_252
      | ~ r1_tarski(A_252,k4_xboole_0(A_253,B_254)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_228])).

tff(c_14657,plain,(
    ! [A_255,B_256] : k4_xboole_0(k4_xboole_0(A_255,B_256),k3_xboole_0(A_255,B_256)) = k4_xboole_0(A_255,B_256) ),
    inference(resolution,[status(thm)],[c_1496,c_14588])).

tff(c_14736,plain,(
    ! [A_255,B_256] : k5_xboole_0(k3_xboole_0(A_255,B_256),k4_xboole_0(A_255,B_256)) = k2_xboole_0(k3_xboole_0(A_255,B_256),k4_xboole_0(A_255,B_256)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14657,c_28])).

tff(c_14867,plain,(
    ! [A_257,B_258] : k2_xboole_0(A_257,k3_xboole_0(A_257,B_258)) = A_257 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_206,c_14736])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(k2_xboole_0(A_5,B_6),k3_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14960,plain,(
    ! [A_257,B_258] : k4_xboole_0(A_257,k3_xboole_0(A_257,k3_xboole_0(A_257,B_258))) = k5_xboole_0(A_257,k3_xboole_0(A_257,B_258)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14867,c_6])).

tff(c_15044,plain,(
    ! [A_257,B_258] : k5_xboole_0(A_257,k3_xboole_0(A_257,B_258)) = k4_xboole_0(A_257,B_258) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_14960])).

tff(c_30,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15044,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:21:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.20/5.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.20/5.05  
% 12.20/5.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.20/5.05  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 12.20/5.05  
% 12.20/5.05  %Foreground sorts:
% 12.20/5.05  
% 12.20/5.05  
% 12.20/5.05  %Background operators:
% 12.20/5.05  
% 12.20/5.05  
% 12.20/5.05  %Foreground operators:
% 12.20/5.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.20/5.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.20/5.05  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.20/5.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.20/5.05  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.20/5.05  tff('#skF_2', type, '#skF_2': $i).
% 12.20/5.05  tff('#skF_1', type, '#skF_1': $i).
% 12.20/5.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.20/5.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.20/5.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.20/5.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.20/5.05  
% 12.20/5.07  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 12.20/5.07  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.20/5.07  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 12.20/5.07  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 12.20/5.07  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 12.20/5.07  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 12.20/5.07  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.20/5.07  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 12.20/5.07  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 12.20/5.07  tff(f_62, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.20/5.07  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.20/5.07  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.20/5.07  tff(c_145, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k3_xboole_0(A_48, B_49))=k4_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.20/5.07  tff(c_28, plain, (![A_27, B_28]: (k5_xboole_0(A_27, k4_xboole_0(B_28, A_27))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.20/5.07  tff(c_154, plain, (![A_48, B_49]: (k5_xboole_0(k3_xboole_0(A_48, B_49), k4_xboole_0(A_48, B_49))=k2_xboole_0(k3_xboole_0(A_48, B_49), A_48))), inference(superposition, [status(thm), theory('equality')], [c_145, c_28])).
% 12.20/5.07  tff(c_162, plain, (![A_48, B_49]: (k5_xboole_0(k3_xboole_0(A_48, B_49), k4_xboole_0(A_48, B_49))=k2_xboole_0(A_48, k3_xboole_0(A_48, B_49)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_154])).
% 12.20/5.07  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.20/5.07  tff(c_190, plain, (![A_52, B_53]: (k2_xboole_0(A_52, k4_xboole_0(B_53, A_52))=B_53 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.20/5.07  tff(c_199, plain, (![A_13, B_14]: (k2_xboole_0(k3_xboole_0(A_13, B_14), k4_xboole_0(A_13, B_14))=A_13 | ~r1_tarski(k3_xboole_0(A_13, B_14), A_13))), inference(superposition, [status(thm), theory('equality')], [c_14, c_190])).
% 12.20/5.07  tff(c_206, plain, (![A_13, B_14]: (k2_xboole_0(k3_xboole_0(A_13, B_14), k4_xboole_0(A_13, B_14))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_199])).
% 12.20/5.07  tff(c_444, plain, (![A_70, B_71]: (k4_xboole_0(k2_xboole_0(A_70, B_71), k3_xboole_0(A_70, B_71))=k5_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.20/5.07  tff(c_486, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), k3_xboole_0(B_2, A_1))=k5_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_444])).
% 12.20/5.07  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.20/5.07  tff(c_109, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k4_xboole_0(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.20/5.07  tff(c_118, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k3_xboole_0(A_15, k4_xboole_0(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_109])).
% 12.20/5.07  tff(c_848, plain, (![A_86, B_87]: (k3_xboole_0(A_86, k4_xboole_0(A_86, B_87))=k4_xboole_0(A_86, B_87))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_118])).
% 12.20/5.07  tff(c_917, plain, (![A_88, B_89]: (r1_tarski(k4_xboole_0(A_88, B_89), A_88))), inference(superposition, [status(thm), theory('equality')], [c_848, c_8])).
% 12.20/5.07  tff(c_951, plain, (![B_92, A_93]: (r1_tarski(k5_xboole_0(B_92, A_93), k2_xboole_0(A_93, B_92)))), inference(superposition, [status(thm), theory('equality')], [c_486, c_917])).
% 12.20/5.07  tff(c_137, plain, (![A_45, C_46, B_47]: (r1_xboole_0(A_45, k4_xboole_0(C_46, B_47)) | ~r1_tarski(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.20/5.07  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=A_17 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.20/5.07  tff(c_144, plain, (![A_45, C_46, B_47]: (k4_xboole_0(A_45, k4_xboole_0(C_46, B_47))=A_45 | ~r1_tarski(A_45, B_47))), inference(resolution, [status(thm)], [c_137, c_18])).
% 12.20/5.07  tff(c_929, plain, (![A_45, B_47]: (r1_tarski(A_45, A_45) | ~r1_tarski(A_45, B_47))), inference(superposition, [status(thm), theory('equality')], [c_144, c_917])).
% 12.20/5.07  tff(c_1172, plain, (![B_100, A_101]: (r1_tarski(k5_xboole_0(B_100, A_101), k5_xboole_0(B_100, A_101)))), inference(resolution, [status(thm)], [c_951, c_929])).
% 12.20/5.07  tff(c_1219, plain, (![A_27, B_28]: (r1_tarski(k5_xboole_0(A_27, k4_xboole_0(B_28, A_27)), k2_xboole_0(A_27, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1172])).
% 12.20/5.07  tff(c_1463, plain, (![A_106, B_107]: (r1_tarski(k2_xboole_0(A_106, B_107), k2_xboole_0(A_106, B_107)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1219])).
% 12.20/5.07  tff(c_1471, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(k3_xboole_0(A_13, B_14), k4_xboole_0(A_13, B_14))))), inference(superposition, [status(thm), theory('equality')], [c_206, c_1463])).
% 12.20/5.07  tff(c_1496, plain, (![A_13]: (r1_tarski(A_13, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_1471])).
% 12.20/5.07  tff(c_228, plain, (![A_56, C_57, B_58]: (k4_xboole_0(A_56, k4_xboole_0(C_57, B_58))=A_56 | ~r1_tarski(A_56, B_58))), inference(resolution, [status(thm)], [c_137, c_18])).
% 12.20/5.07  tff(c_14588, plain, (![A_252, A_253, B_254]: (k4_xboole_0(A_252, k3_xboole_0(A_253, B_254))=A_252 | ~r1_tarski(A_252, k4_xboole_0(A_253, B_254)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_228])).
% 12.20/5.07  tff(c_14657, plain, (![A_255, B_256]: (k4_xboole_0(k4_xboole_0(A_255, B_256), k3_xboole_0(A_255, B_256))=k4_xboole_0(A_255, B_256))), inference(resolution, [status(thm)], [c_1496, c_14588])).
% 12.20/5.07  tff(c_14736, plain, (![A_255, B_256]: (k5_xboole_0(k3_xboole_0(A_255, B_256), k4_xboole_0(A_255, B_256))=k2_xboole_0(k3_xboole_0(A_255, B_256), k4_xboole_0(A_255, B_256)))), inference(superposition, [status(thm), theory('equality')], [c_14657, c_28])).
% 12.20/5.07  tff(c_14867, plain, (![A_257, B_258]: (k2_xboole_0(A_257, k3_xboole_0(A_257, B_258))=A_257)), inference(demodulation, [status(thm), theory('equality')], [c_162, c_206, c_14736])).
% 12.20/5.07  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(k2_xboole_0(A_5, B_6), k3_xboole_0(A_5, B_6))=k5_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.20/5.07  tff(c_14960, plain, (![A_257, B_258]: (k4_xboole_0(A_257, k3_xboole_0(A_257, k3_xboole_0(A_257, B_258)))=k5_xboole_0(A_257, k3_xboole_0(A_257, B_258)))), inference(superposition, [status(thm), theory('equality')], [c_14867, c_6])).
% 12.20/5.07  tff(c_15044, plain, (![A_257, B_258]: (k5_xboole_0(A_257, k3_xboole_0(A_257, B_258))=k4_xboole_0(A_257, B_258))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_14960])).
% 12.20/5.07  tff(c_30, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.20/5.07  tff(c_16354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15044, c_30])).
% 12.20/5.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.20/5.07  
% 12.20/5.07  Inference rules
% 12.20/5.07  ----------------------
% 12.20/5.07  #Ref     : 1
% 12.20/5.07  #Sup     : 4240
% 12.20/5.07  #Fact    : 0
% 12.20/5.07  #Define  : 0
% 12.20/5.07  #Split   : 0
% 12.20/5.07  #Chain   : 0
% 12.20/5.07  #Close   : 0
% 12.20/5.07  
% 12.20/5.07  Ordering : KBO
% 12.20/5.07  
% 12.20/5.07  Simplification rules
% 12.20/5.07  ----------------------
% 12.20/5.07  #Subsume      : 244
% 12.20/5.07  #Demod        : 6105
% 12.20/5.07  #Tautology    : 1272
% 12.20/5.07  #SimpNegUnit  : 0
% 12.20/5.07  #BackRed      : 10
% 12.20/5.07  
% 12.20/5.07  #Partial instantiations: 0
% 12.20/5.07  #Strategies tried      : 1
% 12.20/5.07  
% 12.20/5.07  Timing (in seconds)
% 12.20/5.07  ----------------------
% 12.35/5.07  Preprocessing        : 0.31
% 12.35/5.07  Parsing              : 0.17
% 12.35/5.07  CNF conversion       : 0.02
% 12.35/5.07  Main loop            : 3.91
% 12.35/5.07  Inferencing          : 0.67
% 12.35/5.07  Reduction            : 2.61
% 12.35/5.07  Demodulation         : 2.43
% 12.35/5.07  BG Simplification    : 0.11
% 12.35/5.07  Subsumption          : 0.39
% 12.35/5.07  Abstraction          : 0.19
% 12.35/5.07  MUC search           : 0.00
% 12.35/5.07  Cooper               : 0.00
% 12.35/5.07  Total                : 4.25
% 12.35/5.07  Index Insertion      : 0.00
% 12.35/5.07  Index Deletion       : 0.00
% 12.35/5.07  Index Matching       : 0.00
% 12.35/5.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
