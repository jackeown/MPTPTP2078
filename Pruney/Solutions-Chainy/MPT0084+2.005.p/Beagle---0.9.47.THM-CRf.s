%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:05 EST 2020

% Result     : Theorem 8.30s
% Output     : CNFRefutation 8.30s
% Verified   : 
% Statistics : Number of formulae       :   51 (  80 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   61 ( 105 expanded)
%              Number of equality atoms :   32 (  55 expanded)
%              Maximal formula depth    :    8 (   3 average)
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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(c_92,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(A_26,B_27)
      | k3_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_100,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_92,c_28])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_83,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_87,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_83])).

tff(c_225,plain,(
    ! [A_41,B_42,C_43] : k2_xboole_0(k4_xboole_0(A_41,B_42),k4_xboole_0(A_41,C_43)) = k4_xboole_0(A_41,k3_xboole_0(B_42,C_43)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_273,plain,(
    ! [B_42] : k4_xboole_0('#skF_1',k3_xboole_0(B_42,'#skF_3')) = k2_xboole_0(k4_xboole_0('#skF_1',B_42),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_225])).

tff(c_401,plain,(
    ! [B_48] : k4_xboole_0('#skF_1',k3_xboole_0(B_48,'#skF_3')) = k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',B_48)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_273])).

tff(c_16,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_9084,plain,(
    ! [B_176] : k4_xboole_0('#skF_1',k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',B_176))) = k3_xboole_0('#skF_1',k3_xboole_0(B_176,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_16])).

tff(c_355,plain,(
    ! [C_47] : k4_xboole_0('#skF_1',k3_xboole_0('#skF_3',C_47)) = k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',C_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_225])).

tff(c_373,plain,(
    ! [C_47] : k4_xboole_0('#skF_1',k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',C_47))) = k3_xboole_0('#skF_1',k3_xboole_0('#skF_3',C_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_16])).

tff(c_9297,plain,(
    ! [B_177] : k3_xboole_0('#skF_1',k3_xboole_0(B_177,'#skF_3')) = k3_xboole_0('#skF_1',k3_xboole_0('#skF_3',B_177)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9084,c_373])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_63,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_xboole_0(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_63])).

tff(c_9393,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_9297,c_70])).

tff(c_20,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_132,plain,(
    ! [A_32,B_33,C_34] :
      ( r1_tarski(A_32,B_33)
      | ~ r1_xboole_0(A_32,C_34)
      | ~ r1_tarski(A_32,k2_xboole_0(B_33,C_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_937,plain,(
    ! [A_61,B_62,C_63] :
      ( r1_tarski(A_61,B_62)
      | ~ r1_xboole_0(A_61,C_63)
      | k4_xboole_0(A_61,k2_xboole_0(B_62,C_63)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_132])).

tff(c_2582,plain,(
    ! [A_101,A_102,B_103] :
      ( r1_tarski(A_101,A_102)
      | ~ r1_xboole_0(A_101,B_103)
      | k4_xboole_0(A_101,k2_xboole_0(B_103,A_102)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_937])).

tff(c_2597,plain,(
    ! [C_47] :
      ( r1_tarski('#skF_1',k4_xboole_0('#skF_1',C_47))
      | ~ r1_xboole_0('#skF_1',k1_xboole_0)
      | k3_xboole_0('#skF_1',k3_xboole_0('#skF_3',C_47)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_2582])).

tff(c_4238,plain,(
    ! [C_126] :
      ( r1_tarski('#skF_1',k4_xboole_0('#skF_1',C_126))
      | k3_xboole_0('#skF_1',k3_xboole_0('#skF_3',C_126)) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2597])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4245,plain,(
    ! [C_126] :
      ( k4_xboole_0('#skF_1',k4_xboole_0('#skF_1',C_126)) = k1_xboole_0
      | k3_xboole_0('#skF_1',k3_xboole_0('#skF_3',C_126)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4238,c_14])).

tff(c_4314,plain,(
    ! [C_126] :
      ( k3_xboole_0('#skF_1',C_126) = k1_xboole_0
      | k3_xboole_0('#skF_1',k3_xboole_0('#skF_3',C_126)) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_4245])).

tff(c_9460,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_9393,c_4314])).

tff(c_9497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_9460])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:20:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.30/3.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.30/3.21  
% 8.30/3.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.30/3.21  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.30/3.21  
% 8.30/3.21  %Foreground sorts:
% 8.30/3.21  
% 8.30/3.21  
% 8.30/3.21  %Background operators:
% 8.30/3.21  
% 8.30/3.21  
% 8.30/3.21  %Foreground operators:
% 8.30/3.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.30/3.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.30/3.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.30/3.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.30/3.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.30/3.21  tff('#skF_2', type, '#skF_2': $i).
% 8.30/3.21  tff('#skF_3', type, '#skF_3': $i).
% 8.30/3.21  tff('#skF_1', type, '#skF_1': $i).
% 8.30/3.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.30/3.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.30/3.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.30/3.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.30/3.21  
% 8.30/3.22  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.30/3.22  tff(f_60, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 8.30/3.22  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.30/3.22  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 8.30/3.22  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_xboole_1)).
% 8.30/3.22  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.30/3.22  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.30/3.22  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 8.30/3.22  tff(c_92, plain, (![A_26, B_27]: (r1_xboole_0(A_26, B_27) | k3_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.30/3.22  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.30/3.22  tff(c_100, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_92, c_28])).
% 8.30/3.22  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.30/3.22  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.30/3.22  tff(c_83, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.30/3.22  tff(c_87, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_83])).
% 8.30/3.22  tff(c_225, plain, (![A_41, B_42, C_43]: (k2_xboole_0(k4_xboole_0(A_41, B_42), k4_xboole_0(A_41, C_43))=k4_xboole_0(A_41, k3_xboole_0(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.30/3.22  tff(c_273, plain, (![B_42]: (k4_xboole_0('#skF_1', k3_xboole_0(B_42, '#skF_3'))=k2_xboole_0(k4_xboole_0('#skF_1', B_42), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_87, c_225])).
% 8.30/3.22  tff(c_401, plain, (![B_48]: (k4_xboole_0('#skF_1', k3_xboole_0(B_48, '#skF_3'))=k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', B_48)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_273])).
% 8.30/3.22  tff(c_16, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.30/3.22  tff(c_9084, plain, (![B_176]: (k4_xboole_0('#skF_1', k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', B_176)))=k3_xboole_0('#skF_1', k3_xboole_0(B_176, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_401, c_16])).
% 8.30/3.22  tff(c_355, plain, (![C_47]: (k4_xboole_0('#skF_1', k3_xboole_0('#skF_3', C_47))=k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', C_47)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_225])).
% 8.30/3.22  tff(c_373, plain, (![C_47]: (k4_xboole_0('#skF_1', k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', C_47)))=k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', C_47)))), inference(superposition, [status(thm), theory('equality')], [c_355, c_16])).
% 8.30/3.22  tff(c_9297, plain, (![B_177]: (k3_xboole_0('#skF_1', k3_xboole_0(B_177, '#skF_3'))=k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', B_177)))), inference(superposition, [status(thm), theory('equality')], [c_9084, c_373])).
% 8.30/3.22  tff(c_24, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.30/3.22  tff(c_63, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=k1_xboole_0 | ~r1_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.30/3.22  tff(c_70, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_63])).
% 8.30/3.22  tff(c_9393, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_9297, c_70])).
% 8.30/3.22  tff(c_20, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.30/3.22  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.30/3.22  tff(c_132, plain, (![A_32, B_33, C_34]: (r1_tarski(A_32, B_33) | ~r1_xboole_0(A_32, C_34) | ~r1_tarski(A_32, k2_xboole_0(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.30/3.22  tff(c_937, plain, (![A_61, B_62, C_63]: (r1_tarski(A_61, B_62) | ~r1_xboole_0(A_61, C_63) | k4_xboole_0(A_61, k2_xboole_0(B_62, C_63))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_132])).
% 8.30/3.22  tff(c_2582, plain, (![A_101, A_102, B_103]: (r1_tarski(A_101, A_102) | ~r1_xboole_0(A_101, B_103) | k4_xboole_0(A_101, k2_xboole_0(B_103, A_102))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_937])).
% 8.30/3.22  tff(c_2597, plain, (![C_47]: (r1_tarski('#skF_1', k4_xboole_0('#skF_1', C_47)) | ~r1_xboole_0('#skF_1', k1_xboole_0) | k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', C_47))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_373, c_2582])).
% 8.30/3.22  tff(c_4238, plain, (![C_126]: (r1_tarski('#skF_1', k4_xboole_0('#skF_1', C_126)) | k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', C_126))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2597])).
% 8.30/3.22  tff(c_14, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.30/3.22  tff(c_4245, plain, (![C_126]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_1', C_126))=k1_xboole_0 | k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', C_126))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4238, c_14])).
% 8.30/3.22  tff(c_4314, plain, (![C_126]: (k3_xboole_0('#skF_1', C_126)=k1_xboole_0 | k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', C_126))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_4245])).
% 8.30/3.22  tff(c_9460, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_9393, c_4314])).
% 8.30/3.22  tff(c_9497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_9460])).
% 8.30/3.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.30/3.22  
% 8.30/3.22  Inference rules
% 8.30/3.22  ----------------------
% 8.30/3.22  #Ref     : 0
% 8.30/3.22  #Sup     : 2399
% 8.30/3.22  #Fact    : 0
% 8.30/3.22  #Define  : 0
% 8.30/3.22  #Split   : 2
% 8.30/3.22  #Chain   : 0
% 8.30/3.22  #Close   : 0
% 8.30/3.22  
% 8.30/3.22  Ordering : KBO
% 8.30/3.22  
% 8.30/3.22  Simplification rules
% 8.30/3.22  ----------------------
% 8.30/3.22  #Subsume      : 307
% 8.30/3.22  #Demod        : 2666
% 8.30/3.22  #Tautology    : 1092
% 8.30/3.22  #SimpNegUnit  : 17
% 8.30/3.22  #BackRed      : 9
% 8.30/3.22  
% 8.30/3.22  #Partial instantiations: 0
% 8.30/3.22  #Strategies tried      : 1
% 8.30/3.22  
% 8.30/3.22  Timing (in seconds)
% 8.30/3.22  ----------------------
% 8.30/3.22  Preprocessing        : 0.43
% 8.30/3.22  Parsing              : 0.23
% 8.30/3.22  CNF conversion       : 0.03
% 8.30/3.22  Main loop            : 1.87
% 8.30/3.22  Inferencing          : 0.55
% 8.30/3.22  Reduction            : 0.85
% 8.30/3.22  Demodulation         : 0.71
% 8.30/3.22  BG Simplification    : 0.07
% 8.30/3.22  Subsumption          : 0.32
% 8.30/3.22  Abstraction          : 0.08
% 8.30/3.22  MUC search           : 0.00
% 8.30/3.22  Cooper               : 0.00
% 8.30/3.22  Total                : 2.34
% 8.30/3.22  Index Insertion      : 0.00
% 8.30/3.22  Index Deletion       : 0.00
% 8.30/3.22  Index Matching       : 0.00
% 8.30/3.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
