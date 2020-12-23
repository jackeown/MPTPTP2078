%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:58 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   47 (  81 expanded)
%              Number of leaves         :   19 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   40 (  82 expanded)
%              Number of equality atoms :   32 (  61 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
          & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_46,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_xboole_0(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_50,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_46])).

tff(c_163,plain,(
    ! [A_31,B_32,C_33] : k4_xboole_0(k3_xboole_0(A_31,B_32),C_33) = k3_xboole_0(A_31,k4_xboole_0(B_32,C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_210,plain,(
    ! [C_33] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_33)) = k4_xboole_0(k1_xboole_0,C_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_163])).

tff(c_8,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_85,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_106,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_85])).

tff(c_116,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_106])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_109,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_85])).

tff(c_117,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_109])).

tff(c_511,plain,(
    ! [A_45,B_46,C_47] : k2_xboole_0(k4_xboole_0(A_45,B_46),k3_xboole_0(A_45,C_47)) = k4_xboole_0(A_45,k4_xboole_0(B_46,C_47)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_559,plain,(
    ! [A_4,C_47] : k4_xboole_0(A_4,k4_xboole_0(A_4,C_47)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_4,C_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_511])).

tff(c_942,plain,(
    ! [A_57,C_58] : k2_xboole_0(k1_xboole_0,k3_xboole_0(A_57,C_58)) = k3_xboole_0(A_57,C_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_559])).

tff(c_981,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k2_xboole_0(k1_xboole_0,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_942])).

tff(c_1001,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_981])).

tff(c_740,plain,(
    ! [A_52,B_53,B_54] : k3_xboole_0(A_52,k4_xboole_0(B_53,k2_xboole_0(k3_xboole_0(A_52,B_53),B_54))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_163])).

tff(c_821,plain,(
    ! [B_54] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',k2_xboole_0(k1_xboole_0,B_54))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_740])).

tff(c_1031,plain,(
    ! [B_54] : k4_xboole_0(k1_xboole_0,B_54) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_1001,c_821])).

tff(c_1304,plain,(
    ! [C_65] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_65)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1031,c_210])).

tff(c_1339,plain,(
    ! [B_10] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',B_10)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1304])).

tff(c_55,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | k3_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ~ r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_63,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_22])).

tff(c_1421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1339,c_63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:19:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.47  
% 2.91/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.47  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.91/1.47  
% 2.91/1.47  %Foreground sorts:
% 2.91/1.47  
% 2.91/1.47  
% 2.91/1.47  %Background operators:
% 2.91/1.47  
% 2.91/1.47  
% 2.91/1.47  %Foreground operators:
% 2.91/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.91/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.91/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.91/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.91/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.91/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.91/1.47  
% 3.10/1.48  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.10/1.48  tff(f_50, negated_conjecture, ~(![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 3.10/1.48  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.10/1.48  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.10/1.48  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.10/1.48  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.10/1.48  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.10/1.48  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 3.10/1.48  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.10/1.48  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.10/1.48  tff(c_46, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=k1_xboole_0 | ~r1_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.10/1.48  tff(c_50, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_46])).
% 3.10/1.48  tff(c_163, plain, (![A_31, B_32, C_33]: (k4_xboole_0(k3_xboole_0(A_31, B_32), C_33)=k3_xboole_0(A_31, k4_xboole_0(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.10/1.48  tff(c_210, plain, (![C_33]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_33))=k4_xboole_0(k1_xboole_0, C_33))), inference(superposition, [status(thm), theory('equality')], [c_50, c_163])).
% 3.10/1.48  tff(c_8, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.10/1.48  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.10/1.48  tff(c_85, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.10/1.48  tff(c_106, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_85])).
% 3.10/1.48  tff(c_116, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_106])).
% 3.10/1.48  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.10/1.48  tff(c_109, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_85])).
% 3.10/1.48  tff(c_117, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_109])).
% 3.10/1.48  tff(c_511, plain, (![A_45, B_46, C_47]: (k2_xboole_0(k4_xboole_0(A_45, B_46), k3_xboole_0(A_45, C_47))=k4_xboole_0(A_45, k4_xboole_0(B_46, C_47)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.10/1.48  tff(c_559, plain, (![A_4, C_47]: (k4_xboole_0(A_4, k4_xboole_0(A_4, C_47))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_4, C_47)))), inference(superposition, [status(thm), theory('equality')], [c_117, c_511])).
% 3.10/1.48  tff(c_942, plain, (![A_57, C_58]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(A_57, C_58))=k3_xboole_0(A_57, C_58))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_559])).
% 3.10/1.48  tff(c_981, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k2_xboole_0(k1_xboole_0, A_5))), inference(superposition, [status(thm), theory('equality')], [c_116, c_942])).
% 3.10/1.48  tff(c_1001, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_116, c_981])).
% 3.10/1.48  tff(c_740, plain, (![A_52, B_53, B_54]: (k3_xboole_0(A_52, k4_xboole_0(B_53, k2_xboole_0(k3_xboole_0(A_52, B_53), B_54)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_163])).
% 3.10/1.48  tff(c_821, plain, (![B_54]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', k2_xboole_0(k1_xboole_0, B_54)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_740])).
% 3.10/1.48  tff(c_1031, plain, (![B_54]: (k4_xboole_0(k1_xboole_0, B_54)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_210, c_1001, c_821])).
% 3.10/1.48  tff(c_1304, plain, (![C_65]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_65))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1031, c_210])).
% 3.10/1.48  tff(c_1339, plain, (![B_10]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', B_10))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_1304])).
% 3.10/1.48  tff(c_55, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | k3_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.10/1.48  tff(c_22, plain, (~r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.10/1.48  tff(c_63, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_55, c_22])).
% 3.10/1.48  tff(c_1421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1339, c_63])).
% 3.10/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.48  
% 3.10/1.48  Inference rules
% 3.10/1.48  ----------------------
% 3.10/1.48  #Ref     : 0
% 3.10/1.48  #Sup     : 336
% 3.10/1.48  #Fact    : 0
% 3.10/1.48  #Define  : 0
% 3.10/1.48  #Split   : 0
% 3.10/1.48  #Chain   : 0
% 3.10/1.48  #Close   : 0
% 3.10/1.48  
% 3.10/1.48  Ordering : KBO
% 3.10/1.48  
% 3.10/1.48  Simplification rules
% 3.10/1.48  ----------------------
% 3.10/1.48  #Subsume      : 0
% 3.10/1.48  #Demod        : 297
% 3.10/1.48  #Tautology    : 253
% 3.10/1.48  #SimpNegUnit  : 0
% 3.10/1.48  #BackRed      : 4
% 3.10/1.48  
% 3.10/1.48  #Partial instantiations: 0
% 3.10/1.48  #Strategies tried      : 1
% 3.10/1.48  
% 3.10/1.48  Timing (in seconds)
% 3.10/1.48  ----------------------
% 3.10/1.49  Preprocessing        : 0.29
% 3.10/1.49  Parsing              : 0.15
% 3.10/1.49  CNF conversion       : 0.02
% 3.10/1.49  Main loop            : 0.43
% 3.10/1.49  Inferencing          : 0.16
% 3.10/1.49  Reduction            : 0.16
% 3.10/1.49  Demodulation         : 0.13
% 3.10/1.49  BG Simplification    : 0.02
% 3.10/1.49  Subsumption          : 0.06
% 3.10/1.49  Abstraction          : 0.03
% 3.10/1.49  MUC search           : 0.00
% 3.10/1.49  Cooper               : 0.00
% 3.10/1.49  Total                : 0.75
% 3.10/1.49  Index Insertion      : 0.00
% 3.10/1.49  Index Deletion       : 0.00
% 3.10/1.49  Index Matching       : 0.00
% 3.10/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
