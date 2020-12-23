%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:59 EST 2020

% Result     : Theorem 5.73s
% Output     : CNFRefutation 5.73s
% Verified   : 
% Statistics : Number of formulae       :   52 (  85 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 (  92 expanded)
%              Number of equality atoms :   32 (  64 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_573,plain,(
    ! [A_72,B_73] :
      ( r1_xboole_0(A_72,B_73)
      | k3_xboole_0(A_72,B_73) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_52,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_589,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_573,c_52])).

tff(c_134,plain,(
    ! [B_49,A_50] : k2_xboole_0(B_49,A_50) = k2_xboole_0(A_50,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_19] : k2_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_150,plain,(
    ! [A_50] : k2_xboole_0(k1_xboole_0,A_50) = A_50 ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_20])).

tff(c_1187,plain,(
    ! [A_109,B_110] : k2_xboole_0(A_109,k4_xboole_0(B_110,A_109)) = k2_xboole_0(A_109,B_110) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1225,plain,(
    ! [B_110] : k4_xboole_0(B_110,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_1187,c_150])).

tff(c_1258,plain,(
    ! [B_110] : k4_xboole_0(B_110,k1_xboole_0) = B_110 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_1225])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | k4_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1075,plain,(
    ! [A_100,C_101,B_102] :
      ( r1_tarski(A_100,k2_xboole_0(C_101,B_102))
      | ~ r1_tarski(A_100,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1110,plain,(
    ! [A_103,A_104] :
      ( r1_tarski(A_103,A_104)
      | ~ r1_tarski(A_103,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1075])).

tff(c_1120,plain,(
    ! [A_23,A_104] :
      ( r1_tarski(A_23,A_104)
      | k4_xboole_0(A_23,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_1110])).

tff(c_1715,plain,(
    ! [A_125,A_126] :
      ( r1_tarski(A_125,A_126)
      | k1_xboole_0 != A_125 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1258,c_1120])).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2667,plain,(
    ! [A_153,A_154] :
      ( k4_xboole_0(A_153,A_154) = k1_xboole_0
      | k1_xboole_0 != A_153 ) ),
    inference(resolution,[status(thm)],[c_1715,c_28])).

tff(c_38,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3704,plain,(
    ! [B_34] : k3_xboole_0(k1_xboole_0,B_34) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2667,c_38])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1380,plain,(
    ! [A_113,B_114] : k4_xboole_0(A_113,k4_xboole_0(A_113,B_114)) = k3_xboole_0(A_113,B_114) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1666,plain,(
    ! [A_123,B_124] : r1_tarski(k3_xboole_0(A_123,B_124),A_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_1380,c_24])).

tff(c_2030,plain,(
    ! [A_138,B_139] : k4_xboole_0(k3_xboole_0(A_138,B_139),A_138) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1666,c_28])).

tff(c_2090,plain,(
    ! [A_3,B_4] : k4_xboole_0(k3_xboole_0(A_3,B_4),B_4) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2030])).

tff(c_50,plain,(
    r1_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_269,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,B_56) = k1_xboole_0
      | ~ r1_xboole_0(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_280,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_269])).

tff(c_8161,plain,(
    ! [A_311,B_312] : k4_xboole_0(A_311,k3_xboole_0(A_311,B_312)) = k3_xboole_0(A_311,k4_xboole_0(A_311,B_312)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1380,c_38])).

tff(c_8278,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')) = k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_8161])).

tff(c_8309,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3704,c_4,c_2090,c_1258,c_8278])).

tff(c_8311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_589,c_8309])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.73/2.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.73/2.25  
% 5.73/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.73/2.25  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 5.73/2.25  
% 5.73/2.25  %Foreground sorts:
% 5.73/2.25  
% 5.73/2.25  
% 5.73/2.25  %Background operators:
% 5.73/2.25  
% 5.73/2.25  
% 5.73/2.25  %Foreground operators:
% 5.73/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.73/2.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.73/2.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.73/2.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.73/2.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.73/2.25  tff('#skF_2', type, '#skF_2': $i).
% 5.73/2.25  tff('#skF_1', type, '#skF_1': $i).
% 5.73/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.73/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.73/2.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.73/2.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.73/2.25  
% 5.73/2.26  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.73/2.26  tff(f_108, negated_conjecture, ~(![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 5.73/2.26  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.73/2.26  tff(f_53, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.73/2.26  tff(f_67, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.73/2.26  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 5.73/2.26  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 5.73/2.26  tff(f_73, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.73/2.26  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.73/2.26  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.73/2.26  tff(c_573, plain, (![A_72, B_73]: (r1_xboole_0(A_72, B_73) | k3_xboole_0(A_72, B_73)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.73/2.26  tff(c_52, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.73/2.26  tff(c_589, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_573, c_52])).
% 5.73/2.26  tff(c_134, plain, (![B_49, A_50]: (k2_xboole_0(B_49, A_50)=k2_xboole_0(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.73/2.26  tff(c_20, plain, (![A_19]: (k2_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.73/2.26  tff(c_150, plain, (![A_50]: (k2_xboole_0(k1_xboole_0, A_50)=A_50)), inference(superposition, [status(thm), theory('equality')], [c_134, c_20])).
% 5.73/2.26  tff(c_1187, plain, (![A_109, B_110]: (k2_xboole_0(A_109, k4_xboole_0(B_110, A_109))=k2_xboole_0(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.73/2.26  tff(c_1225, plain, (![B_110]: (k4_xboole_0(B_110, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_110))), inference(superposition, [status(thm), theory('equality')], [c_1187, c_150])).
% 5.73/2.26  tff(c_1258, plain, (![B_110]: (k4_xboole_0(B_110, k1_xboole_0)=B_110)), inference(demodulation, [status(thm), theory('equality')], [c_150, c_1225])).
% 5.73/2.26  tff(c_26, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | k4_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.73/2.26  tff(c_1075, plain, (![A_100, C_101, B_102]: (r1_tarski(A_100, k2_xboole_0(C_101, B_102)) | ~r1_tarski(A_100, B_102))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.73/2.26  tff(c_1110, plain, (![A_103, A_104]: (r1_tarski(A_103, A_104) | ~r1_tarski(A_103, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1075])).
% 5.73/2.26  tff(c_1120, plain, (![A_23, A_104]: (r1_tarski(A_23, A_104) | k4_xboole_0(A_23, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_1110])).
% 5.73/2.26  tff(c_1715, plain, (![A_125, A_126]: (r1_tarski(A_125, A_126) | k1_xboole_0!=A_125)), inference(demodulation, [status(thm), theory('equality')], [c_1258, c_1120])).
% 5.73/2.26  tff(c_28, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.73/2.26  tff(c_2667, plain, (![A_153, A_154]: (k4_xboole_0(A_153, A_154)=k1_xboole_0 | k1_xboole_0!=A_153)), inference(resolution, [status(thm)], [c_1715, c_28])).
% 5.73/2.26  tff(c_38, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.73/2.26  tff(c_3704, plain, (![B_34]: (k3_xboole_0(k1_xboole_0, B_34)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2667, c_38])).
% 5.73/2.26  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.73/2.26  tff(c_1380, plain, (![A_113, B_114]: (k4_xboole_0(A_113, k4_xboole_0(A_113, B_114))=k3_xboole_0(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.73/2.26  tff(c_24, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.73/2.26  tff(c_1666, plain, (![A_123, B_124]: (r1_tarski(k3_xboole_0(A_123, B_124), A_123))), inference(superposition, [status(thm), theory('equality')], [c_1380, c_24])).
% 5.73/2.26  tff(c_2030, plain, (![A_138, B_139]: (k4_xboole_0(k3_xboole_0(A_138, B_139), A_138)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1666, c_28])).
% 5.73/2.26  tff(c_2090, plain, (![A_3, B_4]: (k4_xboole_0(k3_xboole_0(A_3, B_4), B_4)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_2030])).
% 5.73/2.26  tff(c_50, plain, (r1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.73/2.26  tff(c_269, plain, (![A_55, B_56]: (k3_xboole_0(A_55, B_56)=k1_xboole_0 | ~r1_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.73/2.26  tff(c_280, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_269])).
% 5.73/2.26  tff(c_8161, plain, (![A_311, B_312]: (k4_xboole_0(A_311, k3_xboole_0(A_311, B_312))=k3_xboole_0(A_311, k4_xboole_0(A_311, B_312)))), inference(superposition, [status(thm), theory('equality')], [c_1380, c_38])).
% 5.73/2.26  tff(c_8278, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2'))=k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_280, c_8161])).
% 5.73/2.26  tff(c_8309, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3704, c_4, c_2090, c_1258, c_8278])).
% 5.73/2.26  tff(c_8311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_589, c_8309])).
% 5.73/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.73/2.26  
% 5.73/2.26  Inference rules
% 5.73/2.26  ----------------------
% 5.73/2.26  #Ref     : 1
% 5.73/2.26  #Sup     : 2112
% 5.73/2.26  #Fact    : 0
% 5.73/2.26  #Define  : 0
% 5.73/2.26  #Split   : 1
% 5.73/2.26  #Chain   : 0
% 5.73/2.26  #Close   : 0
% 5.73/2.26  
% 5.73/2.26  Ordering : KBO
% 5.73/2.26  
% 5.73/2.26  Simplification rules
% 5.73/2.26  ----------------------
% 5.73/2.26  #Subsume      : 401
% 5.73/2.26  #Demod        : 1144
% 5.73/2.26  #Tautology    : 1268
% 5.73/2.26  #SimpNegUnit  : 8
% 5.73/2.26  #BackRed      : 1
% 5.73/2.26  
% 5.73/2.26  #Partial instantiations: 0
% 5.73/2.26  #Strategies tried      : 1
% 5.73/2.26  
% 5.73/2.26  Timing (in seconds)
% 5.73/2.26  ----------------------
% 5.73/2.27  Preprocessing        : 0.33
% 5.73/2.27  Parsing              : 0.18
% 5.73/2.27  CNF conversion       : 0.02
% 5.73/2.27  Main loop            : 1.11
% 5.73/2.27  Inferencing          : 0.32
% 5.73/2.27  Reduction            : 0.50
% 5.73/2.27  Demodulation         : 0.41
% 5.73/2.27  BG Simplification    : 0.04
% 5.73/2.27  Subsumption          : 0.18
% 5.73/2.27  Abstraction          : 0.04
% 5.73/2.27  MUC search           : 0.00
% 5.73/2.27  Cooper               : 0.00
% 5.73/2.27  Total                : 1.47
% 5.73/2.27  Index Insertion      : 0.00
% 5.73/2.27  Index Deletion       : 0.00
% 5.73/2.27  Index Matching       : 0.00
% 5.73/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
