%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:01 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   43 (  51 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  51 expanded)
%              Number of equality atoms :   23 (  30 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_56,plain,(
    ! [B_18,A_19] :
      ( r1_xboole_0(B_18,A_19)
      | ~ r1_xboole_0(A_19,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_61,plain,(
    ! [A_14] : r1_xboole_0(k1_xboole_0,A_14) ),
    inference(resolution,[status(thm)],[c_16,c_56])).

tff(c_80,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61,c_80])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_100,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_80])).

tff(c_372,plain,(
    ! [A_37,B_38,C_39] : k3_xboole_0(k3_xboole_0(A_37,B_38),C_39) = k3_xboole_0(A_37,k3_xboole_0(B_38,C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_413,plain,(
    ! [C_39] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_39)) = k3_xboole_0(k1_xboole_0,C_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_372])).

tff(c_439,plain,(
    ! [C_40] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_40)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_413])).

tff(c_458,plain,(
    ! [B_2] : k3_xboole_0('#skF_1',k3_xboole_0(B_2,'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_439])).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_280,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_323,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,k3_xboole_0(A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_280])).

tff(c_336,plain,(
    ! [A_10,B_11] : k3_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_323])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] : k3_xboole_0(k3_xboole_0(A_7,B_8),C_9) = k3_xboole_0(A_7,k3_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_21,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18])).

tff(c_79,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_21])).

tff(c_371,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_2'))) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_79])).

tff(c_823,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_371])).

tff(c_826,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_823])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:40:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.37  
% 2.65/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.37  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.65/1.37  
% 2.65/1.37  %Foreground sorts:
% 2.65/1.37  
% 2.65/1.37  
% 2.65/1.37  %Background operators:
% 2.65/1.37  
% 2.65/1.37  
% 2.65/1.37  %Foreground operators:
% 2.65/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.65/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.65/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.65/1.37  
% 2.65/1.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.65/1.38  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.65/1.38  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.65/1.38  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.65/1.38  tff(f_48, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_xboole_1)).
% 2.65/1.38  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.65/1.38  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.65/1.38  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.65/1.38  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.65/1.38  tff(c_16, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.65/1.38  tff(c_56, plain, (![B_18, A_19]: (r1_xboole_0(B_18, A_19) | ~r1_xboole_0(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.65/1.38  tff(c_61, plain, (![A_14]: (r1_xboole_0(k1_xboole_0, A_14))), inference(resolution, [status(thm)], [c_16, c_56])).
% 2.65/1.38  tff(c_80, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.38  tff(c_98, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_61, c_80])).
% 2.65/1.38  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.65/1.38  tff(c_100, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_80])).
% 2.65/1.38  tff(c_372, plain, (![A_37, B_38, C_39]: (k3_xboole_0(k3_xboole_0(A_37, B_38), C_39)=k3_xboole_0(A_37, k3_xboole_0(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.65/1.38  tff(c_413, plain, (![C_39]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_39))=k3_xboole_0(k1_xboole_0, C_39))), inference(superposition, [status(thm), theory('equality')], [c_100, c_372])).
% 2.65/1.38  tff(c_439, plain, (![C_40]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_40))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_98, c_413])).
% 2.65/1.38  tff(c_458, plain, (![B_2]: (k3_xboole_0('#skF_1', k3_xboole_0(B_2, '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_439])).
% 2.65/1.38  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.65/1.38  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.65/1.38  tff(c_280, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.65/1.38  tff(c_323, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, k3_xboole_0(A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_280])).
% 2.65/1.38  tff(c_336, plain, (![A_10, B_11]: (k3_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_323])).
% 2.65/1.38  tff(c_10, plain, (![A_7, B_8, C_9]: (k3_xboole_0(k3_xboole_0(A_7, B_8), C_9)=k3_xboole_0(A_7, k3_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.65/1.38  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.38  tff(c_18, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.65/1.38  tff(c_21, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18])).
% 2.65/1.38  tff(c_79, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_21])).
% 2.65/1.38  tff(c_371, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_2')))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_79])).
% 2.65/1.38  tff(c_823, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_336, c_371])).
% 2.65/1.38  tff(c_826, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_458, c_823])).
% 2.65/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.38  
% 2.65/1.38  Inference rules
% 2.65/1.38  ----------------------
% 2.65/1.38  #Ref     : 0
% 2.65/1.38  #Sup     : 208
% 2.65/1.38  #Fact    : 0
% 2.65/1.38  #Define  : 0
% 2.65/1.38  #Split   : 0
% 2.65/1.38  #Chain   : 0
% 2.65/1.38  #Close   : 0
% 2.65/1.38  
% 2.65/1.38  Ordering : KBO
% 2.65/1.38  
% 2.65/1.38  Simplification rules
% 2.65/1.38  ----------------------
% 2.65/1.38  #Subsume      : 20
% 2.65/1.38  #Demod        : 138
% 2.65/1.38  #Tautology    : 134
% 2.65/1.38  #SimpNegUnit  : 0
% 2.65/1.38  #BackRed      : 2
% 2.65/1.38  
% 2.65/1.38  #Partial instantiations: 0
% 2.65/1.39  #Strategies tried      : 1
% 2.65/1.39  
% 2.65/1.39  Timing (in seconds)
% 2.65/1.39  ----------------------
% 2.65/1.39  Preprocessing        : 0.27
% 2.65/1.39  Parsing              : 0.15
% 2.65/1.39  CNF conversion       : 0.02
% 2.65/1.39  Main loop            : 0.36
% 2.65/1.39  Inferencing          : 0.13
% 2.65/1.39  Reduction            : 0.15
% 2.65/1.39  Demodulation         : 0.12
% 2.65/1.39  BG Simplification    : 0.01
% 2.65/1.39  Subsumption          : 0.05
% 2.65/1.39  Abstraction          : 0.02
% 2.65/1.39  MUC search           : 0.00
% 2.65/1.39  Cooper               : 0.00
% 2.65/1.39  Total                : 0.66
% 2.65/1.39  Index Insertion      : 0.00
% 2.65/1.39  Index Deletion       : 0.00
% 2.65/1.39  Index Matching       : 0.00
% 2.65/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
