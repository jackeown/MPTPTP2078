%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:40 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   48 (  75 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   41 (  79 expanded)
%              Number of equality atoms :   34 (  64 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

tff(c_28,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_162,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_xboole_0(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_170,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_162])).

tff(c_243,plain,(
    ! [A_41,B_42] : k2_xboole_0(k3_xboole_0(A_41,B_42),k4_xboole_0(A_41,B_42)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_261,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_243])).

tff(c_64,plain,(
    ! [B_24,A_25] : k2_xboole_0(B_24,A_25) = k2_xboole_0(A_25,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,(
    ! [A_25] : k2_xboole_0(k1_xboole_0,A_25) = A_25 ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_14])).

tff(c_280,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_80])).

tff(c_16,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_184,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_199,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_184])).

tff(c_202,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_199])).

tff(c_417,plain,(
    ! [A_48,C_49,B_50] : k2_xboole_0(k4_xboole_0(A_48,C_49),k4_xboole_0(B_50,C_49)) = k4_xboole_0(k2_xboole_0(A_48,B_50),C_49) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_455,plain,(
    ! [A_48,A_13] : k4_xboole_0(k2_xboole_0(A_48,A_13),A_13) = k2_xboole_0(k4_xboole_0(A_48,A_13),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_417])).

tff(c_481,plain,(
    ! [A_48,A_13] : k4_xboole_0(k2_xboole_0(A_48,A_13),A_13) = k4_xboole_0(A_48,A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_455])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_169,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_162])).

tff(c_264,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_243])).

tff(c_369,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_80])).

tff(c_34,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_671,plain,(
    ! [A_55,A_56] : k4_xboole_0(k2_xboole_0(A_55,A_56),A_56) = k4_xboole_0(A_55,A_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_455])).

tff(c_731,plain,(
    k4_xboole_0(k2_xboole_0('#skF_1','#skF_2'),'#skF_2') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_671])).

tff(c_753,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_481,c_369,c_731])).

tff(c_755,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_753])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.41  
% 2.66/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.41  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.66/1.41  
% 2.66/1.41  %Foreground sorts:
% 2.66/1.41  
% 2.66/1.41  
% 2.66/1.41  %Background operators:
% 2.66/1.41  
% 2.66/1.41  
% 2.66/1.41  %Foreground operators:
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.66/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.66/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.66/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.66/1.41  
% 2.66/1.43  tff(f_62, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_xboole_1)).
% 2.66/1.43  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.66/1.43  tff(f_53, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.66/1.43  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.66/1.43  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.66/1.43  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.66/1.43  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.66/1.43  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.66/1.43  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 2.66/1.43  tff(c_28, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.66/1.43  tff(c_32, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.66/1.43  tff(c_162, plain, (![A_33, B_34]: (k3_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.66/1.43  tff(c_170, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_162])).
% 2.66/1.43  tff(c_243, plain, (![A_41, B_42]: (k2_xboole_0(k3_xboole_0(A_41, B_42), k4_xboole_0(A_41, B_42))=A_41)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.66/1.43  tff(c_261, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_170, c_243])).
% 2.66/1.43  tff(c_64, plain, (![B_24, A_25]: (k2_xboole_0(B_24, A_25)=k2_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.66/1.43  tff(c_14, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.66/1.43  tff(c_80, plain, (![A_25]: (k2_xboole_0(k1_xboole_0, A_25)=A_25)), inference(superposition, [status(thm), theory('equality')], [c_64, c_14])).
% 2.66/1.43  tff(c_280, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_261, c_80])).
% 2.66/1.43  tff(c_16, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.66/1.43  tff(c_20, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.66/1.43  tff(c_184, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.66/1.43  tff(c_199, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_184])).
% 2.66/1.43  tff(c_202, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_199])).
% 2.66/1.43  tff(c_417, plain, (![A_48, C_49, B_50]: (k2_xboole_0(k4_xboole_0(A_48, C_49), k4_xboole_0(B_50, C_49))=k4_xboole_0(k2_xboole_0(A_48, B_50), C_49))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.66/1.43  tff(c_455, plain, (![A_48, A_13]: (k4_xboole_0(k2_xboole_0(A_48, A_13), A_13)=k2_xboole_0(k4_xboole_0(A_48, A_13), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_202, c_417])).
% 2.66/1.43  tff(c_481, plain, (![A_48, A_13]: (k4_xboole_0(k2_xboole_0(A_48, A_13), A_13)=k4_xboole_0(A_48, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_455])).
% 2.66/1.43  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.66/1.43  tff(c_169, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_162])).
% 2.66/1.43  tff(c_264, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_169, c_243])).
% 2.66/1.43  tff(c_369, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_264, c_80])).
% 2.66/1.43  tff(c_34, plain, (k2_xboole_0('#skF_3', '#skF_2')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.66/1.43  tff(c_671, plain, (![A_55, A_56]: (k4_xboole_0(k2_xboole_0(A_55, A_56), A_56)=k4_xboole_0(A_55, A_56))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_455])).
% 2.66/1.43  tff(c_731, plain, (k4_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), '#skF_2')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_34, c_671])).
% 2.66/1.43  tff(c_753, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_280, c_481, c_369, c_731])).
% 2.66/1.43  tff(c_755, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_753])).
% 2.66/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.43  
% 2.66/1.43  Inference rules
% 2.66/1.43  ----------------------
% 2.66/1.43  #Ref     : 0
% 2.66/1.43  #Sup     : 183
% 2.66/1.43  #Fact    : 0
% 2.66/1.43  #Define  : 0
% 2.66/1.43  #Split   : 2
% 2.66/1.43  #Chain   : 0
% 2.66/1.43  #Close   : 0
% 2.66/1.43  
% 2.66/1.43  Ordering : KBO
% 2.66/1.43  
% 2.66/1.43  Simplification rules
% 2.66/1.43  ----------------------
% 2.66/1.43  #Subsume      : 0
% 2.66/1.43  #Demod        : 113
% 2.66/1.43  #Tautology    : 123
% 2.66/1.43  #SimpNegUnit  : 1
% 2.66/1.43  #BackRed      : 2
% 2.66/1.43  
% 2.66/1.43  #Partial instantiations: 0
% 2.66/1.43  #Strategies tried      : 1
% 2.66/1.43  
% 2.66/1.43  Timing (in seconds)
% 2.66/1.43  ----------------------
% 2.66/1.43  Preprocessing        : 0.31
% 2.66/1.43  Parsing              : 0.16
% 2.66/1.43  CNF conversion       : 0.02
% 2.66/1.43  Main loop            : 0.34
% 2.66/1.43  Inferencing          : 0.12
% 2.66/1.43  Reduction            : 0.13
% 2.66/1.43  Demodulation         : 0.11
% 2.66/1.43  BG Simplification    : 0.02
% 2.66/1.43  Subsumption          : 0.05
% 2.66/1.43  Abstraction          : 0.02
% 2.66/1.43  MUC search           : 0.00
% 2.66/1.43  Cooper               : 0.00
% 2.66/1.43  Total                : 0.68
% 2.66/1.43  Index Insertion      : 0.00
% 2.66/1.43  Index Deletion       : 0.00
% 2.91/1.43  Index Matching       : 0.00
% 2.91/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
