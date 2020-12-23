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
% DateTime   : Thu Dec  3 09:45:18 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   48 (  67 expanded)
%              Number of leaves         :   18 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  74 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_18,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_23,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_57,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_65,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_20,c_57])).

tff(c_261,plain,(
    ! [A_40,B_41,C_42] : k4_xboole_0(k3_xboole_0(A_40,B_41),C_42) = k3_xboole_0(A_40,k4_xboole_0(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1098,plain,(
    ! [A_80,B_81,C_82] : r1_tarski(k3_xboole_0(A_80,k4_xboole_0(B_81,C_82)),k3_xboole_0(A_80,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_8])).

tff(c_1139,plain,(
    r1_tarski('#skF_1',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_1098])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1170,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1139,c_6])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_539,plain,(
    ! [A_62,B_63] : k3_xboole_0(k4_xboole_0(A_62,B_63),A_62) = k4_xboole_0(A_62,B_63) ),
    inference(resolution,[status(thm)],[c_8,c_57])).

tff(c_589,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(k3_xboole_0(A_9,B_10),A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_539])).

tff(c_607,plain,(
    ! [A_9,B_10] : k3_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2,c_589])).

tff(c_1183,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1170,c_607])).

tff(c_102,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_127,plain,(
    ! [A_31,B_32] : r1_tarski(k3_xboole_0(A_31,B_32),A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_8])).

tff(c_136,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_127])).

tff(c_1294,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1183,c_136])).

tff(c_1313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23,c_1294])).

tff(c_1314,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_1349,plain,(
    ! [A_85,B_86] :
      ( k3_xboole_0(A_85,B_86) = A_85
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1361,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_20,c_1349])).

tff(c_1851,plain,(
    ! [A_114,B_115,C_116] : k4_xboole_0(k3_xboole_0(A_114,B_115),C_116) = k3_xboole_0(A_114,k4_xboole_0(B_115,C_116)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1921,plain,(
    ! [A_117,B_118,C_119] : r1_xboole_0(k3_xboole_0(A_117,k4_xboole_0(B_118,C_119)),C_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_1851,c_16])).

tff(c_1942,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1361,c_1921])).

tff(c_1953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1314,c_1942])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:54:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.52  
% 3.37/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.52  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 3.37/1.52  
% 3.37/1.52  %Foreground sorts:
% 3.37/1.52  
% 3.37/1.52  
% 3.37/1.52  %Background operators:
% 3.37/1.52  
% 3.37/1.52  
% 3.37/1.52  %Foreground operators:
% 3.37/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.37/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.37/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.37/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.37/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.37/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.37/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.37/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.37/1.52  
% 3.37/1.53  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.37/1.53  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.37/1.53  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.37/1.53  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.37/1.53  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.37/1.53  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.37/1.53  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.37/1.53  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.37/1.53  tff(c_23, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_18])).
% 3.37/1.53  tff(c_20, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.37/1.53  tff(c_57, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.37/1.53  tff(c_65, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_20, c_57])).
% 3.37/1.53  tff(c_261, plain, (![A_40, B_41, C_42]: (k4_xboole_0(k3_xboole_0(A_40, B_41), C_42)=k3_xboole_0(A_40, k4_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.37/1.53  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.37/1.53  tff(c_1098, plain, (![A_80, B_81, C_82]: (r1_tarski(k3_xboole_0(A_80, k4_xboole_0(B_81, C_82)), k3_xboole_0(A_80, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_261, c_8])).
% 3.37/1.53  tff(c_1139, plain, (r1_tarski('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_1098])).
% 3.37/1.53  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.37/1.53  tff(c_1170, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_1139, c_6])).
% 3.37/1.53  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.37/1.53  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.37/1.53  tff(c_539, plain, (![A_62, B_63]: (k3_xboole_0(k4_xboole_0(A_62, B_63), A_62)=k4_xboole_0(A_62, B_63))), inference(resolution, [status(thm)], [c_8, c_57])).
% 3.37/1.53  tff(c_589, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(k3_xboole_0(A_9, B_10), A_9))), inference(superposition, [status(thm), theory('equality')], [c_10, c_539])).
% 3.37/1.53  tff(c_607, plain, (![A_9, B_10]: (k3_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2, c_589])).
% 3.37/1.53  tff(c_1183, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1170, c_607])).
% 3.37/1.53  tff(c_102, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.37/1.53  tff(c_127, plain, (![A_31, B_32]: (r1_tarski(k3_xboole_0(A_31, B_32), A_31))), inference(superposition, [status(thm), theory('equality')], [c_102, c_8])).
% 3.37/1.53  tff(c_136, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_127])).
% 3.37/1.53  tff(c_1294, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1183, c_136])).
% 3.37/1.53  tff(c_1313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23, c_1294])).
% 3.37/1.53  tff(c_1314, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_18])).
% 3.37/1.53  tff(c_1349, plain, (![A_85, B_86]: (k3_xboole_0(A_85, B_86)=A_85 | ~r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.37/1.53  tff(c_1361, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_20, c_1349])).
% 3.37/1.53  tff(c_1851, plain, (![A_114, B_115, C_116]: (k4_xboole_0(k3_xboole_0(A_114, B_115), C_116)=k3_xboole_0(A_114, k4_xboole_0(B_115, C_116)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.37/1.53  tff(c_16, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.37/1.53  tff(c_1921, plain, (![A_117, B_118, C_119]: (r1_xboole_0(k3_xboole_0(A_117, k4_xboole_0(B_118, C_119)), C_119))), inference(superposition, [status(thm), theory('equality')], [c_1851, c_16])).
% 3.37/1.53  tff(c_1942, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1361, c_1921])).
% 3.37/1.53  tff(c_1953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1314, c_1942])).
% 3.37/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.53  
% 3.37/1.53  Inference rules
% 3.37/1.53  ----------------------
% 3.37/1.53  #Ref     : 0
% 3.37/1.53  #Sup     : 518
% 3.37/1.53  #Fact    : 0
% 3.37/1.53  #Define  : 0
% 3.37/1.53  #Split   : 1
% 3.37/1.53  #Chain   : 0
% 3.37/1.53  #Close   : 0
% 3.37/1.53  
% 3.37/1.53  Ordering : KBO
% 3.37/1.53  
% 3.37/1.53  Simplification rules
% 3.37/1.53  ----------------------
% 3.37/1.53  #Subsume      : 0
% 3.37/1.53  #Demod        : 343
% 3.37/1.53  #Tautology    : 272
% 3.37/1.53  #SimpNegUnit  : 2
% 3.37/1.53  #BackRed      : 10
% 3.37/1.53  
% 3.37/1.53  #Partial instantiations: 0
% 3.37/1.53  #Strategies tried      : 1
% 3.37/1.53  
% 3.37/1.53  Timing (in seconds)
% 3.37/1.53  ----------------------
% 3.37/1.53  Preprocessing        : 0.27
% 3.37/1.53  Parsing              : 0.14
% 3.37/1.53  CNF conversion       : 0.01
% 3.37/1.53  Main loop            : 0.51
% 3.37/1.53  Inferencing          : 0.16
% 3.37/1.53  Reduction            : 0.21
% 3.37/1.53  Demodulation         : 0.17
% 3.37/1.53  BG Simplification    : 0.02
% 3.37/1.53  Subsumption          : 0.08
% 3.37/1.53  Abstraction          : 0.03
% 3.37/1.53  MUC search           : 0.00
% 3.37/1.53  Cooper               : 0.00
% 3.37/1.53  Total                : 0.80
% 3.37/1.53  Index Insertion      : 0.00
% 3.37/1.53  Index Deletion       : 0.00
% 3.37/1.53  Index Matching       : 0.00
% 3.37/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
