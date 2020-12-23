%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:16 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   52 (  69 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  81 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_957,plain,(
    ! [A_66,B_67] :
      ( r1_xboole_0(A_66,B_67)
      | k3_xboole_0(A_66,B_67) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_81,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_116,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_123,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_116])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_757,plain,(
    ! [A_58,B_59] : k3_xboole_0(k4_xboole_0(A_58,B_59),A_58) = k4_xboole_0(A_58,B_59) ),
    inference(resolution,[status(thm)],[c_16,c_116])).

tff(c_448,plain,(
    ! [A_47,B_48,C_49] : k3_xboole_0(k3_xboole_0(A_47,B_48),C_49) = k3_xboole_0(A_47,k3_xboole_0(B_48,C_49)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_490,plain,(
    ! [C_49] : k3_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_49)) = k3_xboole_0('#skF_1',C_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_448])).

tff(c_773,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_757,c_490])).

tff(c_824,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_773])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_306,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k4_xboole_0(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_579,plain,(
    ! [A_51,B_52] : r1_tarski(k3_xboole_0(A_51,B_52),A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_16])).

tff(c_606,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_579])).

tff(c_876,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_824,c_606])).

tff(c_892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_876])).

tff(c_893,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_965,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_957,c_893])).

tff(c_14,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_952,plain,(
    ! [A_64,B_65] :
      ( k3_xboole_0(A_64,B_65) = k1_xboole_0
      | ~ r1_xboole_0(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_956,plain,(
    ! [A_17,B_18] : k3_xboole_0(k4_xboole_0(A_17,B_18),B_18) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_952])).

tff(c_931,plain,(
    ! [A_62,B_63] :
      ( k3_xboole_0(A_62,B_63) = A_62
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_942,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_931])).

tff(c_1302,plain,(
    ! [A_85,B_86,C_87] : k3_xboole_0(k3_xboole_0(A_85,B_86),C_87) = k3_xboole_0(A_85,k3_xboole_0(B_86,C_87)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1394,plain,(
    ! [C_88] : k3_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_88)) = k3_xboole_0('#skF_1',C_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_942,c_1302])).

tff(c_1420,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_956,c_1394])).

tff(c_1439,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1420])).

tff(c_1441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_965,c_1439])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:32:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.57  
% 3.07/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.57  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.23/1.57  
% 3.23/1.57  %Foreground sorts:
% 3.23/1.57  
% 3.23/1.57  
% 3.23/1.57  %Background operators:
% 3.23/1.57  
% 3.23/1.57  
% 3.23/1.57  %Foreground operators:
% 3.23/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.23/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.23/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.23/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.23/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.23/1.57  
% 3.23/1.58  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.23/1.58  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.23/1.58  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.23/1.58  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.23/1.58  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 3.23/1.58  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.23/1.58  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.23/1.58  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.23/1.58  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.23/1.58  tff(c_957, plain, (![A_66, B_67]: (r1_xboole_0(A_66, B_67) | k3_xboole_0(A_66, B_67)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.58  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.23/1.58  tff(c_81, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_22])).
% 3.23/1.58  tff(c_24, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.23/1.58  tff(c_116, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.23/1.58  tff(c_123, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_24, c_116])).
% 3.23/1.58  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.23/1.58  tff(c_757, plain, (![A_58, B_59]: (k3_xboole_0(k4_xboole_0(A_58, B_59), A_58)=k4_xboole_0(A_58, B_59))), inference(resolution, [status(thm)], [c_16, c_116])).
% 3.23/1.58  tff(c_448, plain, (![A_47, B_48, C_49]: (k3_xboole_0(k3_xboole_0(A_47, B_48), C_49)=k3_xboole_0(A_47, k3_xboole_0(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.23/1.58  tff(c_490, plain, (![C_49]: (k3_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_49))=k3_xboole_0('#skF_1', C_49))), inference(superposition, [status(thm), theory('equality')], [c_123, c_448])).
% 3.23/1.58  tff(c_773, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_757, c_490])).
% 3.23/1.58  tff(c_824, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_123, c_773])).
% 3.23/1.58  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.58  tff(c_306, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k4_xboole_0(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.23/1.58  tff(c_579, plain, (![A_51, B_52]: (r1_tarski(k3_xboole_0(A_51, B_52), A_51))), inference(superposition, [status(thm), theory('equality')], [c_306, c_16])).
% 3.23/1.58  tff(c_606, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_579])).
% 3.23/1.58  tff(c_876, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_824, c_606])).
% 3.23/1.58  tff(c_892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_876])).
% 3.23/1.58  tff(c_893, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_22])).
% 3.23/1.58  tff(c_965, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_957, c_893])).
% 3.23/1.58  tff(c_14, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.23/1.58  tff(c_20, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.23/1.58  tff(c_952, plain, (![A_64, B_65]: (k3_xboole_0(A_64, B_65)=k1_xboole_0 | ~r1_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.58  tff(c_956, plain, (![A_17, B_18]: (k3_xboole_0(k4_xboole_0(A_17, B_18), B_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_952])).
% 3.23/1.58  tff(c_931, plain, (![A_62, B_63]: (k3_xboole_0(A_62, B_63)=A_62 | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.23/1.58  tff(c_942, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_24, c_931])).
% 3.23/1.58  tff(c_1302, plain, (![A_85, B_86, C_87]: (k3_xboole_0(k3_xboole_0(A_85, B_86), C_87)=k3_xboole_0(A_85, k3_xboole_0(B_86, C_87)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.23/1.58  tff(c_1394, plain, (![C_88]: (k3_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_88))=k3_xboole_0('#skF_1', C_88))), inference(superposition, [status(thm), theory('equality')], [c_942, c_1302])).
% 3.23/1.58  tff(c_1420, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_956, c_1394])).
% 3.23/1.58  tff(c_1439, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1420])).
% 3.23/1.58  tff(c_1441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_965, c_1439])).
% 3.23/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.58  
% 3.23/1.58  Inference rules
% 3.23/1.58  ----------------------
% 3.23/1.58  #Ref     : 0
% 3.23/1.58  #Sup     : 377
% 3.23/1.58  #Fact    : 0
% 3.23/1.58  #Define  : 0
% 3.23/1.58  #Split   : 1
% 3.23/1.58  #Chain   : 0
% 3.23/1.58  #Close   : 0
% 3.23/1.58  
% 3.23/1.58  Ordering : KBO
% 3.23/1.58  
% 3.23/1.58  Simplification rules
% 3.23/1.58  ----------------------
% 3.23/1.58  #Subsume      : 2
% 3.23/1.58  #Demod        : 213
% 3.23/1.58  #Tautology    : 218
% 3.23/1.58  #SimpNegUnit  : 2
% 3.23/1.58  #BackRed      : 3
% 3.23/1.58  
% 3.23/1.58  #Partial instantiations: 0
% 3.23/1.58  #Strategies tried      : 1
% 3.23/1.58  
% 3.23/1.58  Timing (in seconds)
% 3.23/1.58  ----------------------
% 3.23/1.59  Preprocessing        : 0.31
% 3.23/1.59  Parsing              : 0.18
% 3.23/1.59  CNF conversion       : 0.02
% 3.23/1.59  Main loop            : 0.49
% 3.23/1.59  Inferencing          : 0.17
% 3.23/1.59  Reduction            : 0.19
% 3.23/1.59  Demodulation         : 0.15
% 3.23/1.59  BG Simplification    : 0.02
% 3.23/1.59  Subsumption          : 0.07
% 3.23/1.59  Abstraction          : 0.02
% 3.23/1.59  MUC search           : 0.00
% 3.23/1.59  Cooper               : 0.00
% 3.23/1.59  Total                : 0.83
% 3.23/1.59  Index Insertion      : 0.00
% 3.23/1.59  Index Deletion       : 0.00
% 3.23/1.59  Index Matching       : 0.00
% 3.23/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
