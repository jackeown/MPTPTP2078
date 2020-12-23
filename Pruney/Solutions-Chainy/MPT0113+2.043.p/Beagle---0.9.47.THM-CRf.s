%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:17 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   53 (  72 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  86 expanded)
%              Number of equality atoms :   25 (  35 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_1258,plain,(
    ! [A_65,B_66] :
      ( r1_xboole_0(A_65,B_66)
      | k3_xboole_0(A_65,B_66) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_61,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_62,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_70,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_62])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1078,plain,(
    ! [A_60,B_61] : k3_xboole_0(k4_xboole_0(A_60,B_61),A_60) = k4_xboole_0(A_60,B_61) ),
    inference(resolution,[status(thm)],[c_14,c_62])).

tff(c_371,plain,(
    ! [A_48,B_49,C_50] : k3_xboole_0(k3_xboole_0(A_48,B_49),C_50) = k3_xboole_0(A_48,k3_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_432,plain,(
    ! [C_50] : k3_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_50)) = k3_xboole_0('#skF_1',C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_371])).

tff(c_1091,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1078,c_432])).

tff(c_1157,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1091])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_191,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_218,plain,(
    ! [A_40,B_41] : r1_tarski(k3_xboole_0(A_40,B_41),A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_14])).

tff(c_239,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_218])).

tff(c_1224,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1157,c_239])).

tff(c_1234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_1224])).

tff(c_1235,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_1262,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1258,c_1235])).

tff(c_18,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1263,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(A_67,B_68) = k1_xboole_0
      | ~ r1_xboole_0(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1275,plain,(
    ! [A_16] : k3_xboole_0(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_1263])).

tff(c_20,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1274,plain,(
    ! [A_17,B_18] : k3_xboole_0(k4_xboole_0(A_17,B_18),B_18) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_1263])).

tff(c_1237,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = A_63
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1249,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_1237])).

tff(c_1525,plain,(
    ! [A_82,B_83,C_84] : k3_xboole_0(k3_xboole_0(A_82,B_83),C_84) = k3_xboole_0(A_82,k3_xboole_0(B_83,C_84)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1660,plain,(
    ! [C_88] : k3_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_88)) = k3_xboole_0('#skF_1',C_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_1249,c_1525])).

tff(c_1686,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1274,c_1660])).

tff(c_1705,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1275,c_1686])).

tff(c_1707,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1262,c_1705])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n004.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 10:51:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.54  
% 3.23/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.54  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.23/1.54  
% 3.23/1.54  %Foreground sorts:
% 3.23/1.54  
% 3.23/1.54  
% 3.23/1.54  %Background operators:
% 3.23/1.54  
% 3.23/1.54  
% 3.23/1.54  %Foreground operators:
% 3.23/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.23/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.23/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.23/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.23/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.23/1.54  
% 3.23/1.55  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.23/1.55  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.23/1.55  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.23/1.55  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.23/1.55  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 3.23/1.55  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.23/1.55  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.23/1.55  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.23/1.55  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.23/1.55  tff(c_1258, plain, (![A_65, B_66]: (r1_xboole_0(A_65, B_66) | k3_xboole_0(A_65, B_66)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.55  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.23/1.55  tff(c_61, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_22])).
% 3.23/1.55  tff(c_24, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.23/1.55  tff(c_62, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.23/1.55  tff(c_70, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_24, c_62])).
% 3.23/1.55  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.23/1.55  tff(c_1078, plain, (![A_60, B_61]: (k3_xboole_0(k4_xboole_0(A_60, B_61), A_60)=k4_xboole_0(A_60, B_61))), inference(resolution, [status(thm)], [c_14, c_62])).
% 3.23/1.55  tff(c_371, plain, (![A_48, B_49, C_50]: (k3_xboole_0(k3_xboole_0(A_48, B_49), C_50)=k3_xboole_0(A_48, k3_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.23/1.55  tff(c_432, plain, (![C_50]: (k3_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_50))=k3_xboole_0('#skF_1', C_50))), inference(superposition, [status(thm), theory('equality')], [c_70, c_371])).
% 3.23/1.55  tff(c_1091, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1078, c_432])).
% 3.23/1.55  tff(c_1157, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1091])).
% 3.23/1.55  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.55  tff(c_191, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.23/1.55  tff(c_218, plain, (![A_40, B_41]: (r1_tarski(k3_xboole_0(A_40, B_41), A_40))), inference(superposition, [status(thm), theory('equality')], [c_191, c_14])).
% 3.23/1.55  tff(c_239, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_218])).
% 3.23/1.55  tff(c_1224, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1157, c_239])).
% 3.23/1.55  tff(c_1234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_1224])).
% 3.23/1.55  tff(c_1235, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_22])).
% 3.23/1.55  tff(c_1262, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1258, c_1235])).
% 3.23/1.55  tff(c_18, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.23/1.55  tff(c_1263, plain, (![A_67, B_68]: (k3_xboole_0(A_67, B_68)=k1_xboole_0 | ~r1_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.55  tff(c_1275, plain, (![A_16]: (k3_xboole_0(A_16, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_1263])).
% 3.23/1.55  tff(c_20, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.23/1.55  tff(c_1274, plain, (![A_17, B_18]: (k3_xboole_0(k4_xboole_0(A_17, B_18), B_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_1263])).
% 3.23/1.55  tff(c_1237, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=A_63 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.23/1.55  tff(c_1249, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_24, c_1237])).
% 3.23/1.55  tff(c_1525, plain, (![A_82, B_83, C_84]: (k3_xboole_0(k3_xboole_0(A_82, B_83), C_84)=k3_xboole_0(A_82, k3_xboole_0(B_83, C_84)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.23/1.55  tff(c_1660, plain, (![C_88]: (k3_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_88))=k3_xboole_0('#skF_1', C_88))), inference(superposition, [status(thm), theory('equality')], [c_1249, c_1525])).
% 3.23/1.55  tff(c_1686, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1274, c_1660])).
% 3.23/1.55  tff(c_1705, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1275, c_1686])).
% 3.23/1.55  tff(c_1707, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1262, c_1705])).
% 3.23/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.55  
% 3.23/1.55  Inference rules
% 3.23/1.55  ----------------------
% 3.23/1.55  #Ref     : 0
% 3.23/1.55  #Sup     : 449
% 3.23/1.55  #Fact    : 0
% 3.23/1.55  #Define  : 0
% 3.23/1.55  #Split   : 1
% 3.23/1.55  #Chain   : 0
% 3.23/1.55  #Close   : 0
% 3.23/1.55  
% 3.23/1.55  Ordering : KBO
% 3.23/1.55  
% 3.23/1.55  Simplification rules
% 3.23/1.55  ----------------------
% 3.23/1.55  #Subsume      : 0
% 3.23/1.55  #Demod        : 276
% 3.23/1.55  #Tautology    : 288
% 3.23/1.55  #SimpNegUnit  : 2
% 3.23/1.55  #BackRed      : 11
% 3.23/1.55  
% 3.23/1.55  #Partial instantiations: 0
% 3.23/1.55  #Strategies tried      : 1
% 3.23/1.55  
% 3.23/1.55  Timing (in seconds)
% 3.23/1.55  ----------------------
% 3.23/1.55  Preprocessing        : 0.30
% 3.23/1.55  Parsing              : 0.16
% 3.23/1.55  CNF conversion       : 0.02
% 3.23/1.55  Main loop            : 0.47
% 3.23/1.55  Inferencing          : 0.16
% 3.23/1.55  Reduction            : 0.19
% 3.23/1.55  Demodulation         : 0.15
% 3.23/1.55  BG Simplification    : 0.02
% 3.23/1.55  Subsumption          : 0.06
% 3.23/1.55  Abstraction          : 0.02
% 3.23/1.55  MUC search           : 0.00
% 3.23/1.55  Cooper               : 0.00
% 3.23/1.55  Total                : 0.79
% 3.23/1.55  Index Insertion      : 0.00
% 3.23/1.55  Index Deletion       : 0.00
% 3.23/1.55  Index Matching       : 0.00
% 3.23/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
