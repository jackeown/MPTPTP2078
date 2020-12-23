%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:13 EST 2020

% Result     : Theorem 11.34s
% Output     : CNFRefutation 11.34s
% Verified   : 
% Statistics : Number of formulae       :   60 (  84 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 (  94 expanded)
%              Number of equality atoms :   33 (  46 expanded)
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

tff(f_58,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_26,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_99,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_197,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,B_39) = A_38
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_204,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_197])).

tff(c_14,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2314,plain,(
    ! [A_100,B_101] : k3_xboole_0(k4_xboole_0(A_100,B_101),A_100) = k4_xboole_0(A_100,B_101) ),
    inference(resolution,[status(thm)],[c_14,c_197])).

tff(c_964,plain,(
    ! [A_67,B_68,C_69] : k3_xboole_0(k3_xboole_0(A_67,B_68),C_69) = k3_xboole_0(A_67,k3_xboole_0(B_68,C_69)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1012,plain,(
    ! [C_69] : k3_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_69)) = k3_xboole_0('#skF_1',C_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_964])).

tff(c_2342,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2314,c_1012])).

tff(c_2424,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_2342])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_206,plain,(
    ! [A_40,B_41] : k5_xboole_0(A_40,k3_xboole_0(A_40,B_41)) = k4_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1371,plain,(
    ! [A_82,B_83] : k5_xboole_0(A_82,k3_xboole_0(B_83,A_82)) = k4_xboole_0(A_82,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_206])).

tff(c_100,plain,(
    ! [B_35,A_36] : k5_xboole_0(B_35,A_36) = k5_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_116,plain,(
    ! [A_36] : k5_xboole_0(k1_xboole_0,A_36) = A_36 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_18])).

tff(c_24,plain,(
    ! [A_25] : k5_xboole_0(A_25,A_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_503,plain,(
    ! [A_55,B_56,C_57] : k5_xboole_0(k5_xboole_0(A_55,B_56),C_57) = k5_xboole_0(A_55,k5_xboole_0(B_56,C_57)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_567,plain,(
    ! [A_25,C_57] : k5_xboole_0(A_25,k5_xboole_0(A_25,C_57)) = k5_xboole_0(k1_xboole_0,C_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_503])).

tff(c_580,plain,(
    ! [A_25,C_57] : k5_xboole_0(A_25,k5_xboole_0(A_25,C_57)) = C_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_567])).

tff(c_1386,plain,(
    ! [A_82,B_83] : k5_xboole_0(A_82,k4_xboole_0(A_82,B_83)) = k3_xboole_0(B_83,A_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_1371,c_580])).

tff(c_223,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_206])).

tff(c_2332,plain,(
    ! [A_100,B_101] : k5_xboole_0(A_100,k4_xboole_0(A_100,B_101)) = k4_xboole_0(A_100,k4_xboole_0(A_100,B_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2314,c_223])).

tff(c_34025,plain,(
    ! [A_408,B_409] : k4_xboole_0(A_408,k4_xboole_0(A_408,B_409)) = k3_xboole_0(B_409,A_408) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1386,c_2332])).

tff(c_34659,plain,(
    ! [B_410,A_411] : r1_tarski(k3_xboole_0(B_410,A_411),A_411) ),
    inference(superposition,[status(thm),theory(equality)],[c_34025,c_14])).

tff(c_34785,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2424,c_34659])).

tff(c_34866,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_34785])).

tff(c_34867,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_34966,plain,(
    ! [A_415,B_416] :
      ( k3_xboole_0(A_415,B_416) = A_415
      | ~ r1_tarski(A_415,B_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34977,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_34966])).

tff(c_35359,plain,(
    ! [A_433,B_434,C_435] : k4_xboole_0(k3_xboole_0(A_433,B_434),C_435) = k3_xboole_0(A_433,k4_xboole_0(B_434,C_435)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_20,B_21] : r1_xboole_0(k4_xboole_0(A_20,B_21),B_21) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_35818,plain,(
    ! [A_446,B_447,C_448] : r1_xboole_0(k3_xboole_0(A_446,k4_xboole_0(B_447,C_448)),C_448) ),
    inference(superposition,[status(thm),theory(equality)],[c_35359,c_20])).

tff(c_35846,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34977,c_35818])).

tff(c_35869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34867,c_35846])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n013.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 18:55:39 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.34/5.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.34/5.56  
% 11.34/5.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.34/5.56  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.34/5.56  
% 11.34/5.56  %Foreground sorts:
% 11.34/5.56  
% 11.34/5.56  
% 11.34/5.56  %Background operators:
% 11.34/5.56  
% 11.34/5.56  
% 11.34/5.56  %Foreground operators:
% 11.34/5.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.34/5.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.34/5.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.34/5.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.34/5.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.34/5.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.34/5.56  tff('#skF_2', type, '#skF_2': $i).
% 11.34/5.56  tff('#skF_3', type, '#skF_3': $i).
% 11.34/5.56  tff('#skF_1', type, '#skF_1': $i).
% 11.34/5.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.34/5.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.34/5.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.34/5.56  
% 11.34/5.58  tff(f_58, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 11.34/5.58  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.34/5.58  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.34/5.58  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 11.34/5.58  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.34/5.58  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.34/5.58  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 11.34/5.58  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 11.34/5.58  tff(f_51, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 11.34/5.58  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.34/5.58  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 11.34/5.58  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 11.34/5.58  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.34/5.58  tff(c_99, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_26])).
% 11.34/5.58  tff(c_28, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.34/5.58  tff(c_197, plain, (![A_38, B_39]: (k3_xboole_0(A_38, B_39)=A_38 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.34/5.58  tff(c_204, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_28, c_197])).
% 11.34/5.58  tff(c_14, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.34/5.58  tff(c_2314, plain, (![A_100, B_101]: (k3_xboole_0(k4_xboole_0(A_100, B_101), A_100)=k4_xboole_0(A_100, B_101))), inference(resolution, [status(thm)], [c_14, c_197])).
% 11.34/5.58  tff(c_964, plain, (![A_67, B_68, C_69]: (k3_xboole_0(k3_xboole_0(A_67, B_68), C_69)=k3_xboole_0(A_67, k3_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.34/5.58  tff(c_1012, plain, (![C_69]: (k3_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_69))=k3_xboole_0('#skF_1', C_69))), inference(superposition, [status(thm), theory('equality')], [c_204, c_964])).
% 11.34/5.58  tff(c_2342, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2314, c_1012])).
% 11.34/5.58  tff(c_2424, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_204, c_2342])).
% 11.34/5.58  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.34/5.58  tff(c_206, plain, (![A_40, B_41]: (k5_xboole_0(A_40, k3_xboole_0(A_40, B_41))=k4_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.34/5.58  tff(c_1371, plain, (![A_82, B_83]: (k5_xboole_0(A_82, k3_xboole_0(B_83, A_82))=k4_xboole_0(A_82, B_83))), inference(superposition, [status(thm), theory('equality')], [c_2, c_206])).
% 11.34/5.58  tff(c_100, plain, (![B_35, A_36]: (k5_xboole_0(B_35, A_36)=k5_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.34/5.58  tff(c_18, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.34/5.58  tff(c_116, plain, (![A_36]: (k5_xboole_0(k1_xboole_0, A_36)=A_36)), inference(superposition, [status(thm), theory('equality')], [c_100, c_18])).
% 11.34/5.58  tff(c_24, plain, (![A_25]: (k5_xboole_0(A_25, A_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.34/5.58  tff(c_503, plain, (![A_55, B_56, C_57]: (k5_xboole_0(k5_xboole_0(A_55, B_56), C_57)=k5_xboole_0(A_55, k5_xboole_0(B_56, C_57)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.34/5.58  tff(c_567, plain, (![A_25, C_57]: (k5_xboole_0(A_25, k5_xboole_0(A_25, C_57))=k5_xboole_0(k1_xboole_0, C_57))), inference(superposition, [status(thm), theory('equality')], [c_24, c_503])).
% 11.34/5.58  tff(c_580, plain, (![A_25, C_57]: (k5_xboole_0(A_25, k5_xboole_0(A_25, C_57))=C_57)), inference(demodulation, [status(thm), theory('equality')], [c_116, c_567])).
% 11.34/5.58  tff(c_1386, plain, (![A_82, B_83]: (k5_xboole_0(A_82, k4_xboole_0(A_82, B_83))=k3_xboole_0(B_83, A_82))), inference(superposition, [status(thm), theory('equality')], [c_1371, c_580])).
% 11.34/5.58  tff(c_223, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_206])).
% 11.34/5.58  tff(c_2332, plain, (![A_100, B_101]: (k5_xboole_0(A_100, k4_xboole_0(A_100, B_101))=k4_xboole_0(A_100, k4_xboole_0(A_100, B_101)))), inference(superposition, [status(thm), theory('equality')], [c_2314, c_223])).
% 11.34/5.58  tff(c_34025, plain, (![A_408, B_409]: (k4_xboole_0(A_408, k4_xboole_0(A_408, B_409))=k3_xboole_0(B_409, A_408))), inference(demodulation, [status(thm), theory('equality')], [c_1386, c_2332])).
% 11.34/5.58  tff(c_34659, plain, (![B_410, A_411]: (r1_tarski(k3_xboole_0(B_410, A_411), A_411))), inference(superposition, [status(thm), theory('equality')], [c_34025, c_14])).
% 11.34/5.58  tff(c_34785, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2424, c_34659])).
% 11.34/5.58  tff(c_34866, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_34785])).
% 11.34/5.58  tff(c_34867, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 11.34/5.58  tff(c_34966, plain, (![A_415, B_416]: (k3_xboole_0(A_415, B_416)=A_415 | ~r1_tarski(A_415, B_416))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.34/5.58  tff(c_34977, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_28, c_34966])).
% 11.34/5.58  tff(c_35359, plain, (![A_433, B_434, C_435]: (k4_xboole_0(k3_xboole_0(A_433, B_434), C_435)=k3_xboole_0(A_433, k4_xboole_0(B_434, C_435)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.34/5.58  tff(c_20, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.34/5.58  tff(c_35818, plain, (![A_446, B_447, C_448]: (r1_xboole_0(k3_xboole_0(A_446, k4_xboole_0(B_447, C_448)), C_448))), inference(superposition, [status(thm), theory('equality')], [c_35359, c_20])).
% 11.34/5.58  tff(c_35846, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34977, c_35818])).
% 11.34/5.58  tff(c_35869, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34867, c_35846])).
% 11.34/5.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.34/5.58  
% 11.34/5.58  Inference rules
% 11.34/5.58  ----------------------
% 11.34/5.58  #Ref     : 0
% 11.34/5.58  #Sup     : 8989
% 11.34/5.58  #Fact    : 0
% 11.34/5.58  #Define  : 0
% 11.34/5.58  #Split   : 1
% 11.34/5.58  #Chain   : 0
% 11.34/5.58  #Close   : 0
% 11.34/5.58  
% 11.34/5.58  Ordering : KBO
% 11.34/5.58  
% 11.34/5.58  Simplification rules
% 11.34/5.58  ----------------------
% 11.34/5.58  #Subsume      : 121
% 11.34/5.58  #Demod        : 10543
% 11.34/5.58  #Tautology    : 6389
% 11.34/5.58  #SimpNegUnit  : 2
% 11.34/5.58  #BackRed      : 5
% 11.34/5.58  
% 11.34/5.58  #Partial instantiations: 0
% 11.34/5.58  #Strategies tried      : 1
% 11.34/5.58  
% 11.34/5.58  Timing (in seconds)
% 11.34/5.58  ----------------------
% 11.34/5.58  Preprocessing        : 0.28
% 11.34/5.58  Parsing              : 0.15
% 11.34/5.58  CNF conversion       : 0.02
% 11.34/5.58  Main loop            : 4.42
% 11.34/5.58  Inferencing          : 0.72
% 11.34/5.58  Reduction            : 2.71
% 11.34/5.58  Demodulation         : 2.47
% 11.34/5.58  BG Simplification    : 0.08
% 11.34/5.58  Subsumption          : 0.71
% 11.34/5.58  Abstraction          : 0.13
% 11.34/5.58  MUC search           : 0.00
% 11.34/5.58  Cooper               : 0.00
% 11.34/5.58  Total                : 4.72
% 11.34/5.58  Index Insertion      : 0.00
% 11.34/5.58  Index Deletion       : 0.00
% 11.34/5.58  Index Matching       : 0.00
% 11.34/5.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
