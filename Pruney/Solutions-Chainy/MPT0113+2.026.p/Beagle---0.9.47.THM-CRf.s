%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:14 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   48 (  63 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 (  75 expanded)
%              Number of equality atoms :   22 (  28 expanded)
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
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_76,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | k4_xboole_0(A_28,B_29) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_65,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_80,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_76,c_65])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_81,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_81])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_164,plain,(
    r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_14])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_175,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_164,c_12])).

tff(c_198,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_175])).

tff(c_100,plain,(
    ! [A_11,B_12] : k4_xboole_0(k4_xboole_0(A_11,B_12),A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_81])).

tff(c_133,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = A_37
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_157,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_133])).

tff(c_373,plain,(
    ! [A_41,B_42,C_43] : k4_xboole_0(k3_xboole_0(A_41,B_42),C_43) = k3_xboole_0(A_41,k4_xboole_0(B_42,C_43)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_463,plain,(
    ! [C_46] : k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_46)) = k4_xboole_0('#skF_1',C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_373])).

tff(c_490,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_463])).

tff(c_495,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_490])).

tff(c_497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_495])).

tff(c_498,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_586,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_618,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_586])).

tff(c_817,plain,(
    ! [A_60,B_61,C_62] : k4_xboole_0(k3_xboole_0(A_60,B_61),C_62) = k3_xboole_0(A_60,k4_xboole_0(B_61,C_62)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1167,plain,(
    ! [A_75,B_76,C_77] : r1_xboole_0(k3_xboole_0(A_75,k4_xboole_0(B_76,C_77)),C_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_817,c_18])).

tff(c_1191,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_618,c_1167])).

tff(c_1215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_498,c_1191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:07:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.36  
% 2.63/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.36  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.63/1.36  
% 2.63/1.36  %Foreground sorts:
% 2.63/1.36  
% 2.63/1.36  
% 2.63/1.36  %Background operators:
% 2.63/1.36  
% 2.63/1.36  
% 2.63/1.36  %Foreground operators:
% 2.63/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.63/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.63/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.63/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.63/1.36  
% 2.72/1.37  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.72/1.37  tff(f_52, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.72/1.37  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.72/1.37  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.72/1.37  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.72/1.37  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.72/1.37  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.72/1.37  tff(c_76, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | k4_xboole_0(A_28, B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.37  tff(c_20, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.72/1.37  tff(c_65, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_20])).
% 2.72/1.37  tff(c_80, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_76, c_65])).
% 2.72/1.37  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.72/1.37  tff(c_22, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.72/1.37  tff(c_81, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.37  tff(c_101, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_81])).
% 2.72/1.37  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.72/1.37  tff(c_164, plain, (r1_tarski(k1_xboole_0, '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_101, c_14])).
% 2.72/1.37  tff(c_12, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.37  tff(c_175, plain, (k3_xboole_0(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_164, c_12])).
% 2.72/1.37  tff(c_198, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2, c_175])).
% 2.72/1.37  tff(c_100, plain, (![A_11, B_12]: (k4_xboole_0(k4_xboole_0(A_11, B_12), A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_81])).
% 2.72/1.37  tff(c_133, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=A_37 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.37  tff(c_157, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_22, c_133])).
% 2.72/1.37  tff(c_373, plain, (![A_41, B_42, C_43]: (k4_xboole_0(k3_xboole_0(A_41, B_42), C_43)=k3_xboole_0(A_41, k4_xboole_0(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.72/1.37  tff(c_463, plain, (![C_46]: (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_46))=k4_xboole_0('#skF_1', C_46))), inference(superposition, [status(thm), theory('equality')], [c_157, c_373])).
% 2.72/1.37  tff(c_490, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_100, c_463])).
% 2.72/1.37  tff(c_495, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_198, c_490])).
% 2.72/1.37  tff(c_497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_495])).
% 2.72/1.37  tff(c_498, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_20])).
% 2.72/1.37  tff(c_586, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.37  tff(c_618, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_22, c_586])).
% 2.72/1.37  tff(c_817, plain, (![A_60, B_61, C_62]: (k4_xboole_0(k3_xboole_0(A_60, B_61), C_62)=k3_xboole_0(A_60, k4_xboole_0(B_61, C_62)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.72/1.37  tff(c_18, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.72/1.37  tff(c_1167, plain, (![A_75, B_76, C_77]: (r1_xboole_0(k3_xboole_0(A_75, k4_xboole_0(B_76, C_77)), C_77))), inference(superposition, [status(thm), theory('equality')], [c_817, c_18])).
% 2.72/1.37  tff(c_1191, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_618, c_1167])).
% 2.72/1.37  tff(c_1215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_498, c_1191])).
% 2.72/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.37  
% 2.72/1.37  Inference rules
% 2.72/1.37  ----------------------
% 2.72/1.37  #Ref     : 0
% 2.72/1.37  #Sup     : 341
% 2.72/1.37  #Fact    : 0
% 2.72/1.37  #Define  : 0
% 2.72/1.37  #Split   : 1
% 2.72/1.37  #Chain   : 0
% 2.72/1.37  #Close   : 0
% 2.72/1.37  
% 2.72/1.37  Ordering : KBO
% 2.72/1.37  
% 2.72/1.37  Simplification rules
% 2.72/1.37  ----------------------
% 2.72/1.37  #Subsume      : 0
% 2.72/1.37  #Demod        : 136
% 2.72/1.37  #Tautology    : 210
% 2.72/1.37  #SimpNegUnit  : 2
% 2.72/1.37  #BackRed      : 0
% 2.72/1.37  
% 2.72/1.37  #Partial instantiations: 0
% 2.72/1.37  #Strategies tried      : 1
% 2.72/1.37  
% 2.72/1.37  Timing (in seconds)
% 2.72/1.37  ----------------------
% 2.72/1.38  Preprocessing        : 0.27
% 2.72/1.38  Parsing              : 0.14
% 2.72/1.38  CNF conversion       : 0.01
% 2.72/1.38  Main loop            : 0.36
% 2.72/1.38  Inferencing          : 0.13
% 2.72/1.38  Reduction            : 0.13
% 2.72/1.38  Demodulation         : 0.10
% 2.72/1.38  BG Simplification    : 0.02
% 2.72/1.38  Subsumption          : 0.05
% 2.72/1.38  Abstraction          : 0.02
% 2.72/1.38  MUC search           : 0.00
% 2.72/1.38  Cooper               : 0.00
% 2.72/1.38  Total                : 0.65
% 2.72/1.38  Index Insertion      : 0.00
% 2.72/1.38  Index Deletion       : 0.00
% 2.72/1.38  Index Matching       : 0.00
% 2.72/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
