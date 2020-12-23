%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:11 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 130 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :   70 ( 172 expanded)
%              Number of equality atoms :   34 (  74 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_xboole_0(A,B)
          & r1_tarski(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(c_10,plain,(
    ! [A_5] : ~ r2_xboole_0(A_5,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_43,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ r2_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_47,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_43])).

tff(c_81,plain,(
    ! [A_27,B_28] :
      ( k2_xboole_0(A_27,B_28) = B_28
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_88,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_47,c_81])).

tff(c_117,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_124,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_47,c_117])).

tff(c_22,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_229,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_250,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_229])).

tff(c_260,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_250])).

tff(c_26,plain,(
    ! [A_19,B_20] : k2_xboole_0(k3_xboole_0(A_19,B_20),k4_xboole_0(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_275,plain,(
    k2_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_26])).

tff(c_278,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_275])).

tff(c_328,plain,(
    ! [A_41,B_42] :
      ( r2_xboole_0(A_41,B_42)
      | B_42 = A_41
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_28,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_342,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_328,c_28])).

tff(c_343,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_342])).

tff(c_238,plain,(
    ! [A_38,B_39] : k2_xboole_0(k3_xboole_0(A_38,k4_xboole_0(A_38,B_39)),k3_xboole_0(A_38,B_39)) = A_38 ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_26])).

tff(c_20,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1077,plain,(
    ! [A_67,B_68] : k2_xboole_0(k3_xboole_0(A_67,k4_xboole_0(A_67,B_68)),k3_xboole_0(A_67,B_68)) = A_67 ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_26])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] : r1_tarski(k2_xboole_0(k3_xboole_0(A_11,B_12),k3_xboole_0(A_11,C_13)),k2_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1083,plain,(
    ! [A_67,B_68] : r1_tarski(A_67,k2_xboole_0(k4_xboole_0(A_67,B_68),B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1077,c_18])).

tff(c_1163,plain,(
    ! [A_69,B_70] : r1_tarski(A_69,k2_xboole_0(B_70,A_69)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2,c_1083])).

tff(c_1607,plain,(
    ! [A_82,B_83] : r1_tarski(k3_xboole_0(A_82,B_83),A_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_1163])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2218,plain,(
    ! [A_97,B_98] : k2_xboole_0(k3_xboole_0(A_97,B_98),A_97) = A_97 ),
    inference(resolution,[status(thm)],[c_1607,c_16])).

tff(c_2254,plain,(
    ! [A_97,B_98] : k2_xboole_0(A_97,k3_xboole_0(A_97,B_98)) = A_97 ),
    inference(superposition,[status(thm),theory(equality)],[c_2218,c_2])).

tff(c_30,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_89,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_81])).

tff(c_366,plain,(
    ! [A_44,B_45,C_46] : r1_tarski(k2_xboole_0(k3_xboole_0(A_44,B_45),k3_xboole_0(A_44,C_46)),k2_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_423,plain,(
    ! [A_44] : r1_tarski(k2_xboole_0(k3_xboole_0(A_44,'#skF_2'),k3_xboole_0(A_44,'#skF_3')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_366])).

tff(c_465,plain,(
    ! [A_49] : r1_tarski(k2_xboole_0(k3_xboole_0(A_49,'#skF_3'),k3_xboole_0(A_49,'#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_423])).

tff(c_474,plain,(
    r1_tarski(k2_xboole_0(k3_xboole_0('#skF_1','#skF_3'),'#skF_1'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_465])).

tff(c_480,plain,(
    r1_tarski(k2_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_474])).

tff(c_3180,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2254,c_480])).

tff(c_3183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_343,c_3180])).

tff(c_3184,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_342])).

tff(c_125,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_117])).

tff(c_3188,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3184,c_125])).

tff(c_3301,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3188,c_20])).

tff(c_3305,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_278,c_3301])).

tff(c_3315,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3305,c_32])).

tff(c_3320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_3315])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.78/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.67  
% 3.78/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.67  %$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.78/1.67  
% 3.78/1.67  %Foreground sorts:
% 3.78/1.67  
% 3.78/1.67  
% 3.78/1.67  %Background operators:
% 3.78/1.67  
% 3.78/1.67  
% 3.78/1.67  %Foreground operators:
% 3.78/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.78/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.78/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.78/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.78/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.78/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.78/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.78/1.67  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.78/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.78/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.78/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.78/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.78/1.67  
% 3.78/1.69  tff(f_37, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 3.78/1.69  tff(f_62, negated_conjecture, ~(![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_xboole_1)).
% 3.78/1.69  tff(f_34, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.78/1.69  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.78/1.69  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.78/1.69  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.78/1.69  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.78/1.69  tff(f_55, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.78/1.69  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.78/1.69  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.78/1.69  tff(f_47, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 3.78/1.69  tff(c_10, plain, (![A_5]: (~r2_xboole_0(A_5, A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.78/1.69  tff(c_32, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.78/1.69  tff(c_43, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~r2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.78/1.69  tff(c_47, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_43])).
% 3.78/1.69  tff(c_81, plain, (![A_27, B_28]: (k2_xboole_0(A_27, B_28)=B_28 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.78/1.69  tff(c_88, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_47, c_81])).
% 3.78/1.69  tff(c_117, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.78/1.69  tff(c_124, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_47, c_117])).
% 3.78/1.69  tff(c_22, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.78/1.69  tff(c_229, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.78/1.69  tff(c_250, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_124, c_229])).
% 3.78/1.69  tff(c_260, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_250])).
% 3.78/1.69  tff(c_26, plain, (![A_19, B_20]: (k2_xboole_0(k3_xboole_0(A_19, B_20), k4_xboole_0(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.78/1.69  tff(c_275, plain, (k2_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_260, c_26])).
% 3.78/1.69  tff(c_278, plain, (k2_xboole_0('#skF_1', k1_xboole_0)='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_275])).
% 3.78/1.69  tff(c_328, plain, (![A_41, B_42]: (r2_xboole_0(A_41, B_42) | B_42=A_41 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.78/1.69  tff(c_28, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.78/1.69  tff(c_342, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_328, c_28])).
% 3.78/1.69  tff(c_343, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_342])).
% 3.78/1.69  tff(c_238, plain, (![A_38, B_39]: (k2_xboole_0(k3_xboole_0(A_38, k4_xboole_0(A_38, B_39)), k3_xboole_0(A_38, B_39))=A_38)), inference(superposition, [status(thm), theory('equality')], [c_229, c_26])).
% 3.78/1.69  tff(c_20, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.78/1.69  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.78/1.69  tff(c_1077, plain, (![A_67, B_68]: (k2_xboole_0(k3_xboole_0(A_67, k4_xboole_0(A_67, B_68)), k3_xboole_0(A_67, B_68))=A_67)), inference(superposition, [status(thm), theory('equality')], [c_229, c_26])).
% 3.78/1.69  tff(c_18, plain, (![A_11, B_12, C_13]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_11, B_12), k3_xboole_0(A_11, C_13)), k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.78/1.69  tff(c_1083, plain, (![A_67, B_68]: (r1_tarski(A_67, k2_xboole_0(k4_xboole_0(A_67, B_68), B_68)))), inference(superposition, [status(thm), theory('equality')], [c_1077, c_18])).
% 3.78/1.69  tff(c_1163, plain, (![A_69, B_70]: (r1_tarski(A_69, k2_xboole_0(B_70, A_69)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2, c_1083])).
% 3.78/1.69  tff(c_1607, plain, (![A_82, B_83]: (r1_tarski(k3_xboole_0(A_82, B_83), A_82))), inference(superposition, [status(thm), theory('equality')], [c_238, c_1163])).
% 3.78/1.69  tff(c_16, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.78/1.69  tff(c_2218, plain, (![A_97, B_98]: (k2_xboole_0(k3_xboole_0(A_97, B_98), A_97)=A_97)), inference(resolution, [status(thm)], [c_1607, c_16])).
% 3.78/1.69  tff(c_2254, plain, (![A_97, B_98]: (k2_xboole_0(A_97, k3_xboole_0(A_97, B_98))=A_97)), inference(superposition, [status(thm), theory('equality')], [c_2218, c_2])).
% 3.78/1.69  tff(c_30, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.78/1.69  tff(c_89, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_30, c_81])).
% 3.78/1.69  tff(c_366, plain, (![A_44, B_45, C_46]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_44, B_45), k3_xboole_0(A_44, C_46)), k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.78/1.69  tff(c_423, plain, (![A_44]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_44, '#skF_2'), k3_xboole_0(A_44, '#skF_3')), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_366])).
% 3.78/1.69  tff(c_465, plain, (![A_49]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_49, '#skF_3'), k3_xboole_0(A_49, '#skF_2')), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_423])).
% 3.78/1.69  tff(c_474, plain, (r1_tarski(k2_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), '#skF_1'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_260, c_465])).
% 3.78/1.69  tff(c_480, plain, (r1_tarski(k2_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_474])).
% 3.78/1.69  tff(c_3180, plain, (r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2254, c_480])).
% 3.78/1.69  tff(c_3183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_343, c_3180])).
% 3.78/1.69  tff(c_3184, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_342])).
% 3.78/1.69  tff(c_125, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_117])).
% 3.78/1.69  tff(c_3188, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3184, c_125])).
% 3.78/1.69  tff(c_3301, plain, (k2_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3188, c_20])).
% 3.78/1.69  tff(c_3305, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_278, c_3301])).
% 3.78/1.69  tff(c_3315, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3305, c_32])).
% 3.78/1.69  tff(c_3320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_3315])).
% 3.78/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.69  
% 3.78/1.69  Inference rules
% 3.78/1.69  ----------------------
% 3.78/1.69  #Ref     : 0
% 3.78/1.69  #Sup     : 818
% 3.78/1.69  #Fact    : 0
% 3.78/1.69  #Define  : 0
% 3.78/1.69  #Split   : 1
% 3.78/1.69  #Chain   : 0
% 3.78/1.69  #Close   : 0
% 3.78/1.69  
% 3.78/1.69  Ordering : KBO
% 3.78/1.69  
% 3.78/1.69  Simplification rules
% 3.78/1.69  ----------------------
% 3.78/1.69  #Subsume      : 11
% 3.78/1.69  #Demod        : 708
% 3.78/1.69  #Tautology    : 542
% 3.78/1.69  #SimpNegUnit  : 2
% 3.78/1.69  #BackRed      : 26
% 3.78/1.69  
% 3.78/1.69  #Partial instantiations: 0
% 3.78/1.69  #Strategies tried      : 1
% 3.78/1.69  
% 3.78/1.69  Timing (in seconds)
% 3.78/1.69  ----------------------
% 3.78/1.69  Preprocessing        : 0.27
% 3.78/1.69  Parsing              : 0.15
% 3.78/1.69  CNF conversion       : 0.02
% 3.78/1.69  Main loop            : 0.66
% 3.78/1.69  Inferencing          : 0.20
% 3.78/1.69  Reduction            : 0.29
% 3.78/1.69  Demodulation         : 0.24
% 3.78/1.69  BG Simplification    : 0.02
% 3.78/1.69  Subsumption          : 0.09
% 3.78/1.69  Abstraction          : 0.03
% 3.78/1.69  MUC search           : 0.00
% 3.78/1.69  Cooper               : 0.00
% 3.78/1.69  Total                : 0.95
% 3.78/1.69  Index Insertion      : 0.00
% 3.78/1.69  Index Deletion       : 0.00
% 3.78/1.69  Index Matching       : 0.00
% 3.78/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
