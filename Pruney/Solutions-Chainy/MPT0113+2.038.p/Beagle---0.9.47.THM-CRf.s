%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:16 EST 2020

% Result     : Theorem 12.88s
% Output     : CNFRefutation 12.88s
% Verified   : 
% Statistics : Number of formulae       :   61 (  79 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   64 (  94 expanded)
%              Number of equality atoms :   32 (  40 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_84,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | k4_xboole_0(A_28,B_29) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_50,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_88,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_50])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_177,plain,(
    ! [A_38,B_39] : k5_xboole_0(A_38,k4_xboole_0(B_39,A_38)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_189,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = k2_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_177])).

tff(c_192,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_189])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_506,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_xboole_0(A_56,C_57)
      | ~ r1_xboole_0(B_58,C_57)
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_943,plain,(
    ! [A_81,B_82,A_83] :
      ( r1_xboole_0(A_81,B_82)
      | ~ r1_tarski(A_81,k4_xboole_0(A_83,B_82)) ) ),
    inference(resolution,[status(thm)],[c_22,c_506])).

tff(c_967,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_943])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_974,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_967,c_4])).

tff(c_990,plain,(
    k5_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_12])).

tff(c_1001,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_990])).

tff(c_16,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k3_xboole_0(A_10,B_11),C_12) = k3_xboole_0(A_10,k4_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_593,plain,(
    ! [A_65,B_66,C_67] : k4_xboole_0(k3_xboole_0(A_65,B_66),C_67) = k3_xboole_0(A_65,k4_xboole_0(B_66,C_67)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1333,plain,(
    ! [B_93,A_94,C_95] : k4_xboole_0(k3_xboole_0(B_93,A_94),C_95) = k3_xboole_0(A_94,k4_xboole_0(B_93,C_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_593])).

tff(c_8031,plain,(
    ! [B_234,A_235,C_236] : k3_xboole_0(B_234,k4_xboole_0(A_235,C_236)) = k3_xboole_0(A_235,k4_xboole_0(B_234,C_236)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1333])).

tff(c_35524,plain,(
    ! [B_549,C_550,A_551] : k3_xboole_0(k4_xboole_0(B_549,C_550),A_551) = k3_xboole_0(B_549,k4_xboole_0(A_551,C_550)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8031,c_2])).

tff(c_36476,plain,(
    ! [A_555] : k3_xboole_0('#skF_1',k4_xboole_0(A_555,'#skF_3')) = k3_xboole_0('#skF_1',A_555) ),
    inference(superposition,[status(thm),theory(equality)],[c_1001,c_35524])).

tff(c_36705,plain,(
    ! [A_555] : k5_xboole_0('#skF_1',k3_xboole_0('#skF_1',A_555)) = k4_xboole_0('#skF_1',k4_xboole_0(A_555,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36476,c_12])).

tff(c_46136,plain,(
    ! [A_611] : k4_xboole_0('#skF_1',k4_xboole_0(A_611,'#skF_3')) = k4_xboole_0('#skF_1',A_611) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_36705])).

tff(c_89,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_97,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_89])).

tff(c_46475,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_46136,c_97])).

tff(c_46602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_46475])).

tff(c_46603,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_46917,plain,(
    ! [A_635,C_636,B_637] :
      ( r1_xboole_0(A_635,C_636)
      | ~ r1_xboole_0(B_637,C_636)
      | ~ r1_tarski(A_635,B_637) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_47921,plain,(
    ! [A_688,B_689,A_690] :
      ( r1_xboole_0(A_688,B_689)
      | ~ r1_tarski(A_688,k4_xboole_0(A_690,B_689)) ) ),
    inference(resolution,[status(thm)],[c_22,c_46917])).

tff(c_47946,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_47921])).

tff(c_47951,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46603,c_47946])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:44:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.88/6.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.88/6.77  
% 12.88/6.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.88/6.77  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.88/6.77  
% 12.88/6.77  %Foreground sorts:
% 12.88/6.77  
% 12.88/6.77  
% 12.88/6.77  %Background operators:
% 12.88/6.77  
% 12.88/6.77  
% 12.88/6.77  %Foreground operators:
% 12.88/6.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.88/6.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.88/6.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.88/6.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.88/6.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.88/6.77  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.88/6.77  tff('#skF_2', type, '#skF_2': $i).
% 12.88/6.77  tff('#skF_3', type, '#skF_3': $i).
% 12.88/6.77  tff('#skF_1', type, '#skF_1': $i).
% 12.88/6.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.88/6.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.88/6.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.88/6.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.88/6.77  
% 12.88/6.79  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 12.88/6.79  tff(f_60, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 12.88/6.79  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.88/6.79  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 12.88/6.79  tff(f_43, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 12.88/6.79  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 12.88/6.79  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 12.88/6.79  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 12.88/6.79  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 12.88/6.79  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 12.88/6.79  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.88/6.79  tff(c_84, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | k4_xboole_0(A_28, B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.88/6.79  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.88/6.79  tff(c_50, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_26])).
% 12.88/6.79  tff(c_88, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_84, c_50])).
% 12.88/6.79  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.88/6.79  tff(c_14, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.88/6.79  tff(c_18, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.88/6.79  tff(c_177, plain, (![A_38, B_39]: (k5_xboole_0(A_38, k4_xboole_0(B_39, A_38))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.88/6.79  tff(c_189, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=k2_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_177])).
% 12.88/6.79  tff(c_192, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_189])).
% 12.88/6.79  tff(c_28, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.88/6.79  tff(c_22, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.88/6.79  tff(c_506, plain, (![A_56, C_57, B_58]: (r1_xboole_0(A_56, C_57) | ~r1_xboole_0(B_58, C_57) | ~r1_tarski(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.88/6.79  tff(c_943, plain, (![A_81, B_82, A_83]: (r1_xboole_0(A_81, B_82) | ~r1_tarski(A_81, k4_xboole_0(A_83, B_82)))), inference(resolution, [status(thm)], [c_22, c_506])).
% 12.88/6.79  tff(c_967, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_943])).
% 12.88/6.79  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.88/6.79  tff(c_974, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_967, c_4])).
% 12.88/6.79  tff(c_990, plain, (k5_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_974, c_12])).
% 12.88/6.79  tff(c_1001, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_192, c_990])).
% 12.88/6.79  tff(c_16, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k3_xboole_0(A_10, B_11), C_12)=k3_xboole_0(A_10, k4_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.88/6.79  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.88/6.79  tff(c_593, plain, (![A_65, B_66, C_67]: (k4_xboole_0(k3_xboole_0(A_65, B_66), C_67)=k3_xboole_0(A_65, k4_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.88/6.79  tff(c_1333, plain, (![B_93, A_94, C_95]: (k4_xboole_0(k3_xboole_0(B_93, A_94), C_95)=k3_xboole_0(A_94, k4_xboole_0(B_93, C_95)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_593])).
% 12.88/6.79  tff(c_8031, plain, (![B_234, A_235, C_236]: (k3_xboole_0(B_234, k4_xboole_0(A_235, C_236))=k3_xboole_0(A_235, k4_xboole_0(B_234, C_236)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1333])).
% 12.88/6.79  tff(c_35524, plain, (![B_549, C_550, A_551]: (k3_xboole_0(k4_xboole_0(B_549, C_550), A_551)=k3_xboole_0(B_549, k4_xboole_0(A_551, C_550)))), inference(superposition, [status(thm), theory('equality')], [c_8031, c_2])).
% 12.88/6.79  tff(c_36476, plain, (![A_555]: (k3_xboole_0('#skF_1', k4_xboole_0(A_555, '#skF_3'))=k3_xboole_0('#skF_1', A_555))), inference(superposition, [status(thm), theory('equality')], [c_1001, c_35524])).
% 12.88/6.79  tff(c_36705, plain, (![A_555]: (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', A_555))=k4_xboole_0('#skF_1', k4_xboole_0(A_555, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_36476, c_12])).
% 12.88/6.79  tff(c_46136, plain, (![A_611]: (k4_xboole_0('#skF_1', k4_xboole_0(A_611, '#skF_3'))=k4_xboole_0('#skF_1', A_611))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_36705])).
% 12.88/6.79  tff(c_89, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.88/6.79  tff(c_97, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_89])).
% 12.88/6.79  tff(c_46475, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_46136, c_97])).
% 12.88/6.79  tff(c_46602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_46475])).
% 12.88/6.79  tff(c_46603, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 12.88/6.79  tff(c_46917, plain, (![A_635, C_636, B_637]: (r1_xboole_0(A_635, C_636) | ~r1_xboole_0(B_637, C_636) | ~r1_tarski(A_635, B_637))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.88/6.79  tff(c_47921, plain, (![A_688, B_689, A_690]: (r1_xboole_0(A_688, B_689) | ~r1_tarski(A_688, k4_xboole_0(A_690, B_689)))), inference(resolution, [status(thm)], [c_22, c_46917])).
% 12.88/6.79  tff(c_47946, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_47921])).
% 12.88/6.79  tff(c_47951, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46603, c_47946])).
% 12.88/6.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.88/6.79  
% 12.88/6.79  Inference rules
% 12.88/6.79  ----------------------
% 12.88/6.79  #Ref     : 0
% 12.88/6.79  #Sup     : 12065
% 12.88/6.79  #Fact    : 0
% 12.88/6.79  #Define  : 0
% 12.88/6.79  #Split   : 4
% 12.88/6.79  #Chain   : 0
% 12.88/6.79  #Close   : 0
% 12.88/6.79  
% 12.88/6.79  Ordering : KBO
% 12.88/6.79  
% 12.88/6.79  Simplification rules
% 12.88/6.79  ----------------------
% 12.88/6.79  #Subsume      : 1458
% 12.88/6.79  #Demod        : 9179
% 12.88/6.79  #Tautology    : 8087
% 12.88/6.79  #SimpNegUnit  : 18
% 12.88/6.79  #BackRed      : 19
% 12.88/6.79  
% 12.88/6.79  #Partial instantiations: 0
% 12.88/6.79  #Strategies tried      : 1
% 12.88/6.79  
% 12.88/6.79  Timing (in seconds)
% 12.88/6.79  ----------------------
% 12.88/6.79  Preprocessing        : 0.32
% 12.88/6.79  Parsing              : 0.16
% 12.88/6.79  CNF conversion       : 0.02
% 12.88/6.79  Main loop            : 5.72
% 12.88/6.79  Inferencing          : 0.84
% 12.88/6.79  Reduction            : 3.44
% 12.88/6.79  Demodulation         : 3.04
% 12.88/6.79  BG Simplification    : 0.08
% 12.88/6.79  Subsumption          : 1.12
% 12.88/6.79  Abstraction          : 0.13
% 12.88/6.79  MUC search           : 0.00
% 12.88/6.79  Cooper               : 0.00
% 12.88/6.79  Total                : 6.07
% 12.88/6.79  Index Insertion      : 0.00
% 12.88/6.79  Index Deletion       : 0.00
% 12.88/6.79  Index Matching       : 0.00
% 12.88/6.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
