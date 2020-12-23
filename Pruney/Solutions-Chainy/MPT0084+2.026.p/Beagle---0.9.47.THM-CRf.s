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
% DateTime   : Thu Dec  3 09:44:07 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 153 expanded)
%              Number of leaves         :   20 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :   59 ( 158 expanded)
%              Number of equality atoms :   46 ( 132 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(c_134,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | k3_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_138,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_134,c_24])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_124,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_128,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_124])).

tff(c_336,plain,(
    ! [A_34,B_35,C_36] : k4_xboole_0(k3_xboole_0(A_34,B_35),C_36) = k3_xboole_0(A_34,k4_xboole_0(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_382,plain,(
    ! [C_36] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_3',C_36)) = k4_xboole_0('#skF_1',C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_336])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_25,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_139,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_147,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_25,c_139])).

tff(c_204,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_14])).

tff(c_207,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_204])).

tff(c_16,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_217,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_252,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_217])).

tff(c_263,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_252])).

tff(c_230,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,k4_xboole_0(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_217])).

tff(c_482,plain,(
    ! [A_39,B_40] : k3_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k4_xboole_0(A_39,B_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_230])).

tff(c_148,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k3_xboole_0(A_27,B_28)) = k4_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_163,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_148])).

tff(c_488,plain,(
    ! [A_39,B_40] : k4_xboole_0(k4_xboole_0(A_39,B_40),k4_xboole_0(A_39,B_40)) = k4_xboole_0(k4_xboole_0(A_39,B_40),A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_163])).

tff(c_591,plain,(
    ! [A_42,B_43] : k4_xboole_0(k4_xboole_0(A_42,B_43),A_42) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_488])).

tff(c_658,plain,(
    ! [A_44,B_45] : k4_xboole_0(k3_xboole_0(A_44,B_45),A_44) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_591])).

tff(c_819,plain,(
    ! [B_48,A_49] : k4_xboole_0(k3_xboole_0(B_48,A_49),A_49) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_658])).

tff(c_1056,plain,(
    ! [C_52] : k4_xboole_0(k4_xboole_0('#skF_1',C_52),k4_xboole_0('#skF_3',C_52)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_819])).

tff(c_1113,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_2'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_1056])).

tff(c_1140,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1113])).

tff(c_1338,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1140,c_16])).

tff(c_1347,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_12,c_1338])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k3_xboole_0(A_13,B_14),C_15) = k3_xboole_0(A_13,k4_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_728,plain,(
    ! [A_46,B_47] : k3_xboole_0(A_46,k4_xboole_0(B_47,A_46)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_658,c_18])).

tff(c_750,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k4_xboole_0(B_47,A_46)) = k4_xboole_0(A_46,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_728,c_14])).

tff(c_950,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k4_xboole_0(B_51,A_50)) = A_50 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_750])).

tff(c_669,plain,(
    ! [A_44,B_45] : k3_xboole_0(A_44,k4_xboole_0(B_45,A_44)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_658,c_18])).

tff(c_959,plain,(
    ! [B_51,A_50] : k3_xboole_0(k4_xboole_0(B_51,A_50),A_50) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_950,c_669])).

tff(c_1352,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1347,c_959])).

tff(c_1374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_1352])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.90  
% 3.31/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.91  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.31/1.91  
% 3.31/1.91  %Foreground sorts:
% 3.31/1.91  
% 3.31/1.91  
% 3.31/1.91  %Background operators:
% 3.31/1.91  
% 3.31/1.91  
% 3.31/1.91  %Foreground operators:
% 3.31/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.31/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.31/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.91  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.31/1.91  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.91  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.91  tff('#skF_1', type, '#skF_1': $i).
% 3.31/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.31/1.91  
% 3.71/1.93  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.71/1.93  tff(f_54, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 3.71/1.93  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.71/1.93  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.71/1.93  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.71/1.93  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.71/1.93  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.71/1.93  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.71/1.93  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.71/1.93  tff(c_134, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | k3_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.71/1.93  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.71/1.93  tff(c_138, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_134, c_24])).
% 3.71/1.93  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.71/1.93  tff(c_124, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.71/1.93  tff(c_128, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_22, c_124])).
% 3.71/1.93  tff(c_336, plain, (![A_34, B_35, C_36]: (k4_xboole_0(k3_xboole_0(A_34, B_35), C_36)=k3_xboole_0(A_34, k4_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.71/1.93  tff(c_382, plain, (![C_36]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_3', C_36))=k4_xboole_0('#skF_1', C_36))), inference(superposition, [status(thm), theory('equality')], [c_128, c_336])).
% 3.71/1.93  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.71/1.93  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.71/1.93  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.71/1.93  tff(c_20, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.71/1.93  tff(c_25, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 3.71/1.93  tff(c_139, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.71/1.93  tff(c_147, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_25, c_139])).
% 3.71/1.93  tff(c_204, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_147, c_14])).
% 3.71/1.93  tff(c_207, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_204])).
% 3.71/1.93  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.71/1.93  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.71/1.93  tff(c_217, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.71/1.93  tff(c_252, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_217])).
% 3.71/1.93  tff(c_263, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_252])).
% 3.71/1.93  tff(c_230, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k3_xboole_0(A_11, k4_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_217])).
% 3.71/1.93  tff(c_482, plain, (![A_39, B_40]: (k3_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k4_xboole_0(A_39, B_40))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_230])).
% 3.71/1.93  tff(c_148, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k3_xboole_0(A_27, B_28))=k4_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.71/1.93  tff(c_163, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_148])).
% 3.71/1.93  tff(c_488, plain, (![A_39, B_40]: (k4_xboole_0(k4_xboole_0(A_39, B_40), k4_xboole_0(A_39, B_40))=k4_xboole_0(k4_xboole_0(A_39, B_40), A_39))), inference(superposition, [status(thm), theory('equality')], [c_482, c_163])).
% 3.71/1.93  tff(c_591, plain, (![A_42, B_43]: (k4_xboole_0(k4_xboole_0(A_42, B_43), A_42)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_263, c_488])).
% 3.71/1.93  tff(c_658, plain, (![A_44, B_45]: (k4_xboole_0(k3_xboole_0(A_44, B_45), A_44)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_591])).
% 3.71/1.93  tff(c_819, plain, (![B_48, A_49]: (k4_xboole_0(k3_xboole_0(B_48, A_49), A_49)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_658])).
% 3.71/1.93  tff(c_1056, plain, (![C_52]: (k4_xboole_0(k4_xboole_0('#skF_1', C_52), k4_xboole_0('#skF_3', C_52))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_382, c_819])).
% 3.71/1.93  tff(c_1113, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_2')))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_207, c_1056])).
% 3.71/1.93  tff(c_1140, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1113])).
% 3.71/1.93  tff(c_1338, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1140, c_16])).
% 3.71/1.93  tff(c_1347, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_382, c_12, c_1338])).
% 3.71/1.93  tff(c_18, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k3_xboole_0(A_13, B_14), C_15)=k3_xboole_0(A_13, k4_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.71/1.93  tff(c_728, plain, (![A_46, B_47]: (k3_xboole_0(A_46, k4_xboole_0(B_47, A_46))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_658, c_18])).
% 3.71/1.93  tff(c_750, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k4_xboole_0(B_47, A_46))=k4_xboole_0(A_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_728, c_14])).
% 3.71/1.93  tff(c_950, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k4_xboole_0(B_51, A_50))=A_50)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_750])).
% 3.71/1.93  tff(c_669, plain, (![A_44, B_45]: (k3_xboole_0(A_44, k4_xboole_0(B_45, A_44))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_658, c_18])).
% 3.71/1.93  tff(c_959, plain, (![B_51, A_50]: (k3_xboole_0(k4_xboole_0(B_51, A_50), A_50)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_950, c_669])).
% 3.71/1.93  tff(c_1352, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1347, c_959])).
% 3.71/1.93  tff(c_1374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_1352])).
% 3.71/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.93  
% 3.71/1.93  Inference rules
% 3.71/1.93  ----------------------
% 3.71/1.93  #Ref     : 0
% 3.71/1.93  #Sup     : 340
% 3.71/1.93  #Fact    : 0
% 3.71/1.93  #Define  : 0
% 3.71/1.93  #Split   : 0
% 3.71/1.93  #Chain   : 0
% 3.71/1.93  #Close   : 0
% 3.71/1.93  
% 3.71/1.93  Ordering : KBO
% 3.71/1.93  
% 3.71/1.93  Simplification rules
% 3.71/1.93  ----------------------
% 3.71/1.93  #Subsume      : 0
% 3.71/1.93  #Demod        : 241
% 3.71/1.93  #Tautology    : 242
% 3.71/1.93  #SimpNegUnit  : 1
% 3.71/1.93  #BackRed      : 1
% 3.71/1.93  
% 3.71/1.93  #Partial instantiations: 0
% 3.71/1.93  #Strategies tried      : 1
% 3.71/1.93  
% 3.71/1.93  Timing (in seconds)
% 3.71/1.93  ----------------------
% 3.71/1.94  Preprocessing        : 0.44
% 3.71/1.94  Parsing              : 0.23
% 3.71/1.94  CNF conversion       : 0.03
% 3.71/1.94  Main loop            : 0.59
% 3.71/1.94  Inferencing          : 0.20
% 3.71/1.94  Reduction            : 0.25
% 3.71/1.94  Demodulation         : 0.21
% 3.71/1.94  BG Simplification    : 0.03
% 3.71/1.94  Subsumption          : 0.08
% 3.71/1.94  Abstraction          : 0.03
% 3.71/1.94  MUC search           : 0.00
% 3.71/1.94  Cooper               : 0.00
% 3.71/1.94  Total                : 1.08
% 3.71/1.94  Index Insertion      : 0.00
% 3.71/1.94  Index Deletion       : 0.00
% 3.71/1.94  Index Matching       : 0.00
% 3.71/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
