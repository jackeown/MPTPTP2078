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
% DateTime   : Thu Dec  3 09:43:20 EST 2020

% Result     : Theorem 4.81s
% Output     : CNFRefutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 163 expanded)
%              Number of leaves         :   26 (  65 expanded)
%              Depth                    :   16
%              Number of atoms          :   80 ( 184 expanded)
%              Number of equality atoms :   51 ( 109 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_155,plain,(
    ! [A_37,B_38] :
      ( r1_xboole_0(A_37,B_38)
      | k3_xboole_0(A_37,B_38) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_322,plain,(
    ! [B_50,A_51] :
      ( r1_xboole_0(B_50,A_51)
      | k3_xboole_0(A_51,B_50) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_155,c_8])).

tff(c_32,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_333,plain,(
    k3_xboole_0('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_322,c_32])).

tff(c_24,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_55,plain,(
    ! [A_29,B_30] : r1_tarski(k4_xboole_0(A_29,B_30),A_29) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_58,plain,(
    ! [A_19] : r1_tarski(A_19,A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_55])).

tff(c_163,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,B_40) = k1_xboole_0
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_195,plain,(
    ! [A_41] : k4_xboole_0(A_41,A_41) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_163])).

tff(c_20,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_216,plain,(
    ! [A_42] : r1_tarski(k1_xboole_0,A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_20])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_220,plain,(
    ! [A_42] : k4_xboole_0(k1_xboole_0,A_42) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_216,c_16])).

tff(c_334,plain,(
    ! [A_52,B_53] : k4_xboole_0(A_52,k4_xboole_0(A_52,B_53)) = k3_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_366,plain,(
    ! [B_53] : k3_xboole_0(k1_xboole_0,B_53) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_334])).

tff(c_28,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_34,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_60,plain,(
    ! [B_32,A_33] :
      ( r1_xboole_0(B_32,A_33)
      | ~ r1_xboole_0(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_63,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_60])).

tff(c_296,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = k1_xboole_0
      | ~ r1_xboole_0(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_307,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_63,c_296])).

tff(c_621,plain,(
    ! [A_68,B_69] : k2_xboole_0(k3_xboole_0(A_68,B_69),k4_xboole_0(A_68,B_69)) = A_68 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_645,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_4','#skF_3')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_621])).

tff(c_68,plain,(
    ! [B_34,A_35] : k2_xboole_0(B_34,A_35) = k2_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_84,plain,(
    ! [A_35] : k2_xboole_0(k1_xboole_0,A_35) = A_35 ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_18])).

tff(c_783,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_84])).

tff(c_173,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_163])).

tff(c_438,plain,(
    ! [A_57,B_58] : k2_xboole_0(A_57,k4_xboole_0(B_58,A_57)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_460,plain,(
    ! [A_19] : k2_xboole_0(A_19,k1_xboole_0) = k2_xboole_0(A_19,A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_438])).

tff(c_477,plain,(
    ! [A_19] : k2_xboole_0(A_19,A_19) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_460])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_175,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_163])).

tff(c_926,plain,(
    ! [A_78,B_79,C_80] : k4_xboole_0(k4_xboole_0(A_78,B_79),C_80) = k4_xboole_0(A_78,k2_xboole_0(B_79,C_80)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1007,plain,(
    ! [C_80] : k4_xboole_0('#skF_2',k2_xboole_0('#skF_3',C_80)) = k4_xboole_0(k1_xboole_0,C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_926])).

tff(c_1120,plain,(
    ! [C_83] : k4_xboole_0('#skF_2',k2_xboole_0('#skF_3',C_83)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_1007])).

tff(c_22,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1137,plain,(
    ! [C_83] : k2_xboole_0(k2_xboole_0('#skF_3',C_83),k1_xboole_0) = k2_xboole_0(k2_xboole_0('#skF_3',C_83),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1120,c_22])).

tff(c_5483,plain,(
    ! [C_162] : k2_xboole_0('#skF_2',k2_xboole_0('#skF_3',C_162)) = k2_xboole_0('#skF_3',C_162) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18,c_1137])).

tff(c_5546,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k2_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_5483])).

tff(c_5583,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_5546])).

tff(c_962,plain,(
    ! [A_78,B_79,C_80] : r1_tarski(k4_xboole_0(A_78,k2_xboole_0(B_79,C_80)),k4_xboole_0(A_78,B_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_926,c_20])).

tff(c_5648,plain,(
    ! [A_163] : r1_tarski(k4_xboole_0(A_163,'#skF_3'),k4_xboole_0(A_163,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5583,c_962])).

tff(c_5676,plain,(
    r1_tarski('#skF_4',k4_xboole_0('#skF_4','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_5648])).

tff(c_5731,plain,(
    k4_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5676,c_16])).

tff(c_375,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k3_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_334])).

tff(c_382,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_375])).

tff(c_174,plain,(
    ! [A_15,B_16] : k4_xboole_0(k4_xboole_0(A_15,B_16),A_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_163])).

tff(c_1770,plain,(
    ! [A_99,B_100] : k2_xboole_0(k3_xboole_0(A_99,k4_xboole_0(A_99,B_100)),k3_xboole_0(A_99,B_100)) = A_99 ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_621])).

tff(c_1858,plain,(
    ! [A_15,B_16] : k2_xboole_0(k3_xboole_0(k4_xboole_0(A_15,B_16),k1_xboole_0),k3_xboole_0(k4_xboole_0(A_15,B_16),A_15)) = k4_xboole_0(A_15,B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_1770])).

tff(c_1898,plain,(
    ! [A_15,B_16] : k3_xboole_0(k4_xboole_0(A_15,B_16),A_15) = k4_xboole_0(A_15,B_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_382,c_1858])).

tff(c_5754,plain,(
    k4_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_2')) = k3_xboole_0(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5731,c_1898])).

tff(c_5797,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_28,c_5754])).

tff(c_5799,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_333,c_5797])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:14:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.81/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/2.03  
% 4.81/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/2.03  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.81/2.03  
% 4.81/2.03  %Foreground sorts:
% 4.81/2.03  
% 4.81/2.03  
% 4.81/2.03  %Background operators:
% 4.81/2.03  
% 4.81/2.03  
% 4.81/2.03  %Foreground operators:
% 4.81/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.81/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.81/2.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.81/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.81/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.81/2.03  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.81/2.03  tff('#skF_2', type, '#skF_2': $i).
% 4.81/2.03  tff('#skF_3', type, '#skF_3': $i).
% 4.81/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.81/2.03  tff('#skF_4', type, '#skF_4': $i).
% 4.81/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.81/2.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.81/2.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.81/2.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.81/2.03  
% 4.81/2.05  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.81/2.05  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.81/2.05  tff(f_74, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 4.81/2.05  tff(f_61, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.81/2.05  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.81/2.05  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.81/2.05  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.81/2.05  tff(f_67, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.81/2.05  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.81/2.05  tff(f_55, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.81/2.05  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.81/2.05  tff(f_63, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.81/2.05  tff(c_155, plain, (![A_37, B_38]: (r1_xboole_0(A_37, B_38) | k3_xboole_0(A_37, B_38)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.81/2.05  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.81/2.05  tff(c_322, plain, (![B_50, A_51]: (r1_xboole_0(B_50, A_51) | k3_xboole_0(A_51, B_50)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_155, c_8])).
% 4.81/2.05  tff(c_32, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.81/2.05  tff(c_333, plain, (k3_xboole_0('#skF_4', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_322, c_32])).
% 4.81/2.05  tff(c_24, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.81/2.05  tff(c_55, plain, (![A_29, B_30]: (r1_tarski(k4_xboole_0(A_29, B_30), A_29))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.81/2.05  tff(c_58, plain, (![A_19]: (r1_tarski(A_19, A_19))), inference(superposition, [status(thm), theory('equality')], [c_24, c_55])).
% 4.81/2.05  tff(c_163, plain, (![A_39, B_40]: (k4_xboole_0(A_39, B_40)=k1_xboole_0 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.81/2.05  tff(c_195, plain, (![A_41]: (k4_xboole_0(A_41, A_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_163])).
% 4.81/2.05  tff(c_20, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.81/2.05  tff(c_216, plain, (![A_42]: (r1_tarski(k1_xboole_0, A_42))), inference(superposition, [status(thm), theory('equality')], [c_195, c_20])).
% 4.81/2.05  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.81/2.05  tff(c_220, plain, (![A_42]: (k4_xboole_0(k1_xboole_0, A_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_216, c_16])).
% 4.81/2.05  tff(c_334, plain, (![A_52, B_53]: (k4_xboole_0(A_52, k4_xboole_0(A_52, B_53))=k3_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.81/2.05  tff(c_366, plain, (![B_53]: (k3_xboole_0(k1_xboole_0, B_53)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_220, c_334])).
% 4.81/2.05  tff(c_28, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.81/2.05  tff(c_34, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.81/2.05  tff(c_60, plain, (![B_32, A_33]: (r1_xboole_0(B_32, A_33) | ~r1_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.81/2.05  tff(c_63, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_60])).
% 4.81/2.05  tff(c_296, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=k1_xboole_0 | ~r1_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.81/2.05  tff(c_307, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_63, c_296])).
% 4.81/2.05  tff(c_621, plain, (![A_68, B_69]: (k2_xboole_0(k3_xboole_0(A_68, B_69), k4_xboole_0(A_68, B_69))=A_68)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.81/2.05  tff(c_645, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_4', '#skF_3'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_307, c_621])).
% 4.81/2.05  tff(c_68, plain, (![B_34, A_35]: (k2_xboole_0(B_34, A_35)=k2_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.81/2.05  tff(c_18, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.81/2.05  tff(c_84, plain, (![A_35]: (k2_xboole_0(k1_xboole_0, A_35)=A_35)), inference(superposition, [status(thm), theory('equality')], [c_68, c_18])).
% 4.81/2.05  tff(c_783, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_645, c_84])).
% 4.81/2.05  tff(c_173, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_163])).
% 4.81/2.05  tff(c_438, plain, (![A_57, B_58]: (k2_xboole_0(A_57, k4_xboole_0(B_58, A_57))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.81/2.05  tff(c_460, plain, (![A_19]: (k2_xboole_0(A_19, k1_xboole_0)=k2_xboole_0(A_19, A_19))), inference(superposition, [status(thm), theory('equality')], [c_173, c_438])).
% 4.81/2.05  tff(c_477, plain, (![A_19]: (k2_xboole_0(A_19, A_19)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_460])).
% 4.81/2.05  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.81/2.05  tff(c_36, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.81/2.05  tff(c_175, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_163])).
% 4.81/2.05  tff(c_926, plain, (![A_78, B_79, C_80]: (k4_xboole_0(k4_xboole_0(A_78, B_79), C_80)=k4_xboole_0(A_78, k2_xboole_0(B_79, C_80)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.81/2.05  tff(c_1007, plain, (![C_80]: (k4_xboole_0('#skF_2', k2_xboole_0('#skF_3', C_80))=k4_xboole_0(k1_xboole_0, C_80))), inference(superposition, [status(thm), theory('equality')], [c_175, c_926])).
% 4.81/2.05  tff(c_1120, plain, (![C_83]: (k4_xboole_0('#skF_2', k2_xboole_0('#skF_3', C_83))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_220, c_1007])).
% 4.81/2.05  tff(c_22, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.81/2.05  tff(c_1137, plain, (![C_83]: (k2_xboole_0(k2_xboole_0('#skF_3', C_83), k1_xboole_0)=k2_xboole_0(k2_xboole_0('#skF_3', C_83), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1120, c_22])).
% 4.81/2.05  tff(c_5483, plain, (![C_162]: (k2_xboole_0('#skF_2', k2_xboole_0('#skF_3', C_162))=k2_xboole_0('#skF_3', C_162))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18, c_1137])).
% 4.81/2.05  tff(c_5546, plain, (k2_xboole_0('#skF_2', '#skF_3')=k2_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_477, c_5483])).
% 4.81/2.05  tff(c_5583, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_477, c_5546])).
% 4.81/2.05  tff(c_962, plain, (![A_78, B_79, C_80]: (r1_tarski(k4_xboole_0(A_78, k2_xboole_0(B_79, C_80)), k4_xboole_0(A_78, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_926, c_20])).
% 4.81/2.05  tff(c_5648, plain, (![A_163]: (r1_tarski(k4_xboole_0(A_163, '#skF_3'), k4_xboole_0(A_163, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_5583, c_962])).
% 4.81/2.05  tff(c_5676, plain, (r1_tarski('#skF_4', k4_xboole_0('#skF_4', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_783, c_5648])).
% 4.81/2.05  tff(c_5731, plain, (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_5676, c_16])).
% 4.81/2.05  tff(c_375, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k3_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_334])).
% 4.81/2.05  tff(c_382, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_173, c_375])).
% 4.81/2.05  tff(c_174, plain, (![A_15, B_16]: (k4_xboole_0(k4_xboole_0(A_15, B_16), A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_163])).
% 4.81/2.05  tff(c_1770, plain, (![A_99, B_100]: (k2_xboole_0(k3_xboole_0(A_99, k4_xboole_0(A_99, B_100)), k3_xboole_0(A_99, B_100))=A_99)), inference(superposition, [status(thm), theory('equality')], [c_28, c_621])).
% 4.81/2.05  tff(c_1858, plain, (![A_15, B_16]: (k2_xboole_0(k3_xboole_0(k4_xboole_0(A_15, B_16), k1_xboole_0), k3_xboole_0(k4_xboole_0(A_15, B_16), A_15))=k4_xboole_0(A_15, B_16))), inference(superposition, [status(thm), theory('equality')], [c_174, c_1770])).
% 4.81/2.05  tff(c_1898, plain, (![A_15, B_16]: (k3_xboole_0(k4_xboole_0(A_15, B_16), A_15)=k4_xboole_0(A_15, B_16))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_382, c_1858])).
% 4.81/2.05  tff(c_5754, plain, (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_2'))=k3_xboole_0(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5731, c_1898])).
% 4.81/2.05  tff(c_5797, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_366, c_28, c_5754])).
% 4.81/2.05  tff(c_5799, plain, $false, inference(negUnitSimplification, [status(thm)], [c_333, c_5797])).
% 4.81/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/2.05  
% 4.81/2.05  Inference rules
% 4.81/2.05  ----------------------
% 4.81/2.05  #Ref     : 0
% 4.81/2.05  #Sup     : 1425
% 4.81/2.05  #Fact    : 0
% 4.81/2.05  #Define  : 0
% 4.81/2.05  #Split   : 1
% 4.81/2.05  #Chain   : 0
% 4.81/2.05  #Close   : 0
% 4.81/2.05  
% 4.81/2.05  Ordering : KBO
% 4.81/2.05  
% 4.81/2.05  Simplification rules
% 4.81/2.05  ----------------------
% 4.81/2.05  #Subsume      : 16
% 4.81/2.05  #Demod        : 1428
% 4.81/2.05  #Tautology    : 1050
% 4.81/2.05  #SimpNegUnit  : 11
% 4.81/2.05  #BackRed      : 2
% 4.81/2.05  
% 4.81/2.05  #Partial instantiations: 0
% 4.81/2.05  #Strategies tried      : 1
% 4.81/2.05  
% 4.81/2.05  Timing (in seconds)
% 4.81/2.05  ----------------------
% 4.81/2.05  Preprocessing        : 0.31
% 4.81/2.05  Parsing              : 0.17
% 4.81/2.05  CNF conversion       : 0.02
% 4.81/2.05  Main loop            : 0.90
% 4.81/2.05  Inferencing          : 0.29
% 4.81/2.05  Reduction            : 0.41
% 4.81/2.05  Demodulation         : 0.34
% 4.81/2.05  BG Simplification    : 0.03
% 4.81/2.06  Subsumption          : 0.12
% 4.81/2.06  Abstraction          : 0.04
% 4.81/2.06  MUC search           : 0.00
% 4.81/2.06  Cooper               : 0.00
% 4.81/2.06  Total                : 1.25
% 4.81/2.06  Index Insertion      : 0.00
% 4.81/2.06  Index Deletion       : 0.00
% 4.81/2.06  Index Matching       : 0.00
% 4.81/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
