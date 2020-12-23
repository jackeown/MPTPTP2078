%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:11 EST 2020

% Result     : Theorem 5.59s
% Output     : CNFRefutation 5.96s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 213 expanded)
%              Number of leaves         :   33 (  82 expanded)
%              Depth                    :   14
%              Number of atoms          :  121 ( 252 expanded)
%              Number of equality atoms :   63 ( 139 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_81,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_77,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_79,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_99,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_5789,plain,(
    ! [A_238,B_239] :
      ( r1_xboole_0(A_238,B_239)
      | k3_xboole_0(A_238,B_239) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_116,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_22,plain,(
    ! [A_21] : k2_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_34,plain,(
    ! [A_31] : r1_xboole_0(A_31,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_249,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(A_61,B_62) = k1_xboole_0
      | ~ r1_xboole_0(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_269,plain,(
    ! [A_31] : k3_xboole_0(A_31,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_249])).

tff(c_30,plain,(
    ! [A_28] : k4_xboole_0(A_28,k1_xboole_0) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_442,plain,(
    ! [A_70,B_71] : k4_xboole_0(A_70,k4_xboole_0(A_70,B_71)) = k3_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_472,plain,(
    ! [A_28] : k4_xboole_0(A_28,A_28) = k3_xboole_0(A_28,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_442])).

tff(c_476,plain,(
    ! [A_28] : k4_xboole_0(A_28,A_28) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_472])).

tff(c_66,plain,(
    ! [A_40,B_41] : r1_tarski(k4_xboole_0(A_40,B_41),A_40) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_69,plain,(
    ! [A_28] : r1_tarski(A_28,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_66])).

tff(c_179,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,B_56) = A_55
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_190,plain,(
    ! [A_28] : k3_xboole_0(A_28,A_28) = A_28 ),
    inference(resolution,[status(thm)],[c_69,c_179])).

tff(c_301,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k3_xboole_0(A_64,B_65)) = k4_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_313,plain,(
    ! [A_28] : k5_xboole_0(A_28,A_28) = k4_xboole_0(A_28,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_301])).

tff(c_852,plain,(
    ! [A_28] : k5_xboole_0(A_28,A_28) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_313])).

tff(c_26,plain,(
    ! [A_24,B_25] : r1_tarski(k4_xboole_0(A_24,B_25),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2656,plain,(
    ! [A_167,B_168] : k3_xboole_0(k4_xboole_0(A_167,B_168),A_167) = k4_xboole_0(A_167,B_168) ),
    inference(resolution,[status(thm)],[c_26,c_179])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2693,plain,(
    ! [A_167,B_168] : k5_xboole_0(k4_xboole_0(A_167,B_168),k4_xboole_0(A_167,B_168)) = k4_xboole_0(k4_xboole_0(A_167,B_168),A_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_2656,c_18])).

tff(c_2766,plain,(
    ! [A_169,B_170] : k4_xboole_0(k4_xboole_0(A_169,B_170),A_169) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_852,c_2693])).

tff(c_28,plain,(
    ! [A_26,B_27] : k2_xboole_0(A_26,k4_xboole_0(B_27,A_26)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2810,plain,(
    ! [A_169,B_170] : k2_xboole_0(A_169,k4_xboole_0(A_169,B_170)) = k2_xboole_0(A_169,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2766,c_28])).

tff(c_2880,plain,(
    ! [A_169,B_170] : k2_xboole_0(A_169,k4_xboole_0(A_169,B_170)) = A_169 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2810])).

tff(c_46,plain,(
    r1_tarski('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_189,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_46,c_179])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2898,plain,(
    ! [A_171,B_172] : k2_xboole_0(A_171,k4_xboole_0(A_171,B_172)) = A_171 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2810])).

tff(c_3190,plain,(
    ! [A_175,B_176] : k2_xboole_0(A_175,k3_xboole_0(A_175,B_176)) = A_175 ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2898])).

tff(c_3491,plain,(
    ! [A_179,B_180] : k2_xboole_0(A_179,k3_xboole_0(B_180,A_179)) = A_179 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3190])).

tff(c_3607,plain,(
    k2_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_3') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_3491])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1425,plain,(
    ! [A_115,C_116,B_117] :
      ( r1_tarski(A_115,C_116)
      | ~ r1_tarski(k2_xboole_0(A_115,B_117),C_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1450,plain,(
    ! [A_118,B_119] : r1_tarski(A_118,k2_xboole_0(A_118,B_119)) ),
    inference(resolution,[status(thm)],[c_69,c_1425])).

tff(c_1469,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1450])).

tff(c_2540,plain,(
    ! [A_161,C_162,B_163] :
      ( r1_tarski(A_161,C_162)
      | ~ r1_tarski(k2_xboole_0(B_163,A_161),C_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1425])).

tff(c_2586,plain,(
    ! [A_161,B_2,B_163] : r1_tarski(A_161,k2_xboole_0(B_2,k2_xboole_0(B_163,A_161))) ),
    inference(resolution,[status(thm)],[c_1469,c_2540])).

tff(c_5655,plain,(
    ! [B_230] : r1_tarski('#skF_3',k2_xboole_0(B_230,k4_xboole_0('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3607,c_2586])).

tff(c_5662,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2880,c_5655])).

tff(c_5685,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_5662])).

tff(c_5686,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_5795,plain,(
    k3_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5789,c_5686])).

tff(c_5798,plain,(
    ! [A_240,B_241] :
      ( k3_xboole_0(A_240,B_241) = k1_xboole_0
      | ~ r1_xboole_0(A_240,B_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5818,plain,(
    ! [A_31] : k3_xboole_0(A_31,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_5798])).

tff(c_6607,plain,(
    ! [A_288,B_289] : k5_xboole_0(A_288,k3_xboole_0(A_288,B_289)) = k4_xboole_0(A_288,B_289) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6643,plain,(
    ! [A_31] : k5_xboole_0(A_31,k1_xboole_0) = k4_xboole_0(A_31,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5818,c_6607])).

tff(c_6653,plain,(
    ! [A_31] : k5_xboole_0(A_31,k1_xboole_0) = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6643])).

tff(c_42,plain,(
    ! [A_35,B_36] : r1_xboole_0(k4_xboole_0(A_35,B_36),B_36) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_5817,plain,(
    ! [A_35,B_36] : k3_xboole_0(k4_xboole_0(A_35,B_36),B_36) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_5798])).

tff(c_7733,plain,(
    ! [B_324,A_325] : k5_xboole_0(B_324,k3_xboole_0(A_325,B_324)) = k4_xboole_0(B_324,A_325) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_6607])).

tff(c_7765,plain,(
    ! [B_36,A_35] : k4_xboole_0(B_36,k4_xboole_0(A_35,B_36)) = k5_xboole_0(B_36,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5817,c_7733])).

tff(c_7797,plain,(
    ! [B_36,A_35] : k4_xboole_0(B_36,k4_xboole_0(A_35,B_36)) = B_36 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6653,c_7765])).

tff(c_6142,plain,(
    ! [A_263,B_264] : k4_xboole_0(A_263,k4_xboole_0(A_263,B_264)) = k3_xboole_0(A_263,B_264) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6172,plain,(
    ! [A_28] : k4_xboole_0(A_28,A_28) = k3_xboole_0(A_28,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_6142])).

tff(c_6175,plain,(
    ! [A_28] : k4_xboole_0(A_28,A_28) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5818,c_6172])).

tff(c_5873,plain,(
    ! [A_244,B_245] :
      ( k3_xboole_0(A_244,B_245) = A_244
      | ~ r1_tarski(A_244,B_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5888,plain,(
    ! [A_28] : k3_xboole_0(A_28,A_28) = A_28 ),
    inference(resolution,[status(thm)],[c_69,c_5873])).

tff(c_6628,plain,(
    ! [A_28] : k5_xboole_0(A_28,A_28) = k4_xboole_0(A_28,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_5888,c_6607])).

tff(c_6652,plain,(
    ! [A_28] : k5_xboole_0(A_28,A_28) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6175,c_6628])).

tff(c_5887,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_46,c_5873])).

tff(c_6631,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k5_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5887,c_6607])).

tff(c_6963,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6652,c_6631])).

tff(c_6969,plain,(
    k2_xboole_0(k4_xboole_0('#skF_4','#skF_5'),k1_xboole_0) = k2_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6963,c_28])).

tff(c_6993,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22,c_6969])).

tff(c_6464,plain,(
    ! [A_281,B_282,C_283] :
      ( r1_xboole_0(A_281,B_282)
      | ~ r1_xboole_0(A_281,k2_xboole_0(B_282,C_283)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6493,plain,(
    ! [A_35,B_282,C_283] : r1_xboole_0(k4_xboole_0(A_35,k2_xboole_0(B_282,C_283)),B_282) ),
    inference(resolution,[status(thm)],[c_42,c_6464])).

tff(c_9113,plain,(
    ! [A_361] : r1_xboole_0(k4_xboole_0(A_361,k4_xboole_0('#skF_4','#skF_5')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6993,c_6493])).

tff(c_9125,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7797,c_9113])).

tff(c_16,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_2'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5920,plain,(
    ! [A_246,B_247,C_248] :
      ( ~ r1_xboole_0(A_246,B_247)
      | ~ r2_hidden(C_248,k3_xboole_0(A_246,B_247)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8129,plain,(
    ! [B_336,A_337,C_338] :
      ( ~ r1_xboole_0(B_336,A_337)
      | ~ r2_hidden(C_338,k3_xboole_0(A_337,B_336)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_5920])).

tff(c_8192,plain,(
    ! [B_336,A_337] :
      ( ~ r1_xboole_0(B_336,A_337)
      | k3_xboole_0(A_337,B_336) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_8129])).

tff(c_9146,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9125,c_8192])).

tff(c_9155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5795,c_9146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:23:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.59/2.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.96/2.24  
% 5.96/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.96/2.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 5.96/2.24  
% 5.96/2.24  %Foreground sorts:
% 5.96/2.24  
% 5.96/2.24  
% 5.96/2.24  %Background operators:
% 5.96/2.24  
% 5.96/2.24  
% 5.96/2.24  %Foreground operators:
% 5.96/2.24  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.96/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.96/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.96/2.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.96/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.96/2.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.96/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.96/2.24  tff('#skF_5', type, '#skF_5': $i).
% 5.96/2.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.96/2.24  tff('#skF_3', type, '#skF_3': $i).
% 5.96/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.96/2.24  tff('#skF_4', type, '#skF_4': $i).
% 5.96/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.96/2.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.96/2.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.96/2.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.96/2.24  
% 5.96/2.26  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.96/2.26  tff(f_106, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 5.96/2.26  tff(f_67, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.96/2.26  tff(f_81, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.96/2.26  tff(f_77, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.96/2.26  tff(f_79, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.96/2.26  tff(f_73, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.96/2.26  tff(f_71, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.96/2.26  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.96/2.26  tff(f_75, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.96/2.26  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.96/2.26  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.96/2.26  tff(f_65, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.96/2.26  tff(f_99, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.96/2.26  tff(f_97, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 5.96/2.26  tff(f_59, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.96/2.26  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.96/2.26  tff(c_5789, plain, (![A_238, B_239]: (r1_xboole_0(A_238, B_239) | k3_xboole_0(A_238, B_239)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.96/2.26  tff(c_44, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.96/2.26  tff(c_116, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_44])).
% 5.96/2.26  tff(c_22, plain, (![A_21]: (k2_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.96/2.26  tff(c_34, plain, (![A_31]: (r1_xboole_0(A_31, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.96/2.26  tff(c_249, plain, (![A_61, B_62]: (k3_xboole_0(A_61, B_62)=k1_xboole_0 | ~r1_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.96/2.26  tff(c_269, plain, (![A_31]: (k3_xboole_0(A_31, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_249])).
% 5.96/2.26  tff(c_30, plain, (![A_28]: (k4_xboole_0(A_28, k1_xboole_0)=A_28)), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.96/2.26  tff(c_442, plain, (![A_70, B_71]: (k4_xboole_0(A_70, k4_xboole_0(A_70, B_71))=k3_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.96/2.26  tff(c_472, plain, (![A_28]: (k4_xboole_0(A_28, A_28)=k3_xboole_0(A_28, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_442])).
% 5.96/2.26  tff(c_476, plain, (![A_28]: (k4_xboole_0(A_28, A_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_269, c_472])).
% 5.96/2.26  tff(c_66, plain, (![A_40, B_41]: (r1_tarski(k4_xboole_0(A_40, B_41), A_40))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.96/2.26  tff(c_69, plain, (![A_28]: (r1_tarski(A_28, A_28))), inference(superposition, [status(thm), theory('equality')], [c_30, c_66])).
% 5.96/2.26  tff(c_179, plain, (![A_55, B_56]: (k3_xboole_0(A_55, B_56)=A_55 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.96/2.26  tff(c_190, plain, (![A_28]: (k3_xboole_0(A_28, A_28)=A_28)), inference(resolution, [status(thm)], [c_69, c_179])).
% 5.96/2.26  tff(c_301, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k3_xboole_0(A_64, B_65))=k4_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.96/2.26  tff(c_313, plain, (![A_28]: (k5_xboole_0(A_28, A_28)=k4_xboole_0(A_28, A_28))), inference(superposition, [status(thm), theory('equality')], [c_190, c_301])).
% 5.96/2.26  tff(c_852, plain, (![A_28]: (k5_xboole_0(A_28, A_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_476, c_313])).
% 5.96/2.26  tff(c_26, plain, (![A_24, B_25]: (r1_tarski(k4_xboole_0(A_24, B_25), A_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.96/2.26  tff(c_2656, plain, (![A_167, B_168]: (k3_xboole_0(k4_xboole_0(A_167, B_168), A_167)=k4_xboole_0(A_167, B_168))), inference(resolution, [status(thm)], [c_26, c_179])).
% 5.96/2.26  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.96/2.26  tff(c_2693, plain, (![A_167, B_168]: (k5_xboole_0(k4_xboole_0(A_167, B_168), k4_xboole_0(A_167, B_168))=k4_xboole_0(k4_xboole_0(A_167, B_168), A_167))), inference(superposition, [status(thm), theory('equality')], [c_2656, c_18])).
% 5.96/2.26  tff(c_2766, plain, (![A_169, B_170]: (k4_xboole_0(k4_xboole_0(A_169, B_170), A_169)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_852, c_2693])).
% 5.96/2.26  tff(c_28, plain, (![A_26, B_27]: (k2_xboole_0(A_26, k4_xboole_0(B_27, A_26))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.96/2.26  tff(c_2810, plain, (![A_169, B_170]: (k2_xboole_0(A_169, k4_xboole_0(A_169, B_170))=k2_xboole_0(A_169, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2766, c_28])).
% 5.96/2.26  tff(c_2880, plain, (![A_169, B_170]: (k2_xboole_0(A_169, k4_xboole_0(A_169, B_170))=A_169)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2810])).
% 5.96/2.26  tff(c_46, plain, (r1_tarski('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.96/2.26  tff(c_189, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(resolution, [status(thm)], [c_46, c_179])).
% 5.96/2.26  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.96/2.26  tff(c_32, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.96/2.26  tff(c_2898, plain, (![A_171, B_172]: (k2_xboole_0(A_171, k4_xboole_0(A_171, B_172))=A_171)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2810])).
% 5.96/2.26  tff(c_3190, plain, (![A_175, B_176]: (k2_xboole_0(A_175, k3_xboole_0(A_175, B_176))=A_175)), inference(superposition, [status(thm), theory('equality')], [c_32, c_2898])).
% 5.96/2.26  tff(c_3491, plain, (![A_179, B_180]: (k2_xboole_0(A_179, k3_xboole_0(B_180, A_179))=A_179)), inference(superposition, [status(thm), theory('equality')], [c_4, c_3190])).
% 5.96/2.26  tff(c_3607, plain, (k2_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_3')=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_189, c_3491])).
% 5.96/2.26  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.96/2.26  tff(c_1425, plain, (![A_115, C_116, B_117]: (r1_tarski(A_115, C_116) | ~r1_tarski(k2_xboole_0(A_115, B_117), C_116))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.96/2.26  tff(c_1450, plain, (![A_118, B_119]: (r1_tarski(A_118, k2_xboole_0(A_118, B_119)))), inference(resolution, [status(thm)], [c_69, c_1425])).
% 5.96/2.26  tff(c_1469, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1450])).
% 5.96/2.26  tff(c_2540, plain, (![A_161, C_162, B_163]: (r1_tarski(A_161, C_162) | ~r1_tarski(k2_xboole_0(B_163, A_161), C_162))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1425])).
% 5.96/2.26  tff(c_2586, plain, (![A_161, B_2, B_163]: (r1_tarski(A_161, k2_xboole_0(B_2, k2_xboole_0(B_163, A_161))))), inference(resolution, [status(thm)], [c_1469, c_2540])).
% 5.96/2.26  tff(c_5655, plain, (![B_230]: (r1_tarski('#skF_3', k2_xboole_0(B_230, k4_xboole_0('#skF_4', '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_3607, c_2586])).
% 5.96/2.26  tff(c_5662, plain, (r1_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2880, c_5655])).
% 5.96/2.26  tff(c_5685, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_5662])).
% 5.96/2.26  tff(c_5686, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_44])).
% 5.96/2.26  tff(c_5795, plain, (k3_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_5789, c_5686])).
% 5.96/2.26  tff(c_5798, plain, (![A_240, B_241]: (k3_xboole_0(A_240, B_241)=k1_xboole_0 | ~r1_xboole_0(A_240, B_241))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.96/2.26  tff(c_5818, plain, (![A_31]: (k3_xboole_0(A_31, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_5798])).
% 5.96/2.26  tff(c_6607, plain, (![A_288, B_289]: (k5_xboole_0(A_288, k3_xboole_0(A_288, B_289))=k4_xboole_0(A_288, B_289))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.96/2.26  tff(c_6643, plain, (![A_31]: (k5_xboole_0(A_31, k1_xboole_0)=k4_xboole_0(A_31, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5818, c_6607])).
% 5.96/2.26  tff(c_6653, plain, (![A_31]: (k5_xboole_0(A_31, k1_xboole_0)=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_6643])).
% 5.96/2.26  tff(c_42, plain, (![A_35, B_36]: (r1_xboole_0(k4_xboole_0(A_35, B_36), B_36))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.96/2.26  tff(c_5817, plain, (![A_35, B_36]: (k3_xboole_0(k4_xboole_0(A_35, B_36), B_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_5798])).
% 5.96/2.26  tff(c_7733, plain, (![B_324, A_325]: (k5_xboole_0(B_324, k3_xboole_0(A_325, B_324))=k4_xboole_0(B_324, A_325))), inference(superposition, [status(thm), theory('equality')], [c_4, c_6607])).
% 5.96/2.26  tff(c_7765, plain, (![B_36, A_35]: (k4_xboole_0(B_36, k4_xboole_0(A_35, B_36))=k5_xboole_0(B_36, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5817, c_7733])).
% 5.96/2.26  tff(c_7797, plain, (![B_36, A_35]: (k4_xboole_0(B_36, k4_xboole_0(A_35, B_36))=B_36)), inference(demodulation, [status(thm), theory('equality')], [c_6653, c_7765])).
% 5.96/2.26  tff(c_6142, plain, (![A_263, B_264]: (k4_xboole_0(A_263, k4_xboole_0(A_263, B_264))=k3_xboole_0(A_263, B_264))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.96/2.26  tff(c_6172, plain, (![A_28]: (k4_xboole_0(A_28, A_28)=k3_xboole_0(A_28, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_6142])).
% 5.96/2.26  tff(c_6175, plain, (![A_28]: (k4_xboole_0(A_28, A_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5818, c_6172])).
% 5.96/2.26  tff(c_5873, plain, (![A_244, B_245]: (k3_xboole_0(A_244, B_245)=A_244 | ~r1_tarski(A_244, B_245))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.96/2.26  tff(c_5888, plain, (![A_28]: (k3_xboole_0(A_28, A_28)=A_28)), inference(resolution, [status(thm)], [c_69, c_5873])).
% 5.96/2.26  tff(c_6628, plain, (![A_28]: (k5_xboole_0(A_28, A_28)=k4_xboole_0(A_28, A_28))), inference(superposition, [status(thm), theory('equality')], [c_5888, c_6607])).
% 5.96/2.26  tff(c_6652, plain, (![A_28]: (k5_xboole_0(A_28, A_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6175, c_6628])).
% 5.96/2.26  tff(c_5887, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(resolution, [status(thm)], [c_46, c_5873])).
% 5.96/2.26  tff(c_6631, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k5_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5887, c_6607])).
% 5.96/2.26  tff(c_6963, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6652, c_6631])).
% 5.96/2.26  tff(c_6969, plain, (k2_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), k1_xboole_0)=k2_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6963, c_28])).
% 5.96/2.26  tff(c_6993, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k4_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22, c_6969])).
% 5.96/2.26  tff(c_6464, plain, (![A_281, B_282, C_283]: (r1_xboole_0(A_281, B_282) | ~r1_xboole_0(A_281, k2_xboole_0(B_282, C_283)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.96/2.26  tff(c_6493, plain, (![A_35, B_282, C_283]: (r1_xboole_0(k4_xboole_0(A_35, k2_xboole_0(B_282, C_283)), B_282))), inference(resolution, [status(thm)], [c_42, c_6464])).
% 5.96/2.26  tff(c_9113, plain, (![A_361]: (r1_xboole_0(k4_xboole_0(A_361, k4_xboole_0('#skF_4', '#skF_5')), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6993, c_6493])).
% 5.96/2.26  tff(c_9125, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7797, c_9113])).
% 5.96/2.26  tff(c_16, plain, (![A_14]: (r2_hidden('#skF_2'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.96/2.26  tff(c_5920, plain, (![A_246, B_247, C_248]: (~r1_xboole_0(A_246, B_247) | ~r2_hidden(C_248, k3_xboole_0(A_246, B_247)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.96/2.26  tff(c_8129, plain, (![B_336, A_337, C_338]: (~r1_xboole_0(B_336, A_337) | ~r2_hidden(C_338, k3_xboole_0(A_337, B_336)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_5920])).
% 5.96/2.26  tff(c_8192, plain, (![B_336, A_337]: (~r1_xboole_0(B_336, A_337) | k3_xboole_0(A_337, B_336)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_8129])).
% 5.96/2.26  tff(c_9146, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_9125, c_8192])).
% 5.96/2.26  tff(c_9155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5795, c_9146])).
% 5.96/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.96/2.26  
% 5.96/2.26  Inference rules
% 5.96/2.26  ----------------------
% 5.96/2.26  #Ref     : 0
% 5.96/2.26  #Sup     : 2256
% 5.96/2.26  #Fact    : 0
% 5.96/2.26  #Define  : 0
% 5.96/2.26  #Split   : 7
% 5.96/2.26  #Chain   : 0
% 5.96/2.26  #Close   : 0
% 5.96/2.26  
% 5.96/2.26  Ordering : KBO
% 5.96/2.26  
% 5.96/2.26  Simplification rules
% 5.96/2.26  ----------------------
% 5.96/2.26  #Subsume      : 89
% 5.96/2.26  #Demod        : 1674
% 5.96/2.26  #Tautology    : 1639
% 5.96/2.26  #SimpNegUnit  : 18
% 5.96/2.26  #BackRed      : 10
% 5.96/2.26  
% 5.96/2.26  #Partial instantiations: 0
% 5.96/2.26  #Strategies tried      : 1
% 5.96/2.26  
% 5.96/2.26  Timing (in seconds)
% 5.96/2.26  ----------------------
% 5.96/2.27  Preprocessing        : 0.31
% 5.96/2.27  Parsing              : 0.18
% 5.96/2.27  CNF conversion       : 0.02
% 5.96/2.27  Main loop            : 1.15
% 5.96/2.27  Inferencing          : 0.35
% 5.96/2.27  Reduction            : 0.50
% 5.96/2.27  Demodulation         : 0.39
% 5.96/2.27  BG Simplification    : 0.03
% 5.96/2.27  Subsumption          : 0.18
% 5.96/2.27  Abstraction          : 0.04
% 5.96/2.27  MUC search           : 0.00
% 5.96/2.27  Cooper               : 0.00
% 5.96/2.27  Total                : 1.50
% 5.96/2.27  Index Insertion      : 0.00
% 5.96/2.27  Index Deletion       : 0.00
% 5.96/2.27  Index Matching       : 0.00
% 5.96/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
