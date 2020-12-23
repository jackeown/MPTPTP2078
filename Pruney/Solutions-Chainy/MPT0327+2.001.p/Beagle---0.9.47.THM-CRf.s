%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:30 EST 2020

% Result     : Theorem 6.41s
% Output     : CNFRefutation 6.57s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 138 expanded)
%              Number of leaves         :   34 (  59 expanded)
%              Depth                    :   16
%              Number of atoms          :   82 ( 144 expanded)
%              Number of equality atoms :   58 ( 108 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_69,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_50,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1246,plain,(
    ! [A_118,B_119,C_120] :
      ( r1_tarski(k2_tarski(A_118,B_119),C_120)
      | ~ r2_hidden(B_119,C_120)
      | ~ r2_hidden(A_118,C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3387,plain,(
    ! [A_171,C_172] :
      ( r1_tarski(k1_tarski(A_171),C_172)
      | ~ r2_hidden(A_171,C_172)
      | ~ r2_hidden(A_171,C_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1246])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k2_xboole_0(A_10,B_11) = B_11
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3411,plain,(
    ! [A_174,C_175] :
      ( k2_xboole_0(k1_tarski(A_174),C_175) = C_175
      | ~ r2_hidden(A_174,C_175) ) ),
    inference(resolution,[status(thm)],[c_3387,c_14])).

tff(c_30,plain,(
    ! [B_27,A_26] : k2_tarski(B_27,A_26) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_138,plain,(
    ! [A_51,B_52] : k3_tarski(k2_tarski(A_51,B_52)) = k2_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_339,plain,(
    ! [B_68,A_69] : k3_tarski(k2_tarski(B_68,A_69)) = k2_xboole_0(A_69,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_138])).

tff(c_40,plain,(
    ! [A_38,B_39] : k3_tarski(k2_tarski(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_345,plain,(
    ! [B_68,A_69] : k2_xboole_0(B_68,A_69) = k2_xboole_0(A_69,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_40])).

tff(c_3448,plain,(
    ! [C_175,A_174] :
      ( k2_xboole_0(C_175,k1_tarski(A_174)) = C_175
      | ~ r2_hidden(A_174,C_175) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3411,c_345])).

tff(c_24,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_229,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(A_61,B_62) = A_61
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_247,plain,(
    ! [A_64] : k3_xboole_0(k1_xboole_0,A_64) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_229])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_256,plain,(
    ! [A_64] : k3_xboole_0(A_64,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_2])).

tff(c_503,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_512,plain,(
    ! [A_64] : k5_xboole_0(A_64,k1_xboole_0) = k4_xboole_0(A_64,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_503])).

tff(c_550,plain,(
    ! [A_82] : k4_xboole_0(A_82,k1_xboole_0) = A_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_512])).

tff(c_560,plain,(
    ! [A_82] : k4_xboole_0(A_82,A_82) = k3_xboole_0(A_82,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_20])).

tff(c_570,plain,(
    ! [A_82] : k4_xboole_0(A_82,A_82) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_560])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_236,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_229])).

tff(c_518,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_503])).

tff(c_652,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_518])).

tff(c_963,plain,(
    ! [A_107,B_108,C_109] : k4_xboole_0(k3_xboole_0(A_107,B_108),C_109) = k3_xboole_0(A_107,k4_xboole_0(B_108,C_109)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1084,plain,(
    ! [B_112,C_113] : k3_xboole_0(B_112,k4_xboole_0(B_112,C_113)) = k4_xboole_0(B_112,C_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_963])).

tff(c_524,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_503])).

tff(c_1090,plain,(
    ! [B_112,C_113] : k5_xboole_0(k4_xboole_0(B_112,C_113),k4_xboole_0(B_112,C_113)) = k4_xboole_0(k4_xboole_0(B_112,C_113),B_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_1084,c_524])).

tff(c_1137,plain,(
    ! [B_114,C_115] : k4_xboole_0(k4_xboole_0(B_114,C_115),B_114) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_1090])).

tff(c_1188,plain,(
    ! [A_116,B_117] : k4_xboole_0(k3_xboole_0(A_116,B_117),A_116) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1137])).

tff(c_22,plain,(
    ! [A_17,B_18,C_19] : k4_xboole_0(k3_xboole_0(A_17,B_18),C_19) = k3_xboole_0(A_17,k4_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1199,plain,(
    ! [A_116,B_117] : k3_xboole_0(A_116,k4_xboole_0(B_117,A_116)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1188,c_22])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_845,plain,(
    ! [A_104,B_105] : k5_xboole_0(k5_xboole_0(A_104,B_105),k3_xboole_0(A_104,B_105)) = k2_xboole_0(A_104,B_105) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2356,plain,(
    ! [A_150,B_151] : k5_xboole_0(k5_xboole_0(A_150,B_151),k3_xboole_0(B_151,A_150)) = k2_xboole_0(A_150,B_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_845])).

tff(c_26,plain,(
    ! [A_21,B_22,C_23] : k5_xboole_0(k5_xboole_0(A_21,B_22),C_23) = k5_xboole_0(A_21,k5_xboole_0(B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2381,plain,(
    ! [A_150,B_151] : k5_xboole_0(A_150,k5_xboole_0(B_151,k3_xboole_0(B_151,A_150))) = k2_xboole_0(A_150,B_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_2356,c_26])).

tff(c_2484,plain,(
    ! [A_152,B_153] : k5_xboole_0(A_152,k4_xboole_0(B_153,A_152)) = k2_xboole_0(A_152,B_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2381])).

tff(c_894,plain,(
    ! [A_1,B_2] : k5_xboole_0(k5_xboole_0(A_1,B_2),k3_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_845])).

tff(c_2490,plain,(
    ! [A_152,B_153] : k5_xboole_0(k2_xboole_0(A_152,B_153),k3_xboole_0(k4_xboole_0(B_153,A_152),A_152)) = k2_xboole_0(A_152,k4_xboole_0(B_153,A_152)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2484,c_894])).

tff(c_2567,plain,(
    ! [A_152,B_153] : k2_xboole_0(A_152,k4_xboole_0(B_153,A_152)) = k2_xboole_0(A_152,B_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1199,c_2,c_2490])).

tff(c_48,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_366,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_48])).

tff(c_5450,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2567,c_366])).

tff(c_5451,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_5450])).

tff(c_5574,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3448,c_5451])).

tff(c_5578,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5574])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:57:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.41/2.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.57/2.89  
% 6.57/2.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.57/2.90  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 6.57/2.90  
% 6.57/2.90  %Foreground sorts:
% 6.57/2.90  
% 6.57/2.90  
% 6.57/2.90  %Background operators:
% 6.57/2.90  
% 6.57/2.90  
% 6.57/2.90  %Foreground operators:
% 6.57/2.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.57/2.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.57/2.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.57/2.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.57/2.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.57/2.90  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.57/2.90  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.57/2.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.57/2.90  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.57/2.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.57/2.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.57/2.90  tff('#skF_2', type, '#skF_2': $i).
% 6.57/2.90  tff('#skF_1', type, '#skF_1': $i).
% 6.57/2.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.57/2.90  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.57/2.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.57/2.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.57/2.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.57/2.90  
% 6.57/2.92  tff(f_80, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 6.57/2.92  tff(f_61, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.57/2.92  tff(f_75, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.57/2.92  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.57/2.92  tff(f_59, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.57/2.92  tff(f_69, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.57/2.92  tff(f_53, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.57/2.92  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.57/2.92  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.57/2.92  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.57/2.92  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.57/2.92  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.57/2.92  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.57/2.92  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 6.57/2.92  tff(f_57, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 6.57/2.92  tff(f_55, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.57/2.92  tff(c_50, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.57/2.92  tff(c_32, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.57/2.92  tff(c_1246, plain, (![A_118, B_119, C_120]: (r1_tarski(k2_tarski(A_118, B_119), C_120) | ~r2_hidden(B_119, C_120) | ~r2_hidden(A_118, C_120))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.57/2.92  tff(c_3387, plain, (![A_171, C_172]: (r1_tarski(k1_tarski(A_171), C_172) | ~r2_hidden(A_171, C_172) | ~r2_hidden(A_171, C_172))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1246])).
% 6.57/2.92  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, B_11)=B_11 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.57/2.92  tff(c_3411, plain, (![A_174, C_175]: (k2_xboole_0(k1_tarski(A_174), C_175)=C_175 | ~r2_hidden(A_174, C_175))), inference(resolution, [status(thm)], [c_3387, c_14])).
% 6.57/2.92  tff(c_30, plain, (![B_27, A_26]: (k2_tarski(B_27, A_26)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.57/2.92  tff(c_138, plain, (![A_51, B_52]: (k3_tarski(k2_tarski(A_51, B_52))=k2_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.57/2.92  tff(c_339, plain, (![B_68, A_69]: (k3_tarski(k2_tarski(B_68, A_69))=k2_xboole_0(A_69, B_68))), inference(superposition, [status(thm), theory('equality')], [c_30, c_138])).
% 6.57/2.92  tff(c_40, plain, (![A_38, B_39]: (k3_tarski(k2_tarski(A_38, B_39))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.57/2.92  tff(c_345, plain, (![B_68, A_69]: (k2_xboole_0(B_68, A_69)=k2_xboole_0(A_69, B_68))), inference(superposition, [status(thm), theory('equality')], [c_339, c_40])).
% 6.57/2.92  tff(c_3448, plain, (![C_175, A_174]: (k2_xboole_0(C_175, k1_tarski(A_174))=C_175 | ~r2_hidden(A_174, C_175))), inference(superposition, [status(thm), theory('equality')], [c_3411, c_345])).
% 6.57/2.92  tff(c_24, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.57/2.92  tff(c_20, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.57/2.92  tff(c_18, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.57/2.92  tff(c_229, plain, (![A_61, B_62]: (k3_xboole_0(A_61, B_62)=A_61 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.57/2.92  tff(c_247, plain, (![A_64]: (k3_xboole_0(k1_xboole_0, A_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_229])).
% 6.57/2.92  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.57/2.92  tff(c_256, plain, (![A_64]: (k3_xboole_0(A_64, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_247, c_2])).
% 6.57/2.92  tff(c_503, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.57/2.92  tff(c_512, plain, (![A_64]: (k5_xboole_0(A_64, k1_xboole_0)=k4_xboole_0(A_64, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_256, c_503])).
% 6.57/2.92  tff(c_550, plain, (![A_82]: (k4_xboole_0(A_82, k1_xboole_0)=A_82)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_512])).
% 6.57/2.92  tff(c_560, plain, (![A_82]: (k4_xboole_0(A_82, A_82)=k3_xboole_0(A_82, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_550, c_20])).
% 6.57/2.92  tff(c_570, plain, (![A_82]: (k4_xboole_0(A_82, A_82)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_256, c_560])).
% 6.57/2.92  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.57/2.92  tff(c_236, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_229])).
% 6.57/2.92  tff(c_518, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_236, c_503])).
% 6.57/2.92  tff(c_652, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_570, c_518])).
% 6.57/2.92  tff(c_963, plain, (![A_107, B_108, C_109]: (k4_xboole_0(k3_xboole_0(A_107, B_108), C_109)=k3_xboole_0(A_107, k4_xboole_0(B_108, C_109)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.57/2.92  tff(c_1084, plain, (![B_112, C_113]: (k3_xboole_0(B_112, k4_xboole_0(B_112, C_113))=k4_xboole_0(B_112, C_113))), inference(superposition, [status(thm), theory('equality')], [c_236, c_963])).
% 6.57/2.92  tff(c_524, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_503])).
% 6.57/2.92  tff(c_1090, plain, (![B_112, C_113]: (k5_xboole_0(k4_xboole_0(B_112, C_113), k4_xboole_0(B_112, C_113))=k4_xboole_0(k4_xboole_0(B_112, C_113), B_112))), inference(superposition, [status(thm), theory('equality')], [c_1084, c_524])).
% 6.57/2.92  tff(c_1137, plain, (![B_114, C_115]: (k4_xboole_0(k4_xboole_0(B_114, C_115), B_114)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_652, c_1090])).
% 6.57/2.92  tff(c_1188, plain, (![A_116, B_117]: (k4_xboole_0(k3_xboole_0(A_116, B_117), A_116)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_1137])).
% 6.57/2.92  tff(c_22, plain, (![A_17, B_18, C_19]: (k4_xboole_0(k3_xboole_0(A_17, B_18), C_19)=k3_xboole_0(A_17, k4_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.57/2.92  tff(c_1199, plain, (![A_116, B_117]: (k3_xboole_0(A_116, k4_xboole_0(B_117, A_116))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1188, c_22])).
% 6.57/2.92  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.57/2.92  tff(c_845, plain, (![A_104, B_105]: (k5_xboole_0(k5_xboole_0(A_104, B_105), k3_xboole_0(A_104, B_105))=k2_xboole_0(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.57/2.92  tff(c_2356, plain, (![A_150, B_151]: (k5_xboole_0(k5_xboole_0(A_150, B_151), k3_xboole_0(B_151, A_150))=k2_xboole_0(A_150, B_151))), inference(superposition, [status(thm), theory('equality')], [c_2, c_845])).
% 6.57/2.92  tff(c_26, plain, (![A_21, B_22, C_23]: (k5_xboole_0(k5_xboole_0(A_21, B_22), C_23)=k5_xboole_0(A_21, k5_xboole_0(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.57/2.92  tff(c_2381, plain, (![A_150, B_151]: (k5_xboole_0(A_150, k5_xboole_0(B_151, k3_xboole_0(B_151, A_150)))=k2_xboole_0(A_150, B_151))), inference(superposition, [status(thm), theory('equality')], [c_2356, c_26])).
% 6.57/2.92  tff(c_2484, plain, (![A_152, B_153]: (k5_xboole_0(A_152, k4_xboole_0(B_153, A_152))=k2_xboole_0(A_152, B_153))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2381])).
% 6.57/2.92  tff(c_894, plain, (![A_1, B_2]: (k5_xboole_0(k5_xboole_0(A_1, B_2), k3_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_845])).
% 6.57/2.92  tff(c_2490, plain, (![A_152, B_153]: (k5_xboole_0(k2_xboole_0(A_152, B_153), k3_xboole_0(k4_xboole_0(B_153, A_152), A_152))=k2_xboole_0(A_152, k4_xboole_0(B_153, A_152)))), inference(superposition, [status(thm), theory('equality')], [c_2484, c_894])).
% 6.57/2.92  tff(c_2567, plain, (![A_152, B_153]: (k2_xboole_0(A_152, k4_xboole_0(B_153, A_152))=k2_xboole_0(A_152, B_153))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1199, c_2, c_2490])).
% 6.57/2.92  tff(c_48, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.57/2.92  tff(c_366, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_345, c_48])).
% 6.57/2.92  tff(c_5450, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2567, c_366])).
% 6.57/2.92  tff(c_5451, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_345, c_5450])).
% 6.57/2.92  tff(c_5574, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3448, c_5451])).
% 6.57/2.92  tff(c_5578, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_5574])).
% 6.57/2.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.57/2.92  
% 6.57/2.92  Inference rules
% 6.57/2.92  ----------------------
% 6.57/2.92  #Ref     : 0
% 6.57/2.92  #Sup     : 1368
% 6.57/2.92  #Fact    : 0
% 6.57/2.92  #Define  : 0
% 6.57/2.92  #Split   : 1
% 6.57/2.92  #Chain   : 0
% 6.57/2.92  #Close   : 0
% 6.57/2.92  
% 6.57/2.92  Ordering : KBO
% 6.57/2.92  
% 6.57/2.92  Simplification rules
% 6.57/2.92  ----------------------
% 6.57/2.92  #Subsume      : 31
% 6.57/2.92  #Demod        : 1274
% 6.57/2.92  #Tautology    : 899
% 6.57/2.92  #SimpNegUnit  : 0
% 6.57/2.92  #BackRed      : 5
% 6.57/2.92  
% 6.57/2.92  #Partial instantiations: 0
% 6.57/2.92  #Strategies tried      : 1
% 6.57/2.92  
% 6.57/2.92  Timing (in seconds)
% 6.57/2.92  ----------------------
% 6.57/2.93  Preprocessing        : 0.51
% 6.57/2.93  Parsing              : 0.26
% 6.57/2.93  CNF conversion       : 0.03
% 6.57/2.93  Main loop            : 1.50
% 6.57/2.93  Inferencing          : 0.45
% 6.57/2.93  Reduction            : 0.69
% 6.57/2.93  Demodulation         : 0.58
% 6.57/2.93  BG Simplification    : 0.06
% 6.57/2.93  Subsumption          : 0.20
% 6.57/2.93  Abstraction          : 0.08
% 6.57/2.93  MUC search           : 0.00
% 6.57/2.93  Cooper               : 0.00
% 6.57/2.93  Total                : 2.07
% 6.57/2.93  Index Insertion      : 0.00
% 6.57/2.93  Index Deletion       : 0.00
% 6.57/2.93  Index Matching       : 0.00
% 6.57/2.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
