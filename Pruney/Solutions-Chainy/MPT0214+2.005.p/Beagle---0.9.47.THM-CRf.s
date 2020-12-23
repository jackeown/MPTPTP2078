%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:30 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 107 expanded)
%              Number of leaves         :   44 (  54 expanded)
%              Depth                    :   16
%              Number of atoms          :   78 ( 105 expanded)
%              Number of equality atoms :   56 (  71 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_4 > #skF_8 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_93,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_91,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_95,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_89,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_61,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_63,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_76,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_64,plain,(
    ! [A_40,B_41] : k1_enumset1(A_40,A_40,B_41) = k2_tarski(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_62,plain,(
    ! [A_39] : k2_tarski(A_39,A_39) = k1_tarski(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_66,plain,(
    ! [A_42,B_43,C_44] : k2_enumset1(A_42,A_42,B_43,C_44) = k1_enumset1(A_42,B_43,C_44) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2125,plain,(
    ! [A_177,B_178,C_179,D_180] : k2_xboole_0(k1_enumset1(A_177,B_178,C_179),k1_tarski(D_180)) = k2_enumset1(A_177,B_178,C_179,D_180) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2134,plain,(
    ! [A_40,B_41,D_180] : k2_xboole_0(k2_tarski(A_40,B_41),k1_tarski(D_180)) = k2_enumset1(A_40,A_40,B_41,D_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_2125])).

tff(c_2910,plain,(
    ! [A_215,B_216,D_217] : k2_xboole_0(k2_tarski(A_215,B_216),k1_tarski(D_217)) = k1_enumset1(A_215,B_216,D_217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2134])).

tff(c_2919,plain,(
    ! [A_39,D_217] : k2_xboole_0(k1_tarski(A_39),k1_tarski(D_217)) = k1_enumset1(A_39,A_39,D_217) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_2910])).

tff(c_2923,plain,(
    ! [A_218,D_219] : k2_xboole_0(k1_tarski(A_218),k1_tarski(D_219)) = k2_tarski(A_218,D_219) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2919])).

tff(c_18,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_303,plain,(
    ! [A_101,B_102,C_103] :
      ( ~ r1_xboole_0(A_101,B_102)
      | ~ r2_hidden(C_103,k3_xboole_0(A_101,B_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_360,plain,(
    ! [A_109,B_110] :
      ( ~ r1_xboole_0(A_109,B_110)
      | k3_xboole_0(A_109,B_110) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_303])).

tff(c_370,plain,(
    ! [A_111,B_112] : k3_xboole_0(k4_xboole_0(A_111,B_112),B_112) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_360])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_381,plain,(
    ! [B_112,A_111] : k3_xboole_0(B_112,k4_xboole_0(A_111,B_112)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_2])).

tff(c_407,plain,(
    ! [B_113,A_114] : k3_xboole_0(B_113,k4_xboole_0(A_114,B_113)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_2])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_415,plain,(
    ! [B_113,A_114] : k4_xboole_0(B_113,k4_xboole_0(A_114,B_113)) = k5_xboole_0(B_113,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_12])).

tff(c_432,plain,(
    ! [B_115,A_116] : k4_xboole_0(B_115,k4_xboole_0(A_116,B_115)) = B_115 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_415])).

tff(c_16,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_447,plain,(
    ! [B_115,A_116] : k3_xboole_0(B_115,k4_xboole_0(A_116,B_115)) = k4_xboole_0(B_115,B_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_16])).

tff(c_477,plain,(
    ! [B_115] : k4_xboole_0(B_115,B_115) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_447])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_236,plain,(
    ! [A_98,B_99] : k5_xboole_0(A_98,k3_xboole_0(A_98,B_99)) = k4_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_257,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_236])).

tff(c_492,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_257])).

tff(c_78,plain,(
    r1_tarski(k1_tarski('#skF_7'),k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_156,plain,(
    ! [A_87,B_88] :
      ( k3_xboole_0(A_87,B_88) = A_87
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_160,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_156])).

tff(c_248,plain,(
    k5_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_7')) = k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_236])).

tff(c_530,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_248])).

tff(c_22,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_563,plain,(
    k2_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k5_xboole_0(k1_tarski('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_22])).

tff(c_570,plain,(
    k2_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_563])).

tff(c_2929,plain,(
    k2_tarski('#skF_8','#skF_7') = k1_tarski('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2923,c_570])).

tff(c_161,plain,(
    ! [A_89,B_90] : k1_enumset1(A_89,A_89,B_90) = k2_tarski(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    ! [E_29,A_23,B_24] : r2_hidden(E_29,k1_enumset1(A_23,B_24,E_29)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_173,plain,(
    ! [B_90,A_89] : r2_hidden(B_90,k2_tarski(A_89,B_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_26])).

tff(c_2966,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2929,c_173])).

tff(c_48,plain,(
    ! [C_34,A_30] :
      ( C_34 = A_30
      | ~ r2_hidden(C_34,k1_tarski(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2977,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2966,c_48])).

tff(c_2981,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2977])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n022.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 16:38:25 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.65/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.61  
% 3.65/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.62  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_4 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 3.65/1.62  
% 3.65/1.62  %Foreground sorts:
% 3.65/1.62  
% 3.65/1.62  
% 3.65/1.62  %Background operators:
% 3.65/1.62  
% 3.65/1.62  
% 3.65/1.62  %Foreground operators:
% 3.65/1.62  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.65/1.62  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.65/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.65/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.65/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.65/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.65/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.65/1.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.65/1.62  tff('#skF_7', type, '#skF_7': $i).
% 3.65/1.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.65/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.65/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.65/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.65/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.65/1.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.65/1.62  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.65/1.62  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.65/1.62  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.65/1.62  tff('#skF_8', type, '#skF_8': $i).
% 3.65/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.65/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.65/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.65/1.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.65/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.65/1.62  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.65/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.65/1.62  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.65/1.62  
% 3.65/1.63  tff(f_108, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 3.65/1.63  tff(f_93, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.65/1.63  tff(f_91, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.65/1.63  tff(f_95, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.65/1.63  tff(f_89, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 3.65/1.63  tff(f_61, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.65/1.63  tff(f_63, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.65/1.63  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.65/1.63  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.65/1.63  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.65/1.63  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.65/1.63  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.65/1.63  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.65/1.63  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.65/1.63  tff(f_65, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.65/1.63  tff(f_80, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.65/1.63  tff(f_87, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.65/1.63  tff(c_76, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.65/1.63  tff(c_64, plain, (![A_40, B_41]: (k1_enumset1(A_40, A_40, B_41)=k2_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.65/1.63  tff(c_62, plain, (![A_39]: (k2_tarski(A_39, A_39)=k1_tarski(A_39))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.65/1.63  tff(c_66, plain, (![A_42, B_43, C_44]: (k2_enumset1(A_42, A_42, B_43, C_44)=k1_enumset1(A_42, B_43, C_44))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.65/1.63  tff(c_2125, plain, (![A_177, B_178, C_179, D_180]: (k2_xboole_0(k1_enumset1(A_177, B_178, C_179), k1_tarski(D_180))=k2_enumset1(A_177, B_178, C_179, D_180))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.65/1.63  tff(c_2134, plain, (![A_40, B_41, D_180]: (k2_xboole_0(k2_tarski(A_40, B_41), k1_tarski(D_180))=k2_enumset1(A_40, A_40, B_41, D_180))), inference(superposition, [status(thm), theory('equality')], [c_64, c_2125])).
% 3.65/1.63  tff(c_2910, plain, (![A_215, B_216, D_217]: (k2_xboole_0(k2_tarski(A_215, B_216), k1_tarski(D_217))=k1_enumset1(A_215, B_216, D_217))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2134])).
% 3.65/1.63  tff(c_2919, plain, (![A_39, D_217]: (k2_xboole_0(k1_tarski(A_39), k1_tarski(D_217))=k1_enumset1(A_39, A_39, D_217))), inference(superposition, [status(thm), theory('equality')], [c_62, c_2910])).
% 3.65/1.63  tff(c_2923, plain, (![A_218, D_219]: (k2_xboole_0(k1_tarski(A_218), k1_tarski(D_219))=k2_tarski(A_218, D_219))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2919])).
% 3.65/1.63  tff(c_18, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.65/1.63  tff(c_20, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.65/1.63  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.65/1.63  tff(c_303, plain, (![A_101, B_102, C_103]: (~r1_xboole_0(A_101, B_102) | ~r2_hidden(C_103, k3_xboole_0(A_101, B_102)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.65/1.63  tff(c_360, plain, (![A_109, B_110]: (~r1_xboole_0(A_109, B_110) | k3_xboole_0(A_109, B_110)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_303])).
% 3.65/1.63  tff(c_370, plain, (![A_111, B_112]: (k3_xboole_0(k4_xboole_0(A_111, B_112), B_112)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_360])).
% 3.65/1.63  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.65/1.63  tff(c_381, plain, (![B_112, A_111]: (k3_xboole_0(B_112, k4_xboole_0(A_111, B_112))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_370, c_2])).
% 3.65/1.63  tff(c_407, plain, (![B_113, A_114]: (k3_xboole_0(B_113, k4_xboole_0(A_114, B_113))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_370, c_2])).
% 3.65/1.63  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.65/1.63  tff(c_415, plain, (![B_113, A_114]: (k4_xboole_0(B_113, k4_xboole_0(A_114, B_113))=k5_xboole_0(B_113, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_407, c_12])).
% 3.65/1.63  tff(c_432, plain, (![B_115, A_116]: (k4_xboole_0(B_115, k4_xboole_0(A_116, B_115))=B_115)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_415])).
% 3.65/1.63  tff(c_16, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.65/1.63  tff(c_447, plain, (![B_115, A_116]: (k3_xboole_0(B_115, k4_xboole_0(A_116, B_115))=k4_xboole_0(B_115, B_115))), inference(superposition, [status(thm), theory('equality')], [c_432, c_16])).
% 3.65/1.63  tff(c_477, plain, (![B_115]: (k4_xboole_0(B_115, B_115)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_381, c_447])).
% 3.65/1.63  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.65/1.63  tff(c_236, plain, (![A_98, B_99]: (k5_xboole_0(A_98, k3_xboole_0(A_98, B_99))=k4_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.65/1.63  tff(c_257, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_236])).
% 3.65/1.63  tff(c_492, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_477, c_257])).
% 3.65/1.63  tff(c_78, plain, (r1_tarski(k1_tarski('#skF_7'), k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.65/1.63  tff(c_156, plain, (![A_87, B_88]: (k3_xboole_0(A_87, B_88)=A_87 | ~r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.65/1.63  tff(c_160, plain, (k3_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(resolution, [status(thm)], [c_78, c_156])).
% 3.65/1.63  tff(c_248, plain, (k5_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_7'))=k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_160, c_236])).
% 3.65/1.63  tff(c_530, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_492, c_248])).
% 3.65/1.63  tff(c_22, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.65/1.63  tff(c_563, plain, (k2_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k5_xboole_0(k1_tarski('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_530, c_22])).
% 3.65/1.63  tff(c_570, plain, (k2_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_563])).
% 3.65/1.63  tff(c_2929, plain, (k2_tarski('#skF_8', '#skF_7')=k1_tarski('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2923, c_570])).
% 3.65/1.63  tff(c_161, plain, (![A_89, B_90]: (k1_enumset1(A_89, A_89, B_90)=k2_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.65/1.63  tff(c_26, plain, (![E_29, A_23, B_24]: (r2_hidden(E_29, k1_enumset1(A_23, B_24, E_29)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.65/1.63  tff(c_173, plain, (![B_90, A_89]: (r2_hidden(B_90, k2_tarski(A_89, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_161, c_26])).
% 3.65/1.63  tff(c_2966, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2929, c_173])).
% 3.65/1.63  tff(c_48, plain, (![C_34, A_30]: (C_34=A_30 | ~r2_hidden(C_34, k1_tarski(A_30)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.65/1.63  tff(c_2977, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_2966, c_48])).
% 3.65/1.63  tff(c_2981, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_2977])).
% 3.65/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.63  
% 3.65/1.63  Inference rules
% 3.65/1.63  ----------------------
% 3.65/1.63  #Ref     : 0
% 3.65/1.63  #Sup     : 700
% 3.65/1.63  #Fact    : 0
% 3.65/1.63  #Define  : 0
% 3.65/1.63  #Split   : 2
% 3.65/1.63  #Chain   : 0
% 3.65/1.63  #Close   : 0
% 3.65/1.63  
% 3.65/1.63  Ordering : KBO
% 3.65/1.63  
% 3.65/1.63  Simplification rules
% 3.65/1.63  ----------------------
% 3.65/1.63  #Subsume      : 36
% 3.65/1.63  #Demod        : 690
% 3.65/1.63  #Tautology    : 550
% 3.65/1.63  #SimpNegUnit  : 26
% 3.65/1.63  #BackRed      : 4
% 3.65/1.63  
% 3.65/1.63  #Partial instantiations: 0
% 3.65/1.63  #Strategies tried      : 1
% 3.65/1.63  
% 3.65/1.63  Timing (in seconds)
% 3.65/1.63  ----------------------
% 3.65/1.64  Preprocessing        : 0.34
% 3.65/1.64  Parsing              : 0.18
% 3.65/1.64  CNF conversion       : 0.03
% 3.65/1.64  Main loop            : 0.59
% 3.65/1.64  Inferencing          : 0.18
% 3.65/1.64  Reduction            : 0.25
% 3.65/1.64  Demodulation         : 0.20
% 3.65/1.64  BG Simplification    : 0.03
% 3.65/1.64  Subsumption          : 0.09
% 3.65/1.64  Abstraction          : 0.03
% 3.65/1.64  MUC search           : 0.00
% 3.65/1.64  Cooper               : 0.00
% 3.65/1.64  Total                : 0.97
% 3.65/1.64  Index Insertion      : 0.00
% 3.65/1.64  Index Deletion       : 0.00
% 3.65/1.64  Index Matching       : 0.00
% 3.65/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
