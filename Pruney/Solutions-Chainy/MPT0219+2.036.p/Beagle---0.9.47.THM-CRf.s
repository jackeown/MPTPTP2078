%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:54 EST 2020

% Result     : Theorem 7.12s
% Output     : CNFRefutation 7.24s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 182 expanded)
%              Number of leaves         :   36 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :   71 ( 210 expanded)
%              Number of equality atoms :   49 ( 128 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_65,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_42,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_137,plain,(
    ! [B_62,A_63] : k5_xboole_0(B_62,A_63) = k5_xboole_0(A_63,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_153,plain,(
    ! [A_63] : k5_xboole_0(k1_xboole_0,A_63) = A_63 ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_22])).

tff(c_20,plain,(
    ! [A_20,B_21] : r1_tarski(k4_xboole_0(A_20,B_21),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_233,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(A_67,B_68) = A_67
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1244,plain,(
    ! [A_134,B_135] : k3_xboole_0(k4_xboole_0(A_134,B_135),A_134) = k4_xboole_0(A_134,B_135) ),
    inference(resolution,[status(thm)],[c_20,c_233])).

tff(c_24,plain,(
    ! [A_23,B_24] : r1_xboole_0(k4_xboole_0(A_23,B_24),B_24) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_372,plain,(
    ! [A_79,B_80,C_81] :
      ( ~ r1_xboole_0(A_79,B_80)
      | ~ r2_hidden(C_81,k3_xboole_0(A_79,B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_595,plain,(
    ! [A_96,B_97] :
      ( ~ r1_xboole_0(A_96,B_97)
      | k3_xboole_0(A_96,B_97) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_372])).

tff(c_616,plain,(
    ! [A_23,B_24] : k3_xboole_0(k4_xboole_0(A_23,B_24),B_24) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_595])).

tff(c_1261,plain,(
    ! [A_134] : k4_xboole_0(A_134,A_134) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1244,c_616])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_300,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k4_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_323,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_300])).

tff(c_1320,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1261,c_323])).

tff(c_44,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    ! [A_28,B_29] : k5_xboole_0(A_28,k4_xboole_0(B_29,A_28)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_423,plain,(
    ! [A_88,B_89,C_90] : k5_xboole_0(k5_xboole_0(A_88,B_89),C_90) = k5_xboole_0(A_88,k5_xboole_0(B_89,C_90)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6302,plain,(
    ! [A_215,B_216,C_217] : k5_xboole_0(A_215,k5_xboole_0(k4_xboole_0(B_216,A_215),C_217)) = k5_xboole_0(k2_xboole_0(A_215,B_216),C_217) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_423])).

tff(c_6423,plain,(
    ! [A_215,B_216] : k5_xboole_0(k2_xboole_0(A_215,B_216),k4_xboole_0(B_216,A_215)) = k5_xboole_0(A_215,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1320,c_6302])).

tff(c_6737,plain,(
    ! [A_220,B_221] : k5_xboole_0(k2_xboole_0(A_220,B_221),k4_xboole_0(B_221,A_220)) = A_220 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6423])).

tff(c_6827,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3'))) = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_6737])).

tff(c_1379,plain,(
    ! [A_137] : k5_xboole_0(A_137,A_137) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1261,c_323])).

tff(c_26,plain,(
    ! [A_25,B_26,C_27] : k5_xboole_0(k5_xboole_0(A_25,B_26),C_27) = k5_xboole_0(A_25,k5_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1384,plain,(
    ! [A_137,C_27] : k5_xboole_0(A_137,k5_xboole_0(A_137,C_27)) = k5_xboole_0(k1_xboole_0,C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_1379,c_26])).

tff(c_1412,plain,(
    ! [A_137,C_27] : k5_xboole_0(A_137,k5_xboole_0(A_137,C_27)) = C_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_1384])).

tff(c_8377,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6827,c_1412])).

tff(c_8393,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1320,c_8377])).

tff(c_14,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7110,plain,(
    ! [A_224,B_225,C_226] : k5_xboole_0(A_224,k5_xboole_0(k3_xboole_0(A_224,B_225),C_226)) = k5_xboole_0(k4_xboole_0(A_224,B_225),C_226) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_423])).

tff(c_7260,plain,(
    ! [A_224,B_225] : k5_xboole_0(k4_xboole_0(A_224,B_225),k3_xboole_0(A_224,B_225)) = k5_xboole_0(A_224,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1320,c_7110])).

tff(c_8936,plain,(
    ! [A_241,B_242] : k5_xboole_0(k4_xboole_0(A_241,B_242),k3_xboole_0(A_241,B_242)) = A_241 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_7260])).

tff(c_9745,plain,(
    ! [A_246,B_247] : k5_xboole_0(k4_xboole_0(A_246,B_247),A_246) = k3_xboole_0(A_246,B_247) ),
    inference(superposition,[status(thm),theory(equality)],[c_8936,c_1412])).

tff(c_9834,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_xboole_0,k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8393,c_9745])).

tff(c_9908,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_9834])).

tff(c_79,plain,(
    ! [B_57,A_58] : k3_xboole_0(B_57,A_58) = k3_xboole_0(A_58,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_16,B_17] : r1_tarski(k3_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_94,plain,(
    ! [B_57,A_58] : r1_tarski(k3_xboole_0(B_57,A_58),A_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_16])).

tff(c_10040,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9908,c_94])).

tff(c_40,plain,(
    ! [B_46,A_45] :
      ( B_46 = A_45
      | ~ r1_tarski(k1_tarski(A_45),k1_tarski(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_10082,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10040,c_40])).

tff(c_10089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_10082])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:21:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.12/2.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/2.68  
% 7.12/2.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/2.68  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.12/2.68  
% 7.12/2.68  %Foreground sorts:
% 7.12/2.68  
% 7.12/2.68  
% 7.12/2.68  %Background operators:
% 7.12/2.68  
% 7.12/2.68  
% 7.12/2.68  %Foreground operators:
% 7.12/2.68  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.12/2.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.12/2.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.12/2.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.12/2.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.12/2.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.12/2.68  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.12/2.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.12/2.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.12/2.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.12/2.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.12/2.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.12/2.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.12/2.68  tff('#skF_3', type, '#skF_3': $i).
% 7.12/2.68  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.12/2.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.12/2.68  tff('#skF_4', type, '#skF_4': $i).
% 7.12/2.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.12/2.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.12/2.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.12/2.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.12/2.68  
% 7.12/2.70  tff(f_90, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 7.12/2.70  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.12/2.70  tff(f_65, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 7.12/2.70  tff(f_63, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.12/2.70  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.12/2.70  tff(f_67, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.12/2.70  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.12/2.70  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.12/2.70  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.12/2.70  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.12/2.70  tff(f_71, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.12/2.70  tff(f_69, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.12/2.70  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.12/2.70  tff(f_57, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.12/2.70  tff(f_85, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 7.12/2.70  tff(c_42, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.12/2.70  tff(c_137, plain, (![B_62, A_63]: (k5_xboole_0(B_62, A_63)=k5_xboole_0(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.12/2.70  tff(c_22, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.12/2.70  tff(c_153, plain, (![A_63]: (k5_xboole_0(k1_xboole_0, A_63)=A_63)), inference(superposition, [status(thm), theory('equality')], [c_137, c_22])).
% 7.12/2.70  tff(c_20, plain, (![A_20, B_21]: (r1_tarski(k4_xboole_0(A_20, B_21), A_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.12/2.70  tff(c_233, plain, (![A_67, B_68]: (k3_xboole_0(A_67, B_68)=A_67 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.12/2.70  tff(c_1244, plain, (![A_134, B_135]: (k3_xboole_0(k4_xboole_0(A_134, B_135), A_134)=k4_xboole_0(A_134, B_135))), inference(resolution, [status(thm)], [c_20, c_233])).
% 7.12/2.70  tff(c_24, plain, (![A_23, B_24]: (r1_xboole_0(k4_xboole_0(A_23, B_24), B_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.12/2.70  tff(c_12, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.12/2.70  tff(c_372, plain, (![A_79, B_80, C_81]: (~r1_xboole_0(A_79, B_80) | ~r2_hidden(C_81, k3_xboole_0(A_79, B_80)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.12/2.70  tff(c_595, plain, (![A_96, B_97]: (~r1_xboole_0(A_96, B_97) | k3_xboole_0(A_96, B_97)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_372])).
% 7.12/2.70  tff(c_616, plain, (![A_23, B_24]: (k3_xboole_0(k4_xboole_0(A_23, B_24), B_24)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_595])).
% 7.12/2.70  tff(c_1261, plain, (![A_134]: (k4_xboole_0(A_134, A_134)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1244, c_616])).
% 7.24/2.70  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.24/2.70  tff(c_300, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k4_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.24/2.70  tff(c_323, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_300])).
% 7.24/2.70  tff(c_1320, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1261, c_323])).
% 7.24/2.70  tff(c_44, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.24/2.70  tff(c_28, plain, (![A_28, B_29]: (k5_xboole_0(A_28, k4_xboole_0(B_29, A_28))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.24/2.70  tff(c_423, plain, (![A_88, B_89, C_90]: (k5_xboole_0(k5_xboole_0(A_88, B_89), C_90)=k5_xboole_0(A_88, k5_xboole_0(B_89, C_90)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.24/2.70  tff(c_6302, plain, (![A_215, B_216, C_217]: (k5_xboole_0(A_215, k5_xboole_0(k4_xboole_0(B_216, A_215), C_217))=k5_xboole_0(k2_xboole_0(A_215, B_216), C_217))), inference(superposition, [status(thm), theory('equality')], [c_28, c_423])).
% 7.24/2.70  tff(c_6423, plain, (![A_215, B_216]: (k5_xboole_0(k2_xboole_0(A_215, B_216), k4_xboole_0(B_216, A_215))=k5_xboole_0(A_215, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1320, c_6302])).
% 7.24/2.70  tff(c_6737, plain, (![A_220, B_221]: (k5_xboole_0(k2_xboole_0(A_220, B_221), k4_xboole_0(B_221, A_220))=A_220)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6423])).
% 7.24/2.70  tff(c_6827, plain, (k5_xboole_0(k1_tarski('#skF_3'), k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3')))=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_44, c_6737])).
% 7.24/2.70  tff(c_1379, plain, (![A_137]: (k5_xboole_0(A_137, A_137)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1261, c_323])).
% 7.24/2.70  tff(c_26, plain, (![A_25, B_26, C_27]: (k5_xboole_0(k5_xboole_0(A_25, B_26), C_27)=k5_xboole_0(A_25, k5_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.24/2.70  tff(c_1384, plain, (![A_137, C_27]: (k5_xboole_0(A_137, k5_xboole_0(A_137, C_27))=k5_xboole_0(k1_xboole_0, C_27))), inference(superposition, [status(thm), theory('equality')], [c_1379, c_26])).
% 7.24/2.70  tff(c_1412, plain, (![A_137, C_27]: (k5_xboole_0(A_137, k5_xboole_0(A_137, C_27))=C_27)), inference(demodulation, [status(thm), theory('equality')], [c_153, c_1384])).
% 7.24/2.70  tff(c_8377, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6827, c_1412])).
% 7.24/2.70  tff(c_8393, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1320, c_8377])).
% 7.24/2.70  tff(c_14, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.24/2.70  tff(c_7110, plain, (![A_224, B_225, C_226]: (k5_xboole_0(A_224, k5_xboole_0(k3_xboole_0(A_224, B_225), C_226))=k5_xboole_0(k4_xboole_0(A_224, B_225), C_226))), inference(superposition, [status(thm), theory('equality')], [c_14, c_423])).
% 7.24/2.70  tff(c_7260, plain, (![A_224, B_225]: (k5_xboole_0(k4_xboole_0(A_224, B_225), k3_xboole_0(A_224, B_225))=k5_xboole_0(A_224, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1320, c_7110])).
% 7.24/2.70  tff(c_8936, plain, (![A_241, B_242]: (k5_xboole_0(k4_xboole_0(A_241, B_242), k3_xboole_0(A_241, B_242))=A_241)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_7260])).
% 7.24/2.70  tff(c_9745, plain, (![A_246, B_247]: (k5_xboole_0(k4_xboole_0(A_246, B_247), A_246)=k3_xboole_0(A_246, B_247))), inference(superposition, [status(thm), theory('equality')], [c_8936, c_1412])).
% 7.24/2.70  tff(c_9834, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_xboole_0, k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8393, c_9745])).
% 7.24/2.70  tff(c_9908, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_9834])).
% 7.24/2.70  tff(c_79, plain, (![B_57, A_58]: (k3_xboole_0(B_57, A_58)=k3_xboole_0(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.24/2.70  tff(c_16, plain, (![A_16, B_17]: (r1_tarski(k3_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.24/2.70  tff(c_94, plain, (![B_57, A_58]: (r1_tarski(k3_xboole_0(B_57, A_58), A_58))), inference(superposition, [status(thm), theory('equality')], [c_79, c_16])).
% 7.24/2.70  tff(c_10040, plain, (r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_9908, c_94])).
% 7.24/2.70  tff(c_40, plain, (![B_46, A_45]: (B_46=A_45 | ~r1_tarski(k1_tarski(A_45), k1_tarski(B_46)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.24/2.70  tff(c_10082, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_10040, c_40])).
% 7.24/2.70  tff(c_10089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_10082])).
% 7.24/2.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.24/2.70  
% 7.24/2.70  Inference rules
% 7.24/2.70  ----------------------
% 7.24/2.70  #Ref     : 0
% 7.24/2.70  #Sup     : 2499
% 7.24/2.70  #Fact    : 0
% 7.24/2.70  #Define  : 0
% 7.24/2.70  #Split   : 0
% 7.24/2.70  #Chain   : 0
% 7.24/2.70  #Close   : 0
% 7.24/2.70  
% 7.24/2.70  Ordering : KBO
% 7.24/2.70  
% 7.24/2.70  Simplification rules
% 7.24/2.70  ----------------------
% 7.24/2.70  #Subsume      : 93
% 7.24/2.70  #Demod        : 2716
% 7.24/2.70  #Tautology    : 1635
% 7.24/2.70  #SimpNegUnit  : 17
% 7.24/2.70  #BackRed      : 7
% 7.24/2.70  
% 7.24/2.70  #Partial instantiations: 0
% 7.24/2.70  #Strategies tried      : 1
% 7.24/2.70  
% 7.24/2.70  Timing (in seconds)
% 7.24/2.70  ----------------------
% 7.24/2.70  Preprocessing        : 0.34
% 7.24/2.70  Parsing              : 0.18
% 7.24/2.70  CNF conversion       : 0.02
% 7.24/2.70  Main loop            : 1.53
% 7.24/2.70  Inferencing          : 0.39
% 7.24/2.70  Reduction            : 0.82
% 7.24/2.70  Demodulation         : 0.72
% 7.24/2.70  BG Simplification    : 0.05
% 7.24/2.70  Subsumption          : 0.19
% 7.24/2.70  Abstraction          : 0.07
% 7.24/2.70  MUC search           : 0.00
% 7.24/2.70  Cooper               : 0.00
% 7.24/2.70  Total                : 1.90
% 7.24/2.70  Index Insertion      : 0.00
% 7.24/2.70  Index Deletion       : 0.00
% 7.24/2.70  Index Matching       : 0.00
% 7.24/2.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
