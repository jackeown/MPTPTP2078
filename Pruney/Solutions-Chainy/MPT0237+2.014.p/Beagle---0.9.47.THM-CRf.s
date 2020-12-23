%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:46 EST 2020

% Result     : Theorem 7.62s
% Output     : CNFRefutation 7.62s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 315 expanded)
%              Number of leaves         :   43 ( 122 expanded)
%              Depth                    :   13
%              Number of atoms          :  110 ( 435 expanded)
%              Number of equality atoms :   72 ( 248 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_82,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_100,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_113,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_50,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_199,plain,(
    ! [A_95,B_96,C_97] :
      ( ~ r1_xboole_0(A_95,B_96)
      | ~ r2_hidden(C_97,k3_xboole_0(A_95,B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_257,plain,(
    ! [A_104,B_105] :
      ( ~ r1_xboole_0(A_104,B_105)
      | k3_xboole_0(A_104,B_105) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_199])).

tff(c_269,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_257])).

tff(c_141,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(A_85,B_86) = A_85
      | ~ r1_xboole_0(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_153,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(resolution,[status(thm)],[c_18,c_141])).

tff(c_442,plain,(
    ! [A_115,B_116] : k4_xboole_0(A_115,k4_xboole_0(A_115,B_116)) = k3_xboole_0(A_115,B_116) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_471,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k3_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_442])).

tff(c_479,plain,(
    ! [A_117] : k4_xboole_0(A_117,A_117) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_471])).

tff(c_24,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_490,plain,(
    ! [A_117] : k5_xboole_0(A_117,k1_xboole_0) = k2_xboole_0(A_117,A_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_24])).

tff(c_507,plain,(
    ! [A_117] : k2_xboole_0(A_117,A_117) = A_117 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_490])).

tff(c_163,plain,(
    ! [A_88,B_89] : k1_enumset1(A_88,A_88,B_89) = k2_tarski(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    ! [E_28,A_22,C_24] : r2_hidden(E_28,k1_enumset1(A_22,E_28,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_193,plain,(
    ! [A_92,B_93] : r2_hidden(A_92,k2_tarski(A_92,B_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_30])).

tff(c_196,plain,(
    ! [A_29] : r2_hidden(A_29,k1_tarski(A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_193])).

tff(c_68,plain,(
    ! [A_61,B_62] :
      ( r1_xboole_0(k1_tarski(A_61),k1_tarski(B_62))
      | B_62 = A_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1632,plain,(
    ! [A_218,B_219] :
      ( k4_xboole_0(k1_tarski(A_218),k1_tarski(B_219)) = k1_tarski(A_218)
      | B_219 = A_218 ) ),
    inference(resolution,[status(thm)],[c_68,c_141])).

tff(c_8182,plain,(
    ! [B_399,A_400] :
      ( k5_xboole_0(k1_tarski(B_399),k1_tarski(A_400)) = k2_xboole_0(k1_tarski(B_399),k1_tarski(A_400))
      | B_399 = A_400 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1632,c_24])).

tff(c_70,plain,(
    ! [A_63,B_64] :
      ( k5_xboole_0(k1_tarski(A_63),k1_tarski(B_64)) = k2_tarski(A_63,B_64)
      | B_64 = A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_9620,plain,(
    ! [B_409,A_410] :
      ( k2_xboole_0(k1_tarski(B_409),k1_tarski(A_410)) = k2_tarski(B_409,A_410)
      | B_409 = A_410
      | B_409 = A_410 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8182,c_70])).

tff(c_66,plain,(
    ! [A_59,B_60] : k3_tarski(k2_tarski(A_59,B_60)) = k2_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_72,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6'))) != k2_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_73,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k2_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_72])).

tff(c_9648,plain,(
    '#skF_5' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_9620,c_73])).

tff(c_477,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_471])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_270,plain,(
    ! [A_106,B_107] : k5_xboole_0(A_106,k3_xboole_0(A_106,B_107)) = k4_xboole_0(A_106,B_107) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_285,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_270])).

tff(c_478,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_285])).

tff(c_64,plain,(
    ! [B_58,A_57] :
      ( k3_xboole_0(B_58,k1_tarski(A_57)) = k1_tarski(A_57)
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_957,plain,(
    ! [A_159,B_160] : k5_xboole_0(A_159,k3_xboole_0(B_160,A_159)) = k4_xboole_0(A_159,B_160) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_270])).

tff(c_974,plain,(
    ! [A_57,B_58] :
      ( k5_xboole_0(k1_tarski(A_57),k1_tarski(A_57)) = k4_xboole_0(k1_tarski(A_57),B_58)
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_957])).

tff(c_1060,plain,(
    ! [A_167,B_168] :
      ( k4_xboole_0(k1_tarski(A_167),B_168) = k1_xboole_0
      | ~ r2_hidden(A_167,B_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_974])).

tff(c_1080,plain,(
    ! [B_168,A_167] :
      ( k2_xboole_0(B_168,k1_tarski(A_167)) = k5_xboole_0(B_168,k1_xboole_0)
      | ~ r2_hidden(A_167,B_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1060,c_24])).

tff(c_1215,plain,(
    ! [B_179,A_180] :
      ( k2_xboole_0(B_179,k1_tarski(A_180)) = B_179
      | ~ r2_hidden(A_180,B_179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1080])).

tff(c_1225,plain,
    ( k2_tarski('#skF_5','#skF_6') != k1_tarski('#skF_5')
    | ~ r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1215,c_73])).

tff(c_1368,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1225])).

tff(c_9652,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9648,c_1368])).

tff(c_9656,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_9652])).

tff(c_9658,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1225])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(A_18,B_19)
      | k4_xboole_0(A_18,B_19) != A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_236,plain,(
    ! [A_101,C_102] :
      ( ~ r1_xboole_0(A_101,A_101)
      | ~ r2_hidden(C_102,A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_199])).

tff(c_248,plain,(
    ! [C_102,B_19] :
      ( ~ r2_hidden(C_102,B_19)
      | k4_xboole_0(B_19,B_19) != B_19 ) ),
    inference(resolution,[status(thm)],[c_22,c_236])).

tff(c_618,plain,(
    ! [C_125,B_126] :
      ( ~ r2_hidden(C_125,B_126)
      | k1_xboole_0 != B_126 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_248])).

tff(c_641,plain,(
    ! [A_29] : k1_tarski(A_29) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_196,c_618])).

tff(c_1114,plain,(
    ! [A_169,B_170] :
      ( k3_xboole_0(k1_tarski(A_169),k1_tarski(B_170)) = k1_xboole_0
      | B_170 = A_169 ) ),
    inference(resolution,[status(thm)],[c_68,c_257])).

tff(c_1129,plain,(
    ! [B_170,A_169] :
      ( k1_tarski(B_170) = k1_xboole_0
      | ~ r2_hidden(B_170,k1_tarski(A_169))
      | B_170 = A_169 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_64])).

tff(c_1166,plain,(
    ! [B_170,A_169] :
      ( ~ r2_hidden(B_170,k1_tarski(A_169))
      | B_170 = A_169 ) ),
    inference(negUnitSimplification,[status(thm)],[c_641,c_1129])).

tff(c_9665,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_9658,c_1166])).

tff(c_9668,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) != k2_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9665,c_9665,c_73])).

tff(c_9672,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_507,c_9668])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n004.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 10:24:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.62/2.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.62/2.87  
% 7.62/2.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.62/2.87  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 7.62/2.87  
% 7.62/2.87  %Foreground sorts:
% 7.62/2.87  
% 7.62/2.87  
% 7.62/2.87  %Background operators:
% 7.62/2.87  
% 7.62/2.87  
% 7.62/2.87  %Foreground operators:
% 7.62/2.87  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.62/2.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.62/2.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.62/2.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.62/2.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.62/2.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.62/2.87  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.62/2.87  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.62/2.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.62/2.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.62/2.87  tff('#skF_5', type, '#skF_5': $i).
% 7.62/2.87  tff('#skF_6', type, '#skF_6': $i).
% 7.62/2.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.62/2.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.62/2.87  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.62/2.87  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 7.62/2.87  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.62/2.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.62/2.87  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.62/2.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.62/2.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.62/2.87  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.62/2.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.62/2.87  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.62/2.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.62/2.87  
% 7.62/2.89  tff(f_82, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.62/2.89  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 7.62/2.89  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.62/2.89  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.62/2.89  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.62/2.89  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.62/2.89  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.62/2.89  tff(f_65, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.62/2.89  tff(f_84, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.62/2.89  tff(f_80, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 7.62/2.89  tff(f_105, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 7.62/2.89  tff(f_110, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 7.62/2.89  tff(f_100, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.62/2.89  tff(f_113, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 7.62/2.89  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.62/2.89  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.62/2.89  tff(f_98, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 7.62/2.89  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.62/2.89  tff(c_50, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.62/2.89  tff(c_16, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.62/2.89  tff(c_18, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.62/2.89  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.62/2.89  tff(c_199, plain, (![A_95, B_96, C_97]: (~r1_xboole_0(A_95, B_96) | ~r2_hidden(C_97, k3_xboole_0(A_95, B_96)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.62/2.89  tff(c_257, plain, (![A_104, B_105]: (~r1_xboole_0(A_104, B_105) | k3_xboole_0(A_104, B_105)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_199])).
% 7.62/2.89  tff(c_269, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_257])).
% 7.62/2.89  tff(c_141, plain, (![A_85, B_86]: (k4_xboole_0(A_85, B_86)=A_85 | ~r1_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.62/2.89  tff(c_153, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(resolution, [status(thm)], [c_18, c_141])).
% 7.62/2.89  tff(c_442, plain, (![A_115, B_116]: (k4_xboole_0(A_115, k4_xboole_0(A_115, B_116))=k3_xboole_0(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.62/2.89  tff(c_471, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k3_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_153, c_442])).
% 7.62/2.89  tff(c_479, plain, (![A_117]: (k4_xboole_0(A_117, A_117)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_269, c_471])).
% 7.62/2.89  tff(c_24, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.62/2.89  tff(c_490, plain, (![A_117]: (k5_xboole_0(A_117, k1_xboole_0)=k2_xboole_0(A_117, A_117))), inference(superposition, [status(thm), theory('equality')], [c_479, c_24])).
% 7.62/2.89  tff(c_507, plain, (![A_117]: (k2_xboole_0(A_117, A_117)=A_117)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_490])).
% 7.62/2.89  tff(c_163, plain, (![A_88, B_89]: (k1_enumset1(A_88, A_88, B_89)=k2_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.62/2.89  tff(c_30, plain, (![E_28, A_22, C_24]: (r2_hidden(E_28, k1_enumset1(A_22, E_28, C_24)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.62/2.89  tff(c_193, plain, (![A_92, B_93]: (r2_hidden(A_92, k2_tarski(A_92, B_93)))), inference(superposition, [status(thm), theory('equality')], [c_163, c_30])).
% 7.62/2.89  tff(c_196, plain, (![A_29]: (r2_hidden(A_29, k1_tarski(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_193])).
% 7.62/2.89  tff(c_68, plain, (![A_61, B_62]: (r1_xboole_0(k1_tarski(A_61), k1_tarski(B_62)) | B_62=A_61)), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.62/2.89  tff(c_1632, plain, (![A_218, B_219]: (k4_xboole_0(k1_tarski(A_218), k1_tarski(B_219))=k1_tarski(A_218) | B_219=A_218)), inference(resolution, [status(thm)], [c_68, c_141])).
% 7.62/2.89  tff(c_8182, plain, (![B_399, A_400]: (k5_xboole_0(k1_tarski(B_399), k1_tarski(A_400))=k2_xboole_0(k1_tarski(B_399), k1_tarski(A_400)) | B_399=A_400)), inference(superposition, [status(thm), theory('equality')], [c_1632, c_24])).
% 7.62/2.89  tff(c_70, plain, (![A_63, B_64]: (k5_xboole_0(k1_tarski(A_63), k1_tarski(B_64))=k2_tarski(A_63, B_64) | B_64=A_63)), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.62/2.89  tff(c_9620, plain, (![B_409, A_410]: (k2_xboole_0(k1_tarski(B_409), k1_tarski(A_410))=k2_tarski(B_409, A_410) | B_409=A_410 | B_409=A_410)), inference(superposition, [status(thm), theory('equality')], [c_8182, c_70])).
% 7.62/2.89  tff(c_66, plain, (![A_59, B_60]: (k3_tarski(k2_tarski(A_59, B_60))=k2_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.62/2.89  tff(c_72, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6')))!=k2_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.62/2.89  tff(c_73, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k2_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_72])).
% 7.62/2.89  tff(c_9648, plain, ('#skF_5'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_9620, c_73])).
% 7.62/2.89  tff(c_477, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_269, c_471])).
% 7.62/2.89  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.62/2.89  tff(c_270, plain, (![A_106, B_107]: (k5_xboole_0(A_106, k3_xboole_0(A_106, B_107))=k4_xboole_0(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.62/2.89  tff(c_285, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_270])).
% 7.62/2.89  tff(c_478, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_477, c_285])).
% 7.62/2.89  tff(c_64, plain, (![B_58, A_57]: (k3_xboole_0(B_58, k1_tarski(A_57))=k1_tarski(A_57) | ~r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.62/2.89  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.62/2.89  tff(c_957, plain, (![A_159, B_160]: (k5_xboole_0(A_159, k3_xboole_0(B_160, A_159))=k4_xboole_0(A_159, B_160))), inference(superposition, [status(thm), theory('equality')], [c_2, c_270])).
% 7.62/2.89  tff(c_974, plain, (![A_57, B_58]: (k5_xboole_0(k1_tarski(A_57), k1_tarski(A_57))=k4_xboole_0(k1_tarski(A_57), B_58) | ~r2_hidden(A_57, B_58))), inference(superposition, [status(thm), theory('equality')], [c_64, c_957])).
% 7.62/2.89  tff(c_1060, plain, (![A_167, B_168]: (k4_xboole_0(k1_tarski(A_167), B_168)=k1_xboole_0 | ~r2_hidden(A_167, B_168))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_974])).
% 7.62/2.89  tff(c_1080, plain, (![B_168, A_167]: (k2_xboole_0(B_168, k1_tarski(A_167))=k5_xboole_0(B_168, k1_xboole_0) | ~r2_hidden(A_167, B_168))), inference(superposition, [status(thm), theory('equality')], [c_1060, c_24])).
% 7.62/2.89  tff(c_1215, plain, (![B_179, A_180]: (k2_xboole_0(B_179, k1_tarski(A_180))=B_179 | ~r2_hidden(A_180, B_179))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1080])).
% 7.62/2.89  tff(c_1225, plain, (k2_tarski('#skF_5', '#skF_6')!=k1_tarski('#skF_5') | ~r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1215, c_73])).
% 7.62/2.89  tff(c_1368, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_1225])).
% 7.62/2.89  tff(c_9652, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_9648, c_1368])).
% 7.62/2.89  tff(c_9656, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_196, c_9652])).
% 7.62/2.89  tff(c_9658, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_1225])).
% 7.62/2.89  tff(c_22, plain, (![A_18, B_19]: (r1_xboole_0(A_18, B_19) | k4_xboole_0(A_18, B_19)!=A_18)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.62/2.89  tff(c_236, plain, (![A_101, C_102]: (~r1_xboole_0(A_101, A_101) | ~r2_hidden(C_102, A_101))), inference(superposition, [status(thm), theory('equality')], [c_4, c_199])).
% 7.62/2.89  tff(c_248, plain, (![C_102, B_19]: (~r2_hidden(C_102, B_19) | k4_xboole_0(B_19, B_19)!=B_19)), inference(resolution, [status(thm)], [c_22, c_236])).
% 7.62/2.89  tff(c_618, plain, (![C_125, B_126]: (~r2_hidden(C_125, B_126) | k1_xboole_0!=B_126)), inference(demodulation, [status(thm), theory('equality')], [c_477, c_248])).
% 7.62/2.89  tff(c_641, plain, (![A_29]: (k1_tarski(A_29)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_196, c_618])).
% 7.62/2.89  tff(c_1114, plain, (![A_169, B_170]: (k3_xboole_0(k1_tarski(A_169), k1_tarski(B_170))=k1_xboole_0 | B_170=A_169)), inference(resolution, [status(thm)], [c_68, c_257])).
% 7.62/2.89  tff(c_1129, plain, (![B_170, A_169]: (k1_tarski(B_170)=k1_xboole_0 | ~r2_hidden(B_170, k1_tarski(A_169)) | B_170=A_169)), inference(superposition, [status(thm), theory('equality')], [c_1114, c_64])).
% 7.62/2.89  tff(c_1166, plain, (![B_170, A_169]: (~r2_hidden(B_170, k1_tarski(A_169)) | B_170=A_169)), inference(negUnitSimplification, [status(thm)], [c_641, c_1129])).
% 7.62/2.89  tff(c_9665, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_9658, c_1166])).
% 7.62/2.89  tff(c_9668, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))!=k2_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9665, c_9665, c_73])).
% 7.62/2.89  tff(c_9672, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_507, c_9668])).
% 7.62/2.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.62/2.89  
% 7.62/2.89  Inference rules
% 7.62/2.89  ----------------------
% 7.62/2.89  #Ref     : 0
% 7.62/2.89  #Sup     : 2370
% 7.62/2.89  #Fact    : 24
% 7.62/2.89  #Define  : 0
% 7.62/2.89  #Split   : 1
% 7.62/2.89  #Chain   : 0
% 7.62/2.89  #Close   : 0
% 7.62/2.89  
% 7.62/2.89  Ordering : KBO
% 7.62/2.89  
% 7.62/2.89  Simplification rules
% 7.62/2.89  ----------------------
% 7.62/2.89  #Subsume      : 663
% 7.62/2.89  #Demod        : 1752
% 7.62/2.89  #Tautology    : 912
% 7.62/2.89  #SimpNegUnit  : 115
% 7.62/2.89  #BackRed      : 6
% 7.62/2.89  
% 7.62/2.89  #Partial instantiations: 0
% 7.62/2.89  #Strategies tried      : 1
% 7.62/2.89  
% 7.62/2.89  Timing (in seconds)
% 7.62/2.89  ----------------------
% 7.62/2.89  Preprocessing        : 0.38
% 7.62/2.89  Parsing              : 0.19
% 7.62/2.89  CNF conversion       : 0.03
% 7.62/2.89  Main loop            : 1.66
% 7.62/2.89  Inferencing          : 0.47
% 7.62/2.89  Reduction            : 0.67
% 7.62/2.89  Demodulation         : 0.53
% 7.62/2.89  BG Simplification    : 0.06
% 7.62/2.89  Subsumption          : 0.37
% 7.62/2.89  Abstraction          : 0.10
% 7.62/2.89  MUC search           : 0.00
% 7.62/2.89  Cooper               : 0.00
% 7.62/2.89  Total                : 2.09
% 7.62/2.89  Index Insertion      : 0.00
% 7.62/2.89  Index Deletion       : 0.00
% 7.62/2.89  Index Matching       : 0.00
% 7.62/2.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
