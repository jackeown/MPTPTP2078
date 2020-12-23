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
% DateTime   : Thu Dec  3 09:43:49 EST 2020

% Result     : Theorem 51.14s
% Output     : CNFRefutation 51.14s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 432 expanded)
%              Number of leaves         :   31 ( 157 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 486 expanded)
%              Number of equality atoms :   73 ( 399 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k2_xboole_0(A,C),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_38,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_18,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_69,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k2_xboole_0(A_43,B_44)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_79,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_69])).

tff(c_353,plain,(
    ! [A_66,B_67] : k4_xboole_0(A_66,k4_xboole_0(A_66,B_67)) = k3_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_403,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_353])).

tff(c_416,plain,(
    ! [A_68] : k3_xboole_0(A_68,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_403])).

tff(c_30,plain,(
    ! [A_28,B_29] : k2_xboole_0(k3_xboole_0(A_28,B_29),k4_xboole_0(A_28,B_29)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_427,plain,(
    ! [A_68] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_68,k1_xboole_0)) = A_68 ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_30])).

tff(c_439,plain,(
    ! [A_68] : k2_xboole_0(k1_xboole_0,A_68) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_427])).

tff(c_1664,plain,(
    ! [A_109,B_110,C_111] : k2_xboole_0(k2_xboole_0(A_109,B_110),C_111) = k2_xboole_0(A_109,k2_xboole_0(B_110,C_111)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k2_xboole_0(A_19,B_20)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_915,plain,(
    ! [A_84,B_85] : k2_xboole_0(A_84,k4_xboole_0(B_85,A_84)) = k2_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_968,plain,(
    ! [A_19,B_20] : k2_xboole_0(k2_xboole_0(A_19,B_20),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_19,B_20),A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_915])).

tff(c_987,plain,(
    ! [A_19,B_20] : k2_xboole_0(k2_xboole_0(A_19,B_20),A_19) = k2_xboole_0(A_19,B_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_968])).

tff(c_1682,plain,(
    ! [C_111,B_110] : k2_xboole_0(C_111,k2_xboole_0(B_110,C_111)) = k2_xboole_0(C_111,B_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_1664,c_987])).

tff(c_28,plain,(
    ! [A_25,B_26,C_27] : k2_xboole_0(k2_xboole_0(A_25,B_26),C_27) = k2_xboole_0(A_25,k2_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,(
    ! [A_30,C_32,B_31] : k2_xboole_0(k2_xboole_0(A_30,C_32),k2_xboole_0(B_31,C_32)) = k2_xboole_0(k2_xboole_0(A_30,B_31),C_32) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2229,plain,(
    ! [A_124,C_125,B_126] : k2_xboole_0(k2_xboole_0(A_124,C_125),k2_xboole_0(B_126,C_125)) = k2_xboole_0(A_124,k2_xboole_0(B_126,C_125)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_2379,plain,(
    ! [B_126,A_68] : k2_xboole_0(k1_xboole_0,k2_xboole_0(B_126,A_68)) = k2_xboole_0(A_68,k2_xboole_0(B_126,A_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_2229])).

tff(c_2441,plain,(
    ! [B_126,A_68] : k2_xboole_0(B_126,A_68) = k2_xboole_0(A_68,B_126) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1682,c_439,c_2379])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2455,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2441,c_44])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_16,B_17,C_18] :
      ( r1_tarski(k4_xboole_0(A_16,B_17),C_18)
      | ~ r1_tarski(A_16,k2_xboole_0(B_17,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_40,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2034,plain,(
    ! [A_115,B_116,C_117] :
      ( k1_xboole_0 = A_115
      | ~ r1_xboole_0(B_116,C_117)
      | ~ r1_tarski(A_115,C_117)
      | ~ r1_tarski(A_115,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2047,plain,(
    ! [A_118] :
      ( k1_xboole_0 = A_118
      | ~ r1_tarski(A_118,'#skF_4')
      | ~ r1_tarski(A_118,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_2034])).

tff(c_39028,plain,(
    ! [A_365,B_366] :
      ( k4_xboole_0(A_365,B_366) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(A_365,B_366),'#skF_4')
      | ~ r1_tarski(A_365,k2_xboole_0(B_366,'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_20,c_2047])).

tff(c_44383,plain,(
    ! [B_384] :
      ( k4_xboole_0('#skF_4',B_384) = k1_xboole_0
      | ~ r1_tarski('#skF_4',k2_xboole_0(B_384,'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_10,c_39028])).

tff(c_44436,plain,
    ( k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2455,c_44383])).

tff(c_45366,plain,(
    ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_44436])).

tff(c_45369,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_4','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_45366])).

tff(c_45373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_45369])).

tff(c_45374,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44436])).

tff(c_16,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_45471,plain,(
    k2_xboole_0('#skF_5',k1_xboole_0) = k2_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_45374,c_16])).

tff(c_45519,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2441,c_45471])).

tff(c_1780,plain,(
    ! [A_28,B_29,C_111] : k2_xboole_0(k3_xboole_0(A_28,B_29),k2_xboole_0(k4_xboole_0(A_28,B_29),C_111)) = k2_xboole_0(A_28,C_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1664])).

tff(c_11013,plain,(
    ! [A_199,B_200,C_201] : k2_xboole_0(k3_xboole_0(A_199,B_200),k2_xboole_0(k4_xboole_0(A_199,B_200),C_201)) = k2_xboole_0(A_199,C_201) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1664])).

tff(c_36,plain,(
    ! [A_36,B_37] : k2_xboole_0(A_36,k2_xboole_0(A_36,B_37)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_11121,plain,(
    ! [A_199,B_200,C_201] : k2_xboole_0(k3_xboole_0(A_199,B_200),k2_xboole_0(k4_xboole_0(A_199,B_200),C_201)) = k2_xboole_0(k3_xboole_0(A_199,B_200),k2_xboole_0(A_199,C_201)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11013,c_36])).

tff(c_11356,plain,(
    ! [A_199,B_200,C_201] : k2_xboole_0(k3_xboole_0(A_199,B_200),k2_xboole_0(A_199,C_201)) = k2_xboole_0(A_199,C_201) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1780,c_11121])).

tff(c_24,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k3_xboole_0(A_21,B_22)) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1216,plain,(
    ! [A_92,B_93,C_94] :
      ( r1_tarski(k4_xboole_0(A_92,B_93),C_94)
      | ~ r1_tarski(A_92,k2_xboole_0(B_93,C_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_15327,plain,(
    ! [A_239,B_240,C_241] :
      ( r1_tarski(k4_xboole_0(A_239,B_240),C_241)
      | ~ r1_tarski(A_239,k2_xboole_0(k3_xboole_0(A_239,B_240),C_241)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1216])).

tff(c_160177,plain,(
    ! [A_752,B_753,C_754] :
      ( r1_tarski(k4_xboole_0(A_752,B_753),C_754)
      | k4_xboole_0(A_752,k2_xboole_0(k3_xboole_0(A_752,B_753),C_754)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_15327])).

tff(c_160307,plain,(
    ! [A_199,B_200,C_201] :
      ( r1_tarski(k4_xboole_0(A_199,B_200),k2_xboole_0(A_199,C_201))
      | k4_xboole_0(A_199,k2_xboole_0(A_199,C_201)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11356,c_160177])).

tff(c_160820,plain,(
    ! [A_757,B_758,C_759] : r1_tarski(k4_xboole_0(A_757,B_758),k2_xboole_0(A_757,C_759)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_160307])).

tff(c_162051,plain,(
    ! [A_761,C_762] : r1_tarski(A_761,k2_xboole_0(A_761,C_762)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_160820])).

tff(c_162497,plain,(
    r1_tarski('#skF_5',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2455,c_162051])).

tff(c_42,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2082,plain,(
    ! [A_119] :
      ( k1_xboole_0 = A_119
      | ~ r1_tarski(A_119,'#skF_3')
      | ~ r1_tarski(A_119,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_2034])).

tff(c_6784,plain,(
    ! [B_165] :
      ( k4_xboole_0('#skF_5',B_165) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0('#skF_5',B_165),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_2082])).

tff(c_6836,plain,(
    ! [B_17] :
      ( k4_xboole_0('#skF_5',B_17) = k1_xboole_0
      | ~ r1_tarski('#skF_5',k2_xboole_0(B_17,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_20,c_6784])).

tff(c_164353,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_162497,c_6836])).

tff(c_570,plain,(
    ! [A_73,B_74] : k2_xboole_0(A_73,k2_xboole_0(A_73,B_74)) = k2_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_605,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = k2_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_570])).

tff(c_616,plain,(
    ! [A_8] : k2_xboole_0(A_8,A_8) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_605])).

tff(c_2362,plain,(
    ! [A_124,A_8] : k2_xboole_0(k2_xboole_0(A_124,A_8),A_8) = k2_xboole_0(A_124,k2_xboole_0(A_8,A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_2229])).

tff(c_3599,plain,(
    ! [A_137,A_138] : k2_xboole_0(k2_xboole_0(A_137,A_138),A_138) = k2_xboole_0(A_137,A_138) ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_2362])).

tff(c_3686,plain,(
    ! [B_126,A_137] : k2_xboole_0(B_126,k2_xboole_0(A_137,B_126)) = k2_xboole_0(A_137,B_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_2441,c_3599])).

tff(c_1750,plain,(
    ! [A_13,B_14,C_111] : k2_xboole_0(A_13,k2_xboole_0(k4_xboole_0(B_14,A_13),C_111)) = k2_xboole_0(k2_xboole_0(A_13,B_14),C_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1664])).

tff(c_8903,plain,(
    ! [A_184,B_185,C_186] : k2_xboole_0(A_184,k2_xboole_0(k4_xboole_0(B_185,A_184),C_186)) = k2_xboole_0(A_184,k2_xboole_0(B_185,C_186)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1750])).

tff(c_9132,plain,(
    ! [B_185,B_126] : k2_xboole_0(k4_xboole_0(B_185,B_126),B_126) = k2_xboole_0(B_126,k2_xboole_0(B_185,B_126)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3686,c_8903])).

tff(c_9279,plain,(
    ! [B_185,B_126] : k2_xboole_0(k4_xboole_0(B_185,B_126),B_126) = k2_xboole_0(B_126,B_185) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1682,c_9132])).

tff(c_164514,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_4') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_164353,c_9279])).

tff(c_164609,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_45519,c_164514])).

tff(c_164611,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_164609])).
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
% 0.13/0.35  % DateTime   : Tue Dec  1 20:30:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 51.14/41.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.14/41.15  
% 51.14/41.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.14/41.15  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 51.14/41.15  
% 51.14/41.15  %Foreground sorts:
% 51.14/41.15  
% 51.14/41.15  
% 51.14/41.15  %Background operators:
% 51.14/41.15  
% 51.14/41.15  
% 51.14/41.15  %Foreground operators:
% 51.14/41.15  tff('#skF_2', type, '#skF_2': $i > $i).
% 51.14/41.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 51.14/41.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 51.14/41.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 51.14/41.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 51.14/41.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 51.14/41.15  tff('#skF_5', type, '#skF_5': $i).
% 51.14/41.15  tff('#skF_6', type, '#skF_6': $i).
% 51.14/41.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 51.14/41.15  tff('#skF_3', type, '#skF_3': $i).
% 51.14/41.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 51.14/41.15  tff('#skF_4', type, '#skF_4': $i).
% 51.14/41.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 51.14/41.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 51.14/41.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 51.14/41.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 51.14/41.15  
% 51.14/41.17  tff(f_94, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 51.14/41.17  tff(f_59, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 51.14/41.17  tff(f_49, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 51.14/41.17  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 51.14/41.17  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 51.14/41.17  tff(f_73, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 51.14/41.17  tff(f_71, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 51.14/41.17  tff(f_57, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 51.14/41.17  tff(f_75, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_xboole_1)).
% 51.14/41.17  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 51.14/41.17  tff(f_51, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 51.14/41.17  tff(f_63, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 51.14/41.17  tff(f_83, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 51.14/41.17  tff(f_85, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 51.14/41.17  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 51.14/41.17  tff(c_38, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_94])).
% 51.14/41.17  tff(c_18, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_59])).
% 51.14/41.17  tff(c_8, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 51.14/41.17  tff(c_69, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k2_xboole_0(A_43, B_44))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 51.14/41.17  tff(c_79, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_69])).
% 51.14/41.17  tff(c_353, plain, (![A_66, B_67]: (k4_xboole_0(A_66, k4_xboole_0(A_66, B_67))=k3_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_69])).
% 51.14/41.17  tff(c_403, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_353])).
% 51.14/41.17  tff(c_416, plain, (![A_68]: (k3_xboole_0(A_68, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_79, c_403])).
% 51.14/41.17  tff(c_30, plain, (![A_28, B_29]: (k2_xboole_0(k3_xboole_0(A_28, B_29), k4_xboole_0(A_28, B_29))=A_28)), inference(cnfTransformation, [status(thm)], [f_73])).
% 51.14/41.17  tff(c_427, plain, (![A_68]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_68, k1_xboole_0))=A_68)), inference(superposition, [status(thm), theory('equality')], [c_416, c_30])).
% 51.14/41.17  tff(c_439, plain, (![A_68]: (k2_xboole_0(k1_xboole_0, A_68)=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_427])).
% 51.14/41.17  tff(c_1664, plain, (![A_109, B_110, C_111]: (k2_xboole_0(k2_xboole_0(A_109, B_110), C_111)=k2_xboole_0(A_109, k2_xboole_0(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 51.14/41.17  tff(c_22, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k2_xboole_0(A_19, B_20))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 51.14/41.17  tff(c_915, plain, (![A_84, B_85]: (k2_xboole_0(A_84, k4_xboole_0(B_85, A_84))=k2_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_57])).
% 51.14/41.17  tff(c_968, plain, (![A_19, B_20]: (k2_xboole_0(k2_xboole_0(A_19, B_20), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_19, B_20), A_19))), inference(superposition, [status(thm), theory('equality')], [c_22, c_915])).
% 51.14/41.17  tff(c_987, plain, (![A_19, B_20]: (k2_xboole_0(k2_xboole_0(A_19, B_20), A_19)=k2_xboole_0(A_19, B_20))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_968])).
% 51.14/41.17  tff(c_1682, plain, (![C_111, B_110]: (k2_xboole_0(C_111, k2_xboole_0(B_110, C_111))=k2_xboole_0(C_111, B_110))), inference(superposition, [status(thm), theory('equality')], [c_1664, c_987])).
% 51.14/41.17  tff(c_28, plain, (![A_25, B_26, C_27]: (k2_xboole_0(k2_xboole_0(A_25, B_26), C_27)=k2_xboole_0(A_25, k2_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 51.14/41.17  tff(c_32, plain, (![A_30, C_32, B_31]: (k2_xboole_0(k2_xboole_0(A_30, C_32), k2_xboole_0(B_31, C_32))=k2_xboole_0(k2_xboole_0(A_30, B_31), C_32))), inference(cnfTransformation, [status(thm)], [f_75])).
% 51.14/41.17  tff(c_2229, plain, (![A_124, C_125, B_126]: (k2_xboole_0(k2_xboole_0(A_124, C_125), k2_xboole_0(B_126, C_125))=k2_xboole_0(A_124, k2_xboole_0(B_126, C_125)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 51.14/41.17  tff(c_2379, plain, (![B_126, A_68]: (k2_xboole_0(k1_xboole_0, k2_xboole_0(B_126, A_68))=k2_xboole_0(A_68, k2_xboole_0(B_126, A_68)))), inference(superposition, [status(thm), theory('equality')], [c_439, c_2229])).
% 51.14/41.17  tff(c_2441, plain, (![B_126, A_68]: (k2_xboole_0(B_126, A_68)=k2_xboole_0(A_68, B_126))), inference(demodulation, [status(thm), theory('equality')], [c_1682, c_439, c_2379])).
% 51.14/41.17  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | k4_xboole_0(A_11, B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 51.14/41.17  tff(c_44, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 51.14/41.17  tff(c_2455, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2441, c_44])).
% 51.14/41.17  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 51.14/41.17  tff(c_20, plain, (![A_16, B_17, C_18]: (r1_tarski(k4_xboole_0(A_16, B_17), C_18) | ~r1_tarski(A_16, k2_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 51.14/41.17  tff(c_40, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 51.14/41.17  tff(c_2034, plain, (![A_115, B_116, C_117]: (k1_xboole_0=A_115 | ~r1_xboole_0(B_116, C_117) | ~r1_tarski(A_115, C_117) | ~r1_tarski(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_83])).
% 51.14/41.17  tff(c_2047, plain, (![A_118]: (k1_xboole_0=A_118 | ~r1_tarski(A_118, '#skF_4') | ~r1_tarski(A_118, '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_2034])).
% 51.14/41.17  tff(c_39028, plain, (![A_365, B_366]: (k4_xboole_0(A_365, B_366)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(A_365, B_366), '#skF_4') | ~r1_tarski(A_365, k2_xboole_0(B_366, '#skF_6')))), inference(resolution, [status(thm)], [c_20, c_2047])).
% 51.14/41.17  tff(c_44383, plain, (![B_384]: (k4_xboole_0('#skF_4', B_384)=k1_xboole_0 | ~r1_tarski('#skF_4', k2_xboole_0(B_384, '#skF_6')))), inference(resolution, [status(thm)], [c_10, c_39028])).
% 51.14/41.17  tff(c_44436, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | ~r1_tarski('#skF_4', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2455, c_44383])).
% 51.14/41.17  tff(c_45366, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_44436])).
% 51.14/41.17  tff(c_45369, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_4', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_45366])).
% 51.14/41.17  tff(c_45373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_45369])).
% 51.14/41.17  tff(c_45374, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_44436])).
% 51.14/41.17  tff(c_16, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 51.14/41.17  tff(c_45471, plain, (k2_xboole_0('#skF_5', k1_xboole_0)=k2_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_45374, c_16])).
% 51.14/41.17  tff(c_45519, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2441, c_45471])).
% 51.14/41.17  tff(c_1780, plain, (![A_28, B_29, C_111]: (k2_xboole_0(k3_xboole_0(A_28, B_29), k2_xboole_0(k4_xboole_0(A_28, B_29), C_111))=k2_xboole_0(A_28, C_111))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1664])).
% 51.14/41.17  tff(c_11013, plain, (![A_199, B_200, C_201]: (k2_xboole_0(k3_xboole_0(A_199, B_200), k2_xboole_0(k4_xboole_0(A_199, B_200), C_201))=k2_xboole_0(A_199, C_201))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1664])).
% 51.14/41.17  tff(c_36, plain, (![A_36, B_37]: (k2_xboole_0(A_36, k2_xboole_0(A_36, B_37))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_85])).
% 51.14/41.17  tff(c_11121, plain, (![A_199, B_200, C_201]: (k2_xboole_0(k3_xboole_0(A_199, B_200), k2_xboole_0(k4_xboole_0(A_199, B_200), C_201))=k2_xboole_0(k3_xboole_0(A_199, B_200), k2_xboole_0(A_199, C_201)))), inference(superposition, [status(thm), theory('equality')], [c_11013, c_36])).
% 51.14/41.17  tff(c_11356, plain, (![A_199, B_200, C_201]: (k2_xboole_0(k3_xboole_0(A_199, B_200), k2_xboole_0(A_199, C_201))=k2_xboole_0(A_199, C_201))), inference(demodulation, [status(thm), theory('equality')], [c_1780, c_11121])).
% 51.14/41.17  tff(c_24, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k3_xboole_0(A_21, B_22))=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 51.14/41.17  tff(c_1216, plain, (![A_92, B_93, C_94]: (r1_tarski(k4_xboole_0(A_92, B_93), C_94) | ~r1_tarski(A_92, k2_xboole_0(B_93, C_94)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 51.14/41.17  tff(c_15327, plain, (![A_239, B_240, C_241]: (r1_tarski(k4_xboole_0(A_239, B_240), C_241) | ~r1_tarski(A_239, k2_xboole_0(k3_xboole_0(A_239, B_240), C_241)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1216])).
% 51.14/41.17  tff(c_160177, plain, (![A_752, B_753, C_754]: (r1_tarski(k4_xboole_0(A_752, B_753), C_754) | k4_xboole_0(A_752, k2_xboole_0(k3_xboole_0(A_752, B_753), C_754))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_15327])).
% 51.14/41.17  tff(c_160307, plain, (![A_199, B_200, C_201]: (r1_tarski(k4_xboole_0(A_199, B_200), k2_xboole_0(A_199, C_201)) | k4_xboole_0(A_199, k2_xboole_0(A_199, C_201))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11356, c_160177])).
% 51.14/41.17  tff(c_160820, plain, (![A_757, B_758, C_759]: (r1_tarski(k4_xboole_0(A_757, B_758), k2_xboole_0(A_757, C_759)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_160307])).
% 51.14/41.17  tff(c_162051, plain, (![A_761, C_762]: (r1_tarski(A_761, k2_xboole_0(A_761, C_762)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_160820])).
% 51.14/41.17  tff(c_162497, plain, (r1_tarski('#skF_5', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2455, c_162051])).
% 51.14/41.17  tff(c_42, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 51.14/41.17  tff(c_2082, plain, (![A_119]: (k1_xboole_0=A_119 | ~r1_tarski(A_119, '#skF_3') | ~r1_tarski(A_119, '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_2034])).
% 51.14/41.17  tff(c_6784, plain, (![B_165]: (k4_xboole_0('#skF_5', B_165)=k1_xboole_0 | ~r1_tarski(k4_xboole_0('#skF_5', B_165), '#skF_3'))), inference(resolution, [status(thm)], [c_10, c_2082])).
% 51.14/41.17  tff(c_6836, plain, (![B_17]: (k4_xboole_0('#skF_5', B_17)=k1_xboole_0 | ~r1_tarski('#skF_5', k2_xboole_0(B_17, '#skF_3')))), inference(resolution, [status(thm)], [c_20, c_6784])).
% 51.14/41.17  tff(c_164353, plain, (k4_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_162497, c_6836])).
% 51.14/41.17  tff(c_570, plain, (![A_73, B_74]: (k2_xboole_0(A_73, k2_xboole_0(A_73, B_74))=k2_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_85])).
% 51.14/41.17  tff(c_605, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=k2_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_8, c_570])).
% 51.14/41.17  tff(c_616, plain, (![A_8]: (k2_xboole_0(A_8, A_8)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_605])).
% 51.14/41.17  tff(c_2362, plain, (![A_124, A_8]: (k2_xboole_0(k2_xboole_0(A_124, A_8), A_8)=k2_xboole_0(A_124, k2_xboole_0(A_8, A_8)))), inference(superposition, [status(thm), theory('equality')], [c_616, c_2229])).
% 51.14/41.17  tff(c_3599, plain, (![A_137, A_138]: (k2_xboole_0(k2_xboole_0(A_137, A_138), A_138)=k2_xboole_0(A_137, A_138))), inference(demodulation, [status(thm), theory('equality')], [c_616, c_2362])).
% 51.14/41.17  tff(c_3686, plain, (![B_126, A_137]: (k2_xboole_0(B_126, k2_xboole_0(A_137, B_126))=k2_xboole_0(A_137, B_126))), inference(superposition, [status(thm), theory('equality')], [c_2441, c_3599])).
% 51.14/41.17  tff(c_1750, plain, (![A_13, B_14, C_111]: (k2_xboole_0(A_13, k2_xboole_0(k4_xboole_0(B_14, A_13), C_111))=k2_xboole_0(k2_xboole_0(A_13, B_14), C_111))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1664])).
% 51.14/41.17  tff(c_8903, plain, (![A_184, B_185, C_186]: (k2_xboole_0(A_184, k2_xboole_0(k4_xboole_0(B_185, A_184), C_186))=k2_xboole_0(A_184, k2_xboole_0(B_185, C_186)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1750])).
% 51.14/41.17  tff(c_9132, plain, (![B_185, B_126]: (k2_xboole_0(k4_xboole_0(B_185, B_126), B_126)=k2_xboole_0(B_126, k2_xboole_0(B_185, B_126)))), inference(superposition, [status(thm), theory('equality')], [c_3686, c_8903])).
% 51.14/41.17  tff(c_9279, plain, (![B_185, B_126]: (k2_xboole_0(k4_xboole_0(B_185, B_126), B_126)=k2_xboole_0(B_126, B_185))), inference(demodulation, [status(thm), theory('equality')], [c_1682, c_9132])).
% 51.14/41.17  tff(c_164514, plain, (k2_xboole_0(k1_xboole_0, '#skF_4')=k2_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_164353, c_9279])).
% 51.14/41.17  tff(c_164609, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_439, c_45519, c_164514])).
% 51.14/41.17  tff(c_164611, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_164609])).
% 51.14/41.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.14/41.17  
% 51.14/41.17  Inference rules
% 51.14/41.17  ----------------------
% 51.14/41.17  #Ref     : 0
% 51.14/41.17  #Sup     : 40694
% 51.14/41.17  #Fact    : 0
% 51.14/41.17  #Define  : 0
% 51.14/41.17  #Split   : 25
% 51.14/41.17  #Chain   : 0
% 51.14/41.17  #Close   : 0
% 51.14/41.17  
% 51.14/41.17  Ordering : KBO
% 51.14/41.17  
% 51.14/41.17  Simplification rules
% 51.14/41.17  ----------------------
% 51.14/41.17  #Subsume      : 3714
% 51.14/41.17  #Demod        : 55808
% 51.14/41.17  #Tautology    : 22962
% 51.14/41.17  #SimpNegUnit  : 145
% 51.14/41.17  #BackRed      : 189
% 51.14/41.17  
% 51.14/41.17  #Partial instantiations: 0
% 51.14/41.17  #Strategies tried      : 1
% 51.14/41.17  
% 51.14/41.17  Timing (in seconds)
% 51.14/41.17  ----------------------
% 51.14/41.17  Preprocessing        : 0.31
% 51.14/41.17  Parsing              : 0.17
% 51.14/41.17  CNF conversion       : 0.02
% 51.14/41.17  Main loop            : 40.07
% 51.14/41.17  Inferencing          : 2.66
% 51.14/41.17  Reduction            : 30.47
% 51.14/41.17  Demodulation         : 28.75
% 51.14/41.17  BG Simplification    : 0.36
% 51.14/41.17  Subsumption          : 5.30
% 51.14/41.17  Abstraction          : 0.65
% 51.14/41.17  MUC search           : 0.00
% 51.14/41.17  Cooper               : 0.00
% 51.14/41.17  Total                : 40.42
% 51.14/41.17  Index Insertion      : 0.00
% 51.14/41.17  Index Deletion       : 0.00
% 51.14/41.17  Index Matching       : 0.00
% 51.14/41.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
