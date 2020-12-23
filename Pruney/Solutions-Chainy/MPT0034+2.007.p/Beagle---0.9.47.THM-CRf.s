%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:39 EST 2020

% Result     : Theorem 41.67s
% Output     : CNFRefutation 41.83s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 143 expanded)
%              Number of leaves         :   19 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  123 ( 332 expanded)
%              Number of equality atoms :   13 (  33 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k3_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_19,B_20] : r1_tarski(A_19,k2_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_188,plain,(
    ! [A_61,B_62,C_63] :
      ( r1_tarski(A_61,k3_xboole_0(B_62,C_63))
      | ~ r1_tarski(A_61,C_63)
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,C_11)
      | ~ r1_tarski(B_10,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1196,plain,(
    ! [A_161,B_162,C_163,A_164] :
      ( r1_tarski(A_161,k3_xboole_0(B_162,C_163))
      | ~ r1_tarski(A_161,A_164)
      | ~ r1_tarski(A_164,C_163)
      | ~ r1_tarski(A_164,B_162) ) ),
    inference(resolution,[status(thm)],[c_188,c_8])).

tff(c_8455,plain,(
    ! [A_477,B_478,C_479,B_480] :
      ( r1_tarski(A_477,k3_xboole_0(B_478,C_479))
      | ~ r1_tarski(k2_xboole_0(A_477,B_480),C_479)
      | ~ r1_tarski(k2_xboole_0(A_477,B_480),B_478) ) ),
    inference(resolution,[status(thm)],[c_18,c_1196])).

tff(c_83183,plain,(
    ! [A_1426,B_1427,B_1428,B_1429] :
      ( r1_tarski(A_1426,k3_xboole_0(B_1427,k2_xboole_0(k2_xboole_0(A_1426,B_1428),B_1429)))
      | ~ r1_tarski(k2_xboole_0(A_1426,B_1428),B_1427) ) ),
    inference(resolution,[status(thm)],[c_18,c_8455])).

tff(c_28,plain,(
    ! [A_28,C_29,B_30] :
      ( r1_tarski(A_28,C_29)
      | ~ r1_tarski(B_30,C_29)
      | ~ r1_tarski(A_28,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_40,plain,(
    ! [A_28,A_4,B_5] :
      ( r1_tarski(A_28,A_4)
      | ~ r1_tarski(A_28,k3_xboole_0(A_4,B_5)) ) ),
    inference(resolution,[status(thm)],[c_4,c_28])).

tff(c_84491,plain,(
    ! [A_1453,B_1454,B_1455] :
      ( r1_tarski(A_1453,B_1454)
      | ~ r1_tarski(k2_xboole_0(A_1453,B_1455),B_1454) ) ),
    inference(resolution,[status(thm)],[c_83183,c_40])).

tff(c_84638,plain,(
    ! [A_1453,B_1455,B_20] : r1_tarski(A_1453,k2_xboole_0(k2_xboole_0(A_1453,B_1455),B_20)) ),
    inference(resolution,[status(thm)],[c_18,c_84491])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14] :
      ( r1_tarski('#skF_1'(A_12,B_13,C_14),C_14)
      | k3_xboole_0(B_13,C_14) = A_12
      | ~ r1_tarski(A_12,C_14)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_tarski(A_6,k3_xboole_0(B_7,C_8))
      | ~ r1_tarski(A_6,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_290,plain,(
    ! [A_75,B_76,C_77] :
      ( ~ r1_tarski('#skF_1'(A_75,B_76,C_77),A_75)
      | k3_xboole_0(B_76,C_77) = A_75
      | ~ r1_tarski(A_75,C_77)
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2259,plain,(
    ! [B_235,C_236,B_233,C_234] :
      ( k3_xboole_0(B_235,C_236) = k3_xboole_0(B_233,C_234)
      | ~ r1_tarski(k3_xboole_0(B_235,C_236),C_234)
      | ~ r1_tarski(k3_xboole_0(B_235,C_236),B_233)
      | ~ r1_tarski('#skF_1'(k3_xboole_0(B_235,C_236),B_233,C_234),C_236)
      | ~ r1_tarski('#skF_1'(k3_xboole_0(B_235,C_236),B_233,C_234),B_235) ) ),
    inference(resolution,[status(thm)],[c_6,c_290])).

tff(c_33680,plain,(
    ! [B_1070,C_1071,B_1072] :
      ( ~ r1_tarski('#skF_1'(k3_xboole_0(B_1070,C_1071),B_1072,C_1071),B_1070)
      | k3_xboole_0(B_1072,C_1071) = k3_xboole_0(B_1070,C_1071)
      | ~ r1_tarski(k3_xboole_0(B_1070,C_1071),C_1071)
      | ~ r1_tarski(k3_xboole_0(B_1070,C_1071),B_1072) ) ),
    inference(resolution,[status(thm)],[c_12,c_2259])).

tff(c_33795,plain,(
    ! [C_14,B_13] :
      ( k3_xboole_0(C_14,C_14) = k3_xboole_0(B_13,C_14)
      | ~ r1_tarski(k3_xboole_0(C_14,C_14),C_14)
      | ~ r1_tarski(k3_xboole_0(C_14,C_14),B_13) ) ),
    inference(resolution,[status(thm)],[c_12,c_33680])).

tff(c_55847,plain,(
    ! [C_1244,B_1245] :
      ( k3_xboole_0(C_1244,C_1244) = k3_xboole_0(B_1245,C_1244)
      | ~ r1_tarski(k3_xboole_0(C_1244,C_1244),B_1245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_33795])).

tff(c_56452,plain,(
    ! [C_1244,B_20] : k3_xboole_0(k2_xboole_0(k3_xboole_0(C_1244,C_1244),B_20),C_1244) = k3_xboole_0(C_1244,C_1244) ),
    inference(resolution,[status(thm)],[c_18,c_55847])).

tff(c_22,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_16,C_18,B_17] :
      ( r1_tarski(k3_xboole_0(A_16,C_18),k3_xboole_0(B_17,C_18))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_98,plain,(
    ! [A_47,C_48,B_49] :
      ( r1_tarski(k3_xboole_0(A_47,C_48),k3_xboole_0(B_49,C_48))
      | ~ r1_tarski(A_47,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_954,plain,(
    ! [A_131,B_132,C_133,A_134] :
      ( r1_tarski(A_131,k3_xboole_0(B_132,C_133))
      | ~ r1_tarski(A_131,k3_xboole_0(A_134,C_133))
      | ~ r1_tarski(A_134,B_132) ) ),
    inference(resolution,[status(thm)],[c_98,c_8])).

tff(c_4851,plain,(
    ! [A_384,C_385,B_386,B_387] :
      ( r1_tarski(k3_xboole_0(A_384,C_385),k3_xboole_0(B_386,C_385))
      | ~ r1_tarski(B_387,B_386)
      | ~ r1_tarski(A_384,B_387) ) ),
    inference(resolution,[status(thm)],[c_16,c_954])).

tff(c_111813,plain,(
    ! [B_1712,A_1715,C_1711,A_1714,C_1713] :
      ( r1_tarski(k3_xboole_0(A_1715,C_1711),k3_xboole_0(k2_xboole_0(C_1713,B_1712),C_1711))
      | ~ r1_tarski(A_1715,A_1714)
      | ~ r1_tarski(A_1714,B_1712) ) ),
    inference(resolution,[status(thm)],[c_2,c_4851])).

tff(c_113632,plain,(
    ! [C_1721,C_1722,B_1723] :
      ( r1_tarski(k3_xboole_0('#skF_4',C_1721),k3_xboole_0(k2_xboole_0(C_1722,B_1723),C_1721))
      | ~ r1_tarski('#skF_5',B_1723) ) ),
    inference(resolution,[status(thm)],[c_22,c_111813])).

tff(c_113773,plain,(
    ! [C_1244,B_20] :
      ( r1_tarski(k3_xboole_0('#skF_4',C_1244),k3_xboole_0(C_1244,C_1244))
      | ~ r1_tarski('#skF_5',B_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56452,c_113632])).

tff(c_113932,plain,(
    ! [B_1724] : ~ r1_tarski('#skF_5',B_1724) ),
    inference(splitLeft,[status(thm)],[c_113773])).

tff(c_114039,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_84638,c_113932])).

tff(c_114041,plain,(
    ! [C_1725] : r1_tarski(k3_xboole_0('#skF_4',C_1725),k3_xboole_0(C_1725,C_1725)) ),
    inference(splitRight,[status(thm)],[c_113773])).

tff(c_114553,plain,(
    ! [C_1726] : r1_tarski(k3_xboole_0('#skF_4',C_1726),C_1726) ),
    inference(resolution,[status(thm)],[c_114041,c_40])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] :
      ( r1_tarski('#skF_1'(A_12,B_13,C_14),B_13)
      | k3_xboole_0(B_13,C_14) = A_12
      | ~ r1_tarski(A_12,C_14)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_23417,plain,(
    ! [B_1027,B_1028,C_1029] :
      ( ~ r1_tarski('#skF_1'(k3_xboole_0(B_1027,B_1028),B_1028,C_1029),B_1027)
      | k3_xboole_0(B_1028,C_1029) = k3_xboole_0(B_1027,B_1028)
      | ~ r1_tarski(k3_xboole_0(B_1027,B_1028),C_1029)
      | ~ r1_tarski(k3_xboole_0(B_1027,B_1028),B_1028) ) ),
    inference(resolution,[status(thm)],[c_14,c_2259])).

tff(c_23510,plain,(
    ! [C_14,B_13] :
      ( k3_xboole_0(C_14,B_13) = k3_xboole_0(B_13,C_14)
      | ~ r1_tarski(k3_xboole_0(C_14,B_13),C_14)
      | ~ r1_tarski(k3_xboole_0(C_14,B_13),B_13) ) ),
    inference(resolution,[status(thm)],[c_12,c_23417])).

tff(c_23553,plain,(
    ! [C_14,B_13] :
      ( k3_xboole_0(C_14,B_13) = k3_xboole_0(B_13,C_14)
      | ~ r1_tarski(k3_xboole_0(C_14,B_13),B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_23510])).

tff(c_114947,plain,(
    ! [C_1726] : k3_xboole_0(C_1726,'#skF_4') = k3_xboole_0('#skF_4',C_1726) ),
    inference(resolution,[status(thm)],[c_114553,c_23553])).

tff(c_42,plain,(
    ! [A_28] :
      ( r1_tarski(A_28,'#skF_5')
      | ~ r1_tarski(A_28,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_28])).

tff(c_24,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_48,plain,(
    ! [A_32] :
      ( r1_tarski(A_32,'#skF_3')
      | ~ r1_tarski(A_32,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_28])).

tff(c_53,plain,(
    ! [B_5] : r1_tarski(k3_xboole_0('#skF_2',B_5),'#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_48])).

tff(c_20,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_4'),k3_xboole_0('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_205,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_4'),'#skF_5')
    | ~ r1_tarski(k3_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_188,c_20])).

tff(c_215,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_205])).

tff(c_231,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_215])).

tff(c_115794,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114947,c_231])).

tff(c_115799,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_115794])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:44:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 41.67/31.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 41.67/31.19  
% 41.67/31.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 41.67/31.19  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 41.67/31.19  
% 41.67/31.19  %Foreground sorts:
% 41.67/31.19  
% 41.67/31.19  
% 41.67/31.19  %Background operators:
% 41.67/31.19  
% 41.67/31.19  
% 41.67/31.19  %Foreground operators:
% 41.67/31.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 41.67/31.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 41.67/31.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 41.67/31.19  tff('#skF_5', type, '#skF_5': $i).
% 41.67/31.19  tff('#skF_2', type, '#skF_2': $i).
% 41.67/31.19  tff('#skF_3', type, '#skF_3': $i).
% 41.67/31.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 41.67/31.19  tff('#skF_4', type, '#skF_4': $i).
% 41.67/31.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 41.67/31.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 41.67/31.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 41.67/31.19  
% 41.83/31.21  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 41.83/31.21  tff(f_62, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 41.83/31.21  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 41.83/31.21  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 41.83/31.21  tff(f_56, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 41.83/31.21  tff(f_69, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_xboole_1)).
% 41.83/31.21  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 41.83/31.21  tff(f_60, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_xboole_1)).
% 41.83/31.21  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k3_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 41.83/31.21  tff(c_18, plain, (![A_19, B_20]: (r1_tarski(A_19, k2_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 41.83/31.21  tff(c_188, plain, (![A_61, B_62, C_63]: (r1_tarski(A_61, k3_xboole_0(B_62, C_63)) | ~r1_tarski(A_61, C_63) | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_37])).
% 41.83/31.21  tff(c_8, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, C_11) | ~r1_tarski(B_10, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 41.83/31.21  tff(c_1196, plain, (![A_161, B_162, C_163, A_164]: (r1_tarski(A_161, k3_xboole_0(B_162, C_163)) | ~r1_tarski(A_161, A_164) | ~r1_tarski(A_164, C_163) | ~r1_tarski(A_164, B_162))), inference(resolution, [status(thm)], [c_188, c_8])).
% 41.83/31.21  tff(c_8455, plain, (![A_477, B_478, C_479, B_480]: (r1_tarski(A_477, k3_xboole_0(B_478, C_479)) | ~r1_tarski(k2_xboole_0(A_477, B_480), C_479) | ~r1_tarski(k2_xboole_0(A_477, B_480), B_478))), inference(resolution, [status(thm)], [c_18, c_1196])).
% 41.83/31.21  tff(c_83183, plain, (![A_1426, B_1427, B_1428, B_1429]: (r1_tarski(A_1426, k3_xboole_0(B_1427, k2_xboole_0(k2_xboole_0(A_1426, B_1428), B_1429))) | ~r1_tarski(k2_xboole_0(A_1426, B_1428), B_1427))), inference(resolution, [status(thm)], [c_18, c_8455])).
% 41.83/31.21  tff(c_28, plain, (![A_28, C_29, B_30]: (r1_tarski(A_28, C_29) | ~r1_tarski(B_30, C_29) | ~r1_tarski(A_28, B_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 41.83/31.21  tff(c_40, plain, (![A_28, A_4, B_5]: (r1_tarski(A_28, A_4) | ~r1_tarski(A_28, k3_xboole_0(A_4, B_5)))), inference(resolution, [status(thm)], [c_4, c_28])).
% 41.83/31.21  tff(c_84491, plain, (![A_1453, B_1454, B_1455]: (r1_tarski(A_1453, B_1454) | ~r1_tarski(k2_xboole_0(A_1453, B_1455), B_1454))), inference(resolution, [status(thm)], [c_83183, c_40])).
% 41.83/31.21  tff(c_84638, plain, (![A_1453, B_1455, B_20]: (r1_tarski(A_1453, k2_xboole_0(k2_xboole_0(A_1453, B_1455), B_20)))), inference(resolution, [status(thm)], [c_18, c_84491])).
% 41.83/31.21  tff(c_12, plain, (![A_12, B_13, C_14]: (r1_tarski('#skF_1'(A_12, B_13, C_14), C_14) | k3_xboole_0(B_13, C_14)=A_12 | ~r1_tarski(A_12, C_14) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 41.83/31.21  tff(c_6, plain, (![A_6, B_7, C_8]: (r1_tarski(A_6, k3_xboole_0(B_7, C_8)) | ~r1_tarski(A_6, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 41.83/31.21  tff(c_290, plain, (![A_75, B_76, C_77]: (~r1_tarski('#skF_1'(A_75, B_76, C_77), A_75) | k3_xboole_0(B_76, C_77)=A_75 | ~r1_tarski(A_75, C_77) | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_56])).
% 41.83/31.21  tff(c_2259, plain, (![B_235, C_236, B_233, C_234]: (k3_xboole_0(B_235, C_236)=k3_xboole_0(B_233, C_234) | ~r1_tarski(k3_xboole_0(B_235, C_236), C_234) | ~r1_tarski(k3_xboole_0(B_235, C_236), B_233) | ~r1_tarski('#skF_1'(k3_xboole_0(B_235, C_236), B_233, C_234), C_236) | ~r1_tarski('#skF_1'(k3_xboole_0(B_235, C_236), B_233, C_234), B_235))), inference(resolution, [status(thm)], [c_6, c_290])).
% 41.83/31.21  tff(c_33680, plain, (![B_1070, C_1071, B_1072]: (~r1_tarski('#skF_1'(k3_xboole_0(B_1070, C_1071), B_1072, C_1071), B_1070) | k3_xboole_0(B_1072, C_1071)=k3_xboole_0(B_1070, C_1071) | ~r1_tarski(k3_xboole_0(B_1070, C_1071), C_1071) | ~r1_tarski(k3_xboole_0(B_1070, C_1071), B_1072))), inference(resolution, [status(thm)], [c_12, c_2259])).
% 41.83/31.21  tff(c_33795, plain, (![C_14, B_13]: (k3_xboole_0(C_14, C_14)=k3_xboole_0(B_13, C_14) | ~r1_tarski(k3_xboole_0(C_14, C_14), C_14) | ~r1_tarski(k3_xboole_0(C_14, C_14), B_13))), inference(resolution, [status(thm)], [c_12, c_33680])).
% 41.83/31.21  tff(c_55847, plain, (![C_1244, B_1245]: (k3_xboole_0(C_1244, C_1244)=k3_xboole_0(B_1245, C_1244) | ~r1_tarski(k3_xboole_0(C_1244, C_1244), B_1245))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_33795])).
% 41.83/31.21  tff(c_56452, plain, (![C_1244, B_20]: (k3_xboole_0(k2_xboole_0(k3_xboole_0(C_1244, C_1244), B_20), C_1244)=k3_xboole_0(C_1244, C_1244))), inference(resolution, [status(thm)], [c_18, c_55847])).
% 41.83/31.21  tff(c_22, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 41.83/31.21  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 41.83/31.21  tff(c_16, plain, (![A_16, C_18, B_17]: (r1_tarski(k3_xboole_0(A_16, C_18), k3_xboole_0(B_17, C_18)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 41.83/31.21  tff(c_98, plain, (![A_47, C_48, B_49]: (r1_tarski(k3_xboole_0(A_47, C_48), k3_xboole_0(B_49, C_48)) | ~r1_tarski(A_47, B_49))), inference(cnfTransformation, [status(thm)], [f_60])).
% 41.83/31.21  tff(c_954, plain, (![A_131, B_132, C_133, A_134]: (r1_tarski(A_131, k3_xboole_0(B_132, C_133)) | ~r1_tarski(A_131, k3_xboole_0(A_134, C_133)) | ~r1_tarski(A_134, B_132))), inference(resolution, [status(thm)], [c_98, c_8])).
% 41.83/31.21  tff(c_4851, plain, (![A_384, C_385, B_386, B_387]: (r1_tarski(k3_xboole_0(A_384, C_385), k3_xboole_0(B_386, C_385)) | ~r1_tarski(B_387, B_386) | ~r1_tarski(A_384, B_387))), inference(resolution, [status(thm)], [c_16, c_954])).
% 41.83/31.21  tff(c_111813, plain, (![B_1712, A_1715, C_1711, A_1714, C_1713]: (r1_tarski(k3_xboole_0(A_1715, C_1711), k3_xboole_0(k2_xboole_0(C_1713, B_1712), C_1711)) | ~r1_tarski(A_1715, A_1714) | ~r1_tarski(A_1714, B_1712))), inference(resolution, [status(thm)], [c_2, c_4851])).
% 41.83/31.21  tff(c_113632, plain, (![C_1721, C_1722, B_1723]: (r1_tarski(k3_xboole_0('#skF_4', C_1721), k3_xboole_0(k2_xboole_0(C_1722, B_1723), C_1721)) | ~r1_tarski('#skF_5', B_1723))), inference(resolution, [status(thm)], [c_22, c_111813])).
% 41.83/31.21  tff(c_113773, plain, (![C_1244, B_20]: (r1_tarski(k3_xboole_0('#skF_4', C_1244), k3_xboole_0(C_1244, C_1244)) | ~r1_tarski('#skF_5', B_20))), inference(superposition, [status(thm), theory('equality')], [c_56452, c_113632])).
% 41.83/31.21  tff(c_113932, plain, (![B_1724]: (~r1_tarski('#skF_5', B_1724))), inference(splitLeft, [status(thm)], [c_113773])).
% 41.83/31.21  tff(c_114039, plain, $false, inference(resolution, [status(thm)], [c_84638, c_113932])).
% 41.83/31.21  tff(c_114041, plain, (![C_1725]: (r1_tarski(k3_xboole_0('#skF_4', C_1725), k3_xboole_0(C_1725, C_1725)))), inference(splitRight, [status(thm)], [c_113773])).
% 41.83/31.21  tff(c_114553, plain, (![C_1726]: (r1_tarski(k3_xboole_0('#skF_4', C_1726), C_1726))), inference(resolution, [status(thm)], [c_114041, c_40])).
% 41.83/31.21  tff(c_14, plain, (![A_12, B_13, C_14]: (r1_tarski('#skF_1'(A_12, B_13, C_14), B_13) | k3_xboole_0(B_13, C_14)=A_12 | ~r1_tarski(A_12, C_14) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 41.83/31.21  tff(c_23417, plain, (![B_1027, B_1028, C_1029]: (~r1_tarski('#skF_1'(k3_xboole_0(B_1027, B_1028), B_1028, C_1029), B_1027) | k3_xboole_0(B_1028, C_1029)=k3_xboole_0(B_1027, B_1028) | ~r1_tarski(k3_xboole_0(B_1027, B_1028), C_1029) | ~r1_tarski(k3_xboole_0(B_1027, B_1028), B_1028))), inference(resolution, [status(thm)], [c_14, c_2259])).
% 41.83/31.21  tff(c_23510, plain, (![C_14, B_13]: (k3_xboole_0(C_14, B_13)=k3_xboole_0(B_13, C_14) | ~r1_tarski(k3_xboole_0(C_14, B_13), C_14) | ~r1_tarski(k3_xboole_0(C_14, B_13), B_13))), inference(resolution, [status(thm)], [c_12, c_23417])).
% 41.83/31.21  tff(c_23553, plain, (![C_14, B_13]: (k3_xboole_0(C_14, B_13)=k3_xboole_0(B_13, C_14) | ~r1_tarski(k3_xboole_0(C_14, B_13), B_13))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_23510])).
% 41.83/31.21  tff(c_114947, plain, (![C_1726]: (k3_xboole_0(C_1726, '#skF_4')=k3_xboole_0('#skF_4', C_1726))), inference(resolution, [status(thm)], [c_114553, c_23553])).
% 41.83/31.21  tff(c_42, plain, (![A_28]: (r1_tarski(A_28, '#skF_5') | ~r1_tarski(A_28, '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_28])).
% 41.83/31.21  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 41.83/31.21  tff(c_48, plain, (![A_32]: (r1_tarski(A_32, '#skF_3') | ~r1_tarski(A_32, '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_28])).
% 41.83/31.21  tff(c_53, plain, (![B_5]: (r1_tarski(k3_xboole_0('#skF_2', B_5), '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_48])).
% 41.83/31.21  tff(c_20, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_4'), k3_xboole_0('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 41.83/31.21  tff(c_205, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_4'), '#skF_5') | ~r1_tarski(k3_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_188, c_20])).
% 41.83/31.21  tff(c_215, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_205])).
% 41.83/31.21  tff(c_231, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_42, c_215])).
% 41.83/31.21  tff(c_115794, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_114947, c_231])).
% 41.83/31.21  tff(c_115799, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_115794])).
% 41.83/31.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 41.83/31.21  
% 41.83/31.21  Inference rules
% 41.83/31.21  ----------------------
% 41.83/31.21  #Ref     : 0
% 41.83/31.21  #Sup     : 32588
% 41.83/31.21  #Fact    : 0
% 41.83/31.21  #Define  : 0
% 41.83/31.21  #Split   : 38
% 41.83/31.21  #Chain   : 0
% 41.83/31.21  #Close   : 0
% 41.83/31.21  
% 41.83/31.21  Ordering : KBO
% 41.83/31.21  
% 41.83/31.21  Simplification rules
% 41.83/31.21  ----------------------
% 41.83/31.21  #Subsume      : 12974
% 41.83/31.21  #Demod        : 9128
% 41.83/31.21  #Tautology    : 2941
% 41.83/31.21  #SimpNegUnit  : 274
% 41.83/31.21  #BackRed      : 20
% 41.83/31.21  
% 41.83/31.21  #Partial instantiations: 0
% 41.83/31.21  #Strategies tried      : 1
% 41.83/31.21  
% 41.83/31.21  Timing (in seconds)
% 41.83/31.21  ----------------------
% 41.83/31.21  Preprocessing        : 0.28
% 41.83/31.21  Parsing              : 0.16
% 41.83/31.21  CNF conversion       : 0.02
% 41.83/31.21  Main loop            : 30.16
% 41.83/31.21  Inferencing          : 2.37
% 41.83/31.21  Reduction            : 11.26
% 41.83/31.21  Demodulation         : 8.88
% 41.83/31.21  BG Simplification    : 0.33
% 41.83/31.21  Subsumption          : 14.86
% 41.83/31.21  Abstraction          : 0.50
% 41.83/31.21  MUC search           : 0.00
% 41.83/31.21  Cooper               : 0.00
% 41.83/31.21  Total                : 30.48
% 41.83/31.21  Index Insertion      : 0.00
% 41.83/31.21  Index Deletion       : 0.00
% 41.83/31.21  Index Matching       : 0.00
% 41.83/31.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
