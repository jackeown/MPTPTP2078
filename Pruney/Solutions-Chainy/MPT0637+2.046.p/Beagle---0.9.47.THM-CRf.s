%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:30 EST 2020

% Result     : Theorem 6.72s
% Output     : CNFRefutation 6.72s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 781 expanded)
%              Number of leaves         :   33 ( 286 expanded)
%              Depth                    :   23
%              Number of atoms          :  176 (1387 expanded)
%              Number of equality atoms :   57 ( 454 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_51,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_22,plain,(
    ! [A_18] : v1_relat_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [A_28] : k1_relat_1(k6_relat_1(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_352,plain,(
    ! [B_78,A_79] :
      ( k7_relat_1(B_78,k3_xboole_0(k1_relat_1(B_78),A_79)) = k7_relat_1(B_78,A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_248,plain,(
    ! [A_67,B_68] :
      ( k5_relat_1(k6_relat_1(A_67),B_68) = k7_relat_1(B_68,A_67)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    ! [B_30,A_29] :
      ( r1_tarski(k5_relat_1(B_30,k6_relat_1(A_29)),B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_255,plain,(
    ! [A_29,A_67] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_29),A_67),k6_relat_1(A_67))
      | ~ v1_relat_1(k6_relat_1(A_67))
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_34])).

tff(c_292,plain,(
    ! [A_29,A_67] : r1_tarski(k7_relat_1(k6_relat_1(A_29),A_67),k6_relat_1(A_67)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_255])).

tff(c_362,plain,(
    ! [A_29,A_79] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_29),A_79),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_29)),A_79)))
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_292])).

tff(c_378,plain,(
    ! [A_29,A_79] : r1_tarski(k7_relat_1(k6_relat_1(A_29),A_79),k6_relat_1(k3_xboole_0(A_29,A_79))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_28,c_362])).

tff(c_375,plain,(
    ! [A_28,A_79] :
      ( k7_relat_1(k6_relat_1(A_28),k3_xboole_0(A_28,A_79)) = k7_relat_1(k6_relat_1(A_28),A_79)
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_352])).

tff(c_382,plain,(
    ! [A_28,A_79] : k7_relat_1(k6_relat_1(A_28),k3_xboole_0(A_28,A_79)) = k7_relat_1(k6_relat_1(A_28),A_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_375])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_33] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_33)),A_33) = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_259,plain,(
    ! [B_68] :
      ( k7_relat_1(B_68,k1_relat_1(B_68)) = B_68
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(B_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_38])).

tff(c_32,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_29),B_30),B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_343,plain,(
    ! [B_76,A_77] :
      ( r1_tarski(k7_relat_1(B_76,A_77),B_76)
      | ~ v1_relat_1(B_76)
      | ~ v1_relat_1(B_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_32])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_819,plain,(
    ! [B_109,A_110] :
      ( k7_relat_1(B_109,A_110) = B_109
      | ~ r1_tarski(B_109,k7_relat_1(B_109,A_110))
      | ~ v1_relat_1(B_109) ) ),
    inference(resolution,[status(thm)],[c_343,c_2])).

tff(c_828,plain,(
    ! [B_68] :
      ( k7_relat_1(B_68,k1_relat_1(B_68)) = B_68
      | ~ r1_tarski(B_68,B_68)
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(B_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_819])).

tff(c_840,plain,(
    ! [B_68] :
      ( k7_relat_1(B_68,k1_relat_1(B_68)) = B_68
      | ~ v1_relat_1(B_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_828])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [A_28] : k2_relat_1(k6_relat_1(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_324,plain,(
    ! [A_72,B_73] :
      ( k5_relat_1(k6_relat_1(A_72),B_73) = B_73
      | ~ r1_tarski(k1_relat_1(B_73),A_72)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_327,plain,(
    ! [A_72,A_28] :
      ( k5_relat_1(k6_relat_1(A_72),k6_relat_1(A_28)) = k6_relat_1(A_28)
      | ~ r1_tarski(A_28,A_72)
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_324])).

tff(c_499,plain,(
    ! [A_89,A_90] :
      ( k5_relat_1(k6_relat_1(A_89),k6_relat_1(A_90)) = k6_relat_1(A_90)
      | ~ r1_tarski(A_90,A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_327])).

tff(c_42,plain,(
    ! [A_35,B_36] :
      ( k5_relat_1(k6_relat_1(A_35),B_36) = k7_relat_1(B_36,A_35)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_508,plain,(
    ! [A_90,A_89] :
      ( k7_relat_1(k6_relat_1(A_90),A_89) = k6_relat_1(A_90)
      | ~ v1_relat_1(k6_relat_1(A_90))
      | ~ r1_tarski(A_90,A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_42])).

tff(c_586,plain,(
    ! [A_93,A_94] :
      ( k7_relat_1(k6_relat_1(A_93),A_94) = k6_relat_1(A_93)
      | ~ r1_tarski(A_93,A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_508])).

tff(c_592,plain,(
    ! [A_93,A_94] :
      ( r1_tarski(k6_relat_1(A_93),k6_relat_1(k3_xboole_0(A_93,A_94)))
      | ~ r1_tarski(A_93,A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_586,c_378])).

tff(c_511,plain,(
    ! [A_90,A_89] :
      ( r1_tarski(k6_relat_1(A_90),k6_relat_1(A_89))
      | ~ v1_relat_1(k6_relat_1(A_89))
      | ~ r1_tarski(A_90,A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_34])).

tff(c_581,plain,(
    ! [A_91,A_92] :
      ( r1_tarski(k6_relat_1(A_91),k6_relat_1(A_92))
      | ~ r1_tarski(A_91,A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_511])).

tff(c_940,plain,(
    ! [A_117,A_116] :
      ( k6_relat_1(A_117) = k6_relat_1(A_116)
      | ~ r1_tarski(k6_relat_1(A_116),k6_relat_1(A_117))
      | ~ r1_tarski(A_117,A_116) ) ),
    inference(resolution,[status(thm)],[c_581,c_2])).

tff(c_943,plain,(
    ! [A_93,A_94] :
      ( k6_relat_1(k3_xboole_0(A_93,A_94)) = k6_relat_1(A_93)
      | ~ r1_tarski(k3_xboole_0(A_93,A_94),A_93)
      | ~ r1_tarski(A_93,A_94) ) ),
    inference(resolution,[status(thm)],[c_592,c_940])).

tff(c_1123,plain,(
    ! [A_120,A_121] :
      ( k6_relat_1(k3_xboole_0(A_120,A_121)) = k6_relat_1(A_120)
      | ~ r1_tarski(A_120,A_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_943])).

tff(c_1197,plain,(
    ! [A_120,A_121] :
      ( k3_xboole_0(A_120,A_121) = k2_relat_1(k6_relat_1(A_120))
      | ~ r1_tarski(A_120,A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1123,c_30])).

tff(c_1265,plain,(
    ! [A_124,A_125] :
      ( k3_xboole_0(A_124,A_125) = A_124
      | ~ r1_tarski(A_124,A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1197])).

tff(c_1305,plain,(
    ! [A_29,A_67] : k3_xboole_0(k7_relat_1(k6_relat_1(A_29),A_67),k6_relat_1(A_67)) = k7_relat_1(k6_relat_1(A_29),A_67) ),
    inference(resolution,[status(thm)],[c_292,c_1265])).

tff(c_2587,plain,(
    ! [B_163,A_164] :
      ( k3_xboole_0(k5_relat_1(B_163,k6_relat_1(A_164)),B_163) = k5_relat_1(B_163,k6_relat_1(A_164))
      | ~ v1_relat_1(B_163) ) ),
    inference(resolution,[status(thm)],[c_34,c_1265])).

tff(c_2657,plain,(
    ! [A_164,A_35] :
      ( k3_xboole_0(k7_relat_1(k6_relat_1(A_164),A_35),k6_relat_1(A_35)) = k5_relat_1(k6_relat_1(A_35),k6_relat_1(A_164))
      | ~ v1_relat_1(k6_relat_1(A_35))
      | ~ v1_relat_1(k6_relat_1(A_164)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2587])).

tff(c_2694,plain,(
    ! [A_35,A_164] : k5_relat_1(k6_relat_1(A_35),k6_relat_1(A_164)) = k7_relat_1(k6_relat_1(A_164),A_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_1305,c_2657])).

tff(c_40,plain,(
    ! [A_34] :
      ( k5_relat_1(A_34,k6_relat_1(k2_relat_1(A_34))) = A_34
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_289,plain,(
    ! [A_67] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_67))),A_67) = k6_relat_1(A_67)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_67))))
      | ~ v1_relat_1(k6_relat_1(A_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_248])).

tff(c_305,plain,(
    ! [A_67] : k7_relat_1(k6_relat_1(A_67),A_67) = k6_relat_1(A_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_30,c_289])).

tff(c_10,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_108,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k4_xboole_0(A_49,B_50)) = k3_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_117,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,k4_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_108])).

tff(c_654,plain,(
    ! [A_95,B_96] : k3_xboole_0(A_95,k4_xboole_0(A_95,B_96)) = k4_xboole_0(A_95,B_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_117])).

tff(c_676,plain,(
    ! [A_95,B_96] : r1_tarski(k4_xboole_0(A_95,B_96),A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_654,c_8])).

tff(c_1381,plain,(
    ! [A_128,B_129] : k3_xboole_0(k4_xboole_0(A_128,B_129),A_128) = k4_xboole_0(A_128,B_129) ),
    inference(resolution,[status(thm)],[c_676,c_1265])).

tff(c_1399,plain,(
    ! [A_128,B_129] : k7_relat_1(k6_relat_1(k4_xboole_0(A_128,B_129)),k4_xboole_0(A_128,B_129)) = k7_relat_1(k6_relat_1(k4_xboole_0(A_128,B_129)),A_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_1381,c_382])).

tff(c_1433,plain,(
    ! [A_128,B_129] : k7_relat_1(k6_relat_1(k4_xboole_0(A_128,B_129)),A_128) = k6_relat_1(k4_xboole_0(A_128,B_129)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_1399])).

tff(c_707,plain,(
    ! [A_99,A_100] : k7_relat_1(k6_relat_1(A_99),k3_xboole_0(A_99,A_100)) = k7_relat_1(k6_relat_1(A_99),A_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_375])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k5_relat_1(A_16,B_17))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_262,plain,(
    ! [B_68,A_67] :
      ( v1_relat_1(k7_relat_1(B_68,A_67))
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(k6_relat_1(A_67))
      | ~ v1_relat_1(B_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_20])).

tff(c_294,plain,(
    ! [B_68,A_67] :
      ( v1_relat_1(k7_relat_1(B_68,A_67))
      | ~ v1_relat_1(B_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_262])).

tff(c_725,plain,(
    ! [A_99,A_100] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_99),A_100))
      | ~ v1_relat_1(k6_relat_1(A_99)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_707,c_294])).

tff(c_745,plain,(
    ! [A_99,A_100] : v1_relat_1(k7_relat_1(k6_relat_1(A_99),A_100)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_725])).

tff(c_442,plain,(
    ! [A_86,B_87,C_88] :
      ( k5_relat_1(k5_relat_1(A_86,B_87),C_88) = k5_relat_1(A_86,k5_relat_1(B_87,C_88))
      | ~ v1_relat_1(C_88)
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_452,plain,(
    ! [A_86,B_87,A_29] :
      ( r1_tarski(k5_relat_1(A_86,k5_relat_1(B_87,k6_relat_1(A_29))),k5_relat_1(A_86,B_87))
      | ~ v1_relat_1(k5_relat_1(A_86,B_87))
      | ~ v1_relat_1(k6_relat_1(A_29))
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_34])).

tff(c_3693,plain,(
    ! [A_190,B_191,A_192] :
      ( r1_tarski(k5_relat_1(A_190,k5_relat_1(B_191,k6_relat_1(A_192))),k5_relat_1(A_190,B_191))
      | ~ v1_relat_1(k5_relat_1(A_190,B_191))
      | ~ v1_relat_1(B_191)
      | ~ v1_relat_1(A_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_452])).

tff(c_3706,plain,(
    ! [A_35,A_164,A_192] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_35),k5_relat_1(k6_relat_1(A_164),k6_relat_1(A_192))),k7_relat_1(k6_relat_1(A_164),A_35))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_35),k6_relat_1(A_164)))
      | ~ v1_relat_1(k6_relat_1(A_164))
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2694,c_3693])).

tff(c_8390,plain,(
    ! [A_260,A_261,A_262] : r1_tarski(k5_relat_1(k6_relat_1(A_260),k7_relat_1(k6_relat_1(A_261),A_262)),k7_relat_1(k6_relat_1(A_262),A_260)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_745,c_2694,c_2694,c_3706])).

tff(c_8461,plain,(
    ! [A_260,A_128,B_129] : r1_tarski(k5_relat_1(k6_relat_1(A_260),k6_relat_1(k4_xboole_0(A_128,B_129))),k7_relat_1(k6_relat_1(A_128),A_260)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1433,c_8390])).

tff(c_8554,plain,(
    ! [A_263,B_264,A_265] : r1_tarski(k7_relat_1(k6_relat_1(k4_xboole_0(A_263,B_264)),A_265),k7_relat_1(k6_relat_1(A_263),A_265)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2694,c_8461])).

tff(c_8664,plain,(
    ! [A_266,B_267,A_268] : r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(A_266,B_267)),A_268),k7_relat_1(k6_relat_1(A_266),A_268)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_8554])).

tff(c_8760,plain,(
    ! [A_266,B_267] :
      ( r1_tarski(k6_relat_1(k3_xboole_0(A_266,B_267)),k7_relat_1(k6_relat_1(A_266),k1_relat_1(k6_relat_1(k3_xboole_0(A_266,B_267)))))
      | ~ v1_relat_1(k6_relat_1(k3_xboole_0(A_266,B_267))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_840,c_8664])).

tff(c_8831,plain,(
    ! [A_269,B_270] : r1_tarski(k6_relat_1(k3_xboole_0(A_269,B_270)),k7_relat_1(k6_relat_1(A_269),B_270)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_382,c_28,c_8760])).

tff(c_8838,plain,(
    ! [A_269,B_270] :
      ( k7_relat_1(k6_relat_1(A_269),B_270) = k6_relat_1(k3_xboole_0(A_269,B_270))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_269),B_270),k6_relat_1(k3_xboole_0(A_269,B_270))) ) ),
    inference(resolution,[status(thm)],[c_8831,c_2])).

tff(c_8946,plain,(
    ! [A_269,B_270] : k7_relat_1(k6_relat_1(A_269),B_270) = k6_relat_1(k3_xboole_0(A_269,B_270)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_8838])).

tff(c_44,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_268,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_44])).

tff(c_296,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_268])).

tff(c_9003,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8946,c_296])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:31:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.72/2.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.72/2.42  
% 6.72/2.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.72/2.42  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 6.72/2.42  
% 6.72/2.42  %Foreground sorts:
% 6.72/2.42  
% 6.72/2.42  
% 6.72/2.42  %Background operators:
% 6.72/2.42  
% 6.72/2.42  
% 6.72/2.42  %Foreground operators:
% 6.72/2.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.72/2.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.72/2.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.72/2.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.72/2.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.72/2.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.72/2.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.72/2.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.72/2.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.72/2.42  tff('#skF_2', type, '#skF_2': $i).
% 6.72/2.42  tff('#skF_1', type, '#skF_1': $i).
% 6.72/2.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.72/2.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.72/2.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.72/2.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.72/2.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.72/2.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.72/2.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.72/2.42  
% 6.72/2.44  tff(f_51, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 6.72/2.44  tff(f_69, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 6.72/2.44  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 6.72/2.44  tff(f_93, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 6.72/2.44  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 6.72/2.44  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.72/2.44  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 6.72/2.44  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.72/2.44  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.72/2.44  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 6.72/2.44  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 6.72/2.44  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 6.72/2.44  tff(f_49, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 6.72/2.44  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 6.72/2.44  tff(f_96, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 6.72/2.44  tff(c_22, plain, (![A_18]: (v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.72/2.44  tff(c_28, plain, (![A_28]: (k1_relat_1(k6_relat_1(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.72/2.44  tff(c_352, plain, (![B_78, A_79]: (k7_relat_1(B_78, k3_xboole_0(k1_relat_1(B_78), A_79))=k7_relat_1(B_78, A_79) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.72/2.44  tff(c_248, plain, (![A_67, B_68]: (k5_relat_1(k6_relat_1(A_67), B_68)=k7_relat_1(B_68, A_67) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.72/2.44  tff(c_34, plain, (![B_30, A_29]: (r1_tarski(k5_relat_1(B_30, k6_relat_1(A_29)), B_30) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.72/2.44  tff(c_255, plain, (![A_29, A_67]: (r1_tarski(k7_relat_1(k6_relat_1(A_29), A_67), k6_relat_1(A_67)) | ~v1_relat_1(k6_relat_1(A_67)) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_248, c_34])).
% 6.72/2.44  tff(c_292, plain, (![A_29, A_67]: (r1_tarski(k7_relat_1(k6_relat_1(A_29), A_67), k6_relat_1(A_67)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_255])).
% 6.72/2.44  tff(c_362, plain, (![A_29, A_79]: (r1_tarski(k7_relat_1(k6_relat_1(A_29), A_79), k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_29)), A_79))) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_352, c_292])).
% 6.72/2.44  tff(c_378, plain, (![A_29, A_79]: (r1_tarski(k7_relat_1(k6_relat_1(A_29), A_79), k6_relat_1(k3_xboole_0(A_29, A_79))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_28, c_362])).
% 6.72/2.44  tff(c_375, plain, (![A_28, A_79]: (k7_relat_1(k6_relat_1(A_28), k3_xboole_0(A_28, A_79))=k7_relat_1(k6_relat_1(A_28), A_79) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_352])).
% 6.72/2.44  tff(c_382, plain, (![A_28, A_79]: (k7_relat_1(k6_relat_1(A_28), k3_xboole_0(A_28, A_79))=k7_relat_1(k6_relat_1(A_28), A_79))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_375])).
% 6.72/2.44  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.72/2.44  tff(c_38, plain, (![A_33]: (k5_relat_1(k6_relat_1(k1_relat_1(A_33)), A_33)=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.72/2.44  tff(c_259, plain, (![B_68]: (k7_relat_1(B_68, k1_relat_1(B_68))=B_68 | ~v1_relat_1(B_68) | ~v1_relat_1(B_68))), inference(superposition, [status(thm), theory('equality')], [c_248, c_38])).
% 6.72/2.44  tff(c_32, plain, (![A_29, B_30]: (r1_tarski(k5_relat_1(k6_relat_1(A_29), B_30), B_30) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.72/2.44  tff(c_343, plain, (![B_76, A_77]: (r1_tarski(k7_relat_1(B_76, A_77), B_76) | ~v1_relat_1(B_76) | ~v1_relat_1(B_76))), inference(superposition, [status(thm), theory('equality')], [c_248, c_32])).
% 6.72/2.44  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.72/2.44  tff(c_819, plain, (![B_109, A_110]: (k7_relat_1(B_109, A_110)=B_109 | ~r1_tarski(B_109, k7_relat_1(B_109, A_110)) | ~v1_relat_1(B_109))), inference(resolution, [status(thm)], [c_343, c_2])).
% 6.72/2.44  tff(c_828, plain, (![B_68]: (k7_relat_1(B_68, k1_relat_1(B_68))=B_68 | ~r1_tarski(B_68, B_68) | ~v1_relat_1(B_68) | ~v1_relat_1(B_68) | ~v1_relat_1(B_68))), inference(superposition, [status(thm), theory('equality')], [c_259, c_819])).
% 6.72/2.44  tff(c_840, plain, (![B_68]: (k7_relat_1(B_68, k1_relat_1(B_68))=B_68 | ~v1_relat_1(B_68))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_828])).
% 6.72/2.44  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.72/2.44  tff(c_30, plain, (![A_28]: (k2_relat_1(k6_relat_1(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.72/2.44  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.72/2.44  tff(c_324, plain, (![A_72, B_73]: (k5_relat_1(k6_relat_1(A_72), B_73)=B_73 | ~r1_tarski(k1_relat_1(B_73), A_72) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.72/2.44  tff(c_327, plain, (![A_72, A_28]: (k5_relat_1(k6_relat_1(A_72), k6_relat_1(A_28))=k6_relat_1(A_28) | ~r1_tarski(A_28, A_72) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_324])).
% 6.72/2.44  tff(c_499, plain, (![A_89, A_90]: (k5_relat_1(k6_relat_1(A_89), k6_relat_1(A_90))=k6_relat_1(A_90) | ~r1_tarski(A_90, A_89))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_327])).
% 6.72/2.44  tff(c_42, plain, (![A_35, B_36]: (k5_relat_1(k6_relat_1(A_35), B_36)=k7_relat_1(B_36, A_35) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.72/2.44  tff(c_508, plain, (![A_90, A_89]: (k7_relat_1(k6_relat_1(A_90), A_89)=k6_relat_1(A_90) | ~v1_relat_1(k6_relat_1(A_90)) | ~r1_tarski(A_90, A_89))), inference(superposition, [status(thm), theory('equality')], [c_499, c_42])).
% 6.72/2.44  tff(c_586, plain, (![A_93, A_94]: (k7_relat_1(k6_relat_1(A_93), A_94)=k6_relat_1(A_93) | ~r1_tarski(A_93, A_94))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_508])).
% 6.72/2.44  tff(c_592, plain, (![A_93, A_94]: (r1_tarski(k6_relat_1(A_93), k6_relat_1(k3_xboole_0(A_93, A_94))) | ~r1_tarski(A_93, A_94))), inference(superposition, [status(thm), theory('equality')], [c_586, c_378])).
% 6.72/2.44  tff(c_511, plain, (![A_90, A_89]: (r1_tarski(k6_relat_1(A_90), k6_relat_1(A_89)) | ~v1_relat_1(k6_relat_1(A_89)) | ~r1_tarski(A_90, A_89))), inference(superposition, [status(thm), theory('equality')], [c_499, c_34])).
% 6.72/2.44  tff(c_581, plain, (![A_91, A_92]: (r1_tarski(k6_relat_1(A_91), k6_relat_1(A_92)) | ~r1_tarski(A_91, A_92))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_511])).
% 6.72/2.44  tff(c_940, plain, (![A_117, A_116]: (k6_relat_1(A_117)=k6_relat_1(A_116) | ~r1_tarski(k6_relat_1(A_116), k6_relat_1(A_117)) | ~r1_tarski(A_117, A_116))), inference(resolution, [status(thm)], [c_581, c_2])).
% 6.72/2.44  tff(c_943, plain, (![A_93, A_94]: (k6_relat_1(k3_xboole_0(A_93, A_94))=k6_relat_1(A_93) | ~r1_tarski(k3_xboole_0(A_93, A_94), A_93) | ~r1_tarski(A_93, A_94))), inference(resolution, [status(thm)], [c_592, c_940])).
% 6.72/2.44  tff(c_1123, plain, (![A_120, A_121]: (k6_relat_1(k3_xboole_0(A_120, A_121))=k6_relat_1(A_120) | ~r1_tarski(A_120, A_121))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_943])).
% 6.72/2.44  tff(c_1197, plain, (![A_120, A_121]: (k3_xboole_0(A_120, A_121)=k2_relat_1(k6_relat_1(A_120)) | ~r1_tarski(A_120, A_121))), inference(superposition, [status(thm), theory('equality')], [c_1123, c_30])).
% 6.72/2.44  tff(c_1265, plain, (![A_124, A_125]: (k3_xboole_0(A_124, A_125)=A_124 | ~r1_tarski(A_124, A_125))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1197])).
% 6.72/2.44  tff(c_1305, plain, (![A_29, A_67]: (k3_xboole_0(k7_relat_1(k6_relat_1(A_29), A_67), k6_relat_1(A_67))=k7_relat_1(k6_relat_1(A_29), A_67))), inference(resolution, [status(thm)], [c_292, c_1265])).
% 6.72/2.44  tff(c_2587, plain, (![B_163, A_164]: (k3_xboole_0(k5_relat_1(B_163, k6_relat_1(A_164)), B_163)=k5_relat_1(B_163, k6_relat_1(A_164)) | ~v1_relat_1(B_163))), inference(resolution, [status(thm)], [c_34, c_1265])).
% 6.72/2.44  tff(c_2657, plain, (![A_164, A_35]: (k3_xboole_0(k7_relat_1(k6_relat_1(A_164), A_35), k6_relat_1(A_35))=k5_relat_1(k6_relat_1(A_35), k6_relat_1(A_164)) | ~v1_relat_1(k6_relat_1(A_35)) | ~v1_relat_1(k6_relat_1(A_164)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_2587])).
% 6.72/2.44  tff(c_2694, plain, (![A_35, A_164]: (k5_relat_1(k6_relat_1(A_35), k6_relat_1(A_164))=k7_relat_1(k6_relat_1(A_164), A_35))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_1305, c_2657])).
% 6.72/2.44  tff(c_40, plain, (![A_34]: (k5_relat_1(A_34, k6_relat_1(k2_relat_1(A_34)))=A_34 | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.72/2.44  tff(c_289, plain, (![A_67]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_67))), A_67)=k6_relat_1(A_67) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_67)))) | ~v1_relat_1(k6_relat_1(A_67)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_248])).
% 6.72/2.44  tff(c_305, plain, (![A_67]: (k7_relat_1(k6_relat_1(A_67), A_67)=k6_relat_1(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_30, c_289])).
% 6.72/2.44  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.72/2.44  tff(c_108, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k4_xboole_0(A_49, B_50))=k3_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.72/2.44  tff(c_117, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k3_xboole_0(A_7, k4_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_108])).
% 6.72/2.44  tff(c_654, plain, (![A_95, B_96]: (k3_xboole_0(A_95, k4_xboole_0(A_95, B_96))=k4_xboole_0(A_95, B_96))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_117])).
% 6.72/2.44  tff(c_676, plain, (![A_95, B_96]: (r1_tarski(k4_xboole_0(A_95, B_96), A_95))), inference(superposition, [status(thm), theory('equality')], [c_654, c_8])).
% 6.72/2.44  tff(c_1381, plain, (![A_128, B_129]: (k3_xboole_0(k4_xboole_0(A_128, B_129), A_128)=k4_xboole_0(A_128, B_129))), inference(resolution, [status(thm)], [c_676, c_1265])).
% 6.72/2.44  tff(c_1399, plain, (![A_128, B_129]: (k7_relat_1(k6_relat_1(k4_xboole_0(A_128, B_129)), k4_xboole_0(A_128, B_129))=k7_relat_1(k6_relat_1(k4_xboole_0(A_128, B_129)), A_128))), inference(superposition, [status(thm), theory('equality')], [c_1381, c_382])).
% 6.72/2.44  tff(c_1433, plain, (![A_128, B_129]: (k7_relat_1(k6_relat_1(k4_xboole_0(A_128, B_129)), A_128)=k6_relat_1(k4_xboole_0(A_128, B_129)))), inference(demodulation, [status(thm), theory('equality')], [c_305, c_1399])).
% 6.72/2.44  tff(c_707, plain, (![A_99, A_100]: (k7_relat_1(k6_relat_1(A_99), k3_xboole_0(A_99, A_100))=k7_relat_1(k6_relat_1(A_99), A_100))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_375])).
% 6.72/2.44  tff(c_20, plain, (![A_16, B_17]: (v1_relat_1(k5_relat_1(A_16, B_17)) | ~v1_relat_1(B_17) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.72/2.44  tff(c_262, plain, (![B_68, A_67]: (v1_relat_1(k7_relat_1(B_68, A_67)) | ~v1_relat_1(B_68) | ~v1_relat_1(k6_relat_1(A_67)) | ~v1_relat_1(B_68))), inference(superposition, [status(thm), theory('equality')], [c_248, c_20])).
% 6.72/2.44  tff(c_294, plain, (![B_68, A_67]: (v1_relat_1(k7_relat_1(B_68, A_67)) | ~v1_relat_1(B_68))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_262])).
% 6.72/2.44  tff(c_725, plain, (![A_99, A_100]: (v1_relat_1(k7_relat_1(k6_relat_1(A_99), A_100)) | ~v1_relat_1(k6_relat_1(A_99)))), inference(superposition, [status(thm), theory('equality')], [c_707, c_294])).
% 6.72/2.44  tff(c_745, plain, (![A_99, A_100]: (v1_relat_1(k7_relat_1(k6_relat_1(A_99), A_100)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_725])).
% 6.72/2.44  tff(c_442, plain, (![A_86, B_87, C_88]: (k5_relat_1(k5_relat_1(A_86, B_87), C_88)=k5_relat_1(A_86, k5_relat_1(B_87, C_88)) | ~v1_relat_1(C_88) | ~v1_relat_1(B_87) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.72/2.44  tff(c_452, plain, (![A_86, B_87, A_29]: (r1_tarski(k5_relat_1(A_86, k5_relat_1(B_87, k6_relat_1(A_29))), k5_relat_1(A_86, B_87)) | ~v1_relat_1(k5_relat_1(A_86, B_87)) | ~v1_relat_1(k6_relat_1(A_29)) | ~v1_relat_1(B_87) | ~v1_relat_1(A_86))), inference(superposition, [status(thm), theory('equality')], [c_442, c_34])).
% 6.72/2.44  tff(c_3693, plain, (![A_190, B_191, A_192]: (r1_tarski(k5_relat_1(A_190, k5_relat_1(B_191, k6_relat_1(A_192))), k5_relat_1(A_190, B_191)) | ~v1_relat_1(k5_relat_1(A_190, B_191)) | ~v1_relat_1(B_191) | ~v1_relat_1(A_190))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_452])).
% 6.72/2.44  tff(c_3706, plain, (![A_35, A_164, A_192]: (r1_tarski(k5_relat_1(k6_relat_1(A_35), k5_relat_1(k6_relat_1(A_164), k6_relat_1(A_192))), k7_relat_1(k6_relat_1(A_164), A_35)) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_35), k6_relat_1(A_164))) | ~v1_relat_1(k6_relat_1(A_164)) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_2694, c_3693])).
% 6.72/2.44  tff(c_8390, plain, (![A_260, A_261, A_262]: (r1_tarski(k5_relat_1(k6_relat_1(A_260), k7_relat_1(k6_relat_1(A_261), A_262)), k7_relat_1(k6_relat_1(A_262), A_260)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_745, c_2694, c_2694, c_3706])).
% 6.72/2.44  tff(c_8461, plain, (![A_260, A_128, B_129]: (r1_tarski(k5_relat_1(k6_relat_1(A_260), k6_relat_1(k4_xboole_0(A_128, B_129))), k7_relat_1(k6_relat_1(A_128), A_260)))), inference(superposition, [status(thm), theory('equality')], [c_1433, c_8390])).
% 6.72/2.44  tff(c_8554, plain, (![A_263, B_264, A_265]: (r1_tarski(k7_relat_1(k6_relat_1(k4_xboole_0(A_263, B_264)), A_265), k7_relat_1(k6_relat_1(A_263), A_265)))), inference(demodulation, [status(thm), theory('equality')], [c_2694, c_8461])).
% 6.72/2.44  tff(c_8664, plain, (![A_266, B_267, A_268]: (r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(A_266, B_267)), A_268), k7_relat_1(k6_relat_1(A_266), A_268)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_8554])).
% 6.72/2.44  tff(c_8760, plain, (![A_266, B_267]: (r1_tarski(k6_relat_1(k3_xboole_0(A_266, B_267)), k7_relat_1(k6_relat_1(A_266), k1_relat_1(k6_relat_1(k3_xboole_0(A_266, B_267))))) | ~v1_relat_1(k6_relat_1(k3_xboole_0(A_266, B_267))))), inference(superposition, [status(thm), theory('equality')], [c_840, c_8664])).
% 6.72/2.44  tff(c_8831, plain, (![A_269, B_270]: (r1_tarski(k6_relat_1(k3_xboole_0(A_269, B_270)), k7_relat_1(k6_relat_1(A_269), B_270)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_382, c_28, c_8760])).
% 6.72/2.44  tff(c_8838, plain, (![A_269, B_270]: (k7_relat_1(k6_relat_1(A_269), B_270)=k6_relat_1(k3_xboole_0(A_269, B_270)) | ~r1_tarski(k7_relat_1(k6_relat_1(A_269), B_270), k6_relat_1(k3_xboole_0(A_269, B_270))))), inference(resolution, [status(thm)], [c_8831, c_2])).
% 6.72/2.44  tff(c_8946, plain, (![A_269, B_270]: (k7_relat_1(k6_relat_1(A_269), B_270)=k6_relat_1(k3_xboole_0(A_269, B_270)))), inference(demodulation, [status(thm), theory('equality')], [c_378, c_8838])).
% 6.72/2.44  tff(c_44, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.72/2.44  tff(c_268, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_248, c_44])).
% 6.72/2.44  tff(c_296, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_268])).
% 6.72/2.44  tff(c_9003, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8946, c_296])).
% 6.72/2.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.72/2.44  
% 6.72/2.44  Inference rules
% 6.72/2.44  ----------------------
% 6.72/2.44  #Ref     : 0
% 6.72/2.44  #Sup     : 2141
% 6.72/2.44  #Fact    : 0
% 6.72/2.44  #Define  : 0
% 6.72/2.44  #Split   : 1
% 6.72/2.44  #Chain   : 0
% 6.72/2.44  #Close   : 0
% 6.72/2.44  
% 6.72/2.44  Ordering : KBO
% 6.72/2.44  
% 6.72/2.44  Simplification rules
% 6.72/2.44  ----------------------
% 6.72/2.44  #Subsume      : 212
% 6.72/2.44  #Demod        : 2317
% 6.72/2.44  #Tautology    : 948
% 6.72/2.44  #SimpNegUnit  : 0
% 6.72/2.44  #BackRed      : 36
% 6.72/2.44  
% 6.72/2.44  #Partial instantiations: 0
% 6.72/2.44  #Strategies tried      : 1
% 6.72/2.44  
% 6.72/2.44  Timing (in seconds)
% 6.72/2.44  ----------------------
% 6.72/2.44  Preprocessing        : 0.33
% 6.72/2.44  Parsing              : 0.18
% 6.72/2.44  CNF conversion       : 0.02
% 6.72/2.44  Main loop            : 1.34
% 6.72/2.44  Inferencing          : 0.41
% 6.72/2.44  Reduction            : 0.53
% 6.72/2.44  Demodulation         : 0.42
% 6.72/2.44  BG Simplification    : 0.06
% 6.72/2.44  Subsumption          : 0.25
% 6.72/2.44  Abstraction          : 0.09
% 6.72/2.44  MUC search           : 0.00
% 6.72/2.44  Cooper               : 0.00
% 6.72/2.44  Total                : 1.71
% 6.72/2.44  Index Insertion      : 0.00
% 6.72/2.44  Index Deletion       : 0.00
% 6.72/2.44  Index Matching       : 0.00
% 6.72/2.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
