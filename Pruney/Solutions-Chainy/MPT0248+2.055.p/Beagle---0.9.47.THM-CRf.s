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
% DateTime   : Thu Dec  3 09:50:11 EST 2020

% Result     : Theorem 4.78s
% Output     : CNFRefutation 4.78s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 290 expanded)
%              Number of leaves         :   36 ( 108 expanded)
%              Depth                    :   12
%              Number of atoms          :  186 ( 604 expanded)
%              Number of equality atoms :   55 ( 315 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_50,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_68,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_18,plain,(
    ! [B_14] : r1_tarski(B_14,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_614,plain,(
    ! [A_131,B_132] :
      ( k2_xboole_0(A_131,B_132) = B_132
      | ~ r1_tarski(A_131,B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_630,plain,(
    ! [B_14] : k2_xboole_0(B_14,B_14) = B_14 ),
    inference(resolution,[status(thm)],[c_18,c_614])).

tff(c_52,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_79,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,(
    ! [A_54,B_55] :
      ( r1_xboole_0(k1_tarski(A_54),B_55)
      | r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_56,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_64,plain,(
    ! [A_60,B_61] : r1_tarski(A_60,k2_xboole_0(A_60,B_61)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_67,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_64])).

tff(c_225,plain,(
    ! [A_88,B_89] :
      ( k3_xboole_0(A_88,B_89) = A_88
      | ~ r1_tarski(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_239,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_67,c_225])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_276,plain,(
    ! [A_93,B_94,C_95] :
      ( ~ r1_xboole_0(A_93,B_94)
      | ~ r2_hidden(C_95,k3_xboole_0(A_93,B_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_303,plain,(
    ! [A_98,B_99] :
      ( ~ r1_xboole_0(A_98,B_99)
      | v1_xboole_0(k3_xboole_0(A_98,B_99)) ) ),
    inference(resolution,[status(thm)],[c_6,c_276])).

tff(c_416,plain,(
    ! [A_106,B_107] :
      ( ~ r1_xboole_0(A_106,B_107)
      | v1_xboole_0(k3_xboole_0(B_107,A_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_303])).

tff(c_428,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_416])).

tff(c_439,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_428])).

tff(c_443,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_439])).

tff(c_44,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(k1_tarski(A_52),B_53)
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_448,plain,(
    ! [B_108,A_109] :
      ( B_108 = A_109
      | ~ r1_tarski(B_108,A_109)
      | ~ r1_tarski(A_109,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_456,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_67,c_448])).

tff(c_466,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_456])).

tff(c_474,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_466])).

tff(c_478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_474])).

tff(c_479,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_428])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_483,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_479,c_8])).

tff(c_487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_483])).

tff(c_488,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1559,plain,(
    ! [A_212,B_213] :
      ( r2_hidden('#skF_2'(A_212,B_213),k3_xboole_0(A_212,B_213))
      | r1_xboole_0(A_212,B_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_714,plain,(
    ! [A_141,B_142,C_143] :
      ( ~ r1_xboole_0(A_141,B_142)
      | ~ r2_hidden(C_143,k3_xboole_0(A_141,B_142)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_729,plain,(
    ! [B_2,A_1,C_143] :
      ( ~ r1_xboole_0(B_2,A_1)
      | ~ r2_hidden(C_143,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_714])).

tff(c_1610,plain,(
    ! [B_214,A_215] :
      ( ~ r1_xboole_0(B_214,A_215)
      | r1_xboole_0(A_215,B_214) ) ),
    inference(resolution,[status(thm)],[c_1559,c_729])).

tff(c_1621,plain,(
    ! [B_55,A_54] :
      ( r1_xboole_0(B_55,k1_tarski(A_54))
      | r2_hidden(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_46,c_1610])).

tff(c_735,plain,(
    ! [A_144,C_145,B_146] :
      ( r1_tarski(A_144,k2_xboole_0(C_145,B_146))
      | ~ r1_tarski(A_144,B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_795,plain,(
    ! [A_152] :
      ( r1_tarski(A_152,k1_tarski('#skF_3'))
      | ~ r1_tarski(A_152,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_735])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,B_19) = B_19
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1656,plain,(
    ! [A_218] :
      ( k2_xboole_0(A_218,k1_tarski('#skF_3')) = k1_tarski('#skF_3')
      | ~ r1_tarski(A_218,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_795,c_22])).

tff(c_26,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_545,plain,(
    ! [A_116,B_117] :
      ( k3_xboole_0(A_116,B_117) = A_116
      | ~ r1_tarski(A_116,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_556,plain,(
    ! [A_22,B_23] : k3_xboole_0(A_22,k2_xboole_0(A_22,B_23)) = A_22 ),
    inference(resolution,[status(thm)],[c_26,c_545])).

tff(c_767,plain,(
    ! [A_149,B_150] :
      ( ~ r1_xboole_0(A_149,B_150)
      | v1_xboole_0(k3_xboole_0(A_149,B_150)) ) ),
    inference(resolution,[status(thm)],[c_6,c_714])).

tff(c_773,plain,(
    ! [A_22,B_23] :
      ( ~ r1_xboole_0(A_22,k2_xboole_0(A_22,B_23))
      | v1_xboole_0(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_767])).

tff(c_2521,plain,(
    ! [A_278] :
      ( ~ r1_xboole_0(A_278,k1_tarski('#skF_3'))
      | v1_xboole_0(A_278)
      | ~ r1_tarski(A_278,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1656,c_773])).

tff(c_2549,plain,(
    ! [B_55] :
      ( v1_xboole_0(B_55)
      | ~ r1_tarski(B_55,'#skF_5')
      | r2_hidden('#skF_3',B_55) ) ),
    inference(resolution,[status(thm)],[c_1621,c_2521])).

tff(c_756,plain,(
    ! [A_144] :
      ( r1_tarski(A_144,k1_tarski('#skF_3'))
      | ~ r1_tarski(A_144,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_735])).

tff(c_692,plain,(
    ! [B_139,A_140] :
      ( B_139 = A_140
      | ~ r1_tarski(B_139,A_140)
      | ~ r1_tarski(A_140,B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3289,plain,(
    ! [A_299,B_300] :
      ( k1_tarski(A_299) = B_300
      | ~ r1_tarski(B_300,k1_tarski(A_299))
      | ~ r2_hidden(A_299,B_300) ) ),
    inference(resolution,[status(thm)],[c_44,c_692])).

tff(c_3312,plain,(
    ! [A_301] :
      ( k1_tarski('#skF_3') = A_301
      | ~ r2_hidden('#skF_3',A_301)
      | ~ r1_tarski(A_301,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_756,c_3289])).

tff(c_3352,plain,(
    ! [B_302] :
      ( k1_tarski('#skF_3') = B_302
      | v1_xboole_0(B_302)
      | ~ r1_tarski(B_302,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2549,c_3312])).

tff(c_3360,plain,
    ( k1_tarski('#skF_3') = '#skF_5'
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_3352])).

tff(c_3366,plain,(
    v1_xboole_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_488,c_3360])).

tff(c_489,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_490,plain,(
    ! [A_7] :
      ( A_7 = '#skF_4'
      | ~ v1_xboole_0(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_8])).

tff(c_3370,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3366,c_490])).

tff(c_3387,plain,(
    k2_xboole_0('#skF_4','#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3370,c_56])).

tff(c_3389,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_3387])).

tff(c_3391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3389])).

tff(c_3392,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3393,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3395,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3393,c_56])).

tff(c_3836,plain,(
    ! [A_347,C_348,B_349] :
      ( r1_tarski(A_347,k2_xboole_0(C_348,B_349))
      | ~ r1_tarski(A_347,B_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3861,plain,(
    ! [A_350] :
      ( r1_tarski(A_350,'#skF_4')
      | ~ r1_tarski(A_350,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3395,c_3836])).

tff(c_3950,plain,(
    ! [A_354] :
      ( r1_tarski(k1_tarski(A_354),'#skF_4')
      | ~ r2_hidden(A_354,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_3861])).

tff(c_42,plain,(
    ! [A_52,B_53] :
      ( r2_hidden(A_52,B_53)
      | ~ r1_tarski(k1_tarski(A_52),B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3985,plain,(
    ! [A_357] :
      ( r2_hidden(A_357,'#skF_4')
      | ~ r2_hidden(A_357,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3950,c_42])).

tff(c_4002,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_3985])).

tff(c_4028,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4002])).

tff(c_4050,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4028,c_8])).

tff(c_4054,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3392,c_4050])).

tff(c_4056,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_4002])).

tff(c_54,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3422,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3393,c_3393,c_54])).

tff(c_3871,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_3861])).

tff(c_4004,plain,(
    ! [B_358,A_359] :
      ( B_358 = A_359
      | ~ r1_tarski(B_358,A_359)
      | ~ r1_tarski(A_359,B_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4008,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_3871,c_4004])).

tff(c_4020,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_3422,c_4008])).

tff(c_3598,plain,(
    ! [A_329,B_330] :
      ( r1_xboole_0(k1_tarski(A_329),B_330)
      | r2_hidden(A_329,B_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3602,plain,(
    ! [B_331] :
      ( r1_xboole_0('#skF_4',B_331)
      | r2_hidden('#skF_3',B_331) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3393,c_3598])).

tff(c_3548,plain,(
    ! [A_325,B_326] :
      ( r1_tarski(k1_tarski(A_325),B_326)
      | ~ r2_hidden(A_325,B_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3557,plain,(
    ! [B_326] :
      ( r1_tarski('#skF_4',B_326)
      | ~ r2_hidden('#skF_3',B_326) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3393,c_3548])).

tff(c_3609,plain,(
    ! [B_331] :
      ( r1_tarski('#skF_4',B_331)
      | r1_xboole_0('#skF_4',B_331) ) ),
    inference(resolution,[status(thm)],[c_3602,c_3557])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3879,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3871,c_24])).

tff(c_3907,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3879])).

tff(c_12,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3945,plain,(
    ! [C_12] :
      ( ~ r1_xboole_0('#skF_4','#skF_5')
      | ~ r2_hidden(C_12,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3907,c_12])).

tff(c_4061,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3945])).

tff(c_4064,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_3609,c_4061])).

tff(c_4071,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4020,c_4064])).

tff(c_4083,plain,(
    ! [C_365] : ~ r2_hidden(C_365,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_3945])).

tff(c_4095,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_4083])).

tff(c_4101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4056,c_4095])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:36:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.78/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.93  
% 4.78/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.94  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 4.78/1.94  
% 4.78/1.94  %Foreground sorts:
% 4.78/1.94  
% 4.78/1.94  
% 4.78/1.94  %Background operators:
% 4.78/1.94  
% 4.78/1.94  
% 4.78/1.94  %Foreground operators:
% 4.78/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.78/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.78/1.94  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.78/1.94  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.78/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.78/1.94  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.78/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.78/1.94  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.78/1.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.78/1.94  tff('#skF_5', type, '#skF_5': $i).
% 4.78/1.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.78/1.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.78/1.94  tff('#skF_3', type, '#skF_3': $i).
% 4.78/1.94  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.78/1.94  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.78/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.78/1.94  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.78/1.94  tff('#skF_4', type, '#skF_4': $i).
% 4.78/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.78/1.94  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.78/1.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.78/1.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.78/1.94  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.78/1.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.78/1.94  
% 4.78/1.95  tff(f_115, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.78/1.95  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.78/1.95  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.78/1.95  tff(f_94, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.78/1.95  tff(f_71, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.78/1.95  tff(f_69, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.78/1.95  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.78/1.95  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.78/1.95  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.78/1.95  tff(f_89, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.78/1.95  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.78/1.95  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 4.78/1.95  tff(c_50, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.78/1.95  tff(c_68, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_50])).
% 4.78/1.95  tff(c_18, plain, (![B_14]: (r1_tarski(B_14, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.78/1.95  tff(c_614, plain, (![A_131, B_132]: (k2_xboole_0(A_131, B_132)=B_132 | ~r1_tarski(A_131, B_132))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.78/1.95  tff(c_630, plain, (![B_14]: (k2_xboole_0(B_14, B_14)=B_14)), inference(resolution, [status(thm)], [c_18, c_614])).
% 4.78/1.95  tff(c_52, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.78/1.95  tff(c_79, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_52])).
% 4.78/1.95  tff(c_46, plain, (![A_54, B_55]: (r1_xboole_0(k1_tarski(A_54), B_55) | r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.78/1.95  tff(c_56, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.78/1.95  tff(c_64, plain, (![A_60, B_61]: (r1_tarski(A_60, k2_xboole_0(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.78/1.95  tff(c_67, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_64])).
% 4.78/1.95  tff(c_225, plain, (![A_88, B_89]: (k3_xboole_0(A_88, B_89)=A_88 | ~r1_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.78/1.95  tff(c_239, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(resolution, [status(thm)], [c_67, c_225])).
% 4.78/1.95  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.78/1.95  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.78/1.95  tff(c_276, plain, (![A_93, B_94, C_95]: (~r1_xboole_0(A_93, B_94) | ~r2_hidden(C_95, k3_xboole_0(A_93, B_94)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.78/1.95  tff(c_303, plain, (![A_98, B_99]: (~r1_xboole_0(A_98, B_99) | v1_xboole_0(k3_xboole_0(A_98, B_99)))), inference(resolution, [status(thm)], [c_6, c_276])).
% 4.78/1.95  tff(c_416, plain, (![A_106, B_107]: (~r1_xboole_0(A_106, B_107) | v1_xboole_0(k3_xboole_0(B_107, A_106)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_303])).
% 4.78/1.95  tff(c_428, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_239, c_416])).
% 4.78/1.95  tff(c_439, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_428])).
% 4.78/1.95  tff(c_443, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_439])).
% 4.78/1.95  tff(c_44, plain, (![A_52, B_53]: (r1_tarski(k1_tarski(A_52), B_53) | ~r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.78/1.95  tff(c_448, plain, (![B_108, A_109]: (B_108=A_109 | ~r1_tarski(B_108, A_109) | ~r1_tarski(A_109, B_108))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.78/1.95  tff(c_456, plain, (k1_tarski('#skF_3')='#skF_4' | ~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_67, c_448])).
% 4.78/1.95  tff(c_466, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_456])).
% 4.78/1.95  tff(c_474, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_466])).
% 4.78/1.95  tff(c_478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_443, c_474])).
% 4.78/1.95  tff(c_479, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_428])).
% 4.78/1.95  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.78/1.95  tff(c_483, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_479, c_8])).
% 4.78/1.95  tff(c_487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_483])).
% 4.78/1.95  tff(c_488, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_52])).
% 4.78/1.95  tff(c_1559, plain, (![A_212, B_213]: (r2_hidden('#skF_2'(A_212, B_213), k3_xboole_0(A_212, B_213)) | r1_xboole_0(A_212, B_213))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.78/1.95  tff(c_714, plain, (![A_141, B_142, C_143]: (~r1_xboole_0(A_141, B_142) | ~r2_hidden(C_143, k3_xboole_0(A_141, B_142)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.78/1.95  tff(c_729, plain, (![B_2, A_1, C_143]: (~r1_xboole_0(B_2, A_1) | ~r2_hidden(C_143, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_714])).
% 4.78/1.95  tff(c_1610, plain, (![B_214, A_215]: (~r1_xboole_0(B_214, A_215) | r1_xboole_0(A_215, B_214))), inference(resolution, [status(thm)], [c_1559, c_729])).
% 4.78/1.95  tff(c_1621, plain, (![B_55, A_54]: (r1_xboole_0(B_55, k1_tarski(A_54)) | r2_hidden(A_54, B_55))), inference(resolution, [status(thm)], [c_46, c_1610])).
% 4.78/1.95  tff(c_735, plain, (![A_144, C_145, B_146]: (r1_tarski(A_144, k2_xboole_0(C_145, B_146)) | ~r1_tarski(A_144, B_146))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.78/1.95  tff(c_795, plain, (![A_152]: (r1_tarski(A_152, k1_tarski('#skF_3')) | ~r1_tarski(A_152, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_735])).
% 4.78/1.96  tff(c_22, plain, (![A_18, B_19]: (k2_xboole_0(A_18, B_19)=B_19 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.78/1.96  tff(c_1656, plain, (![A_218]: (k2_xboole_0(A_218, k1_tarski('#skF_3'))=k1_tarski('#skF_3') | ~r1_tarski(A_218, '#skF_5'))), inference(resolution, [status(thm)], [c_795, c_22])).
% 4.78/1.96  tff(c_26, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.78/1.96  tff(c_545, plain, (![A_116, B_117]: (k3_xboole_0(A_116, B_117)=A_116 | ~r1_tarski(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.78/1.96  tff(c_556, plain, (![A_22, B_23]: (k3_xboole_0(A_22, k2_xboole_0(A_22, B_23))=A_22)), inference(resolution, [status(thm)], [c_26, c_545])).
% 4.78/1.96  tff(c_767, plain, (![A_149, B_150]: (~r1_xboole_0(A_149, B_150) | v1_xboole_0(k3_xboole_0(A_149, B_150)))), inference(resolution, [status(thm)], [c_6, c_714])).
% 4.78/1.96  tff(c_773, plain, (![A_22, B_23]: (~r1_xboole_0(A_22, k2_xboole_0(A_22, B_23)) | v1_xboole_0(A_22))), inference(superposition, [status(thm), theory('equality')], [c_556, c_767])).
% 4.78/1.96  tff(c_2521, plain, (![A_278]: (~r1_xboole_0(A_278, k1_tarski('#skF_3')) | v1_xboole_0(A_278) | ~r1_tarski(A_278, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1656, c_773])).
% 4.78/1.96  tff(c_2549, plain, (![B_55]: (v1_xboole_0(B_55) | ~r1_tarski(B_55, '#skF_5') | r2_hidden('#skF_3', B_55))), inference(resolution, [status(thm)], [c_1621, c_2521])).
% 4.78/1.96  tff(c_756, plain, (![A_144]: (r1_tarski(A_144, k1_tarski('#skF_3')) | ~r1_tarski(A_144, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_735])).
% 4.78/1.96  tff(c_692, plain, (![B_139, A_140]: (B_139=A_140 | ~r1_tarski(B_139, A_140) | ~r1_tarski(A_140, B_139))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.78/1.96  tff(c_3289, plain, (![A_299, B_300]: (k1_tarski(A_299)=B_300 | ~r1_tarski(B_300, k1_tarski(A_299)) | ~r2_hidden(A_299, B_300))), inference(resolution, [status(thm)], [c_44, c_692])).
% 4.78/1.96  tff(c_3312, plain, (![A_301]: (k1_tarski('#skF_3')=A_301 | ~r2_hidden('#skF_3', A_301) | ~r1_tarski(A_301, '#skF_5'))), inference(resolution, [status(thm)], [c_756, c_3289])).
% 4.78/1.96  tff(c_3352, plain, (![B_302]: (k1_tarski('#skF_3')=B_302 | v1_xboole_0(B_302) | ~r1_tarski(B_302, '#skF_5'))), inference(resolution, [status(thm)], [c_2549, c_3312])).
% 4.78/1.96  tff(c_3360, plain, (k1_tarski('#skF_3')='#skF_5' | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_18, c_3352])).
% 4.78/1.96  tff(c_3366, plain, (v1_xboole_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_488, c_3360])).
% 4.78/1.96  tff(c_489, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_52])).
% 4.78/1.96  tff(c_490, plain, (![A_7]: (A_7='#skF_4' | ~v1_xboole_0(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_489, c_8])).
% 4.78/1.96  tff(c_3370, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_3366, c_490])).
% 4.78/1.96  tff(c_3387, plain, (k2_xboole_0('#skF_4', '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3370, c_56])).
% 4.78/1.96  tff(c_3389, plain, (k1_tarski('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_630, c_3387])).
% 4.78/1.96  tff(c_3391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_3389])).
% 4.78/1.96  tff(c_3392, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_50])).
% 4.78/1.96  tff(c_3393, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_50])).
% 4.78/1.96  tff(c_3395, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3393, c_56])).
% 4.78/1.96  tff(c_3836, plain, (![A_347, C_348, B_349]: (r1_tarski(A_347, k2_xboole_0(C_348, B_349)) | ~r1_tarski(A_347, B_349))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.78/1.96  tff(c_3861, plain, (![A_350]: (r1_tarski(A_350, '#skF_4') | ~r1_tarski(A_350, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3395, c_3836])).
% 4.78/1.96  tff(c_3950, plain, (![A_354]: (r1_tarski(k1_tarski(A_354), '#skF_4') | ~r2_hidden(A_354, '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_3861])).
% 4.78/1.96  tff(c_42, plain, (![A_52, B_53]: (r2_hidden(A_52, B_53) | ~r1_tarski(k1_tarski(A_52), B_53))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.78/1.96  tff(c_3985, plain, (![A_357]: (r2_hidden(A_357, '#skF_4') | ~r2_hidden(A_357, '#skF_5'))), inference(resolution, [status(thm)], [c_3950, c_42])).
% 4.78/1.96  tff(c_4002, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_6, c_3985])).
% 4.78/1.96  tff(c_4028, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_4002])).
% 4.78/1.96  tff(c_4050, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_4028, c_8])).
% 4.78/1.96  tff(c_4054, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3392, c_4050])).
% 4.78/1.96  tff(c_4056, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_4002])).
% 4.78/1.96  tff(c_54, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.78/1.96  tff(c_3422, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3393, c_3393, c_54])).
% 4.78/1.96  tff(c_3871, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_18, c_3861])).
% 4.78/1.96  tff(c_4004, plain, (![B_358, A_359]: (B_358=A_359 | ~r1_tarski(B_358, A_359) | ~r1_tarski(A_359, B_358))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.78/1.96  tff(c_4008, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_3871, c_4004])).
% 4.78/1.96  tff(c_4020, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_3422, c_4008])).
% 4.78/1.96  tff(c_3598, plain, (![A_329, B_330]: (r1_xboole_0(k1_tarski(A_329), B_330) | r2_hidden(A_329, B_330))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.78/1.96  tff(c_3602, plain, (![B_331]: (r1_xboole_0('#skF_4', B_331) | r2_hidden('#skF_3', B_331))), inference(superposition, [status(thm), theory('equality')], [c_3393, c_3598])).
% 4.78/1.96  tff(c_3548, plain, (![A_325, B_326]: (r1_tarski(k1_tarski(A_325), B_326) | ~r2_hidden(A_325, B_326))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.78/1.96  tff(c_3557, plain, (![B_326]: (r1_tarski('#skF_4', B_326) | ~r2_hidden('#skF_3', B_326))), inference(superposition, [status(thm), theory('equality')], [c_3393, c_3548])).
% 4.78/1.96  tff(c_3609, plain, (![B_331]: (r1_tarski('#skF_4', B_331) | r1_xboole_0('#skF_4', B_331))), inference(resolution, [status(thm)], [c_3602, c_3557])).
% 4.78/1.96  tff(c_24, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.78/1.96  tff(c_3879, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_3871, c_24])).
% 4.78/1.96  tff(c_3907, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2, c_3879])).
% 4.78/1.96  tff(c_12, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.78/1.96  tff(c_3945, plain, (![C_12]: (~r1_xboole_0('#skF_4', '#skF_5') | ~r2_hidden(C_12, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3907, c_12])).
% 4.78/1.96  tff(c_4061, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_3945])).
% 4.78/1.96  tff(c_4064, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_3609, c_4061])).
% 4.78/1.96  tff(c_4071, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4020, c_4064])).
% 4.78/1.96  tff(c_4083, plain, (![C_365]: (~r2_hidden(C_365, '#skF_5'))), inference(splitRight, [status(thm)], [c_3945])).
% 4.78/1.96  tff(c_4095, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_6, c_4083])).
% 4.78/1.96  tff(c_4101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4056, c_4095])).
% 4.78/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.96  
% 4.78/1.96  Inference rules
% 4.78/1.96  ----------------------
% 4.78/1.96  #Ref     : 0
% 4.78/1.96  #Sup     : 964
% 4.78/1.96  #Fact    : 0
% 4.78/1.96  #Define  : 0
% 4.78/1.96  #Split   : 10
% 4.78/1.96  #Chain   : 0
% 4.78/1.96  #Close   : 0
% 4.78/1.96  
% 4.78/1.96  Ordering : KBO
% 4.78/1.96  
% 4.78/1.96  Simplification rules
% 4.78/1.96  ----------------------
% 4.78/1.96  #Subsume      : 258
% 4.78/1.96  #Demod        : 269
% 4.78/1.96  #Tautology    : 412
% 4.78/1.96  #SimpNegUnit  : 54
% 4.78/1.96  #BackRed      : 28
% 4.78/1.96  
% 4.78/1.96  #Partial instantiations: 0
% 4.78/1.96  #Strategies tried      : 1
% 4.78/1.96  
% 4.78/1.96  Timing (in seconds)
% 4.78/1.96  ----------------------
% 4.78/1.96  Preprocessing        : 0.36
% 4.78/1.96  Parsing              : 0.19
% 4.78/1.96  CNF conversion       : 0.02
% 4.78/1.96  Main loop            : 0.75
% 4.78/1.96  Inferencing          : 0.28
% 4.78/1.96  Reduction            : 0.24
% 4.78/1.96  Demodulation         : 0.17
% 4.78/1.96  BG Simplification    : 0.03
% 4.78/1.96  Subsumption          : 0.14
% 4.78/1.96  Abstraction          : 0.03
% 4.78/1.96  MUC search           : 0.00
% 4.78/1.96  Cooper               : 0.00
% 4.78/1.96  Total                : 1.15
% 4.78/1.96  Index Insertion      : 0.00
% 4.78/1.96  Index Deletion       : 0.00
% 4.78/1.96  Index Matching       : 0.00
% 4.78/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
