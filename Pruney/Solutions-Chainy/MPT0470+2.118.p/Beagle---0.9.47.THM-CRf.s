%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:17 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 221 expanded)
%              Number of leaves         :   40 (  92 expanded)
%              Depth                    :   15
%              Number of atoms          :  164 ( 400 expanded)
%              Number of equality atoms :   46 ( 101 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_108,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_50,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_90,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_52,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_28,plain,(
    ! [A_34] :
      ( r2_hidden('#skF_1'(A_34),A_34)
      | v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_136,plain,(
    ! [A_80,C_81,B_82] :
      ( ~ r2_hidden(A_80,C_81)
      | ~ r1_xboole_0(k2_tarski(A_80,B_82),C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_151,plain,(
    ! [A_86] : ~ r2_hidden(A_86,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_136])).

tff(c_156,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_151])).

tff(c_32,plain,(
    ! [A_53,B_54] :
      ( v1_relat_1(k5_relat_1(A_53,B_54))
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_366,plain,(
    ! [A_110,B_111] :
      ( k1_relat_1(k5_relat_1(A_110,B_111)) = k1_relat_1(A_110)
      | ~ r1_tarski(k2_relat_1(A_110),k1_relat_1(B_111))
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_378,plain,(
    ! [B_111] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_111)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_111))
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_366])).

tff(c_383,plain,(
    ! [B_112] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_112)) = k1_xboole_0
      | ~ v1_relat_1(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_6,c_48,c_378])).

tff(c_34,plain,(
    ! [A_55] :
      ( ~ v1_xboole_0(k1_relat_1(A_55))
      | ~ v1_relat_1(A_55)
      | v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_392,plain,(
    ! [B_112] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_112))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_112))
      | ~ v1_relat_1(B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_34])).

tff(c_403,plain,(
    ! [B_113] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_113))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_113))
      | ~ v1_relat_1(B_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_392])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_411,plain,(
    ! [B_114] :
      ( k5_relat_1(k1_xboole_0,B_114) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_114))
      | ~ v1_relat_1(B_114) ) ),
    inference(resolution,[status(thm)],[c_403,c_4])).

tff(c_421,plain,(
    ! [B_54] :
      ( k5_relat_1(k1_xboole_0,B_54) = k1_xboole_0
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_411])).

tff(c_470,plain,(
    ! [B_121] :
      ( k5_relat_1(k1_xboole_0,B_121) = k1_xboole_0
      | ~ v1_relat_1(B_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_421])).

tff(c_485,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_470])).

tff(c_494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_485])).

tff(c_495,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_30,plain,(
    ! [A_52] :
      ( v1_relat_1(k4_relat_1(A_52))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_545,plain,(
    ! [A_131,C_132,B_133] :
      ( ~ r2_hidden(A_131,C_132)
      | ~ r1_xboole_0(k2_tarski(A_131,B_133),C_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_551,plain,(
    ! [A_134] : ~ r2_hidden(A_134,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_545])).

tff(c_556,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_551])).

tff(c_509,plain,(
    ! [A_127] :
      ( k1_relat_1(k4_relat_1(A_127)) = k2_relat_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_581,plain,(
    ! [A_144] :
      ( ~ v1_xboole_0(k2_relat_1(A_144))
      | ~ v1_relat_1(k4_relat_1(A_144))
      | v1_xboole_0(k4_relat_1(A_144))
      | ~ v1_relat_1(A_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_509,c_34])).

tff(c_589,plain,(
    ! [A_145] :
      ( k4_relat_1(A_145) = k1_xboole_0
      | ~ v1_xboole_0(k2_relat_1(A_145))
      | ~ v1_relat_1(k4_relat_1(A_145))
      | ~ v1_relat_1(A_145) ) ),
    inference(resolution,[status(thm)],[c_581,c_4])).

tff(c_595,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_589])).

tff(c_597,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_2,c_595])).

tff(c_598,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_597])).

tff(c_610,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_598])).

tff(c_614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_610])).

tff(c_615,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_597])).

tff(c_790,plain,(
    ! [A_168,B_169] :
      ( k1_relat_1(k5_relat_1(A_168,B_169)) = k1_relat_1(A_168)
      | ~ r1_tarski(k2_relat_1(A_168),k1_relat_1(B_169))
      | ~ v1_relat_1(B_169)
      | ~ v1_relat_1(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_802,plain,(
    ! [B_169] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_169)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_169))
      | ~ v1_relat_1(B_169)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_790])).

tff(c_807,plain,(
    ! [B_170] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_170)) = k1_xboole_0
      | ~ v1_relat_1(B_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_6,c_48,c_802])).

tff(c_816,plain,(
    ! [B_170] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_170))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_170))
      | ~ v1_relat_1(B_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_807,c_34])).

tff(c_832,plain,(
    ! [B_171] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_171))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_171))
      | ~ v1_relat_1(B_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_816])).

tff(c_845,plain,(
    ! [B_172] :
      ( k5_relat_1(k1_xboole_0,B_172) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_172))
      | ~ v1_relat_1(B_172) ) ),
    inference(resolution,[status(thm)],[c_832,c_4])).

tff(c_855,plain,(
    ! [B_54] :
      ( k5_relat_1(k1_xboole_0,B_54) = k1_xboole_0
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_845])).

tff(c_900,plain,(
    ! [B_173] :
      ( k5_relat_1(k1_xboole_0,B_173) = k1_xboole_0
      | ~ v1_relat_1(B_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_855])).

tff(c_920,plain,(
    ! [A_52] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_52)) = k1_xboole_0
      | ~ v1_relat_1(A_52) ) ),
    inference(resolution,[status(thm)],[c_30,c_900])).

tff(c_36,plain,(
    ! [A_56] :
      ( k4_relat_1(k4_relat_1(A_56)) = A_56
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_656,plain,(
    ! [B_156,A_157] :
      ( k5_relat_1(k4_relat_1(B_156),k4_relat_1(A_157)) = k4_relat_1(k5_relat_1(A_157,B_156))
      | ~ v1_relat_1(B_156)
      | ~ v1_relat_1(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_671,plain,(
    ! [B_156] :
      ( k5_relat_1(k4_relat_1(B_156),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,B_156))
      | ~ v1_relat_1(B_156)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_656])).

tff(c_736,plain,(
    ! [B_159] :
      ( k5_relat_1(k4_relat_1(B_159),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,B_159))
      | ~ v1_relat_1(B_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_671])).

tff(c_1384,plain,(
    ! [A_198] :
      ( k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(A_198))) = k5_relat_1(A_198,k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_198))
      | ~ v1_relat_1(A_198) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_736])).

tff(c_1447,plain,(
    ! [A_52] :
      ( k5_relat_1(A_52,k1_xboole_0) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_52))
      | ~ v1_relat_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_920,c_1384])).

tff(c_1467,plain,(
    ! [A_199] :
      ( k5_relat_1(A_199,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_199))
      | ~ v1_relat_1(A_199)
      | ~ v1_relat_1(A_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_615,c_1447])).

tff(c_1500,plain,(
    ! [A_200] :
      ( k5_relat_1(A_200,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_200) ) ),
    inference(resolution,[status(thm)],[c_30,c_1467])).

tff(c_1521,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_1500])).

tff(c_1532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_495,c_1521])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:10:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.59  
% 3.23/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.59  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.23/1.59  
% 3.23/1.59  %Foreground sorts:
% 3.23/1.59  
% 3.23/1.59  
% 3.23/1.59  %Background operators:
% 3.23/1.59  
% 3.23/1.59  
% 3.23/1.59  %Foreground operators:
% 3.23/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.23/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.23/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.59  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.23/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.23/1.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.23/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.23/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.23/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.23/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.23/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.23/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.23/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.23/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.23/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.23/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.23/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.23/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.23/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.23/1.59  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.23/1.59  
% 3.23/1.61  tff(f_115, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.23/1.61  tff(f_61, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 3.23/1.61  tff(f_34, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.23/1.61  tff(f_51, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 3.23/1.61  tff(f_71, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.23/1.61  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.23/1.61  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.23/1.61  tff(f_108, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.23/1.61  tff(f_98, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 3.23/1.61  tff(f_79, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 3.23/1.61  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.23/1.61  tff(f_65, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.23/1.61  tff(f_89, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 3.23/1.61  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 3.23/1.61  tff(f_105, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 3.23/1.61  tff(c_50, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.23/1.61  tff(c_90, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 3.23/1.61  tff(c_52, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.23/1.61  tff(c_28, plain, (![A_34]: (r2_hidden('#skF_1'(A_34), A_34) | v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.23/1.61  tff(c_8, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.23/1.61  tff(c_136, plain, (![A_80, C_81, B_82]: (~r2_hidden(A_80, C_81) | ~r1_xboole_0(k2_tarski(A_80, B_82), C_81))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.23/1.61  tff(c_151, plain, (![A_86]: (~r2_hidden(A_86, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_136])).
% 3.23/1.61  tff(c_156, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_151])).
% 3.23/1.61  tff(c_32, plain, (![A_53, B_54]: (v1_relat_1(k5_relat_1(A_53, B_54)) | ~v1_relat_1(B_54) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.23/1.61  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.23/1.61  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.23/1.61  tff(c_48, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.23/1.61  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.23/1.61  tff(c_366, plain, (![A_110, B_111]: (k1_relat_1(k5_relat_1(A_110, B_111))=k1_relat_1(A_110) | ~r1_tarski(k2_relat_1(A_110), k1_relat_1(B_111)) | ~v1_relat_1(B_111) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/1.61  tff(c_378, plain, (![B_111]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_111))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_111)) | ~v1_relat_1(B_111) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_366])).
% 3.23/1.61  tff(c_383, plain, (![B_112]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_112))=k1_xboole_0 | ~v1_relat_1(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_6, c_48, c_378])).
% 3.23/1.61  tff(c_34, plain, (![A_55]: (~v1_xboole_0(k1_relat_1(A_55)) | ~v1_relat_1(A_55) | v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.23/1.61  tff(c_392, plain, (![B_112]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_112)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_112)) | ~v1_relat_1(B_112))), inference(superposition, [status(thm), theory('equality')], [c_383, c_34])).
% 3.23/1.61  tff(c_403, plain, (![B_113]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_113)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_113)) | ~v1_relat_1(B_113))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_392])).
% 3.23/1.61  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.23/1.61  tff(c_411, plain, (![B_114]: (k5_relat_1(k1_xboole_0, B_114)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_114)) | ~v1_relat_1(B_114))), inference(resolution, [status(thm)], [c_403, c_4])).
% 3.23/1.61  tff(c_421, plain, (![B_54]: (k5_relat_1(k1_xboole_0, B_54)=k1_xboole_0 | ~v1_relat_1(B_54) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_411])).
% 3.23/1.61  tff(c_470, plain, (![B_121]: (k5_relat_1(k1_xboole_0, B_121)=k1_xboole_0 | ~v1_relat_1(B_121))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_421])).
% 3.23/1.61  tff(c_485, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_470])).
% 3.23/1.61  tff(c_494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_485])).
% 3.23/1.61  tff(c_495, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 3.23/1.61  tff(c_30, plain, (![A_52]: (v1_relat_1(k4_relat_1(A_52)) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.23/1.61  tff(c_545, plain, (![A_131, C_132, B_133]: (~r2_hidden(A_131, C_132) | ~r1_xboole_0(k2_tarski(A_131, B_133), C_132))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.23/1.61  tff(c_551, plain, (![A_134]: (~r2_hidden(A_134, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_545])).
% 3.23/1.61  tff(c_556, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_551])).
% 3.23/1.61  tff(c_509, plain, (![A_127]: (k1_relat_1(k4_relat_1(A_127))=k2_relat_1(A_127) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.23/1.61  tff(c_581, plain, (![A_144]: (~v1_xboole_0(k2_relat_1(A_144)) | ~v1_relat_1(k4_relat_1(A_144)) | v1_xboole_0(k4_relat_1(A_144)) | ~v1_relat_1(A_144))), inference(superposition, [status(thm), theory('equality')], [c_509, c_34])).
% 3.23/1.61  tff(c_589, plain, (![A_145]: (k4_relat_1(A_145)=k1_xboole_0 | ~v1_xboole_0(k2_relat_1(A_145)) | ~v1_relat_1(k4_relat_1(A_145)) | ~v1_relat_1(A_145))), inference(resolution, [status(thm)], [c_581, c_4])).
% 3.23/1.61  tff(c_595, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_589])).
% 3.23/1.61  tff(c_597, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_556, c_2, c_595])).
% 3.23/1.61  tff(c_598, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_597])).
% 3.23/1.61  tff(c_610, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_598])).
% 3.23/1.61  tff(c_614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_556, c_610])).
% 3.23/1.61  tff(c_615, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_597])).
% 3.23/1.61  tff(c_790, plain, (![A_168, B_169]: (k1_relat_1(k5_relat_1(A_168, B_169))=k1_relat_1(A_168) | ~r1_tarski(k2_relat_1(A_168), k1_relat_1(B_169)) | ~v1_relat_1(B_169) | ~v1_relat_1(A_168))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/1.61  tff(c_802, plain, (![B_169]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_169))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_169)) | ~v1_relat_1(B_169) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_790])).
% 3.23/1.61  tff(c_807, plain, (![B_170]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_170))=k1_xboole_0 | ~v1_relat_1(B_170))), inference(demodulation, [status(thm), theory('equality')], [c_556, c_6, c_48, c_802])).
% 3.23/1.61  tff(c_816, plain, (![B_170]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_170)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_170)) | ~v1_relat_1(B_170))), inference(superposition, [status(thm), theory('equality')], [c_807, c_34])).
% 3.23/1.61  tff(c_832, plain, (![B_171]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_171)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_171)) | ~v1_relat_1(B_171))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_816])).
% 3.23/1.61  tff(c_845, plain, (![B_172]: (k5_relat_1(k1_xboole_0, B_172)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_172)) | ~v1_relat_1(B_172))), inference(resolution, [status(thm)], [c_832, c_4])).
% 3.23/1.61  tff(c_855, plain, (![B_54]: (k5_relat_1(k1_xboole_0, B_54)=k1_xboole_0 | ~v1_relat_1(B_54) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_845])).
% 3.23/1.61  tff(c_900, plain, (![B_173]: (k5_relat_1(k1_xboole_0, B_173)=k1_xboole_0 | ~v1_relat_1(B_173))), inference(demodulation, [status(thm), theory('equality')], [c_556, c_855])).
% 3.23/1.61  tff(c_920, plain, (![A_52]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_52))=k1_xboole_0 | ~v1_relat_1(A_52))), inference(resolution, [status(thm)], [c_30, c_900])).
% 3.23/1.61  tff(c_36, plain, (![A_56]: (k4_relat_1(k4_relat_1(A_56))=A_56 | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.23/1.61  tff(c_656, plain, (![B_156, A_157]: (k5_relat_1(k4_relat_1(B_156), k4_relat_1(A_157))=k4_relat_1(k5_relat_1(A_157, B_156)) | ~v1_relat_1(B_156) | ~v1_relat_1(A_157))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.23/1.61  tff(c_671, plain, (![B_156]: (k5_relat_1(k4_relat_1(B_156), k1_xboole_0)=k4_relat_1(k5_relat_1(k1_xboole_0, B_156)) | ~v1_relat_1(B_156) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_615, c_656])).
% 3.23/1.61  tff(c_736, plain, (![B_159]: (k5_relat_1(k4_relat_1(B_159), k1_xboole_0)=k4_relat_1(k5_relat_1(k1_xboole_0, B_159)) | ~v1_relat_1(B_159))), inference(demodulation, [status(thm), theory('equality')], [c_556, c_671])).
% 3.23/1.61  tff(c_1384, plain, (![A_198]: (k4_relat_1(k5_relat_1(k1_xboole_0, k4_relat_1(A_198)))=k5_relat_1(A_198, k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_198)) | ~v1_relat_1(A_198))), inference(superposition, [status(thm), theory('equality')], [c_36, c_736])).
% 3.23/1.61  tff(c_1447, plain, (![A_52]: (k5_relat_1(A_52, k1_xboole_0)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_52)) | ~v1_relat_1(A_52) | ~v1_relat_1(A_52))), inference(superposition, [status(thm), theory('equality')], [c_920, c_1384])).
% 3.23/1.61  tff(c_1467, plain, (![A_199]: (k5_relat_1(A_199, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_199)) | ~v1_relat_1(A_199) | ~v1_relat_1(A_199))), inference(demodulation, [status(thm), theory('equality')], [c_615, c_1447])).
% 3.23/1.61  tff(c_1500, plain, (![A_200]: (k5_relat_1(A_200, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_200))), inference(resolution, [status(thm)], [c_30, c_1467])).
% 3.23/1.61  tff(c_1521, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_1500])).
% 3.23/1.61  tff(c_1532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_495, c_1521])).
% 3.23/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.61  
% 3.23/1.61  Inference rules
% 3.23/1.61  ----------------------
% 3.23/1.61  #Ref     : 2
% 3.23/1.61  #Sup     : 345
% 3.23/1.61  #Fact    : 0
% 3.23/1.61  #Define  : 0
% 3.23/1.61  #Split   : 3
% 3.23/1.61  #Chain   : 0
% 3.23/1.61  #Close   : 0
% 3.23/1.61  
% 3.23/1.61  Ordering : KBO
% 3.23/1.61  
% 3.23/1.61  Simplification rules
% 3.23/1.61  ----------------------
% 3.23/1.61  #Subsume      : 11
% 3.23/1.61  #Demod        : 343
% 3.23/1.61  #Tautology    : 196
% 3.23/1.61  #SimpNegUnit  : 2
% 3.23/1.61  #BackRed      : 4
% 3.23/1.61  
% 3.23/1.61  #Partial instantiations: 0
% 3.23/1.61  #Strategies tried      : 1
% 3.23/1.61  
% 3.23/1.61  Timing (in seconds)
% 3.23/1.61  ----------------------
% 3.23/1.62  Preprocessing        : 0.35
% 3.23/1.62  Parsing              : 0.19
% 3.23/1.62  CNF conversion       : 0.02
% 3.23/1.62  Main loop            : 0.44
% 3.23/1.62  Inferencing          : 0.17
% 3.23/1.62  Reduction            : 0.13
% 3.23/1.62  Demodulation         : 0.09
% 3.23/1.62  BG Simplification    : 0.03
% 3.61/1.62  Subsumption          : 0.08
% 3.61/1.62  Abstraction          : 0.02
% 3.61/1.62  MUC search           : 0.00
% 3.61/1.62  Cooper               : 0.00
% 3.61/1.62  Total                : 0.83
% 3.61/1.62  Index Insertion      : 0.00
% 3.61/1.62  Index Deletion       : 0.00
% 3.61/1.62  Index Matching       : 0.00
% 3.61/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
