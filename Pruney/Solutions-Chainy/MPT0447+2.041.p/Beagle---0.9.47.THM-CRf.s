%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:33 EST 2020

% Result     : Theorem 22.60s
% Output     : CNFRefutation 22.84s
% Verified   : 
% Statistics : Number of formulae       :  175 (1512 expanded)
%              Number of leaves         :   49 ( 528 expanded)
%              Depth                    :   38
%              Number of atoms          :  291 (2825 expanded)
%              Number of equality atoms :   63 ( 617 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_10 > #skF_9 > #skF_3 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(r2_tarski,type,(
    r2_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_174,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_164,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_146,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_71,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_132,axiom,(
    ! [A] :
    ? [B] :
      ( r2_hidden(A,B)
      & ! [C,D] :
          ( ( r2_hidden(C,B)
            & r1_tarski(D,C) )
         => r2_hidden(D,B) )
      & ! [C] :
          ~ ( r2_hidden(C,B)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & ! [E] :
                      ( r1_tarski(E,C)
                     => r2_hidden(E,D) ) ) )
      & ! [C] :
          ~ ( r1_tarski(C,B)
            & ~ r2_tarski(C,B)
            & ~ r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tarski)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_142,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_134,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_153,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

tff(c_80,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_78,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_76,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_70,plain,(
    ! [A_105,B_107] :
      ( r1_tarski(k2_relat_1(A_105),k2_relat_1(B_107))
      | ~ r1_tarski(A_105,B_107)
      | ~ v1_relat_1(B_107)
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_205,plain,(
    ! [A_143] :
      ( k2_xboole_0(k1_relat_1(A_143),k2_relat_1(A_143)) = k3_relat_1(A_143)
      | ~ v1_relat_1(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_18,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_tarski(A_12,k2_xboole_0(C_14,B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_211,plain,(
    ! [A_12,A_143] :
      ( r1_tarski(A_12,k3_relat_1(A_143))
      | ~ r1_tarski(A_12,k2_relat_1(A_143))
      | ~ v1_relat_1(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_18])).

tff(c_72,plain,(
    ! [A_105,B_107] :
      ( r1_tarski(k1_relat_1(A_105),k1_relat_1(B_107))
      | ~ r1_tarski(A_105,B_107)
      | ~ v1_relat_1(B_107)
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_26,plain,(
    ! [A_21,B_22,C_23] : k4_xboole_0(k4_xboole_0(A_21,B_22),C_23) = k4_xboole_0(A_21,k2_xboole_0(B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    ! [A_19,B_20] : r1_tarski(k4_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_704,plain,(
    ! [A_198,C_199,B_200] :
      ( r1_tarski(k2_xboole_0(A_198,C_199),B_200)
      | ~ r1_tarski(C_199,B_200)
      | ~ r1_tarski(A_198,B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_442,plain,(
    ! [A_171,B_172,C_173] :
      ( r1_tarski(A_171,k2_xboole_0(B_172,C_173))
      | ~ r1_tarski(k4_xboole_0(A_171,B_172),C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_478,plain,(
    ! [A_174,B_175] : r1_tarski(A_174,k2_xboole_0(B_175,A_174)) ),
    inference(resolution,[status(thm)],[c_24,c_442])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_502,plain,(
    ! [B_175,A_174] :
      ( k2_xboole_0(B_175,A_174) = A_174
      | ~ r1_tarski(k2_xboole_0(B_175,A_174),A_174) ) ),
    inference(resolution,[status(thm)],[c_478,c_12])).

tff(c_716,plain,(
    ! [A_198,B_200] :
      ( k2_xboole_0(A_198,B_200) = B_200
      | ~ r1_tarski(B_200,B_200)
      | ~ r1_tarski(A_198,B_200) ) ),
    inference(resolution,[status(thm)],[c_704,c_502])).

tff(c_761,plain,(
    ! [A_201,B_202] :
      ( k2_xboole_0(A_201,B_202) = B_202
      | ~ r1_tarski(A_201,B_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_716])).

tff(c_1086,plain,(
    ! [A_207,B_208] : k2_xboole_0(k4_xboole_0(A_207,B_208),A_207) = A_207 ),
    inference(resolution,[status(thm)],[c_24,c_761])).

tff(c_351,plain,(
    ! [A_163,B_164,C_165] : k4_xboole_0(k4_xboole_0(A_163,B_164),C_165) = k4_xboole_0(A_163,k2_xboole_0(B_164,C_165)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_366,plain,(
    ! [A_163,B_164,C_165] : r1_tarski(k4_xboole_0(A_163,k2_xboole_0(B_164,C_165)),k4_xboole_0(A_163,B_164)) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_24])).

tff(c_1127,plain,(
    ! [A_163,A_207,B_208] : r1_tarski(k4_xboole_0(A_163,A_207),k4_xboole_0(A_163,k4_xboole_0(A_207,B_208))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1086,c_366])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_477,plain,(
    ! [A_171,B_172] : r1_tarski(A_171,k2_xboole_0(B_172,k4_xboole_0(A_171,B_172))) ),
    inference(resolution,[status(thm)],[c_16,c_442])).

tff(c_14657,plain,(
    ! [A_539,C_540,B_541] :
      ( k2_xboole_0(A_539,C_540) = B_541
      | ~ r1_tarski(B_541,k2_xboole_0(A_539,C_540))
      | ~ r1_tarski(C_540,B_541)
      | ~ r1_tarski(A_539,B_541) ) ),
    inference(resolution,[status(thm)],[c_704,c_12])).

tff(c_14910,plain,(
    ! [B_172,A_171] :
      ( k2_xboole_0(B_172,k4_xboole_0(A_171,B_172)) = A_171
      | ~ r1_tarski(k4_xboole_0(A_171,B_172),A_171)
      | ~ r1_tarski(B_172,A_171) ) ),
    inference(resolution,[status(thm)],[c_477,c_14657])).

tff(c_15039,plain,(
    ! [B_542,A_543] :
      ( k2_xboole_0(B_542,k4_xboole_0(A_543,B_542)) = A_543
      | ~ r1_tarski(B_542,A_543) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_14910])).

tff(c_470,plain,(
    ! [A_163,B_164,C_165] : r1_tarski(A_163,k2_xboole_0(k2_xboole_0(B_164,C_165),k4_xboole_0(A_163,B_164))) ),
    inference(resolution,[status(thm)],[c_366,c_442])).

tff(c_21067,plain,(
    ! [A_638,A_639,B_640] :
      ( r1_tarski(A_638,k2_xboole_0(A_639,k4_xboole_0(A_638,B_640)))
      | ~ r1_tarski(B_640,A_639) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15039,c_470])).

tff(c_26077,plain,(
    ! [A_753,B_754] :
      ( r1_tarski(A_753,k4_xboole_0(A_753,B_754))
      | ~ r1_tarski(B_754,k4_xboole_0(A_753,B_754)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_21067])).

tff(c_26140,plain,(
    ! [B_755] : r1_tarski(B_755,k4_xboole_0(B_755,k4_xboole_0(B_755,B_755))) ),
    inference(resolution,[status(thm)],[c_1127,c_26077])).

tff(c_136,plain,(
    ! [B_133,A_134] :
      ( B_133 = A_134
      | ~ r1_tarski(B_133,A_134)
      | ~ r1_tarski(A_134,B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_148,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,k4_xboole_0(A_19,B_20)) ) ),
    inference(resolution,[status(thm)],[c_24,c_136])).

tff(c_26311,plain,(
    ! [B_756] : k4_xboole_0(B_756,k4_xboole_0(B_756,B_756)) = B_756 ),
    inference(resolution,[status(thm)],[c_26140,c_148])).

tff(c_26613,plain,(
    ! [B_756,B_208] : r1_tarski(B_756,k4_xboole_0(B_756,k4_xboole_0(k4_xboole_0(B_756,B_756),B_208))) ),
    inference(superposition,[status(thm),theory(equality)],[c_26311,c_1127])).

tff(c_27218,plain,(
    ! [B_760,B_761] : r1_tarski(B_760,k4_xboole_0(B_760,k4_xboole_0(B_760,k2_xboole_0(B_760,B_761)))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26613])).

tff(c_27483,plain,(
    ! [B_762,B_763] : k4_xboole_0(B_762,k4_xboole_0(B_762,k2_xboole_0(B_762,B_763))) = B_762 ),
    inference(resolution,[status(thm)],[c_27218,c_148])).

tff(c_34,plain,(
    ! [A_30,B_31] :
      ( r1_xboole_0(A_30,B_31)
      | k4_xboole_0(A_30,B_31) != A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1369,plain,(
    ! [A_219,B_220,C_221] :
      ( r1_tarski(A_219,B_220)
      | ~ r1_xboole_0(A_219,C_221)
      | ~ r1_tarski(A_219,k2_xboole_0(B_220,C_221)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1491,plain,(
    ! [A_229,B_230] :
      ( r1_tarski(A_229,B_230)
      | ~ r1_xboole_0(A_229,k4_xboole_0(A_229,B_230)) ) ),
    inference(resolution,[status(thm)],[c_477,c_1369])).

tff(c_1506,plain,(
    ! [A_30,B_230] :
      ( r1_tarski(A_30,B_230)
      | k4_xboole_0(A_30,k4_xboole_0(A_30,B_230)) != A_30 ) ),
    inference(resolution,[status(thm)],[c_34,c_1491])).

tff(c_28053,plain,(
    ! [B_762,B_763] : r1_tarski(B_762,k2_xboole_0(B_762,B_763)) ),
    inference(superposition,[status(thm),theory(equality)],[c_27483,c_1506])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,A_18) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_156,plain,(
    ! [A_135] :
      ( k1_xboole_0 = A_135
      | ~ r1_tarski(A_135,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_136])).

tff(c_169,plain,(
    ! [B_20] : k4_xboole_0(k1_xboole_0,B_20) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_156])).

tff(c_46,plain,(
    ! [A_39] : r2_hidden(A_39,'#skF_3'(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_185,plain,(
    ! [A_137,B_138,C_139] :
      ( ~ r1_xboole_0(A_137,B_138)
      | ~ r2_hidden(C_139,B_138)
      | ~ r2_hidden(C_139,A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2624,plain,(
    ! [C_288,B_289,A_290] :
      ( ~ r2_hidden(C_288,B_289)
      | ~ r2_hidden(C_288,A_290)
      | k4_xboole_0(A_290,B_289) != A_290 ) ),
    inference(resolution,[status(thm)],[c_34,c_185])).

tff(c_2664,plain,(
    ! [A_291,A_292] :
      ( ~ r2_hidden(A_291,A_292)
      | k4_xboole_0(A_292,'#skF_3'(A_291)) != A_292 ) ),
    inference(resolution,[status(thm)],[c_46,c_2624])).

tff(c_2674,plain,(
    ! [A_293] : ~ r2_hidden(A_293,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_2664])).

tff(c_2693,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_2674])).

tff(c_2990,plain,(
    ! [B_311,C_312] :
      ( r1_tarski(k2_xboole_0(B_311,C_312),B_311)
      | ~ r1_xboole_0(k2_xboole_0(B_311,C_312),C_312) ) ),
    inference(resolution,[status(thm)],[c_16,c_1369])).

tff(c_3106,plain,(
    ! [B_314] : r1_tarski(k2_xboole_0(B_314,k1_xboole_0),B_314) ),
    inference(resolution,[status(thm)],[c_2693,c_2990])).

tff(c_3172,plain,(
    ! [B_314] :
      ( k2_xboole_0(B_314,k1_xboole_0) = B_314
      | ~ r1_tarski(B_314,k2_xboole_0(B_314,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_3106,c_12])).

tff(c_28085,plain,(
    ! [B_314] : k2_xboole_0(B_314,k1_xboole_0) = B_314 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28053,c_3172])).

tff(c_10,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2807,plain,(
    ! [C_301,A_302] :
      ( r2_hidden(k4_tarski(C_301,'#skF_8'(A_302,k1_relat_1(A_302),C_301)),A_302)
      | ~ r2_hidden(C_301,k1_relat_1(A_302)) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2673,plain,(
    ! [A_291] : ~ r2_hidden(A_291,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_2664])).

tff(c_2824,plain,(
    ! [C_303] : ~ r2_hidden(C_303,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2807,c_2673])).

tff(c_2849,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_2824])).

tff(c_28086,plain,(
    ! [B_764,B_765] : r1_tarski(B_764,k2_xboole_0(B_764,B_765)) ),
    inference(superposition,[status(thm),theory(equality)],[c_27483,c_1506])).

tff(c_760,plain,(
    ! [A_198,C_199,B_200] :
      ( k2_xboole_0(A_198,C_199) = B_200
      | ~ r1_tarski(B_200,k2_xboole_0(A_198,C_199))
      | ~ r1_tarski(C_199,B_200)
      | ~ r1_tarski(A_198,B_200) ) ),
    inference(resolution,[status(thm)],[c_704,c_12])).

tff(c_28106,plain,(
    ! [B_764,B_765] :
      ( k2_xboole_0(B_764,B_765) = B_764
      | ~ r1_tarski(B_765,B_764)
      | ~ r1_tarski(B_764,B_764) ) ),
    inference(resolution,[status(thm)],[c_28086,c_760])).

tff(c_29267,plain,(
    ! [B_776,B_777] :
      ( k2_xboole_0(B_776,B_777) = B_776
      | ~ r1_tarski(B_777,B_776) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_28106])).

tff(c_29601,plain,(
    ! [A_19,B_20] : k2_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = A_19 ),
    inference(resolution,[status(thm)],[c_24,c_29267])).

tff(c_26294,plain,(
    ! [B_755] : k4_xboole_0(B_755,k4_xboole_0(B_755,B_755)) = B_755 ),
    inference(resolution,[status(thm)],[c_26140,c_148])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_47604,plain,(
    ! [A_1006,B_1007,A_1008] :
      ( ~ r2_hidden('#skF_1'(A_1006,B_1007),A_1008)
      | k4_xboole_0(A_1008,A_1006) != A_1008
      | r1_xboole_0(A_1006,B_1007) ) ),
    inference(resolution,[status(thm)],[c_8,c_2624])).

tff(c_47767,plain,(
    ! [B_1011,A_1012] :
      ( k4_xboole_0(B_1011,A_1012) != B_1011
      | r1_xboole_0(A_1012,B_1011) ) ),
    inference(resolution,[status(thm)],[c_6,c_47604])).

tff(c_822,plain,(
    ! [A_19,B_20] : k2_xboole_0(k4_xboole_0(A_19,B_20),A_19) = A_19 ),
    inference(resolution,[status(thm)],[c_24,c_761])).

tff(c_35406,plain,(
    ! [B_836,B_837] : k2_xboole_0(k2_xboole_0(B_836,B_837),B_836) = k2_xboole_0(B_836,B_837) ),
    inference(resolution,[status(thm)],[c_28053,c_29267])).

tff(c_189,plain,(
    ! [A_140,C_141,B_142] :
      ( r1_tarski(A_140,C_141)
      | ~ r1_tarski(B_142,C_141)
      | ~ r1_tarski(A_140,B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_203,plain,(
    ! [A_140] :
      ( r1_tarski(A_140,'#skF_10')
      | ~ r1_tarski(A_140,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_76,c_189])).

tff(c_638,plain,(
    ! [A_191,B_192] :
      ( r1_tarski(A_191,k2_xboole_0(B_192,'#skF_10'))
      | ~ r1_tarski(k4_xboole_0(A_191,B_192),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_203,c_442])).

tff(c_651,plain,(
    ! [B_20] : r1_tarski('#skF_9',k2_xboole_0(B_20,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_24,c_638])).

tff(c_1606,plain,(
    ! [B_236] : k2_xboole_0('#skF_9',k2_xboole_0(B_236,'#skF_10')) = k2_xboole_0(B_236,'#skF_10') ),
    inference(resolution,[status(thm)],[c_651,c_761])).

tff(c_1624,plain,(
    ! [A_163,B_236] : r1_tarski(A_163,k2_xboole_0(k2_xboole_0(B_236,'#skF_10'),k4_xboole_0(A_163,'#skF_9'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1606,c_470])).

tff(c_36082,plain,(
    ! [A_842] : r1_tarski(A_842,k2_xboole_0(k4_xboole_0(A_842,'#skF_9'),'#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35406,c_1624])).

tff(c_30,plain,(
    ! [A_27,B_28,C_29] :
      ( r1_tarski(A_27,B_28)
      | ~ r1_xboole_0(A_27,C_29)
      | ~ r1_tarski(A_27,k2_xboole_0(B_28,C_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42683,plain,(
    ! [A_924] :
      ( r1_tarski(A_924,k4_xboole_0(A_924,'#skF_9'))
      | ~ r1_xboole_0(A_924,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_36082,c_30])).

tff(c_28260,plain,(
    ! [B_764,B_765] :
      ( k2_xboole_0(B_764,B_765) = B_764
      | ~ r1_tarski(B_765,B_764) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_28106])).

tff(c_42704,plain,(
    ! [A_924] :
      ( k2_xboole_0(k4_xboole_0(A_924,'#skF_9'),A_924) = k4_xboole_0(A_924,'#skF_9')
      | ~ r1_xboole_0(A_924,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_42683,c_28260])).

tff(c_42803,plain,(
    ! [A_924] :
      ( k4_xboole_0(A_924,'#skF_9') = A_924
      | ~ r1_xboole_0(A_924,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_822,c_42704])).

tff(c_51929,plain,(
    ! [A_1052] :
      ( k4_xboole_0(A_1052,'#skF_9') = A_1052
      | k4_xboole_0('#skF_10',A_1052) != '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_47767,c_42803])).

tff(c_51958,plain,(
    k4_xboole_0(k4_xboole_0('#skF_10','#skF_10'),'#skF_9') = k4_xboole_0('#skF_10','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_26294,c_51929])).

tff(c_52450,plain,
    ( r1_tarski(k4_xboole_0('#skF_10','#skF_10'),'#skF_9')
    | k4_xboole_0(k4_xboole_0('#skF_10','#skF_10'),k4_xboole_0('#skF_10','#skF_10')) != k4_xboole_0('#skF_10','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_51958,c_1506])).

tff(c_52570,plain,(
    r1_tarski(k4_xboole_0('#skF_10','#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29601,c_26,c_52450])).

tff(c_1806,plain,(
    ! [A_242,C_243,B_244] :
      ( r1_tarski(A_242,C_243)
      | ~ r1_xboole_0(A_242,B_244)
      | ~ r1_tarski(A_242,B_244) ) ),
    inference(resolution,[status(thm)],[c_18,c_1369])).

tff(c_9569,plain,(
    ! [A_432,C_433,B_434] :
      ( r1_tarski(A_432,C_433)
      | ~ r1_tarski(A_432,B_434)
      | k4_xboole_0(A_432,B_434) != A_432 ) ),
    inference(resolution,[status(thm)],[c_34,c_1806])).

tff(c_9780,plain,(
    ! [A_140,C_433] :
      ( r1_tarski(A_140,C_433)
      | k4_xboole_0(A_140,'#skF_10') != A_140
      | ~ r1_tarski(A_140,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_203,c_9569])).

tff(c_52615,plain,(
    ! [C_433] :
      ( r1_tarski(k4_xboole_0('#skF_10','#skF_10'),C_433)
      | k4_xboole_0(k4_xboole_0('#skF_10','#skF_10'),'#skF_10') != k4_xboole_0('#skF_10','#skF_10') ) ),
    inference(resolution,[status(thm)],[c_52570,c_9780])).

tff(c_52678,plain,(
    ! [C_1056] : r1_tarski(k4_xboole_0('#skF_10','#skF_10'),C_1056) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_26,c_52615])).

tff(c_149,plain,(
    ! [A_18] :
      ( k1_xboole_0 = A_18
      | ~ r1_tarski(A_18,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_136])).

tff(c_52903,plain,(
    k4_xboole_0('#skF_10','#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52678,c_149])).

tff(c_52,plain,(
    ! [A_80,B_81] : k6_subset_1(A_80,B_81) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_68,plain,(
    ! [A_102,B_104] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_102),k1_relat_1(B_104)),k1_relat_1(k6_subset_1(A_102,B_104)))
      | ~ v1_relat_1(B_104)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2926,plain,(
    ! [A_306,B_307] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_306),k1_relat_1(B_307)),k1_relat_1(k4_xboole_0(A_306,B_307)))
      | ~ v1_relat_1(B_307)
      | ~ v1_relat_1(A_306) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_68])).

tff(c_2964,plain,(
    ! [A_306,B_307] :
      ( k4_xboole_0(k1_relat_1(A_306),k1_relat_1(B_307)) = k1_relat_1(k4_xboole_0(A_306,B_307))
      | ~ r1_tarski(k1_relat_1(k4_xboole_0(A_306,B_307)),k4_xboole_0(k1_relat_1(A_306),k1_relat_1(B_307)))
      | ~ v1_relat_1(B_307)
      | ~ v1_relat_1(A_306) ) ),
    inference(resolution,[status(thm)],[c_2926,c_12])).

tff(c_53015,plain,
    ( k4_xboole_0(k1_relat_1('#skF_10'),k1_relat_1('#skF_10')) = k1_relat_1(k4_xboole_0('#skF_10','#skF_10'))
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),k4_xboole_0(k1_relat_1('#skF_10'),k1_relat_1('#skF_10')))
    | ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_52903,c_2964])).

tff(c_53281,plain,(
    k4_xboole_0(k1_relat_1('#skF_10'),k1_relat_1('#skF_10')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_78,c_22,c_2849,c_2849,c_52903,c_53015])).

tff(c_66,plain,(
    ! [A_101] :
      ( k2_xboole_0(k1_relat_1(A_101),k2_relat_1(A_101)) = k3_relat_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_400,plain,(
    ! [A_168,B_169,C_170] : r1_tarski(k4_xboole_0(A_168,k2_xboole_0(B_169,C_170)),k4_xboole_0(A_168,B_169)) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_24])).

tff(c_419,plain,(
    ! [A_168,A_101] :
      ( r1_tarski(k4_xboole_0(A_168,k3_relat_1(A_101)),k4_xboole_0(A_168,k1_relat_1(A_101)))
      | ~ v1_relat_1(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_400])).

tff(c_54792,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1('#skF_10'),k3_relat_1('#skF_10')),k1_xboole_0)
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_53281,c_419])).

tff(c_55018,plain,(
    r1_tarski(k4_xboole_0(k1_relat_1('#skF_10'),k3_relat_1('#skF_10')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_54792])).

tff(c_56505,plain,
    ( k4_xboole_0(k1_relat_1('#skF_10'),k3_relat_1('#skF_10')) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k4_xboole_0(k1_relat_1('#skF_10'),k3_relat_1('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_55018,c_12])).

tff(c_56542,plain,(
    k4_xboole_0(k1_relat_1('#skF_10'),k3_relat_1('#skF_10')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_56505])).

tff(c_504,plain,(
    ! [A_176,B_177] : r1_tarski(A_176,k2_xboole_0(B_177,k4_xboole_0(A_176,B_177))) ),
    inference(resolution,[status(thm)],[c_16,c_442])).

tff(c_20,plain,(
    ! [A_15,C_17,B_16] :
      ( r1_tarski(A_15,C_17)
      | ~ r1_tarski(B_16,C_17)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_528,plain,(
    ! [A_15,B_177,A_176] :
      ( r1_tarski(A_15,k2_xboole_0(B_177,k4_xboole_0(A_176,B_177)))
      | ~ r1_tarski(A_15,A_176) ) ),
    inference(resolution,[status(thm)],[c_504,c_20])).

tff(c_56799,plain,(
    ! [A_15] :
      ( r1_tarski(A_15,k2_xboole_0(k3_relat_1('#skF_10'),k1_xboole_0))
      | ~ r1_tarski(A_15,k1_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56542,c_528])).

tff(c_73986,plain,(
    ! [A_1229] :
      ( r1_tarski(A_1229,k3_relat_1('#skF_10'))
      | ~ r1_tarski(A_1229,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28085,c_56799])).

tff(c_10896,plain,(
    ! [A_459,B_460] :
      ( r1_tarski(k3_relat_1(A_459),B_460)
      | ~ r1_tarski(k2_relat_1(A_459),B_460)
      | ~ r1_tarski(k1_relat_1(A_459),B_460)
      | ~ v1_relat_1(A_459) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_704])).

tff(c_74,plain,(
    ~ r1_tarski(k3_relat_1('#skF_9'),k3_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_10963,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),k3_relat_1('#skF_10'))
    | ~ r1_tarski(k1_relat_1('#skF_9'),k3_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_10896,c_74])).

tff(c_10988,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),k3_relat_1('#skF_10'))
    | ~ r1_tarski(k1_relat_1('#skF_9'),k3_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_10963])).

tff(c_11339,plain,(
    ~ r1_tarski(k1_relat_1('#skF_9'),k3_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_10988])).

tff(c_74194,plain,(
    ~ r1_tarski(k1_relat_1('#skF_9'),k1_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_73986,c_11339])).

tff(c_74218,plain,
    ( ~ r1_tarski('#skF_9','#skF_10')
    | ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_72,c_74194])).

tff(c_74222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74218])).

tff(c_74223,plain,(
    ~ r1_tarski(k2_relat_1('#skF_9'),k3_relat_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_10988])).

tff(c_74227,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),k2_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_211,c_74223])).

tff(c_74230,plain,(
    ~ r1_tarski(k2_relat_1('#skF_9'),k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74227])).

tff(c_74274,plain,
    ( ~ r1_tarski('#skF_9','#skF_10')
    | ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_74230])).

tff(c_74278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74274])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:04:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.60/13.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.73/13.36  
% 22.73/13.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.73/13.37  %$ r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_10 > #skF_9 > #skF_3 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 22.73/13.37  
% 22.73/13.37  %Foreground sorts:
% 22.73/13.37  
% 22.73/13.37  
% 22.73/13.37  %Background operators:
% 22.73/13.37  
% 22.73/13.37  
% 22.73/13.37  %Foreground operators:
% 22.73/13.37  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 22.73/13.37  tff(r2_tarski, type, r2_tarski: ($i * $i) > $o).
% 22.73/13.37  tff('#skF_2', type, '#skF_2': $i > $i).
% 22.73/13.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.73/13.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.73/13.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 22.73/13.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 22.73/13.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.73/13.37  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 22.73/13.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.73/13.37  tff('#skF_10', type, '#skF_10': $i).
% 22.73/13.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 22.73/13.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.73/13.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 22.73/13.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 22.73/13.37  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 22.73/13.37  tff('#skF_9', type, '#skF_9': $i).
% 22.73/13.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.73/13.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 22.73/13.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 22.73/13.37  tff('#skF_3', type, '#skF_3': $i > $i).
% 22.73/13.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.73/13.37  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 22.73/13.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 22.73/13.37  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 22.73/13.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 22.73/13.37  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 22.73/13.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 22.73/13.37  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 22.73/13.37  
% 22.84/13.39  tff(f_174, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 22.84/13.39  tff(f_164, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 22.84/13.39  tff(f_146, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 22.84/13.39  tff(f_63, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 22.84/13.39  tff(f_75, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 22.84/13.39  tff(f_73, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 22.84/13.39  tff(f_59, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 22.84/13.39  tff(f_95, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 22.84/13.39  tff(f_79, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 22.84/13.39  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 22.84/13.39  tff(f_89, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 22.84/13.39  tff(f_85, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 22.84/13.39  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 22.84/13.39  tff(f_71, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 22.84/13.39  tff(f_132, axiom, (![A]: (?[B]: (((r2_hidden(A, B) & (![C, D]: ((r2_hidden(C, B) & r1_tarski(D, C)) => r2_hidden(D, B)))) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & (![E]: (r1_tarski(E, C) => r2_hidden(E, D)))))))) & (![C]: ~((r1_tarski(C, B) & ~r2_tarski(C, B)) & ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_tarski)).
% 22.84/13.39  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 22.84/13.39  tff(f_142, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 22.84/13.39  tff(f_69, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 22.84/13.39  tff(f_134, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 22.84/13.39  tff(f_153, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_relat_1)).
% 22.84/13.39  tff(c_80, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_174])).
% 22.84/13.39  tff(c_78, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_174])).
% 22.84/13.39  tff(c_76, plain, (r1_tarski('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_174])).
% 22.84/13.39  tff(c_70, plain, (![A_105, B_107]: (r1_tarski(k2_relat_1(A_105), k2_relat_1(B_107)) | ~r1_tarski(A_105, B_107) | ~v1_relat_1(B_107) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_164])).
% 22.84/13.39  tff(c_205, plain, (![A_143]: (k2_xboole_0(k1_relat_1(A_143), k2_relat_1(A_143))=k3_relat_1(A_143) | ~v1_relat_1(A_143))), inference(cnfTransformation, [status(thm)], [f_146])).
% 22.84/13.39  tff(c_18, plain, (![A_12, C_14, B_13]: (r1_tarski(A_12, k2_xboole_0(C_14, B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 22.84/13.39  tff(c_211, plain, (![A_12, A_143]: (r1_tarski(A_12, k3_relat_1(A_143)) | ~r1_tarski(A_12, k2_relat_1(A_143)) | ~v1_relat_1(A_143))), inference(superposition, [status(thm), theory('equality')], [c_205, c_18])).
% 22.84/13.39  tff(c_72, plain, (![A_105, B_107]: (r1_tarski(k1_relat_1(A_105), k1_relat_1(B_107)) | ~r1_tarski(A_105, B_107) | ~v1_relat_1(B_107) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_164])).
% 22.84/13.39  tff(c_26, plain, (![A_21, B_22, C_23]: (k4_xboole_0(k4_xboole_0(A_21, B_22), C_23)=k4_xboole_0(A_21, k2_xboole_0(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 22.84/13.39  tff(c_24, plain, (![A_19, B_20]: (r1_tarski(k4_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 22.84/13.39  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 22.84/13.39  tff(c_704, plain, (![A_198, C_199, B_200]: (r1_tarski(k2_xboole_0(A_198, C_199), B_200) | ~r1_tarski(C_199, B_200) | ~r1_tarski(A_198, B_200))), inference(cnfTransformation, [status(thm)], [f_95])).
% 22.84/13.39  tff(c_442, plain, (![A_171, B_172, C_173]: (r1_tarski(A_171, k2_xboole_0(B_172, C_173)) | ~r1_tarski(k4_xboole_0(A_171, B_172), C_173))), inference(cnfTransformation, [status(thm)], [f_79])).
% 22.84/13.39  tff(c_478, plain, (![A_174, B_175]: (r1_tarski(A_174, k2_xboole_0(B_175, A_174)))), inference(resolution, [status(thm)], [c_24, c_442])).
% 22.84/13.39  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 22.84/13.39  tff(c_502, plain, (![B_175, A_174]: (k2_xboole_0(B_175, A_174)=A_174 | ~r1_tarski(k2_xboole_0(B_175, A_174), A_174))), inference(resolution, [status(thm)], [c_478, c_12])).
% 22.84/13.39  tff(c_716, plain, (![A_198, B_200]: (k2_xboole_0(A_198, B_200)=B_200 | ~r1_tarski(B_200, B_200) | ~r1_tarski(A_198, B_200))), inference(resolution, [status(thm)], [c_704, c_502])).
% 22.84/13.39  tff(c_761, plain, (![A_201, B_202]: (k2_xboole_0(A_201, B_202)=B_202 | ~r1_tarski(A_201, B_202))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_716])).
% 22.84/13.39  tff(c_1086, plain, (![A_207, B_208]: (k2_xboole_0(k4_xboole_0(A_207, B_208), A_207)=A_207)), inference(resolution, [status(thm)], [c_24, c_761])).
% 22.84/13.39  tff(c_351, plain, (![A_163, B_164, C_165]: (k4_xboole_0(k4_xboole_0(A_163, B_164), C_165)=k4_xboole_0(A_163, k2_xboole_0(B_164, C_165)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 22.84/13.39  tff(c_366, plain, (![A_163, B_164, C_165]: (r1_tarski(k4_xboole_0(A_163, k2_xboole_0(B_164, C_165)), k4_xboole_0(A_163, B_164)))), inference(superposition, [status(thm), theory('equality')], [c_351, c_24])).
% 22.84/13.39  tff(c_1127, plain, (![A_163, A_207, B_208]: (r1_tarski(k4_xboole_0(A_163, A_207), k4_xboole_0(A_163, k4_xboole_0(A_207, B_208))))), inference(superposition, [status(thm), theory('equality')], [c_1086, c_366])).
% 22.84/13.39  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 22.84/13.39  tff(c_477, plain, (![A_171, B_172]: (r1_tarski(A_171, k2_xboole_0(B_172, k4_xboole_0(A_171, B_172))))), inference(resolution, [status(thm)], [c_16, c_442])).
% 22.84/13.39  tff(c_14657, plain, (![A_539, C_540, B_541]: (k2_xboole_0(A_539, C_540)=B_541 | ~r1_tarski(B_541, k2_xboole_0(A_539, C_540)) | ~r1_tarski(C_540, B_541) | ~r1_tarski(A_539, B_541))), inference(resolution, [status(thm)], [c_704, c_12])).
% 22.84/13.39  tff(c_14910, plain, (![B_172, A_171]: (k2_xboole_0(B_172, k4_xboole_0(A_171, B_172))=A_171 | ~r1_tarski(k4_xboole_0(A_171, B_172), A_171) | ~r1_tarski(B_172, A_171))), inference(resolution, [status(thm)], [c_477, c_14657])).
% 22.84/13.39  tff(c_15039, plain, (![B_542, A_543]: (k2_xboole_0(B_542, k4_xboole_0(A_543, B_542))=A_543 | ~r1_tarski(B_542, A_543))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_14910])).
% 22.84/13.39  tff(c_470, plain, (![A_163, B_164, C_165]: (r1_tarski(A_163, k2_xboole_0(k2_xboole_0(B_164, C_165), k4_xboole_0(A_163, B_164))))), inference(resolution, [status(thm)], [c_366, c_442])).
% 22.84/13.39  tff(c_21067, plain, (![A_638, A_639, B_640]: (r1_tarski(A_638, k2_xboole_0(A_639, k4_xboole_0(A_638, B_640))) | ~r1_tarski(B_640, A_639))), inference(superposition, [status(thm), theory('equality')], [c_15039, c_470])).
% 22.84/13.39  tff(c_26077, plain, (![A_753, B_754]: (r1_tarski(A_753, k4_xboole_0(A_753, B_754)) | ~r1_tarski(B_754, k4_xboole_0(A_753, B_754)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_21067])).
% 22.84/13.39  tff(c_26140, plain, (![B_755]: (r1_tarski(B_755, k4_xboole_0(B_755, k4_xboole_0(B_755, B_755))))), inference(resolution, [status(thm)], [c_1127, c_26077])).
% 22.84/13.39  tff(c_136, plain, (![B_133, A_134]: (B_133=A_134 | ~r1_tarski(B_133, A_134) | ~r1_tarski(A_134, B_133))), inference(cnfTransformation, [status(thm)], [f_59])).
% 22.84/13.39  tff(c_148, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, k4_xboole_0(A_19, B_20)))), inference(resolution, [status(thm)], [c_24, c_136])).
% 22.84/13.39  tff(c_26311, plain, (![B_756]: (k4_xboole_0(B_756, k4_xboole_0(B_756, B_756))=B_756)), inference(resolution, [status(thm)], [c_26140, c_148])).
% 22.84/13.39  tff(c_26613, plain, (![B_756, B_208]: (r1_tarski(B_756, k4_xboole_0(B_756, k4_xboole_0(k4_xboole_0(B_756, B_756), B_208))))), inference(superposition, [status(thm), theory('equality')], [c_26311, c_1127])).
% 22.84/13.39  tff(c_27218, plain, (![B_760, B_761]: (r1_tarski(B_760, k4_xboole_0(B_760, k4_xboole_0(B_760, k2_xboole_0(B_760, B_761)))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26613])).
% 22.84/13.39  tff(c_27483, plain, (![B_762, B_763]: (k4_xboole_0(B_762, k4_xboole_0(B_762, k2_xboole_0(B_762, B_763)))=B_762)), inference(resolution, [status(thm)], [c_27218, c_148])).
% 22.84/13.39  tff(c_34, plain, (![A_30, B_31]: (r1_xboole_0(A_30, B_31) | k4_xboole_0(A_30, B_31)!=A_30)), inference(cnfTransformation, [status(thm)], [f_89])).
% 22.84/13.39  tff(c_1369, plain, (![A_219, B_220, C_221]: (r1_tarski(A_219, B_220) | ~r1_xboole_0(A_219, C_221) | ~r1_tarski(A_219, k2_xboole_0(B_220, C_221)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 22.84/13.39  tff(c_1491, plain, (![A_229, B_230]: (r1_tarski(A_229, B_230) | ~r1_xboole_0(A_229, k4_xboole_0(A_229, B_230)))), inference(resolution, [status(thm)], [c_477, c_1369])).
% 22.84/13.39  tff(c_1506, plain, (![A_30, B_230]: (r1_tarski(A_30, B_230) | k4_xboole_0(A_30, k4_xboole_0(A_30, B_230))!=A_30)), inference(resolution, [status(thm)], [c_34, c_1491])).
% 22.84/13.39  tff(c_28053, plain, (![B_762, B_763]: (r1_tarski(B_762, k2_xboole_0(B_762, B_763)))), inference(superposition, [status(thm), theory('equality')], [c_27483, c_1506])).
% 22.84/13.39  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 22.84/13.39  tff(c_22, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 22.84/13.39  tff(c_156, plain, (![A_135]: (k1_xboole_0=A_135 | ~r1_tarski(A_135, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_136])).
% 22.84/13.39  tff(c_169, plain, (![B_20]: (k4_xboole_0(k1_xboole_0, B_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_156])).
% 22.84/13.39  tff(c_46, plain, (![A_39]: (r2_hidden(A_39, '#skF_3'(A_39)))), inference(cnfTransformation, [status(thm)], [f_132])).
% 22.84/13.39  tff(c_185, plain, (![A_137, B_138, C_139]: (~r1_xboole_0(A_137, B_138) | ~r2_hidden(C_139, B_138) | ~r2_hidden(C_139, A_137))), inference(cnfTransformation, [status(thm)], [f_45])).
% 22.84/13.39  tff(c_2624, plain, (![C_288, B_289, A_290]: (~r2_hidden(C_288, B_289) | ~r2_hidden(C_288, A_290) | k4_xboole_0(A_290, B_289)!=A_290)), inference(resolution, [status(thm)], [c_34, c_185])).
% 22.84/13.39  tff(c_2664, plain, (![A_291, A_292]: (~r2_hidden(A_291, A_292) | k4_xboole_0(A_292, '#skF_3'(A_291))!=A_292)), inference(resolution, [status(thm)], [c_46, c_2624])).
% 22.84/13.39  tff(c_2674, plain, (![A_293]: (~r2_hidden(A_293, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_169, c_2664])).
% 22.84/13.39  tff(c_2693, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_2674])).
% 22.84/13.39  tff(c_2990, plain, (![B_311, C_312]: (r1_tarski(k2_xboole_0(B_311, C_312), B_311) | ~r1_xboole_0(k2_xboole_0(B_311, C_312), C_312))), inference(resolution, [status(thm)], [c_16, c_1369])).
% 22.84/13.39  tff(c_3106, plain, (![B_314]: (r1_tarski(k2_xboole_0(B_314, k1_xboole_0), B_314))), inference(resolution, [status(thm)], [c_2693, c_2990])).
% 22.84/13.39  tff(c_3172, plain, (![B_314]: (k2_xboole_0(B_314, k1_xboole_0)=B_314 | ~r1_tarski(B_314, k2_xboole_0(B_314, k1_xboole_0)))), inference(resolution, [status(thm)], [c_3106, c_12])).
% 22.84/13.39  tff(c_28085, plain, (![B_314]: (k2_xboole_0(B_314, k1_xboole_0)=B_314)), inference(demodulation, [status(thm), theory('equality')], [c_28053, c_3172])).
% 22.84/13.39  tff(c_10, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_53])).
% 22.84/13.39  tff(c_2807, plain, (![C_301, A_302]: (r2_hidden(k4_tarski(C_301, '#skF_8'(A_302, k1_relat_1(A_302), C_301)), A_302) | ~r2_hidden(C_301, k1_relat_1(A_302)))), inference(cnfTransformation, [status(thm)], [f_142])).
% 22.84/13.39  tff(c_2673, plain, (![A_291]: (~r2_hidden(A_291, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_169, c_2664])).
% 22.84/13.39  tff(c_2824, plain, (![C_303]: (~r2_hidden(C_303, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_2807, c_2673])).
% 22.84/13.39  tff(c_2849, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_2824])).
% 22.84/13.39  tff(c_28086, plain, (![B_764, B_765]: (r1_tarski(B_764, k2_xboole_0(B_764, B_765)))), inference(superposition, [status(thm), theory('equality')], [c_27483, c_1506])).
% 22.84/13.39  tff(c_760, plain, (![A_198, C_199, B_200]: (k2_xboole_0(A_198, C_199)=B_200 | ~r1_tarski(B_200, k2_xboole_0(A_198, C_199)) | ~r1_tarski(C_199, B_200) | ~r1_tarski(A_198, B_200))), inference(resolution, [status(thm)], [c_704, c_12])).
% 22.84/13.39  tff(c_28106, plain, (![B_764, B_765]: (k2_xboole_0(B_764, B_765)=B_764 | ~r1_tarski(B_765, B_764) | ~r1_tarski(B_764, B_764))), inference(resolution, [status(thm)], [c_28086, c_760])).
% 22.84/13.39  tff(c_29267, plain, (![B_776, B_777]: (k2_xboole_0(B_776, B_777)=B_776 | ~r1_tarski(B_777, B_776))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_28106])).
% 22.84/13.39  tff(c_29601, plain, (![A_19, B_20]: (k2_xboole_0(A_19, k4_xboole_0(A_19, B_20))=A_19)), inference(resolution, [status(thm)], [c_24, c_29267])).
% 22.84/13.39  tff(c_26294, plain, (![B_755]: (k4_xboole_0(B_755, k4_xboole_0(B_755, B_755))=B_755)), inference(resolution, [status(thm)], [c_26140, c_148])).
% 22.84/13.39  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 22.84/13.39  tff(c_47604, plain, (![A_1006, B_1007, A_1008]: (~r2_hidden('#skF_1'(A_1006, B_1007), A_1008) | k4_xboole_0(A_1008, A_1006)!=A_1008 | r1_xboole_0(A_1006, B_1007))), inference(resolution, [status(thm)], [c_8, c_2624])).
% 22.84/13.39  tff(c_47767, plain, (![B_1011, A_1012]: (k4_xboole_0(B_1011, A_1012)!=B_1011 | r1_xboole_0(A_1012, B_1011))), inference(resolution, [status(thm)], [c_6, c_47604])).
% 22.84/13.39  tff(c_822, plain, (![A_19, B_20]: (k2_xboole_0(k4_xboole_0(A_19, B_20), A_19)=A_19)), inference(resolution, [status(thm)], [c_24, c_761])).
% 22.84/13.39  tff(c_35406, plain, (![B_836, B_837]: (k2_xboole_0(k2_xboole_0(B_836, B_837), B_836)=k2_xboole_0(B_836, B_837))), inference(resolution, [status(thm)], [c_28053, c_29267])).
% 22.84/13.39  tff(c_189, plain, (![A_140, C_141, B_142]: (r1_tarski(A_140, C_141) | ~r1_tarski(B_142, C_141) | ~r1_tarski(A_140, B_142))), inference(cnfTransformation, [status(thm)], [f_69])).
% 22.84/13.39  tff(c_203, plain, (![A_140]: (r1_tarski(A_140, '#skF_10') | ~r1_tarski(A_140, '#skF_9'))), inference(resolution, [status(thm)], [c_76, c_189])).
% 22.84/13.39  tff(c_638, plain, (![A_191, B_192]: (r1_tarski(A_191, k2_xboole_0(B_192, '#skF_10')) | ~r1_tarski(k4_xboole_0(A_191, B_192), '#skF_9'))), inference(resolution, [status(thm)], [c_203, c_442])).
% 22.84/13.39  tff(c_651, plain, (![B_20]: (r1_tarski('#skF_9', k2_xboole_0(B_20, '#skF_10')))), inference(resolution, [status(thm)], [c_24, c_638])).
% 22.84/13.39  tff(c_1606, plain, (![B_236]: (k2_xboole_0('#skF_9', k2_xboole_0(B_236, '#skF_10'))=k2_xboole_0(B_236, '#skF_10'))), inference(resolution, [status(thm)], [c_651, c_761])).
% 22.84/13.39  tff(c_1624, plain, (![A_163, B_236]: (r1_tarski(A_163, k2_xboole_0(k2_xboole_0(B_236, '#skF_10'), k4_xboole_0(A_163, '#skF_9'))))), inference(superposition, [status(thm), theory('equality')], [c_1606, c_470])).
% 22.84/13.39  tff(c_36082, plain, (![A_842]: (r1_tarski(A_842, k2_xboole_0(k4_xboole_0(A_842, '#skF_9'), '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_35406, c_1624])).
% 22.84/13.39  tff(c_30, plain, (![A_27, B_28, C_29]: (r1_tarski(A_27, B_28) | ~r1_xboole_0(A_27, C_29) | ~r1_tarski(A_27, k2_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 22.84/13.39  tff(c_42683, plain, (![A_924]: (r1_tarski(A_924, k4_xboole_0(A_924, '#skF_9')) | ~r1_xboole_0(A_924, '#skF_10'))), inference(resolution, [status(thm)], [c_36082, c_30])).
% 22.84/13.39  tff(c_28260, plain, (![B_764, B_765]: (k2_xboole_0(B_764, B_765)=B_764 | ~r1_tarski(B_765, B_764))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_28106])).
% 22.84/13.39  tff(c_42704, plain, (![A_924]: (k2_xboole_0(k4_xboole_0(A_924, '#skF_9'), A_924)=k4_xboole_0(A_924, '#skF_9') | ~r1_xboole_0(A_924, '#skF_10'))), inference(resolution, [status(thm)], [c_42683, c_28260])).
% 22.84/13.39  tff(c_42803, plain, (![A_924]: (k4_xboole_0(A_924, '#skF_9')=A_924 | ~r1_xboole_0(A_924, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_822, c_42704])).
% 22.84/13.39  tff(c_51929, plain, (![A_1052]: (k4_xboole_0(A_1052, '#skF_9')=A_1052 | k4_xboole_0('#skF_10', A_1052)!='#skF_10')), inference(resolution, [status(thm)], [c_47767, c_42803])).
% 22.84/13.39  tff(c_51958, plain, (k4_xboole_0(k4_xboole_0('#skF_10', '#skF_10'), '#skF_9')=k4_xboole_0('#skF_10', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_26294, c_51929])).
% 22.84/13.39  tff(c_52450, plain, (r1_tarski(k4_xboole_0('#skF_10', '#skF_10'), '#skF_9') | k4_xboole_0(k4_xboole_0('#skF_10', '#skF_10'), k4_xboole_0('#skF_10', '#skF_10'))!=k4_xboole_0('#skF_10', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_51958, c_1506])).
% 22.84/13.39  tff(c_52570, plain, (r1_tarski(k4_xboole_0('#skF_10', '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_29601, c_26, c_52450])).
% 22.84/13.39  tff(c_1806, plain, (![A_242, C_243, B_244]: (r1_tarski(A_242, C_243) | ~r1_xboole_0(A_242, B_244) | ~r1_tarski(A_242, B_244))), inference(resolution, [status(thm)], [c_18, c_1369])).
% 22.84/13.39  tff(c_9569, plain, (![A_432, C_433, B_434]: (r1_tarski(A_432, C_433) | ~r1_tarski(A_432, B_434) | k4_xboole_0(A_432, B_434)!=A_432)), inference(resolution, [status(thm)], [c_34, c_1806])).
% 22.84/13.39  tff(c_9780, plain, (![A_140, C_433]: (r1_tarski(A_140, C_433) | k4_xboole_0(A_140, '#skF_10')!=A_140 | ~r1_tarski(A_140, '#skF_9'))), inference(resolution, [status(thm)], [c_203, c_9569])).
% 22.84/13.39  tff(c_52615, plain, (![C_433]: (r1_tarski(k4_xboole_0('#skF_10', '#skF_10'), C_433) | k4_xboole_0(k4_xboole_0('#skF_10', '#skF_10'), '#skF_10')!=k4_xboole_0('#skF_10', '#skF_10'))), inference(resolution, [status(thm)], [c_52570, c_9780])).
% 22.84/13.39  tff(c_52678, plain, (![C_1056]: (r1_tarski(k4_xboole_0('#skF_10', '#skF_10'), C_1056))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_26, c_52615])).
% 22.84/13.39  tff(c_149, plain, (![A_18]: (k1_xboole_0=A_18 | ~r1_tarski(A_18, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_136])).
% 22.84/13.39  tff(c_52903, plain, (k4_xboole_0('#skF_10', '#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_52678, c_149])).
% 22.84/13.39  tff(c_52, plain, (![A_80, B_81]: (k6_subset_1(A_80, B_81)=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_134])).
% 22.84/13.39  tff(c_68, plain, (![A_102, B_104]: (r1_tarski(k6_subset_1(k1_relat_1(A_102), k1_relat_1(B_104)), k1_relat_1(k6_subset_1(A_102, B_104))) | ~v1_relat_1(B_104) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_153])).
% 22.84/13.39  tff(c_2926, plain, (![A_306, B_307]: (r1_tarski(k4_xboole_0(k1_relat_1(A_306), k1_relat_1(B_307)), k1_relat_1(k4_xboole_0(A_306, B_307))) | ~v1_relat_1(B_307) | ~v1_relat_1(A_306))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_68])).
% 22.84/13.39  tff(c_2964, plain, (![A_306, B_307]: (k4_xboole_0(k1_relat_1(A_306), k1_relat_1(B_307))=k1_relat_1(k4_xboole_0(A_306, B_307)) | ~r1_tarski(k1_relat_1(k4_xboole_0(A_306, B_307)), k4_xboole_0(k1_relat_1(A_306), k1_relat_1(B_307))) | ~v1_relat_1(B_307) | ~v1_relat_1(A_306))), inference(resolution, [status(thm)], [c_2926, c_12])).
% 22.84/13.39  tff(c_53015, plain, (k4_xboole_0(k1_relat_1('#skF_10'), k1_relat_1('#skF_10'))=k1_relat_1(k4_xboole_0('#skF_10', '#skF_10')) | ~r1_tarski(k1_relat_1(k1_xboole_0), k4_xboole_0(k1_relat_1('#skF_10'), k1_relat_1('#skF_10'))) | ~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_52903, c_2964])).
% 22.84/13.39  tff(c_53281, plain, (k4_xboole_0(k1_relat_1('#skF_10'), k1_relat_1('#skF_10'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_78, c_78, c_22, c_2849, c_2849, c_52903, c_53015])).
% 22.84/13.39  tff(c_66, plain, (![A_101]: (k2_xboole_0(k1_relat_1(A_101), k2_relat_1(A_101))=k3_relat_1(A_101) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_146])).
% 22.84/13.39  tff(c_400, plain, (![A_168, B_169, C_170]: (r1_tarski(k4_xboole_0(A_168, k2_xboole_0(B_169, C_170)), k4_xboole_0(A_168, B_169)))), inference(superposition, [status(thm), theory('equality')], [c_351, c_24])).
% 22.84/13.39  tff(c_419, plain, (![A_168, A_101]: (r1_tarski(k4_xboole_0(A_168, k3_relat_1(A_101)), k4_xboole_0(A_168, k1_relat_1(A_101))) | ~v1_relat_1(A_101))), inference(superposition, [status(thm), theory('equality')], [c_66, c_400])).
% 22.84/13.39  tff(c_54792, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_10'), k3_relat_1('#skF_10')), k1_xboole_0) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_53281, c_419])).
% 22.84/13.39  tff(c_55018, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_10'), k3_relat_1('#skF_10')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_54792])).
% 22.84/13.39  tff(c_56505, plain, (k4_xboole_0(k1_relat_1('#skF_10'), k3_relat_1('#skF_10'))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k4_xboole_0(k1_relat_1('#skF_10'), k3_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_55018, c_12])).
% 22.84/13.39  tff(c_56542, plain, (k4_xboole_0(k1_relat_1('#skF_10'), k3_relat_1('#skF_10'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_56505])).
% 22.84/13.39  tff(c_504, plain, (![A_176, B_177]: (r1_tarski(A_176, k2_xboole_0(B_177, k4_xboole_0(A_176, B_177))))), inference(resolution, [status(thm)], [c_16, c_442])).
% 22.84/13.39  tff(c_20, plain, (![A_15, C_17, B_16]: (r1_tarski(A_15, C_17) | ~r1_tarski(B_16, C_17) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 22.84/13.39  tff(c_528, plain, (![A_15, B_177, A_176]: (r1_tarski(A_15, k2_xboole_0(B_177, k4_xboole_0(A_176, B_177))) | ~r1_tarski(A_15, A_176))), inference(resolution, [status(thm)], [c_504, c_20])).
% 22.84/13.39  tff(c_56799, plain, (![A_15]: (r1_tarski(A_15, k2_xboole_0(k3_relat_1('#skF_10'), k1_xboole_0)) | ~r1_tarski(A_15, k1_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_56542, c_528])).
% 22.84/13.39  tff(c_73986, plain, (![A_1229]: (r1_tarski(A_1229, k3_relat_1('#skF_10')) | ~r1_tarski(A_1229, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_28085, c_56799])).
% 22.84/13.39  tff(c_10896, plain, (![A_459, B_460]: (r1_tarski(k3_relat_1(A_459), B_460) | ~r1_tarski(k2_relat_1(A_459), B_460) | ~r1_tarski(k1_relat_1(A_459), B_460) | ~v1_relat_1(A_459))), inference(superposition, [status(thm), theory('equality')], [c_66, c_704])).
% 22.84/13.39  tff(c_74, plain, (~r1_tarski(k3_relat_1('#skF_9'), k3_relat_1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 22.84/13.39  tff(c_10963, plain, (~r1_tarski(k2_relat_1('#skF_9'), k3_relat_1('#skF_10')) | ~r1_tarski(k1_relat_1('#skF_9'), k3_relat_1('#skF_10')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_10896, c_74])).
% 22.84/13.39  tff(c_10988, plain, (~r1_tarski(k2_relat_1('#skF_9'), k3_relat_1('#skF_10')) | ~r1_tarski(k1_relat_1('#skF_9'), k3_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_10963])).
% 22.84/13.39  tff(c_11339, plain, (~r1_tarski(k1_relat_1('#skF_9'), k3_relat_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_10988])).
% 22.84/13.39  tff(c_74194, plain, (~r1_tarski(k1_relat_1('#skF_9'), k1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_73986, c_11339])).
% 22.84/13.39  tff(c_74218, plain, (~r1_tarski('#skF_9', '#skF_10') | ~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_72, c_74194])).
% 22.84/13.39  tff(c_74222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74218])).
% 22.84/13.39  tff(c_74223, plain, (~r1_tarski(k2_relat_1('#skF_9'), k3_relat_1('#skF_10'))), inference(splitRight, [status(thm)], [c_10988])).
% 22.84/13.39  tff(c_74227, plain, (~r1_tarski(k2_relat_1('#skF_9'), k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_211, c_74223])).
% 22.84/13.39  tff(c_74230, plain, (~r1_tarski(k2_relat_1('#skF_9'), k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74227])).
% 22.84/13.39  tff(c_74274, plain, (~r1_tarski('#skF_9', '#skF_10') | ~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_70, c_74230])).
% 22.84/13.39  tff(c_74278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74274])).
% 22.84/13.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.84/13.39  
% 22.84/13.39  Inference rules
% 22.84/13.39  ----------------------
% 22.84/13.39  #Ref     : 0
% 22.84/13.39  #Sup     : 18752
% 22.84/13.39  #Fact    : 0
% 22.84/13.39  #Define  : 0
% 22.84/13.39  #Split   : 15
% 22.84/13.39  #Chain   : 0
% 22.84/13.39  #Close   : 0
% 22.84/13.39  
% 22.84/13.39  Ordering : KBO
% 22.84/13.39  
% 22.84/13.39  Simplification rules
% 22.84/13.39  ----------------------
% 22.84/13.39  #Subsume      : 5077
% 22.84/13.39  #Demod        : 11655
% 22.84/13.39  #Tautology    : 6621
% 22.84/13.39  #SimpNegUnit  : 113
% 22.84/13.39  #BackRed      : 63
% 22.84/13.39  
% 22.84/13.39  #Partial instantiations: 0
% 22.84/13.39  #Strategies tried      : 1
% 22.84/13.39  
% 22.84/13.39  Timing (in seconds)
% 22.84/13.39  ----------------------
% 22.84/13.40  Preprocessing        : 0.35
% 22.84/13.40  Parsing              : 0.18
% 22.84/13.40  CNF conversion       : 0.03
% 22.84/13.40  Main loop            : 12.24
% 22.84/13.40  Inferencing          : 1.55
% 22.84/13.40  Reduction            : 5.93
% 22.84/13.40  Demodulation         : 4.99
% 22.84/13.40  BG Simplification    : 0.17
% 22.84/13.40  Subsumption          : 3.94
% 22.84/13.40  Abstraction          : 0.26
% 22.84/13.40  MUC search           : 0.00
% 22.84/13.40  Cooper               : 0.00
% 22.84/13.40  Total                : 12.65
% 22.84/13.40  Index Insertion      : 0.00
% 22.84/13.40  Index Deletion       : 0.00
% 22.84/13.40  Index Matching       : 0.00
% 22.84/13.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
