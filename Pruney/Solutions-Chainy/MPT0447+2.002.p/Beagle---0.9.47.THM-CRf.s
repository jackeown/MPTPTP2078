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
% DateTime   : Thu Dec  3 09:58:28 EST 2020

% Result     : Theorem 10.56s
% Output     : CNFRefutation 10.65s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 532 expanded)
%              Number of leaves         :   64 ( 205 expanded)
%              Depth                    :   17
%              Number of atoms          :  245 ( 789 expanded)
%              Number of equality atoms :   50 ( 269 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_11 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(r2_tarski,type,(
    r2_tarski: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

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

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_202,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_169,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_97,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_103,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_69,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_73,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_75,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_165,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_149,axiom,(
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

tff(f_116,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_87,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_55,axiom,(
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

tff(f_79,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_151,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_176,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_35,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_157,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_185,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(f_192,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k2_relat_1(A),k2_relat_1(B)),k2_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).

tff(c_102,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_100,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_88,plain,(
    ! [A_122] :
      ( k2_xboole_0(k1_relat_1(A_122),k2_relat_1(A_122)) = k3_relat_1(A_122)
      | ~ v1_relat_1(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_48,plain,(
    ! [B_42,A_41] : k2_tarski(B_42,A_41) = k2_tarski(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_227,plain,(
    ! [A_152,B_153] : k3_tarski(k2_tarski(A_152,B_153)) = k2_xboole_0(A_152,B_153) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_257,plain,(
    ! [B_156,A_157] : k3_tarski(k2_tarski(B_156,A_157)) = k2_xboole_0(A_157,B_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_227])).

tff(c_54,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_280,plain,(
    ! [B_158,A_159] : k2_xboole_0(B_158,A_159) = k2_xboole_0(A_159,B_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_54])).

tff(c_44,plain,(
    ! [A_36,B_37] : r1_tarski(A_36,k2_xboole_0(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_295,plain,(
    ! [A_159,B_158] : r1_tarski(A_159,k2_xboole_0(B_158,A_159)) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_44])).

tff(c_12,plain,(
    ! [A_8] : k2_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    ! [A_23] : k4_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1947,plain,(
    ! [A_275,B_276,C_277] : k4_xboole_0(k4_xboole_0(A_275,B_276),C_277) = k4_xboole_0(A_275,k2_xboole_0(B_276,C_277)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3109,plain,(
    ! [A_326,C_327] : k4_xboole_0(A_326,k2_xboole_0(k1_xboole_0,C_327)) = k4_xboole_0(A_326,C_327) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1947])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_333,plain,(
    ! [A_162,B_163] : k4_xboole_0(A_162,k4_xboole_0(A_162,B_163)) = k3_xboole_0(A_162,B_163) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_30,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_354,plain,(
    ! [A_164,B_165] : r1_tarski(k3_xboole_0(A_164,B_165),A_164) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_30])).

tff(c_357,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_354])).

tff(c_371,plain,(
    ! [B_168,A_169] :
      ( B_168 = A_169
      | ~ r1_tarski(B_168,A_169)
      | ~ r1_tarski(A_169,B_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_400,plain,(
    ! [A_170] :
      ( k1_xboole_0 = A_170
      | ~ r1_tarski(A_170,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_371])).

tff(c_421,plain,(
    ! [B_2] : k3_xboole_0(B_2,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_357,c_400])).

tff(c_351,plain,(
    ! [A_23] : k4_xboole_0(A_23,A_23) = k3_xboole_0(A_23,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_333])).

tff(c_539,plain,(
    ! [A_23] : k4_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_351])).

tff(c_3248,plain,(
    ! [C_328] : k4_xboole_0(k2_xboole_0(k1_xboole_0,C_328),C_328) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3109,c_539])).

tff(c_38,plain,(
    ! [A_30,B_31,C_32] :
      ( r1_tarski(A_30,k2_xboole_0(B_31,C_32))
      | ~ r1_tarski(k4_xboole_0(A_30,B_31),C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3263,plain,(
    ! [C_328,C_32] :
      ( r1_tarski(k2_xboole_0(k1_xboole_0,C_328),k2_xboole_0(C_328,C_32))
      | ~ r1_tarski(k1_xboole_0,C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3248,c_38])).

tff(c_3399,plain,(
    ! [C_332,C_333] : r1_tarski(k2_xboole_0(k1_xboole_0,C_332),k2_xboole_0(C_332,C_333)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3263])).

tff(c_3434,plain,(
    ! [A_334] : r1_tarski(k2_xboole_0(k1_xboole_0,A_334),A_334) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3399])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | ~ r1_tarski(B_16,A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3463,plain,(
    ! [A_334] :
      ( k2_xboole_0(k1_xboole_0,A_334) = A_334
      | ~ r1_tarski(A_334,k2_xboole_0(k1_xboole_0,A_334)) ) ),
    inference(resolution,[status(thm)],[c_3434,c_20])).

tff(c_3489,plain,(
    ! [A_334] : k2_xboole_0(k1_xboole_0,A_334) = A_334 ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_3463])).

tff(c_263,plain,(
    ! [B_156,A_157] : k2_xboole_0(B_156,A_157) = k2_xboole_0(A_157,B_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_54])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,(
    ! [C_118,A_103] :
      ( r2_hidden(k4_tarski(C_118,'#skF_9'(A_103,k1_relat_1(A_103),C_118)),A_103)
      | ~ r2_hidden(C_118,k1_relat_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_64,plain,(
    ! [A_57] : r2_hidden(A_57,'#skF_4'(A_57)) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_673,plain,(
    ! [C_194,B_195,A_196] :
      ( r2_hidden(C_194,B_195)
      | ~ r2_hidden(C_194,A_196)
      | ~ r1_tarski(A_196,B_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_698,plain,(
    ! [A_199,B_200] :
      ( r2_hidden(A_199,B_200)
      | ~ r1_tarski('#skF_4'(A_199),B_200) ) ),
    inference(resolution,[status(thm)],[c_64,c_673])).

tff(c_712,plain,(
    ! [A_199,B_37] : r2_hidden(A_199,k2_xboole_0('#skF_4'(A_199),B_37)) ),
    inference(resolution,[status(thm)],[c_44,c_698])).

tff(c_58,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_3'(A_50,B_51),B_51)
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_42,plain,(
    ! [A_35] : r1_xboole_0(A_35,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1079,plain,(
    ! [A_225,B_226,C_227] :
      ( ~ r1_xboole_0(A_225,B_226)
      | ~ r2_hidden(C_227,B_226)
      | ~ r2_hidden(C_227,A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1083,plain,(
    ! [C_228,A_229] :
      ( ~ r2_hidden(C_228,k1_xboole_0)
      | ~ r2_hidden(C_228,A_229) ) ),
    inference(resolution,[status(thm)],[c_42,c_1079])).

tff(c_6645,plain,(
    ! [A_436,A_437] :
      ( ~ r2_hidden('#skF_3'(A_436,k1_xboole_0),A_437)
      | ~ r2_hidden(A_436,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_58,c_1083])).

tff(c_6677,plain,(
    ! [A_438] : ~ r2_hidden(A_438,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_712,c_6645])).

tff(c_6760,plain,(
    ! [C_442] : ~ r2_hidden(C_442,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_76,c_6677])).

tff(c_6834,plain,(
    ! [B_446] : r1_tarski(k1_relat_1(k1_xboole_0),B_446) ),
    inference(resolution,[status(thm)],[c_8,c_6760])).

tff(c_398,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_371])).

tff(c_6893,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6834,c_398])).

tff(c_24,plain,(
    ! [B_16] : r1_tarski(B_16,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1314,plain,(
    ! [A_240,B_241,C_242] :
      ( r1_tarski(k4_xboole_0(A_240,B_241),C_242)
      | ~ r1_tarski(A_240,k2_xboole_0(B_241,C_242)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_98,plain,(
    r1_tarski('#skF_11','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_737,plain,(
    ! [A_203,C_204,B_205] :
      ( r1_tarski(A_203,C_204)
      | ~ r1_tarski(B_205,C_204)
      | ~ r1_tarski(A_203,B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_765,plain,(
    ! [A_203] :
      ( r1_tarski(A_203,'#skF_12')
      | ~ r1_tarski(A_203,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_98,c_737])).

tff(c_1353,plain,(
    ! [A_240,B_241] :
      ( r1_tarski(k4_xboole_0(A_240,B_241),'#skF_12')
      | ~ r1_tarski(A_240,k2_xboole_0(B_241,'#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_1314,c_765])).

tff(c_1477,plain,(
    ! [A_249,B_250,C_251] :
      ( r1_tarski(A_249,k2_xboole_0(B_250,C_251))
      | ~ r1_tarski(k4_xboole_0(A_249,B_250),C_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4040,plain,(
    ! [A_358,B_359] :
      ( r1_tarski(A_358,k2_xboole_0(B_359,'#skF_12'))
      | ~ r1_tarski(A_358,k2_xboole_0(B_359,'#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_1353,c_1477])).

tff(c_4155,plain,(
    ! [B_360] : r1_tarski(k2_xboole_0(B_360,'#skF_11'),k2_xboole_0(B_360,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_24,c_4040])).

tff(c_4193,plain,(
    r1_tarski(k2_xboole_0('#skF_12','#skF_11'),'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_4155])).

tff(c_4205,plain,
    ( k2_xboole_0('#skF_12','#skF_11') = '#skF_12'
    | ~ r1_tarski('#skF_12',k2_xboole_0('#skF_12','#skF_11')) ),
    inference(resolution,[status(thm)],[c_4193,c_20])).

tff(c_4210,plain,(
    k2_xboole_0('#skF_12','#skF_11') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4205])).

tff(c_423,plain,(
    ! [B_22] : k4_xboole_0(k1_xboole_0,B_22) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_400])).

tff(c_1992,plain,(
    ! [A_23,C_277] : k4_xboole_0(A_23,k2_xboole_0(A_23,C_277)) = k4_xboole_0(k1_xboole_0,C_277) ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_1947])).

tff(c_2022,plain,(
    ! [A_278,C_279] : k4_xboole_0(A_278,k2_xboole_0(A_278,C_279)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_1992])).

tff(c_2095,plain,(
    ! [A_157,B_156] : k4_xboole_0(A_157,k2_xboole_0(B_156,A_157)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_2022])).

tff(c_4247,plain,(
    k4_xboole_0('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4210,c_2095])).

tff(c_70,plain,(
    ! [A_98,B_99] : k6_subset_1(A_98,B_99) = k4_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_90,plain,(
    ! [A_123,B_125] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_123),k1_relat_1(B_125)),k1_relat_1(k6_subset_1(A_123,B_125)))
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_4781,plain,(
    ! [A_368,B_369] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_368),k1_relat_1(B_369)),k1_relat_1(k4_xboole_0(A_368,B_369)))
      | ~ v1_relat_1(B_369)
      | ~ v1_relat_1(A_368) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_70,c_90])).

tff(c_17089,plain,(
    ! [A_633,B_634] :
      ( r1_tarski(k1_relat_1(A_633),k2_xboole_0(k1_relat_1(B_634),k1_relat_1(k4_xboole_0(A_633,B_634))))
      | ~ v1_relat_1(B_634)
      | ~ v1_relat_1(A_633) ) ),
    inference(resolution,[status(thm)],[c_4781,c_38])).

tff(c_17158,plain,
    ( r1_tarski(k1_relat_1('#skF_11'),k2_xboole_0(k1_relat_1('#skF_12'),k1_relat_1(k1_xboole_0)))
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_4247,c_17089])).

tff(c_17209,plain,(
    r1_tarski(k1_relat_1('#skF_11'),k1_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_3489,c_263,c_6893,c_17158])).

tff(c_46,plain,(
    ! [A_38,C_40,B_39] :
      ( r1_tarski(k2_xboole_0(A_38,C_40),B_39)
      | ~ r1_tarski(C_40,B_39)
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6710,plain,(
    ! [A_439,B_440] :
      ( k2_xboole_0(A_439,B_440) = A_439
      | ~ r1_tarski(k2_xboole_0(A_439,B_440),A_439) ) ),
    inference(resolution,[status(thm)],[c_44,c_371])).

tff(c_6731,plain,(
    ! [B_39,C_40] :
      ( k2_xboole_0(B_39,C_40) = B_39
      | ~ r1_tarski(C_40,B_39)
      | ~ r1_tarski(B_39,B_39) ) ),
    inference(resolution,[status(thm)],[c_46,c_6710])).

tff(c_6753,plain,(
    ! [B_39,C_40] :
      ( k2_xboole_0(B_39,C_40) = B_39
      | ~ r1_tarski(C_40,B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_6731])).

tff(c_17227,plain,(
    k2_xboole_0(k1_relat_1('#skF_12'),k1_relat_1('#skF_11')) = k1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_17209,c_6753])).

tff(c_2212,plain,(
    ! [A_282,B_283] : k4_xboole_0(A_282,k2_xboole_0(B_283,A_282)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_2022])).

tff(c_2240,plain,(
    ! [A_282,B_283,C_32] :
      ( r1_tarski(A_282,k2_xboole_0(k2_xboole_0(B_283,A_282),C_32))
      | ~ r1_tarski(k1_xboole_0,C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2212,c_38])).

tff(c_2306,plain,(
    ! [A_282,B_283,C_32] : r1_tarski(A_282,k2_xboole_0(k2_xboole_0(B_283,A_282),C_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2240])).

tff(c_17580,plain,(
    ! [C_635] : r1_tarski(k1_relat_1('#skF_11'),k2_xboole_0(k1_relat_1('#skF_12'),C_635)) ),
    inference(superposition,[status(thm),theory(equality)],[c_17227,c_2306])).

tff(c_17622,plain,
    ( r1_tarski(k1_relat_1('#skF_11'),k3_relat_1('#skF_12'))
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_17580])).

tff(c_17650,plain,(
    r1_tarski(k1_relat_1('#skF_11'),k3_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_17622])).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_109,plain,(
    ! [A_136] :
      ( v1_relat_1(A_136)
      | ~ v1_xboole_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_113,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_109])).

tff(c_92,plain,(
    ! [A_126,B_127] :
      ( r2_hidden('#skF_10'(A_126,B_127),k1_relat_1(B_127))
      | ~ r2_hidden(A_126,k2_relat_1(B_127))
      | ~ v1_relat_1(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_6772,plain,(
    ! [A_126] :
      ( ~ r2_hidden(A_126,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_92,c_6760])).

tff(c_6935,plain,(
    ! [A_447] : ~ r2_hidden(A_447,k2_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_6772])).

tff(c_7082,plain,(
    ! [B_451] : r1_tarski(k2_relat_1(k1_xboole_0),B_451) ),
    inference(resolution,[status(thm)],[c_8,c_6935])).

tff(c_7141,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7082,c_398])).

tff(c_94,plain,(
    ! [A_129,B_131] :
      ( r1_tarski(k6_subset_1(k2_relat_1(A_129),k2_relat_1(B_131)),k2_relat_1(k6_subset_1(A_129,B_131)))
      | ~ v1_relat_1(B_131)
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_4393,plain,(
    ! [A_361,B_362] :
      ( r1_tarski(k4_xboole_0(k2_relat_1(A_361),k2_relat_1(B_362)),k2_relat_1(k4_xboole_0(A_361,B_362)))
      | ~ v1_relat_1(B_362)
      | ~ v1_relat_1(A_361) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_70,c_94])).

tff(c_13981,plain,(
    ! [A_596,B_597] :
      ( r1_tarski(k2_relat_1(A_596),k2_xboole_0(k2_relat_1(B_597),k2_relat_1(k4_xboole_0(A_596,B_597))))
      | ~ v1_relat_1(B_597)
      | ~ v1_relat_1(A_596) ) ),
    inference(resolution,[status(thm)],[c_4393,c_38])).

tff(c_14032,plain,
    ( r1_tarski(k2_relat_1('#skF_11'),k2_xboole_0(k2_relat_1('#skF_12'),k2_relat_1(k1_xboole_0)))
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_4247,c_13981])).

tff(c_14078,plain,(
    r1_tarski(k2_relat_1('#skF_11'),k2_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_3489,c_263,c_7141,c_14032])).

tff(c_14096,plain,(
    k2_xboole_0(k2_relat_1('#skF_12'),k2_relat_1('#skF_11')) = k2_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_14078,c_6753])).

tff(c_2047,plain,(
    ! [A_278,C_279,C_32] :
      ( r1_tarski(A_278,k2_xboole_0(k2_xboole_0(A_278,C_279),C_32))
      | ~ r1_tarski(k1_xboole_0,C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2022,c_38])).

tff(c_2534,plain,(
    ! [A_292,C_293,C_294] : r1_tarski(A_292,k2_xboole_0(k2_xboole_0(A_292,C_293),C_294)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2047])).

tff(c_2675,plain,(
    ! [A_302,A_303,C_304] : r1_tarski(A_302,k2_xboole_0(A_303,k2_xboole_0(A_302,C_304))) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_2534])).

tff(c_2700,plain,(
    ! [B_156,A_303,A_157] : r1_tarski(B_156,k2_xboole_0(A_303,k2_xboole_0(A_157,B_156))) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_2675])).

tff(c_15065,plain,(
    ! [A_608] : r1_tarski(k2_relat_1('#skF_11'),k2_xboole_0(A_608,k2_relat_1('#skF_12'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14096,c_2700])).

tff(c_15089,plain,
    ( r1_tarski(k2_relat_1('#skF_11'),k3_relat_1('#skF_12'))
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_15065])).

tff(c_15111,plain,(
    r1_tarski(k2_relat_1('#skF_11'),k3_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_15089])).

tff(c_2486,plain,(
    ! [A_289,C_290,B_291] :
      ( r1_tarski(k2_xboole_0(A_289,C_290),B_291)
      | ~ r1_tarski(C_290,B_291)
      | ~ r1_tarski(A_289,B_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_19423,plain,(
    ! [A_654,B_655] :
      ( r1_tarski(k3_relat_1(A_654),B_655)
      | ~ r1_tarski(k2_relat_1(A_654),B_655)
      | ~ r1_tarski(k1_relat_1(A_654),B_655)
      | ~ v1_relat_1(A_654) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_2486])).

tff(c_96,plain,(
    ~ r1_tarski(k3_relat_1('#skF_11'),k3_relat_1('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_19506,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_11'),k3_relat_1('#skF_12'))
    | ~ r1_tarski(k1_relat_1('#skF_11'),k3_relat_1('#skF_12'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_19423,c_96])).

tff(c_19536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_17650,c_15111,c_19506])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 13:44:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.56/4.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.65/4.17  
% 10.65/4.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.65/4.17  %$ r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_11 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_12
% 10.65/4.17  
% 10.65/4.17  %Foreground sorts:
% 10.65/4.17  
% 10.65/4.17  
% 10.65/4.17  %Background operators:
% 10.65/4.17  
% 10.65/4.17  
% 10.65/4.17  %Foreground operators:
% 10.65/4.17  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 10.65/4.17  tff(r2_tarski, type, r2_tarski: ($i * $i) > $o).
% 10.65/4.17  tff('#skF_4', type, '#skF_4': $i > $i).
% 10.65/4.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.65/4.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.65/4.17  tff('#skF_11', type, '#skF_11': $i).
% 10.65/4.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.65/4.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.65/4.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.65/4.17  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 10.65/4.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.65/4.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.65/4.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.65/4.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.65/4.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.65/4.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.65/4.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.65/4.17  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 10.65/4.17  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 10.65/4.17  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 10.65/4.17  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 10.65/4.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.65/4.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.65/4.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.65/4.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.65/4.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.65/4.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.65/4.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.65/4.17  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 10.65/4.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.65/4.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.65/4.17  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 10.65/4.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.65/4.17  tff('#skF_12', type, '#skF_12': $i).
% 10.65/4.17  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.65/4.17  
% 10.65/4.20  tff(f_202, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 10.65/4.20  tff(f_169, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 10.65/4.20  tff(f_97, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.65/4.20  tff(f_103, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 10.65/4.20  tff(f_89, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 10.65/4.20  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 10.65/4.20  tff(f_69, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.65/4.20  tff(f_73, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 10.65/4.20  tff(f_75, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 10.65/4.20  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.65/4.20  tff(f_85, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.65/4.20  tff(f_71, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.65/4.20  tff(f_61, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.65/4.20  tff(f_83, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 10.65/4.20  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.65/4.20  tff(f_165, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 10.65/4.20  tff(f_149, axiom, (![A]: (?[B]: (((r2_hidden(A, B) & (![C, D]: ((r2_hidden(C, B) & r1_tarski(D, C)) => r2_hidden(D, B)))) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & (![E]: (r1_tarski(E, C) => r2_hidden(E, D)))))))) & (![C]: ~((r1_tarski(C, B) & ~r2_tarski(C, B)) & ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_tarski)).
% 10.65/4.20  tff(f_116, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 10.65/4.20  tff(f_87, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 10.65/4.20  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 10.65/4.20  tff(f_79, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 10.65/4.20  tff(f_67, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 10.65/4.20  tff(f_151, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 10.65/4.20  tff(f_176, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_relat_1)).
% 10.65/4.20  tff(f_95, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 10.65/4.20  tff(f_35, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.65/4.20  tff(f_157, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 10.65/4.20  tff(f_185, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 10.65/4.20  tff(f_192, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k2_relat_1(A), k2_relat_1(B)), k2_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_relat_1)).
% 10.65/4.20  tff(c_102, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.65/4.20  tff(c_100, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.65/4.20  tff(c_88, plain, (![A_122]: (k2_xboole_0(k1_relat_1(A_122), k2_relat_1(A_122))=k3_relat_1(A_122) | ~v1_relat_1(A_122))), inference(cnfTransformation, [status(thm)], [f_169])).
% 10.65/4.20  tff(c_48, plain, (![B_42, A_41]: (k2_tarski(B_42, A_41)=k2_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.65/4.20  tff(c_227, plain, (![A_152, B_153]: (k3_tarski(k2_tarski(A_152, B_153))=k2_xboole_0(A_152, B_153))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.65/4.20  tff(c_257, plain, (![B_156, A_157]: (k3_tarski(k2_tarski(B_156, A_157))=k2_xboole_0(A_157, B_156))), inference(superposition, [status(thm), theory('equality')], [c_48, c_227])).
% 10.65/4.20  tff(c_54, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.65/4.20  tff(c_280, plain, (![B_158, A_159]: (k2_xboole_0(B_158, A_159)=k2_xboole_0(A_159, B_158))), inference(superposition, [status(thm), theory('equality')], [c_257, c_54])).
% 10.65/4.20  tff(c_44, plain, (![A_36, B_37]: (r1_tarski(A_36, k2_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.65/4.20  tff(c_295, plain, (![A_159, B_158]: (r1_tarski(A_159, k2_xboole_0(B_158, A_159)))), inference(superposition, [status(thm), theory('equality')], [c_280, c_44])).
% 10.65/4.20  tff(c_12, plain, (![A_8]: (k2_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.65/4.20  tff(c_28, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.65/4.20  tff(c_32, plain, (![A_23]: (k4_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.65/4.20  tff(c_1947, plain, (![A_275, B_276, C_277]: (k4_xboole_0(k4_xboole_0(A_275, B_276), C_277)=k4_xboole_0(A_275, k2_xboole_0(B_276, C_277)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.65/4.20  tff(c_3109, plain, (![A_326, C_327]: (k4_xboole_0(A_326, k2_xboole_0(k1_xboole_0, C_327))=k4_xboole_0(A_326, C_327))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1947])).
% 10.65/4.20  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.65/4.20  tff(c_333, plain, (![A_162, B_163]: (k4_xboole_0(A_162, k4_xboole_0(A_162, B_163))=k3_xboole_0(A_162, B_163))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.65/4.20  tff(c_30, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.65/4.20  tff(c_354, plain, (![A_164, B_165]: (r1_tarski(k3_xboole_0(A_164, B_165), A_164))), inference(superposition, [status(thm), theory('equality')], [c_333, c_30])).
% 10.65/4.20  tff(c_357, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_354])).
% 10.65/4.20  tff(c_371, plain, (![B_168, A_169]: (B_168=A_169 | ~r1_tarski(B_168, A_169) | ~r1_tarski(A_169, B_168))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.65/4.20  tff(c_400, plain, (![A_170]: (k1_xboole_0=A_170 | ~r1_tarski(A_170, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_371])).
% 10.65/4.20  tff(c_421, plain, (![B_2]: (k3_xboole_0(B_2, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_357, c_400])).
% 10.65/4.20  tff(c_351, plain, (![A_23]: (k4_xboole_0(A_23, A_23)=k3_xboole_0(A_23, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_333])).
% 10.65/4.20  tff(c_539, plain, (![A_23]: (k4_xboole_0(A_23, A_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_421, c_351])).
% 10.65/4.20  tff(c_3248, plain, (![C_328]: (k4_xboole_0(k2_xboole_0(k1_xboole_0, C_328), C_328)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3109, c_539])).
% 10.65/4.20  tff(c_38, plain, (![A_30, B_31, C_32]: (r1_tarski(A_30, k2_xboole_0(B_31, C_32)) | ~r1_tarski(k4_xboole_0(A_30, B_31), C_32))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.65/4.20  tff(c_3263, plain, (![C_328, C_32]: (r1_tarski(k2_xboole_0(k1_xboole_0, C_328), k2_xboole_0(C_328, C_32)) | ~r1_tarski(k1_xboole_0, C_32))), inference(superposition, [status(thm), theory('equality')], [c_3248, c_38])).
% 10.65/4.20  tff(c_3399, plain, (![C_332, C_333]: (r1_tarski(k2_xboole_0(k1_xboole_0, C_332), k2_xboole_0(C_332, C_333)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_3263])).
% 10.65/4.20  tff(c_3434, plain, (![A_334]: (r1_tarski(k2_xboole_0(k1_xboole_0, A_334), A_334))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3399])).
% 10.65/4.20  tff(c_20, plain, (![B_16, A_15]: (B_16=A_15 | ~r1_tarski(B_16, A_15) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.65/4.20  tff(c_3463, plain, (![A_334]: (k2_xboole_0(k1_xboole_0, A_334)=A_334 | ~r1_tarski(A_334, k2_xboole_0(k1_xboole_0, A_334)))), inference(resolution, [status(thm)], [c_3434, c_20])).
% 10.65/4.20  tff(c_3489, plain, (![A_334]: (k2_xboole_0(k1_xboole_0, A_334)=A_334)), inference(demodulation, [status(thm), theory('equality')], [c_295, c_3463])).
% 10.65/4.20  tff(c_263, plain, (![B_156, A_157]: (k2_xboole_0(B_156, A_157)=k2_xboole_0(A_157, B_156))), inference(superposition, [status(thm), theory('equality')], [c_257, c_54])).
% 10.65/4.20  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.65/4.20  tff(c_76, plain, (![C_118, A_103]: (r2_hidden(k4_tarski(C_118, '#skF_9'(A_103, k1_relat_1(A_103), C_118)), A_103) | ~r2_hidden(C_118, k1_relat_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_165])).
% 10.65/4.20  tff(c_64, plain, (![A_57]: (r2_hidden(A_57, '#skF_4'(A_57)))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.65/4.20  tff(c_673, plain, (![C_194, B_195, A_196]: (r2_hidden(C_194, B_195) | ~r2_hidden(C_194, A_196) | ~r1_tarski(A_196, B_195))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.65/4.20  tff(c_698, plain, (![A_199, B_200]: (r2_hidden(A_199, B_200) | ~r1_tarski('#skF_4'(A_199), B_200))), inference(resolution, [status(thm)], [c_64, c_673])).
% 10.65/4.20  tff(c_712, plain, (![A_199, B_37]: (r2_hidden(A_199, k2_xboole_0('#skF_4'(A_199), B_37)))), inference(resolution, [status(thm)], [c_44, c_698])).
% 10.65/4.20  tff(c_58, plain, (![A_50, B_51]: (r2_hidden('#skF_3'(A_50, B_51), B_51) | ~r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.65/4.20  tff(c_42, plain, (![A_35]: (r1_xboole_0(A_35, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.65/4.20  tff(c_1079, plain, (![A_225, B_226, C_227]: (~r1_xboole_0(A_225, B_226) | ~r2_hidden(C_227, B_226) | ~r2_hidden(C_227, A_225))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.65/4.20  tff(c_1083, plain, (![C_228, A_229]: (~r2_hidden(C_228, k1_xboole_0) | ~r2_hidden(C_228, A_229))), inference(resolution, [status(thm)], [c_42, c_1079])).
% 10.65/4.20  tff(c_6645, plain, (![A_436, A_437]: (~r2_hidden('#skF_3'(A_436, k1_xboole_0), A_437) | ~r2_hidden(A_436, k1_xboole_0))), inference(resolution, [status(thm)], [c_58, c_1083])).
% 10.65/4.20  tff(c_6677, plain, (![A_438]: (~r2_hidden(A_438, k1_xboole_0))), inference(resolution, [status(thm)], [c_712, c_6645])).
% 10.65/4.20  tff(c_6760, plain, (![C_442]: (~r2_hidden(C_442, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_76, c_6677])).
% 10.65/4.20  tff(c_6834, plain, (![B_446]: (r1_tarski(k1_relat_1(k1_xboole_0), B_446))), inference(resolution, [status(thm)], [c_8, c_6760])).
% 10.65/4.20  tff(c_398, plain, (![A_20]: (k1_xboole_0=A_20 | ~r1_tarski(A_20, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_371])).
% 10.65/4.20  tff(c_6893, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6834, c_398])).
% 10.65/4.20  tff(c_24, plain, (![B_16]: (r1_tarski(B_16, B_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.65/4.20  tff(c_1314, plain, (![A_240, B_241, C_242]: (r1_tarski(k4_xboole_0(A_240, B_241), C_242) | ~r1_tarski(A_240, k2_xboole_0(B_241, C_242)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.65/4.20  tff(c_98, plain, (r1_tarski('#skF_11', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.65/4.20  tff(c_737, plain, (![A_203, C_204, B_205]: (r1_tarski(A_203, C_204) | ~r1_tarski(B_205, C_204) | ~r1_tarski(A_203, B_205))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.65/4.20  tff(c_765, plain, (![A_203]: (r1_tarski(A_203, '#skF_12') | ~r1_tarski(A_203, '#skF_11'))), inference(resolution, [status(thm)], [c_98, c_737])).
% 10.65/4.20  tff(c_1353, plain, (![A_240, B_241]: (r1_tarski(k4_xboole_0(A_240, B_241), '#skF_12') | ~r1_tarski(A_240, k2_xboole_0(B_241, '#skF_11')))), inference(resolution, [status(thm)], [c_1314, c_765])).
% 10.65/4.20  tff(c_1477, plain, (![A_249, B_250, C_251]: (r1_tarski(A_249, k2_xboole_0(B_250, C_251)) | ~r1_tarski(k4_xboole_0(A_249, B_250), C_251))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.65/4.20  tff(c_4040, plain, (![A_358, B_359]: (r1_tarski(A_358, k2_xboole_0(B_359, '#skF_12')) | ~r1_tarski(A_358, k2_xboole_0(B_359, '#skF_11')))), inference(resolution, [status(thm)], [c_1353, c_1477])).
% 10.65/4.20  tff(c_4155, plain, (![B_360]: (r1_tarski(k2_xboole_0(B_360, '#skF_11'), k2_xboole_0(B_360, '#skF_12')))), inference(resolution, [status(thm)], [c_24, c_4040])).
% 10.65/4.20  tff(c_4193, plain, (r1_tarski(k2_xboole_0('#skF_12', '#skF_11'), '#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_12, c_4155])).
% 10.65/4.20  tff(c_4205, plain, (k2_xboole_0('#skF_12', '#skF_11')='#skF_12' | ~r1_tarski('#skF_12', k2_xboole_0('#skF_12', '#skF_11'))), inference(resolution, [status(thm)], [c_4193, c_20])).
% 10.65/4.20  tff(c_4210, plain, (k2_xboole_0('#skF_12', '#skF_11')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4205])).
% 10.65/4.20  tff(c_423, plain, (![B_22]: (k4_xboole_0(k1_xboole_0, B_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_400])).
% 10.65/4.20  tff(c_1992, plain, (![A_23, C_277]: (k4_xboole_0(A_23, k2_xboole_0(A_23, C_277))=k4_xboole_0(k1_xboole_0, C_277))), inference(superposition, [status(thm), theory('equality')], [c_539, c_1947])).
% 10.65/4.20  tff(c_2022, plain, (![A_278, C_279]: (k4_xboole_0(A_278, k2_xboole_0(A_278, C_279))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_423, c_1992])).
% 10.65/4.20  tff(c_2095, plain, (![A_157, B_156]: (k4_xboole_0(A_157, k2_xboole_0(B_156, A_157))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_263, c_2022])).
% 10.65/4.20  tff(c_4247, plain, (k4_xboole_0('#skF_11', '#skF_12')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4210, c_2095])).
% 10.65/4.20  tff(c_70, plain, (![A_98, B_99]: (k6_subset_1(A_98, B_99)=k4_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.65/4.20  tff(c_90, plain, (![A_123, B_125]: (r1_tarski(k6_subset_1(k1_relat_1(A_123), k1_relat_1(B_125)), k1_relat_1(k6_subset_1(A_123, B_125))) | ~v1_relat_1(B_125) | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_176])).
% 10.65/4.20  tff(c_4781, plain, (![A_368, B_369]: (r1_tarski(k4_xboole_0(k1_relat_1(A_368), k1_relat_1(B_369)), k1_relat_1(k4_xboole_0(A_368, B_369))) | ~v1_relat_1(B_369) | ~v1_relat_1(A_368))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_70, c_90])).
% 10.65/4.20  tff(c_17089, plain, (![A_633, B_634]: (r1_tarski(k1_relat_1(A_633), k2_xboole_0(k1_relat_1(B_634), k1_relat_1(k4_xboole_0(A_633, B_634)))) | ~v1_relat_1(B_634) | ~v1_relat_1(A_633))), inference(resolution, [status(thm)], [c_4781, c_38])).
% 10.65/4.20  tff(c_17158, plain, (r1_tarski(k1_relat_1('#skF_11'), k2_xboole_0(k1_relat_1('#skF_12'), k1_relat_1(k1_xboole_0))) | ~v1_relat_1('#skF_12') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_4247, c_17089])).
% 10.65/4.20  tff(c_17209, plain, (r1_tarski(k1_relat_1('#skF_11'), k1_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_3489, c_263, c_6893, c_17158])).
% 10.65/4.20  tff(c_46, plain, (![A_38, C_40, B_39]: (r1_tarski(k2_xboole_0(A_38, C_40), B_39) | ~r1_tarski(C_40, B_39) | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.65/4.20  tff(c_6710, plain, (![A_439, B_440]: (k2_xboole_0(A_439, B_440)=A_439 | ~r1_tarski(k2_xboole_0(A_439, B_440), A_439))), inference(resolution, [status(thm)], [c_44, c_371])).
% 10.65/4.20  tff(c_6731, plain, (![B_39, C_40]: (k2_xboole_0(B_39, C_40)=B_39 | ~r1_tarski(C_40, B_39) | ~r1_tarski(B_39, B_39))), inference(resolution, [status(thm)], [c_46, c_6710])).
% 10.65/4.20  tff(c_6753, plain, (![B_39, C_40]: (k2_xboole_0(B_39, C_40)=B_39 | ~r1_tarski(C_40, B_39))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_6731])).
% 10.65/4.20  tff(c_17227, plain, (k2_xboole_0(k1_relat_1('#skF_12'), k1_relat_1('#skF_11'))=k1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_17209, c_6753])).
% 10.65/4.20  tff(c_2212, plain, (![A_282, B_283]: (k4_xboole_0(A_282, k2_xboole_0(B_283, A_282))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_263, c_2022])).
% 10.65/4.20  tff(c_2240, plain, (![A_282, B_283, C_32]: (r1_tarski(A_282, k2_xboole_0(k2_xboole_0(B_283, A_282), C_32)) | ~r1_tarski(k1_xboole_0, C_32))), inference(superposition, [status(thm), theory('equality')], [c_2212, c_38])).
% 10.65/4.20  tff(c_2306, plain, (![A_282, B_283, C_32]: (r1_tarski(A_282, k2_xboole_0(k2_xboole_0(B_283, A_282), C_32)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2240])).
% 10.65/4.20  tff(c_17580, plain, (![C_635]: (r1_tarski(k1_relat_1('#skF_11'), k2_xboole_0(k1_relat_1('#skF_12'), C_635)))), inference(superposition, [status(thm), theory('equality')], [c_17227, c_2306])).
% 10.65/4.20  tff(c_17622, plain, (r1_tarski(k1_relat_1('#skF_11'), k3_relat_1('#skF_12')) | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_88, c_17580])).
% 10.65/4.20  tff(c_17650, plain, (r1_tarski(k1_relat_1('#skF_11'), k3_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_17622])).
% 10.65/4.20  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.65/4.20  tff(c_109, plain, (![A_136]: (v1_relat_1(A_136) | ~v1_xboole_0(A_136))), inference(cnfTransformation, [status(thm)], [f_157])).
% 10.65/4.20  tff(c_113, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_109])).
% 10.65/4.20  tff(c_92, plain, (![A_126, B_127]: (r2_hidden('#skF_10'(A_126, B_127), k1_relat_1(B_127)) | ~r2_hidden(A_126, k2_relat_1(B_127)) | ~v1_relat_1(B_127))), inference(cnfTransformation, [status(thm)], [f_185])).
% 10.65/4.20  tff(c_6772, plain, (![A_126]: (~r2_hidden(A_126, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_92, c_6760])).
% 10.65/4.20  tff(c_6935, plain, (![A_447]: (~r2_hidden(A_447, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_6772])).
% 10.65/4.20  tff(c_7082, plain, (![B_451]: (r1_tarski(k2_relat_1(k1_xboole_0), B_451))), inference(resolution, [status(thm)], [c_8, c_6935])).
% 10.65/4.20  tff(c_7141, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_7082, c_398])).
% 10.65/4.20  tff(c_94, plain, (![A_129, B_131]: (r1_tarski(k6_subset_1(k2_relat_1(A_129), k2_relat_1(B_131)), k2_relat_1(k6_subset_1(A_129, B_131))) | ~v1_relat_1(B_131) | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.65/4.20  tff(c_4393, plain, (![A_361, B_362]: (r1_tarski(k4_xboole_0(k2_relat_1(A_361), k2_relat_1(B_362)), k2_relat_1(k4_xboole_0(A_361, B_362))) | ~v1_relat_1(B_362) | ~v1_relat_1(A_361))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_70, c_94])).
% 10.65/4.20  tff(c_13981, plain, (![A_596, B_597]: (r1_tarski(k2_relat_1(A_596), k2_xboole_0(k2_relat_1(B_597), k2_relat_1(k4_xboole_0(A_596, B_597)))) | ~v1_relat_1(B_597) | ~v1_relat_1(A_596))), inference(resolution, [status(thm)], [c_4393, c_38])).
% 10.65/4.20  tff(c_14032, plain, (r1_tarski(k2_relat_1('#skF_11'), k2_xboole_0(k2_relat_1('#skF_12'), k2_relat_1(k1_xboole_0))) | ~v1_relat_1('#skF_12') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_4247, c_13981])).
% 10.65/4.20  tff(c_14078, plain, (r1_tarski(k2_relat_1('#skF_11'), k2_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_3489, c_263, c_7141, c_14032])).
% 10.65/4.20  tff(c_14096, plain, (k2_xboole_0(k2_relat_1('#skF_12'), k2_relat_1('#skF_11'))=k2_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_14078, c_6753])).
% 10.65/4.20  tff(c_2047, plain, (![A_278, C_279, C_32]: (r1_tarski(A_278, k2_xboole_0(k2_xboole_0(A_278, C_279), C_32)) | ~r1_tarski(k1_xboole_0, C_32))), inference(superposition, [status(thm), theory('equality')], [c_2022, c_38])).
% 10.65/4.20  tff(c_2534, plain, (![A_292, C_293, C_294]: (r1_tarski(A_292, k2_xboole_0(k2_xboole_0(A_292, C_293), C_294)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2047])).
% 10.65/4.20  tff(c_2675, plain, (![A_302, A_303, C_304]: (r1_tarski(A_302, k2_xboole_0(A_303, k2_xboole_0(A_302, C_304))))), inference(superposition, [status(thm), theory('equality')], [c_263, c_2534])).
% 10.65/4.20  tff(c_2700, plain, (![B_156, A_303, A_157]: (r1_tarski(B_156, k2_xboole_0(A_303, k2_xboole_0(A_157, B_156))))), inference(superposition, [status(thm), theory('equality')], [c_263, c_2675])).
% 10.65/4.20  tff(c_15065, plain, (![A_608]: (r1_tarski(k2_relat_1('#skF_11'), k2_xboole_0(A_608, k2_relat_1('#skF_12'))))), inference(superposition, [status(thm), theory('equality')], [c_14096, c_2700])).
% 10.65/4.20  tff(c_15089, plain, (r1_tarski(k2_relat_1('#skF_11'), k3_relat_1('#skF_12')) | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_88, c_15065])).
% 10.65/4.20  tff(c_15111, plain, (r1_tarski(k2_relat_1('#skF_11'), k3_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_15089])).
% 10.65/4.20  tff(c_2486, plain, (![A_289, C_290, B_291]: (r1_tarski(k2_xboole_0(A_289, C_290), B_291) | ~r1_tarski(C_290, B_291) | ~r1_tarski(A_289, B_291))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.65/4.20  tff(c_19423, plain, (![A_654, B_655]: (r1_tarski(k3_relat_1(A_654), B_655) | ~r1_tarski(k2_relat_1(A_654), B_655) | ~r1_tarski(k1_relat_1(A_654), B_655) | ~v1_relat_1(A_654))), inference(superposition, [status(thm), theory('equality')], [c_88, c_2486])).
% 10.65/4.20  tff(c_96, plain, (~r1_tarski(k3_relat_1('#skF_11'), k3_relat_1('#skF_12'))), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.65/4.20  tff(c_19506, plain, (~r1_tarski(k2_relat_1('#skF_11'), k3_relat_1('#skF_12')) | ~r1_tarski(k1_relat_1('#skF_11'), k3_relat_1('#skF_12')) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_19423, c_96])).
% 10.65/4.20  tff(c_19536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_17650, c_15111, c_19506])).
% 10.65/4.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.65/4.20  
% 10.65/4.20  Inference rules
% 10.65/4.20  ----------------------
% 10.65/4.20  #Ref     : 0
% 10.65/4.20  #Sup     : 4689
% 10.65/4.20  #Fact    : 0
% 10.65/4.20  #Define  : 0
% 10.65/4.20  #Split   : 1
% 10.65/4.20  #Chain   : 0
% 10.65/4.20  #Close   : 0
% 10.65/4.20  
% 10.65/4.20  Ordering : KBO
% 10.65/4.20  
% 10.65/4.20  Simplification rules
% 10.65/4.20  ----------------------
% 10.65/4.20  #Subsume      : 457
% 10.65/4.20  #Demod        : 3528
% 10.65/4.20  #Tautology    : 2368
% 10.65/4.20  #SimpNegUnit  : 5
% 10.65/4.20  #BackRed      : 11
% 10.65/4.20  
% 10.65/4.20  #Partial instantiations: 0
% 10.65/4.20  #Strategies tried      : 1
% 10.65/4.20  
% 10.65/4.20  Timing (in seconds)
% 10.65/4.20  ----------------------
% 10.65/4.20  Preprocessing        : 0.39
% 10.65/4.20  Parsing              : 0.20
% 10.65/4.20  CNF conversion       : 0.03
% 10.65/4.20  Main loop            : 2.98
% 10.65/4.20  Inferencing          : 0.60
% 10.65/4.20  Reduction            : 1.50
% 10.65/4.20  Demodulation         : 1.28
% 10.65/4.20  BG Simplification    : 0.07
% 10.65/4.20  Subsumption          : 0.64
% 10.65/4.20  Abstraction          : 0.09
% 10.65/4.20  MUC search           : 0.00
% 10.65/4.20  Cooper               : 0.00
% 10.65/4.20  Total                : 3.42
% 10.65/4.20  Index Insertion      : 0.00
% 10.65/4.20  Index Deletion       : 0.00
% 10.65/4.20  Index Matching       : 0.00
% 10.65/4.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
