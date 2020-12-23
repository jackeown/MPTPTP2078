%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:33 EST 2020

% Result     : Theorem 8.62s
% Output     : CNFRefutation 8.73s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 153 expanded)
%              Number of leaves         :   52 (  74 expanded)
%              Depth                    :   16
%              Number of atoms          :  168 ( 265 expanded)
%              Number of equality atoms :   24 (  37 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_4 > #skF_11 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_7 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(r2_tarski,type,(
    r2_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_189,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_179,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_161,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_75,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_157,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_145,axiom,(
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

tff(f_112,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_89,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
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

tff(f_77,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_147,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_168,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(c_84,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_82,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_80,plain,(
    r1_tarski('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_74,plain,(
    ! [A_112,B_114] :
      ( r1_tarski(k2_relat_1(A_112),k2_relat_1(B_114))
      | ~ r1_tarski(A_112,B_114)
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_308,plain,(
    ! [A_164] :
      ( k2_xboole_0(k1_relat_1(A_164),k2_relat_1(A_164)) = k3_relat_1(A_164)
      | ~ v1_relat_1(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_16,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_tarski(A_10,k2_xboole_0(C_12,B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_314,plain,(
    ! [A_10,A_164] :
      ( r1_tarski(A_10,k3_relat_1(A_164))
      | ~ r1_tarski(A_10,k2_relat_1(A_164))
      | ~ v1_relat_1(A_164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_16])).

tff(c_70,plain,(
    ! [A_108] :
      ( k2_xboole_0(k1_relat_1(A_108),k2_relat_1(A_108)) = k3_relat_1(A_108)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1022,plain,(
    ! [A_238,C_239,B_240] :
      ( r1_tarski(k2_xboole_0(A_238,C_239),B_240)
      | ~ r1_tarski(C_239,B_240)
      | ~ r1_tarski(A_238,B_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_16978,plain,(
    ! [A_521,B_522] :
      ( r1_tarski(k3_relat_1(A_521),B_522)
      | ~ r1_tarski(k2_relat_1(A_521),B_522)
      | ~ r1_tarski(k1_relat_1(A_521),B_522)
      | ~ v1_relat_1(A_521) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1022])).

tff(c_78,plain,(
    ~ r1_tarski(k3_relat_1('#skF_10'),k3_relat_1('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_17043,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_10'),k3_relat_1('#skF_11'))
    | ~ r1_tarski(k1_relat_1('#skF_10'),k3_relat_1('#skF_11'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_16978,c_78])).

tff(c_17067,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_10'),k3_relat_1('#skF_11'))
    | ~ r1_tarski(k1_relat_1('#skF_10'),k3_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_17043])).

tff(c_17068,plain,(
    ~ r1_tarski(k1_relat_1('#skF_10'),k3_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_17067])).

tff(c_22,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3541,plain,(
    ! [C_324,A_325] :
      ( r2_hidden(k4_tarski(C_324,'#skF_9'(A_325,k1_relat_1(A_325),C_324)),A_325)
      | ~ r2_hidden(C_324,k1_relat_1(A_325)) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_48,plain,(
    ! [A_44] : r2_hidden(A_44,'#skF_4'(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_247,plain,(
    ! [C_151,A_152,D_153] :
      ( r2_hidden(C_151,k1_relat_1(A_152))
      | ~ r2_hidden(k4_tarski(C_151,D_153),A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_252,plain,(
    ! [C_151,D_153] : r2_hidden(C_151,k1_relat_1('#skF_4'(k4_tarski(C_151,D_153)))) ),
    inference(resolution,[status(thm)],[c_48,c_247])).

tff(c_42,plain,(
    ! [A_37,B_38] :
      ( r2_hidden('#skF_3'(A_37,B_38),B_38)
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_32,plain,(
    ! [A_29] : r1_xboole_0(A_29,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_259,plain,(
    ! [A_156,B_157,C_158] :
      ( ~ r1_xboole_0(A_156,B_157)
      | ~ r2_hidden(C_158,B_157)
      | ~ r2_hidden(C_158,A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_263,plain,(
    ! [C_159,A_160] :
      ( ~ r2_hidden(C_159,k1_xboole_0)
      | ~ r2_hidden(C_159,A_160) ) ),
    inference(resolution,[status(thm)],[c_32,c_259])).

tff(c_321,plain,(
    ! [A_165,A_166] :
      ( ~ r2_hidden('#skF_3'(A_165,k1_xboole_0),A_166)
      | ~ r2_hidden(A_165,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_42,c_263])).

tff(c_332,plain,(
    ! [A_165] : ~ r2_hidden(A_165,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_252,c_321])).

tff(c_3560,plain,(
    ! [C_326] : ~ r2_hidden(C_326,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_3541,c_332])).

tff(c_3585,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_3560])).

tff(c_24,plain,(
    ! [A_20,B_21] : r1_tarski(k4_xboole_0(A_20,B_21),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_tarski(A_13,k3_xboole_0(B_14,C_15))
      | ~ r1_tarski(A_13,C_15)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_137,plain,(
    ! [A_136,B_137] : k4_xboole_0(A_136,k4_xboole_0(A_136,B_137)) = k3_xboole_0(A_136,B_137) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_149,plain,(
    ! [A_136,B_137] : r1_tarski(k3_xboole_0(A_136,B_137),A_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_24])).

tff(c_161,plain,(
    ! [B_144,A_145] :
      ( B_144 = A_145
      | ~ r1_tarski(B_144,A_145)
      | ~ r1_tarski(A_145,B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3877,plain,(
    ! [A_333,B_334] :
      ( k3_xboole_0(A_333,B_334) = A_333
      | ~ r1_tarski(A_333,k3_xboole_0(A_333,B_334)) ) ),
    inference(resolution,[status(thm)],[c_149,c_161])).

tff(c_3885,plain,(
    ! [B_14,C_15] :
      ( k3_xboole_0(B_14,C_15) = B_14
      | ~ r1_tarski(B_14,C_15)
      | ~ r1_tarski(B_14,B_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_3877])).

tff(c_3901,plain,(
    ! [B_335,C_336] :
      ( k3_xboole_0(B_335,C_336) = B_335
      | ~ r1_tarski(B_335,C_336) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3885])).

tff(c_4047,plain,(
    k3_xboole_0('#skF_10','#skF_11') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_80,c_3901])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,k4_xboole_0(B_23,A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_11185,plain,(
    ! [A_448,B_449] :
      ( k4_xboole_0(A_448,B_449) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(A_448,B_449),k3_xboole_0(A_448,B_449)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_26])).

tff(c_11242,plain,
    ( k4_xboole_0('#skF_10','#skF_11') = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0('#skF_10','#skF_11'),'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_4047,c_11185])).

tff(c_11290,plain,(
    k4_xboole_0('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_11242])).

tff(c_54,plain,(
    ! [A_85,B_86] : k6_subset_1(A_85,B_86) = k4_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_72,plain,(
    ! [A_109,B_111] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_109),k1_relat_1(B_111)),k1_relat_1(k6_subset_1(A_109,B_111)))
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_85,plain,(
    ! [A_109,B_111] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_109),k1_relat_1(B_111)),k1_relat_1(k4_xboole_0(A_109,B_111)))
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_72])).

tff(c_11334,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1('#skF_10'),k1_relat_1('#skF_11')),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_11290,c_85])).

tff(c_11412,plain,(
    r1_tarski(k4_xboole_0(k1_relat_1('#skF_10'),k1_relat_1('#skF_11')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_3585,c_11334])).

tff(c_182,plain,(
    ! [A_19] :
      ( k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_161])).

tff(c_15689,plain,(
    k4_xboole_0(k1_relat_1('#skF_10'),k1_relat_1('#skF_11')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11412,c_182])).

tff(c_28,plain,(
    ! [A_24,B_25,C_26] :
      ( r1_tarski(A_24,k2_xboole_0(B_25,C_26))
      | ~ r1_tarski(k4_xboole_0(A_24,B_25),C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_15890,plain,(
    ! [C_26] :
      ( r1_tarski(k1_relat_1('#skF_10'),k2_xboole_0(k1_relat_1('#skF_11'),C_26))
      | ~ r1_tarski(k1_xboole_0,C_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15689,c_28])).

tff(c_17611,plain,(
    ! [C_533] : r1_tarski(k1_relat_1('#skF_10'),k2_xboole_0(k1_relat_1('#skF_11'),C_533)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_15890])).

tff(c_17645,plain,
    ( r1_tarski(k1_relat_1('#skF_10'),k3_relat_1('#skF_11'))
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_17611])).

tff(c_17656,plain,(
    r1_tarski(k1_relat_1('#skF_10'),k3_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_17645])).

tff(c_17658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17068,c_17656])).

tff(c_17659,plain,(
    ~ r1_tarski(k2_relat_1('#skF_10'),k3_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_17067])).

tff(c_17663,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_10'),k2_relat_1('#skF_11'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_314,c_17659])).

tff(c_17666,plain,(
    ~ r1_tarski(k2_relat_1('#skF_10'),k2_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_17663])).

tff(c_17692,plain,
    ( ~ r1_tarski('#skF_10','#skF_11')
    | ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_74,c_17666])).

tff(c_17696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_17692])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.62/3.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.62/3.30  
% 8.62/3.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.62/3.30  %$ r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_4 > #skF_11 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_7 > #skF_1 > #skF_5
% 8.62/3.30  
% 8.62/3.30  %Foreground sorts:
% 8.62/3.30  
% 8.62/3.30  
% 8.62/3.30  %Background operators:
% 8.62/3.30  
% 8.62/3.30  
% 8.62/3.30  %Foreground operators:
% 8.62/3.30  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.62/3.30  tff(r2_tarski, type, r2_tarski: ($i * $i) > $o).
% 8.62/3.30  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.62/3.30  tff('#skF_4', type, '#skF_4': $i > $i).
% 8.62/3.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.62/3.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.62/3.30  tff('#skF_11', type, '#skF_11': $i).
% 8.62/3.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.62/3.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.62/3.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.62/3.30  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 8.62/3.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.62/3.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.62/3.30  tff('#skF_10', type, '#skF_10': $i).
% 8.62/3.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.62/3.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.62/3.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.62/3.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.62/3.30  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 8.62/3.30  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 8.62/3.30  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 8.62/3.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.62/3.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.62/3.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.62/3.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.62/3.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.62/3.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.62/3.30  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 8.62/3.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.62/3.30  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.62/3.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.62/3.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.62/3.30  
% 8.73/3.32  tff(f_189, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 8.73/3.32  tff(f_179, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 8.73/3.32  tff(f_161, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 8.73/3.32  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 8.73/3.32  tff(f_95, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 8.73/3.32  tff(f_75, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.73/3.32  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.73/3.32  tff(f_157, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 8.73/3.32  tff(f_145, axiom, (![A]: (?[B]: (((r2_hidden(A, B) & (![C, D]: ((r2_hidden(C, B) & r1_tarski(D, C)) => r2_hidden(D, B)))) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & (![E]: (r1_tarski(E, C) => r2_hidden(E, D)))))))) & (![C]: ~((r1_tarski(C, B) & ~r2_tarski(C, B)) & ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_tarski)).
% 8.73/3.32  tff(f_112, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 8.73/3.32  tff(f_89, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.73/3.32  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.73/3.32  tff(f_77, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.73/3.32  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.73/3.32  tff(f_67, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 8.73/3.32  tff(f_87, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.73/3.32  tff(f_81, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 8.73/3.32  tff(f_147, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 8.73/3.32  tff(f_168, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_relat_1)).
% 8.73/3.32  tff(f_85, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 8.73/3.32  tff(c_84, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_189])).
% 8.73/3.32  tff(c_82, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_189])).
% 8.73/3.32  tff(c_80, plain, (r1_tarski('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_189])).
% 8.73/3.32  tff(c_74, plain, (![A_112, B_114]: (r1_tarski(k2_relat_1(A_112), k2_relat_1(B_114)) | ~r1_tarski(A_112, B_114) | ~v1_relat_1(B_114) | ~v1_relat_1(A_112))), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.73/3.32  tff(c_308, plain, (![A_164]: (k2_xboole_0(k1_relat_1(A_164), k2_relat_1(A_164))=k3_relat_1(A_164) | ~v1_relat_1(A_164))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.73/3.32  tff(c_16, plain, (![A_10, C_12, B_11]: (r1_tarski(A_10, k2_xboole_0(C_12, B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.73/3.32  tff(c_314, plain, (![A_10, A_164]: (r1_tarski(A_10, k3_relat_1(A_164)) | ~r1_tarski(A_10, k2_relat_1(A_164)) | ~v1_relat_1(A_164))), inference(superposition, [status(thm), theory('equality')], [c_308, c_16])).
% 8.73/3.32  tff(c_70, plain, (![A_108]: (k2_xboole_0(k1_relat_1(A_108), k2_relat_1(A_108))=k3_relat_1(A_108) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.73/3.32  tff(c_1022, plain, (![A_238, C_239, B_240]: (r1_tarski(k2_xboole_0(A_238, C_239), B_240) | ~r1_tarski(C_239, B_240) | ~r1_tarski(A_238, B_240))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.73/3.32  tff(c_16978, plain, (![A_521, B_522]: (r1_tarski(k3_relat_1(A_521), B_522) | ~r1_tarski(k2_relat_1(A_521), B_522) | ~r1_tarski(k1_relat_1(A_521), B_522) | ~v1_relat_1(A_521))), inference(superposition, [status(thm), theory('equality')], [c_70, c_1022])).
% 8.73/3.32  tff(c_78, plain, (~r1_tarski(k3_relat_1('#skF_10'), k3_relat_1('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 8.73/3.32  tff(c_17043, plain, (~r1_tarski(k2_relat_1('#skF_10'), k3_relat_1('#skF_11')) | ~r1_tarski(k1_relat_1('#skF_10'), k3_relat_1('#skF_11')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_16978, c_78])).
% 8.73/3.32  tff(c_17067, plain, (~r1_tarski(k2_relat_1('#skF_10'), k3_relat_1('#skF_11')) | ~r1_tarski(k1_relat_1('#skF_10'), k3_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_17043])).
% 8.73/3.32  tff(c_17068, plain, (~r1_tarski(k1_relat_1('#skF_10'), k3_relat_1('#skF_11'))), inference(splitLeft, [status(thm)], [c_17067])).
% 8.73/3.32  tff(c_22, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.73/3.32  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.73/3.32  tff(c_3541, plain, (![C_324, A_325]: (r2_hidden(k4_tarski(C_324, '#skF_9'(A_325, k1_relat_1(A_325), C_324)), A_325) | ~r2_hidden(C_324, k1_relat_1(A_325)))), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.73/3.32  tff(c_48, plain, (![A_44]: (r2_hidden(A_44, '#skF_4'(A_44)))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.73/3.32  tff(c_247, plain, (![C_151, A_152, D_153]: (r2_hidden(C_151, k1_relat_1(A_152)) | ~r2_hidden(k4_tarski(C_151, D_153), A_152))), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.73/3.32  tff(c_252, plain, (![C_151, D_153]: (r2_hidden(C_151, k1_relat_1('#skF_4'(k4_tarski(C_151, D_153)))))), inference(resolution, [status(thm)], [c_48, c_247])).
% 8.73/3.32  tff(c_42, plain, (![A_37, B_38]: (r2_hidden('#skF_3'(A_37, B_38), B_38) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.73/3.32  tff(c_32, plain, (![A_29]: (r1_xboole_0(A_29, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.73/3.32  tff(c_259, plain, (![A_156, B_157, C_158]: (~r1_xboole_0(A_156, B_157) | ~r2_hidden(C_158, B_157) | ~r2_hidden(C_158, A_156))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.73/3.32  tff(c_263, plain, (![C_159, A_160]: (~r2_hidden(C_159, k1_xboole_0) | ~r2_hidden(C_159, A_160))), inference(resolution, [status(thm)], [c_32, c_259])).
% 8.73/3.32  tff(c_321, plain, (![A_165, A_166]: (~r2_hidden('#skF_3'(A_165, k1_xboole_0), A_166) | ~r2_hidden(A_165, k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_263])).
% 8.73/3.32  tff(c_332, plain, (![A_165]: (~r2_hidden(A_165, k1_xboole_0))), inference(resolution, [status(thm)], [c_252, c_321])).
% 8.73/3.32  tff(c_3560, plain, (![C_326]: (~r2_hidden(C_326, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_3541, c_332])).
% 8.73/3.32  tff(c_3585, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_3560])).
% 8.73/3.32  tff(c_24, plain, (![A_20, B_21]: (r1_tarski(k4_xboole_0(A_20, B_21), A_20))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.73/3.32  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.73/3.32  tff(c_18, plain, (![A_13, B_14, C_15]: (r1_tarski(A_13, k3_xboole_0(B_14, C_15)) | ~r1_tarski(A_13, C_15) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.73/3.32  tff(c_137, plain, (![A_136, B_137]: (k4_xboole_0(A_136, k4_xboole_0(A_136, B_137))=k3_xboole_0(A_136, B_137))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.73/3.32  tff(c_149, plain, (![A_136, B_137]: (r1_tarski(k3_xboole_0(A_136, B_137), A_136))), inference(superposition, [status(thm), theory('equality')], [c_137, c_24])).
% 8.73/3.32  tff(c_161, plain, (![B_144, A_145]: (B_144=A_145 | ~r1_tarski(B_144, A_145) | ~r1_tarski(A_145, B_144))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.73/3.32  tff(c_3877, plain, (![A_333, B_334]: (k3_xboole_0(A_333, B_334)=A_333 | ~r1_tarski(A_333, k3_xboole_0(A_333, B_334)))), inference(resolution, [status(thm)], [c_149, c_161])).
% 8.73/3.32  tff(c_3885, plain, (![B_14, C_15]: (k3_xboole_0(B_14, C_15)=B_14 | ~r1_tarski(B_14, C_15) | ~r1_tarski(B_14, B_14))), inference(resolution, [status(thm)], [c_18, c_3877])).
% 8.73/3.32  tff(c_3901, plain, (![B_335, C_336]: (k3_xboole_0(B_335, C_336)=B_335 | ~r1_tarski(B_335, C_336))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3885])).
% 8.73/3.32  tff(c_4047, plain, (k3_xboole_0('#skF_10', '#skF_11')='#skF_10'), inference(resolution, [status(thm)], [c_80, c_3901])).
% 8.73/3.32  tff(c_26, plain, (![A_22, B_23]: (k1_xboole_0=A_22 | ~r1_tarski(A_22, k4_xboole_0(B_23, A_22)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.73/3.32  tff(c_11185, plain, (![A_448, B_449]: (k4_xboole_0(A_448, B_449)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(A_448, B_449), k3_xboole_0(A_448, B_449)))), inference(superposition, [status(thm), theory('equality')], [c_137, c_26])).
% 8.73/3.32  tff(c_11242, plain, (k4_xboole_0('#skF_10', '#skF_11')=k1_xboole_0 | ~r1_tarski(k4_xboole_0('#skF_10', '#skF_11'), '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_4047, c_11185])).
% 8.73/3.32  tff(c_11290, plain, (k4_xboole_0('#skF_10', '#skF_11')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_11242])).
% 8.73/3.32  tff(c_54, plain, (![A_85, B_86]: (k6_subset_1(A_85, B_86)=k4_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.73/3.32  tff(c_72, plain, (![A_109, B_111]: (r1_tarski(k6_subset_1(k1_relat_1(A_109), k1_relat_1(B_111)), k1_relat_1(k6_subset_1(A_109, B_111))) | ~v1_relat_1(B_111) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_168])).
% 8.73/3.32  tff(c_85, plain, (![A_109, B_111]: (r1_tarski(k4_xboole_0(k1_relat_1(A_109), k1_relat_1(B_111)), k1_relat_1(k4_xboole_0(A_109, B_111))) | ~v1_relat_1(B_111) | ~v1_relat_1(A_109))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_72])).
% 8.73/3.32  tff(c_11334, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_10'), k1_relat_1('#skF_11')), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_11290, c_85])).
% 8.73/3.32  tff(c_11412, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_10'), k1_relat_1('#skF_11')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_3585, c_11334])).
% 8.73/3.32  tff(c_182, plain, (![A_19]: (k1_xboole_0=A_19 | ~r1_tarski(A_19, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_161])).
% 8.73/3.32  tff(c_15689, plain, (k4_xboole_0(k1_relat_1('#skF_10'), k1_relat_1('#skF_11'))=k1_xboole_0), inference(resolution, [status(thm)], [c_11412, c_182])).
% 8.73/3.32  tff(c_28, plain, (![A_24, B_25, C_26]: (r1_tarski(A_24, k2_xboole_0(B_25, C_26)) | ~r1_tarski(k4_xboole_0(A_24, B_25), C_26))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.73/3.32  tff(c_15890, plain, (![C_26]: (r1_tarski(k1_relat_1('#skF_10'), k2_xboole_0(k1_relat_1('#skF_11'), C_26)) | ~r1_tarski(k1_xboole_0, C_26))), inference(superposition, [status(thm), theory('equality')], [c_15689, c_28])).
% 8.73/3.32  tff(c_17611, plain, (![C_533]: (r1_tarski(k1_relat_1('#skF_10'), k2_xboole_0(k1_relat_1('#skF_11'), C_533)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_15890])).
% 8.73/3.32  tff(c_17645, plain, (r1_tarski(k1_relat_1('#skF_10'), k3_relat_1('#skF_11')) | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_70, c_17611])).
% 8.73/3.32  tff(c_17656, plain, (r1_tarski(k1_relat_1('#skF_10'), k3_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_17645])).
% 8.73/3.32  tff(c_17658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17068, c_17656])).
% 8.73/3.32  tff(c_17659, plain, (~r1_tarski(k2_relat_1('#skF_10'), k3_relat_1('#skF_11'))), inference(splitRight, [status(thm)], [c_17067])).
% 8.73/3.32  tff(c_17663, plain, (~r1_tarski(k2_relat_1('#skF_10'), k2_relat_1('#skF_11')) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_314, c_17659])).
% 8.73/3.32  tff(c_17666, plain, (~r1_tarski(k2_relat_1('#skF_10'), k2_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_17663])).
% 8.73/3.32  tff(c_17692, plain, (~r1_tarski('#skF_10', '#skF_11') | ~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_74, c_17666])).
% 8.73/3.32  tff(c_17696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_17692])).
% 8.73/3.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.73/3.32  
% 8.73/3.32  Inference rules
% 8.73/3.32  ----------------------
% 8.73/3.32  #Ref     : 0
% 8.73/3.32  #Sup     : 4311
% 8.73/3.32  #Fact    : 0
% 8.73/3.32  #Define  : 0
% 8.73/3.32  #Split   : 3
% 8.73/3.32  #Chain   : 0
% 8.73/3.32  #Close   : 0
% 8.73/3.32  
% 8.73/3.32  Ordering : KBO
% 8.73/3.32  
% 8.73/3.32  Simplification rules
% 8.73/3.32  ----------------------
% 8.73/3.32  #Subsume      : 446
% 8.73/3.32  #Demod        : 3483
% 8.73/3.32  #Tautology    : 2696
% 8.73/3.32  #SimpNegUnit  : 2
% 8.73/3.32  #BackRed      : 12
% 8.73/3.32  
% 8.73/3.32  #Partial instantiations: 0
% 8.73/3.32  #Strategies tried      : 1
% 8.73/3.32  
% 8.73/3.32  Timing (in seconds)
% 8.73/3.32  ----------------------
% 8.73/3.32  Preprocessing        : 0.37
% 8.73/3.32  Parsing              : 0.19
% 8.73/3.32  CNF conversion       : 0.03
% 8.73/3.32  Main loop            : 2.19
% 8.73/3.32  Inferencing          : 0.53
% 8.73/3.32  Reduction            : 0.98
% 8.73/3.32  Demodulation         : 0.80
% 8.73/3.32  BG Simplification    : 0.06
% 8.73/3.32  Subsumption          : 0.47
% 8.73/3.32  Abstraction          : 0.08
% 8.73/3.32  MUC search           : 0.00
% 8.73/3.32  Cooper               : 0.00
% 8.73/3.32  Total                : 2.60
% 8.73/3.32  Index Insertion      : 0.00
% 8.73/3.32  Index Deletion       : 0.00
% 8.73/3.32  Index Matching       : 0.00
% 8.73/3.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
