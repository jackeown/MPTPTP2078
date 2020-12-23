%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:26 EST 2020

% Result     : Theorem 8.15s
% Output     : CNFRefutation 8.42s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 161 expanded)
%              Number of leaves         :   24 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  239 ( 511 expanded)
%              Number of equality atoms :   32 (  87 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v4_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v4_ordinal1,type,(
    v4_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ( ~ ( ~ v4_ordinal1(A)
              & ! [B] :
                  ( v3_ordinal1(B)
                 => A != k1_ordinal1(B) ) )
          & ~ ( ? [B] :
                  ( v3_ordinal1(B)
                  & A = k1_ordinal1(B) )
              & v4_ordinal1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_ordinal1)).

tff(f_100,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v4_ordinal1(A)
      <=> ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(B,A)
             => r2_hidden(k1_ordinal1(B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

tff(f_71,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_67,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_89,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,k1_ordinal1(B))
          <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_80,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
          <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

tff(c_44,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_42,plain,(
    ! [A_20] :
      ( v3_ordinal1('#skF_1'(A_20))
      | v4_ordinal1(A_20)
      | ~ v3_ordinal1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_26,plain,(
    ! [A_13] :
      ( v3_ordinal1(k1_ordinal1(A_13))
      | ~ v3_ordinal1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2843,plain,(
    ! [B_192,A_193] :
      ( r2_hidden(B_192,A_193)
      | B_192 = A_193
      | r2_hidden(A_193,B_192)
      | ~ v3_ordinal1(B_192)
      | ~ v3_ordinal1(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    ! [A_20] :
      ( ~ r2_hidden(k1_ordinal1('#skF_1'(A_20)),A_20)
      | v4_ordinal1(A_20)
      | ~ v3_ordinal1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3661,plain,(
    ! [B_237] :
      ( v4_ordinal1(B_237)
      | r2_hidden(B_237,k1_ordinal1('#skF_1'(B_237)))
      | k1_ordinal1('#skF_1'(B_237)) = B_237
      | ~ v3_ordinal1(B_237)
      | ~ v3_ordinal1(k1_ordinal1('#skF_1'(B_237))) ) ),
    inference(resolution,[status(thm)],[c_2843,c_38])).

tff(c_34,plain,(
    ! [A_17,B_19] :
      ( r1_ordinal1(A_17,B_19)
      | ~ r2_hidden(A_17,k1_ordinal1(B_19))
      | ~ v3_ordinal1(B_19)
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5423,plain,(
    ! [B_297] :
      ( r1_ordinal1(B_297,'#skF_1'(B_297))
      | ~ v3_ordinal1('#skF_1'(B_297))
      | v4_ordinal1(B_297)
      | k1_ordinal1('#skF_1'(B_297)) = B_297
      | ~ v3_ordinal1(B_297)
      | ~ v3_ordinal1(k1_ordinal1('#skF_1'(B_297))) ) ),
    inference(resolution,[status(thm)],[c_3661,c_34])).

tff(c_5428,plain,(
    ! [B_298] :
      ( r1_ordinal1(B_298,'#skF_1'(B_298))
      | v4_ordinal1(B_298)
      | k1_ordinal1('#skF_1'(B_298)) = B_298
      | ~ v3_ordinal1(B_298)
      | ~ v3_ordinal1('#skF_1'(B_298)) ) ),
    inference(resolution,[status(thm)],[c_26,c_5423])).

tff(c_40,plain,(
    ! [A_20] :
      ( r2_hidden('#skF_1'(A_20),A_20)
      | v4_ordinal1(A_20)
      | ~ v3_ordinal1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30,plain,(
    ! [A_14,B_16] :
      ( r1_ordinal1(k1_ordinal1(A_14),B_16)
      | ~ r2_hidden(A_14,B_16)
      | ~ v3_ordinal1(B_16)
      | ~ v3_ordinal1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    ! [A_17,B_19] :
      ( r2_hidden(A_17,k1_ordinal1(B_19))
      | ~ r1_ordinal1(A_17,B_19)
      | ~ v3_ordinal1(B_19)
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden(A_7,B_8)
      | r2_hidden(A_7,k1_ordinal1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2786,plain,(
    ! [A_187,B_188] :
      ( r1_ordinal1(A_187,B_188)
      | ~ r2_hidden(A_187,k1_ordinal1(B_188))
      | ~ v3_ordinal1(B_188)
      | ~ v3_ordinal1(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2804,plain,(
    ! [A_189,B_190] :
      ( r1_ordinal1(A_189,B_190)
      | ~ v3_ordinal1(B_190)
      | ~ v3_ordinal1(A_189)
      | ~ r2_hidden(A_189,B_190) ) ),
    inference(resolution,[status(thm)],[c_20,c_2786])).

tff(c_3371,plain,(
    ! [A_223,B_224] :
      ( r1_ordinal1(A_223,k1_ordinal1(B_224))
      | ~ v3_ordinal1(k1_ordinal1(B_224))
      | ~ r1_ordinal1(A_223,B_224)
      | ~ v3_ordinal1(B_224)
      | ~ v3_ordinal1(A_223) ) ),
    inference(resolution,[status(thm)],[c_32,c_2804])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ r1_ordinal1(A_4,B_5)
      | ~ v3_ordinal1(B_5)
      | ~ v3_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2750,plain,(
    ! [A_176,B_177] :
      ( r1_tarski(A_176,B_177)
      | ~ r1_ordinal1(A_176,B_177)
      | ~ v3_ordinal1(B_177)
      | ~ v3_ordinal1(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2883,plain,(
    ! [B_195,A_196] :
      ( B_195 = A_196
      | ~ r1_tarski(B_195,A_196)
      | ~ r1_ordinal1(A_196,B_195)
      | ~ v3_ordinal1(B_195)
      | ~ v3_ordinal1(A_196) ) ),
    inference(resolution,[status(thm)],[c_2750,c_2])).

tff(c_2890,plain,(
    ! [B_5,A_4] :
      ( B_5 = A_4
      | ~ r1_ordinal1(B_5,A_4)
      | ~ r1_ordinal1(A_4,B_5)
      | ~ v3_ordinal1(B_5)
      | ~ v3_ordinal1(A_4) ) ),
    inference(resolution,[status(thm)],[c_12,c_2883])).

tff(c_4538,plain,(
    ! [B_270,A_271] :
      ( k1_ordinal1(B_270) = A_271
      | ~ r1_ordinal1(k1_ordinal1(B_270),A_271)
      | ~ v3_ordinal1(k1_ordinal1(B_270))
      | ~ r1_ordinal1(A_271,B_270)
      | ~ v3_ordinal1(B_270)
      | ~ v3_ordinal1(A_271) ) ),
    inference(resolution,[status(thm)],[c_3371,c_2890])).

tff(c_4607,plain,(
    ! [A_272,B_273] :
      ( k1_ordinal1(A_272) = B_273
      | ~ v3_ordinal1(k1_ordinal1(A_272))
      | ~ r1_ordinal1(B_273,A_272)
      | ~ r2_hidden(A_272,B_273)
      | ~ v3_ordinal1(B_273)
      | ~ v3_ordinal1(A_272) ) ),
    inference(resolution,[status(thm)],[c_30,c_4538])).

tff(c_4694,plain,(
    ! [A_276,B_277] :
      ( k1_ordinal1(A_276) = B_277
      | ~ r1_ordinal1(B_277,A_276)
      | ~ r2_hidden(A_276,B_277)
      | ~ v3_ordinal1(B_277)
      | ~ v3_ordinal1(A_276) ) ),
    inference(resolution,[status(thm)],[c_26,c_4607])).

tff(c_4766,plain,(
    ! [A_20] :
      ( k1_ordinal1('#skF_1'(A_20)) = A_20
      | ~ r1_ordinal1(A_20,'#skF_1'(A_20))
      | ~ v3_ordinal1('#skF_1'(A_20))
      | v4_ordinal1(A_20)
      | ~ v3_ordinal1(A_20) ) ),
    inference(resolution,[status(thm)],[c_40,c_4694])).

tff(c_5460,plain,(
    ! [B_299] :
      ( v4_ordinal1(B_299)
      | k1_ordinal1('#skF_1'(B_299)) = B_299
      | ~ v3_ordinal1(B_299)
      | ~ v3_ordinal1('#skF_1'(B_299)) ) ),
    inference(resolution,[status(thm)],[c_5428,c_4766])).

tff(c_5465,plain,(
    ! [A_300] :
      ( k1_ordinal1('#skF_1'(A_300)) = A_300
      | v4_ordinal1(A_300)
      | ~ v3_ordinal1(A_300) ) ),
    inference(resolution,[status(thm)],[c_42,c_5460])).

tff(c_2715,plain,(
    ! [A_168] :
      ( v3_ordinal1('#skF_1'(A_168))
      | v4_ordinal1(A_168)
      | ~ v3_ordinal1(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_56,plain,
    ( ~ v4_ordinal1('#skF_2')
    | v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_62,plain,(
    ~ v4_ordinal1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_46,plain,(
    ! [B_26] :
      ( k1_ordinal1(B_26) != '#skF_2'
      | ~ v3_ordinal1(B_26)
      | v4_ordinal1('#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2698,plain,(
    ! [B_26] :
      ( k1_ordinal1(B_26) != '#skF_2'
      | ~ v3_ordinal1(B_26) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_46])).

tff(c_2719,plain,(
    ! [A_168] :
      ( k1_ordinal1('#skF_1'(A_168)) != '#skF_2'
      | v4_ordinal1(A_168)
      | ~ v3_ordinal1(A_168) ) ),
    inference(resolution,[status(thm)],[c_2715,c_2698])).

tff(c_5627,plain,(
    ! [A_300] :
      ( A_300 != '#skF_2'
      | v4_ordinal1(A_300)
      | ~ v3_ordinal1(A_300)
      | v4_ordinal1(A_300)
      | ~ v3_ordinal1(A_300) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5465,c_2719])).

tff(c_5665,plain,(
    ! [A_302] :
      ( A_302 != '#skF_2'
      | ~ v3_ordinal1(A_302)
      | v4_ordinal1(A_302) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_5627])).

tff(c_5671,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_5665,c_62])).

tff(c_5676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5671])).

tff(c_5678,plain,(
    v4_ordinal1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_52,plain,
    ( ~ v4_ordinal1('#skF_2')
    | k1_ordinal1('#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_5680,plain,(
    k1_ordinal1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5678,c_52])).

tff(c_22,plain,(
    ! [A_9] : k1_ordinal1(A_9) != A_9 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_5687,plain,(
    '#skF_2' != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_5680,c_22])).

tff(c_5677,plain,(
    v3_ordinal1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_18,plain,(
    ! [B_8] : r2_hidden(B_8,k1_ordinal1(B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5684,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5680,c_18])).

tff(c_5785,plain,(
    ! [A_321,B_322] :
      ( r1_ordinal1(A_321,B_322)
      | ~ r2_hidden(A_321,k1_ordinal1(B_322))
      | ~ v3_ordinal1(B_322)
      | ~ v3_ordinal1(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5871,plain,(
    ! [A_328,B_329] :
      ( r1_ordinal1(A_328,B_329)
      | ~ v3_ordinal1(B_329)
      | ~ v3_ordinal1(A_328)
      | ~ r2_hidden(A_328,B_329) ) ),
    inference(resolution,[status(thm)],[c_20,c_5785])).

tff(c_5883,plain,
    ( r1_ordinal1('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5684,c_5871])).

tff(c_5894,plain,(
    r1_ordinal1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5677,c_44,c_5883])).

tff(c_6342,plain,(
    ! [B_348,A_349] :
      ( r2_hidden(k1_ordinal1(B_348),A_349)
      | ~ r2_hidden(B_348,A_349)
      | ~ v3_ordinal1(B_348)
      | ~ v4_ordinal1(A_349)
      | ~ v3_ordinal1(A_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_6376,plain,(
    ! [A_349] :
      ( r2_hidden('#skF_2',A_349)
      | ~ r2_hidden('#skF_3',A_349)
      | ~ v3_ordinal1('#skF_3')
      | ~ v4_ordinal1(A_349)
      | ~ v3_ordinal1(A_349) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5680,c_6342])).

tff(c_6395,plain,(
    ! [A_350] :
      ( r2_hidden('#skF_2',A_350)
      | ~ r2_hidden('#skF_3',A_350)
      | ~ v4_ordinal1(A_350)
      | ~ v3_ordinal1(A_350) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5677,c_6376])).

tff(c_5795,plain,(
    ! [A_321] :
      ( r1_ordinal1(A_321,'#skF_3')
      | ~ r2_hidden(A_321,'#skF_2')
      | ~ v3_ordinal1('#skF_3')
      | ~ v3_ordinal1(A_321) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5680,c_5785])).

tff(c_5802,plain,(
    ! [A_321] :
      ( r1_ordinal1(A_321,'#skF_3')
      | ~ r2_hidden(A_321,'#skF_2')
      | ~ v3_ordinal1(A_321) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5677,c_5795])).

tff(c_6410,plain,
    ( r1_ordinal1('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3','#skF_2')
    | ~ v4_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6395,c_5802])).

tff(c_6434,plain,(
    r1_ordinal1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5678,c_5684,c_6410])).

tff(c_5771,plain,(
    ! [A_316,B_317] :
      ( r1_tarski(A_316,B_317)
      | ~ r1_ordinal1(A_316,B_317)
      | ~ v3_ordinal1(B_317)
      | ~ v3_ordinal1(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6538,plain,(
    ! [B_353,A_354] :
      ( B_353 = A_354
      | ~ r1_tarski(B_353,A_354)
      | ~ r1_ordinal1(A_354,B_353)
      | ~ v3_ordinal1(B_353)
      | ~ v3_ordinal1(A_354) ) ),
    inference(resolution,[status(thm)],[c_5771,c_2])).

tff(c_8832,plain,(
    ! [B_405,A_406] :
      ( B_405 = A_406
      | ~ r1_ordinal1(B_405,A_406)
      | ~ r1_ordinal1(A_406,B_405)
      | ~ v3_ordinal1(B_405)
      | ~ v3_ordinal1(A_406) ) ),
    inference(resolution,[status(thm)],[c_12,c_6538])).

tff(c_8880,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_ordinal1('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6434,c_8832])).

tff(c_8971,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5677,c_44,c_5894,c_8880])).

tff(c_8973,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5687,c_8971])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:43:35 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.15/2.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.42/2.67  
% 8.42/2.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.42/2.67  %$ r2_hidden > r1_tarski > r1_ordinal1 > v4_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_2 > #skF_3
% 8.42/2.67  
% 8.42/2.67  %Foreground sorts:
% 8.42/2.67  
% 8.42/2.67  
% 8.42/2.67  %Background operators:
% 8.42/2.67  
% 8.42/2.67  
% 8.42/2.67  %Foreground operators:
% 8.42/2.67  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 8.42/2.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.42/2.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.42/2.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.42/2.67  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.42/2.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.42/2.67  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 8.42/2.67  tff('#skF_2', type, '#skF_2': $i).
% 8.42/2.67  tff('#skF_3', type, '#skF_3': $i).
% 8.42/2.67  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 8.42/2.67  tff(v4_ordinal1, type, v4_ordinal1: $i > $o).
% 8.42/2.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.42/2.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.42/2.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.42/2.67  
% 8.42/2.69  tff(f_121, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (~(~v4_ordinal1(A) & (![B]: (v3_ordinal1(B) => ~(A = k1_ordinal1(B))))) & ~((?[B]: (v3_ordinal1(B) & (A = k1_ordinal1(B)))) & v4_ordinal1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_ordinal1)).
% 8.42/2.69  tff(f_100, axiom, (![A]: (v3_ordinal1(A) => (v4_ordinal1(A) <=> (![B]: (v3_ordinal1(B) => (r2_hidden(B, A) => r2_hidden(k1_ordinal1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_ordinal1)).
% 8.42/2.69  tff(f_71, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 8.42/2.69  tff(f_67, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 8.42/2.69  tff(f_89, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 8.42/2.69  tff(f_80, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 8.42/2.69  tff(f_49, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 8.42/2.69  tff(f_41, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 8.42/2.69  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.42/2.69  tff(f_52, axiom, (![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_ordinal1)).
% 8.42/2.69  tff(c_44, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.42/2.69  tff(c_42, plain, (![A_20]: (v3_ordinal1('#skF_1'(A_20)) | v4_ordinal1(A_20) | ~v3_ordinal1(A_20))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.42/2.69  tff(c_26, plain, (![A_13]: (v3_ordinal1(k1_ordinal1(A_13)) | ~v3_ordinal1(A_13))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.42/2.69  tff(c_2843, plain, (![B_192, A_193]: (r2_hidden(B_192, A_193) | B_192=A_193 | r2_hidden(A_193, B_192) | ~v3_ordinal1(B_192) | ~v3_ordinal1(A_193))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.42/2.69  tff(c_38, plain, (![A_20]: (~r2_hidden(k1_ordinal1('#skF_1'(A_20)), A_20) | v4_ordinal1(A_20) | ~v3_ordinal1(A_20))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.42/2.69  tff(c_3661, plain, (![B_237]: (v4_ordinal1(B_237) | r2_hidden(B_237, k1_ordinal1('#skF_1'(B_237))) | k1_ordinal1('#skF_1'(B_237))=B_237 | ~v3_ordinal1(B_237) | ~v3_ordinal1(k1_ordinal1('#skF_1'(B_237))))), inference(resolution, [status(thm)], [c_2843, c_38])).
% 8.42/2.69  tff(c_34, plain, (![A_17, B_19]: (r1_ordinal1(A_17, B_19) | ~r2_hidden(A_17, k1_ordinal1(B_19)) | ~v3_ordinal1(B_19) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.42/2.69  tff(c_5423, plain, (![B_297]: (r1_ordinal1(B_297, '#skF_1'(B_297)) | ~v3_ordinal1('#skF_1'(B_297)) | v4_ordinal1(B_297) | k1_ordinal1('#skF_1'(B_297))=B_297 | ~v3_ordinal1(B_297) | ~v3_ordinal1(k1_ordinal1('#skF_1'(B_297))))), inference(resolution, [status(thm)], [c_3661, c_34])).
% 8.42/2.69  tff(c_5428, plain, (![B_298]: (r1_ordinal1(B_298, '#skF_1'(B_298)) | v4_ordinal1(B_298) | k1_ordinal1('#skF_1'(B_298))=B_298 | ~v3_ordinal1(B_298) | ~v3_ordinal1('#skF_1'(B_298)))), inference(resolution, [status(thm)], [c_26, c_5423])).
% 8.42/2.69  tff(c_40, plain, (![A_20]: (r2_hidden('#skF_1'(A_20), A_20) | v4_ordinal1(A_20) | ~v3_ordinal1(A_20))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.42/2.69  tff(c_30, plain, (![A_14, B_16]: (r1_ordinal1(k1_ordinal1(A_14), B_16) | ~r2_hidden(A_14, B_16) | ~v3_ordinal1(B_16) | ~v3_ordinal1(A_14))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.42/2.69  tff(c_32, plain, (![A_17, B_19]: (r2_hidden(A_17, k1_ordinal1(B_19)) | ~r1_ordinal1(A_17, B_19) | ~v3_ordinal1(B_19) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.42/2.69  tff(c_20, plain, (![A_7, B_8]: (~r2_hidden(A_7, B_8) | r2_hidden(A_7, k1_ordinal1(B_8)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.42/2.69  tff(c_2786, plain, (![A_187, B_188]: (r1_ordinal1(A_187, B_188) | ~r2_hidden(A_187, k1_ordinal1(B_188)) | ~v3_ordinal1(B_188) | ~v3_ordinal1(A_187))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.42/2.69  tff(c_2804, plain, (![A_189, B_190]: (r1_ordinal1(A_189, B_190) | ~v3_ordinal1(B_190) | ~v3_ordinal1(A_189) | ~r2_hidden(A_189, B_190))), inference(resolution, [status(thm)], [c_20, c_2786])).
% 8.42/2.69  tff(c_3371, plain, (![A_223, B_224]: (r1_ordinal1(A_223, k1_ordinal1(B_224)) | ~v3_ordinal1(k1_ordinal1(B_224)) | ~r1_ordinal1(A_223, B_224) | ~v3_ordinal1(B_224) | ~v3_ordinal1(A_223))), inference(resolution, [status(thm)], [c_32, c_2804])).
% 8.42/2.69  tff(c_12, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~r1_ordinal1(A_4, B_5) | ~v3_ordinal1(B_5) | ~v3_ordinal1(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.42/2.69  tff(c_2750, plain, (![A_176, B_177]: (r1_tarski(A_176, B_177) | ~r1_ordinal1(A_176, B_177) | ~v3_ordinal1(B_177) | ~v3_ordinal1(A_176))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.42/2.69  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.42/2.69  tff(c_2883, plain, (![B_195, A_196]: (B_195=A_196 | ~r1_tarski(B_195, A_196) | ~r1_ordinal1(A_196, B_195) | ~v3_ordinal1(B_195) | ~v3_ordinal1(A_196))), inference(resolution, [status(thm)], [c_2750, c_2])).
% 8.42/2.69  tff(c_2890, plain, (![B_5, A_4]: (B_5=A_4 | ~r1_ordinal1(B_5, A_4) | ~r1_ordinal1(A_4, B_5) | ~v3_ordinal1(B_5) | ~v3_ordinal1(A_4))), inference(resolution, [status(thm)], [c_12, c_2883])).
% 8.42/2.69  tff(c_4538, plain, (![B_270, A_271]: (k1_ordinal1(B_270)=A_271 | ~r1_ordinal1(k1_ordinal1(B_270), A_271) | ~v3_ordinal1(k1_ordinal1(B_270)) | ~r1_ordinal1(A_271, B_270) | ~v3_ordinal1(B_270) | ~v3_ordinal1(A_271))), inference(resolution, [status(thm)], [c_3371, c_2890])).
% 8.42/2.69  tff(c_4607, plain, (![A_272, B_273]: (k1_ordinal1(A_272)=B_273 | ~v3_ordinal1(k1_ordinal1(A_272)) | ~r1_ordinal1(B_273, A_272) | ~r2_hidden(A_272, B_273) | ~v3_ordinal1(B_273) | ~v3_ordinal1(A_272))), inference(resolution, [status(thm)], [c_30, c_4538])).
% 8.42/2.69  tff(c_4694, plain, (![A_276, B_277]: (k1_ordinal1(A_276)=B_277 | ~r1_ordinal1(B_277, A_276) | ~r2_hidden(A_276, B_277) | ~v3_ordinal1(B_277) | ~v3_ordinal1(A_276))), inference(resolution, [status(thm)], [c_26, c_4607])).
% 8.42/2.69  tff(c_4766, plain, (![A_20]: (k1_ordinal1('#skF_1'(A_20))=A_20 | ~r1_ordinal1(A_20, '#skF_1'(A_20)) | ~v3_ordinal1('#skF_1'(A_20)) | v4_ordinal1(A_20) | ~v3_ordinal1(A_20))), inference(resolution, [status(thm)], [c_40, c_4694])).
% 8.42/2.69  tff(c_5460, plain, (![B_299]: (v4_ordinal1(B_299) | k1_ordinal1('#skF_1'(B_299))=B_299 | ~v3_ordinal1(B_299) | ~v3_ordinal1('#skF_1'(B_299)))), inference(resolution, [status(thm)], [c_5428, c_4766])).
% 8.42/2.69  tff(c_5465, plain, (![A_300]: (k1_ordinal1('#skF_1'(A_300))=A_300 | v4_ordinal1(A_300) | ~v3_ordinal1(A_300))), inference(resolution, [status(thm)], [c_42, c_5460])).
% 8.42/2.69  tff(c_2715, plain, (![A_168]: (v3_ordinal1('#skF_1'(A_168)) | v4_ordinal1(A_168) | ~v3_ordinal1(A_168))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.42/2.69  tff(c_56, plain, (~v4_ordinal1('#skF_2') | v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.42/2.69  tff(c_62, plain, (~v4_ordinal1('#skF_2')), inference(splitLeft, [status(thm)], [c_56])).
% 8.42/2.69  tff(c_46, plain, (![B_26]: (k1_ordinal1(B_26)!='#skF_2' | ~v3_ordinal1(B_26) | v4_ordinal1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.42/2.69  tff(c_2698, plain, (![B_26]: (k1_ordinal1(B_26)!='#skF_2' | ~v3_ordinal1(B_26))), inference(negUnitSimplification, [status(thm)], [c_62, c_46])).
% 8.42/2.69  tff(c_2719, plain, (![A_168]: (k1_ordinal1('#skF_1'(A_168))!='#skF_2' | v4_ordinal1(A_168) | ~v3_ordinal1(A_168))), inference(resolution, [status(thm)], [c_2715, c_2698])).
% 8.42/2.69  tff(c_5627, plain, (![A_300]: (A_300!='#skF_2' | v4_ordinal1(A_300) | ~v3_ordinal1(A_300) | v4_ordinal1(A_300) | ~v3_ordinal1(A_300))), inference(superposition, [status(thm), theory('equality')], [c_5465, c_2719])).
% 8.42/2.69  tff(c_5665, plain, (![A_302]: (A_302!='#skF_2' | ~v3_ordinal1(A_302) | v4_ordinal1(A_302))), inference(factorization, [status(thm), theory('equality')], [c_5627])).
% 8.42/2.69  tff(c_5671, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_5665, c_62])).
% 8.42/2.69  tff(c_5676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_5671])).
% 8.42/2.69  tff(c_5678, plain, (v4_ordinal1('#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 8.42/2.69  tff(c_52, plain, (~v4_ordinal1('#skF_2') | k1_ordinal1('#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.42/2.69  tff(c_5680, plain, (k1_ordinal1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5678, c_52])).
% 8.42/2.69  tff(c_22, plain, (![A_9]: (k1_ordinal1(A_9)!=A_9)), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.42/2.69  tff(c_5687, plain, ('#skF_2'!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_5680, c_22])).
% 8.42/2.69  tff(c_5677, plain, (v3_ordinal1('#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 8.42/2.69  tff(c_18, plain, (![B_8]: (r2_hidden(B_8, k1_ordinal1(B_8)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.42/2.69  tff(c_5684, plain, (r2_hidden('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5680, c_18])).
% 8.42/2.69  tff(c_5785, plain, (![A_321, B_322]: (r1_ordinal1(A_321, B_322) | ~r2_hidden(A_321, k1_ordinal1(B_322)) | ~v3_ordinal1(B_322) | ~v3_ordinal1(A_321))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.42/2.69  tff(c_5871, plain, (![A_328, B_329]: (r1_ordinal1(A_328, B_329) | ~v3_ordinal1(B_329) | ~v3_ordinal1(A_328) | ~r2_hidden(A_328, B_329))), inference(resolution, [status(thm)], [c_20, c_5785])).
% 8.42/2.69  tff(c_5883, plain, (r1_ordinal1('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_5684, c_5871])).
% 8.42/2.69  tff(c_5894, plain, (r1_ordinal1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5677, c_44, c_5883])).
% 8.42/2.69  tff(c_6342, plain, (![B_348, A_349]: (r2_hidden(k1_ordinal1(B_348), A_349) | ~r2_hidden(B_348, A_349) | ~v3_ordinal1(B_348) | ~v4_ordinal1(A_349) | ~v3_ordinal1(A_349))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.42/2.69  tff(c_6376, plain, (![A_349]: (r2_hidden('#skF_2', A_349) | ~r2_hidden('#skF_3', A_349) | ~v3_ordinal1('#skF_3') | ~v4_ordinal1(A_349) | ~v3_ordinal1(A_349))), inference(superposition, [status(thm), theory('equality')], [c_5680, c_6342])).
% 8.42/2.69  tff(c_6395, plain, (![A_350]: (r2_hidden('#skF_2', A_350) | ~r2_hidden('#skF_3', A_350) | ~v4_ordinal1(A_350) | ~v3_ordinal1(A_350))), inference(demodulation, [status(thm), theory('equality')], [c_5677, c_6376])).
% 8.42/2.69  tff(c_5795, plain, (![A_321]: (r1_ordinal1(A_321, '#skF_3') | ~r2_hidden(A_321, '#skF_2') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(A_321))), inference(superposition, [status(thm), theory('equality')], [c_5680, c_5785])).
% 8.42/2.69  tff(c_5802, plain, (![A_321]: (r1_ordinal1(A_321, '#skF_3') | ~r2_hidden(A_321, '#skF_2') | ~v3_ordinal1(A_321))), inference(demodulation, [status(thm), theory('equality')], [c_5677, c_5795])).
% 8.42/2.69  tff(c_6410, plain, (r1_ordinal1('#skF_2', '#skF_3') | ~r2_hidden('#skF_3', '#skF_2') | ~v4_ordinal1('#skF_2') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_6395, c_5802])).
% 8.42/2.69  tff(c_6434, plain, (r1_ordinal1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_5678, c_5684, c_6410])).
% 8.42/2.69  tff(c_5771, plain, (![A_316, B_317]: (r1_tarski(A_316, B_317) | ~r1_ordinal1(A_316, B_317) | ~v3_ordinal1(B_317) | ~v3_ordinal1(A_316))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.42/2.69  tff(c_6538, plain, (![B_353, A_354]: (B_353=A_354 | ~r1_tarski(B_353, A_354) | ~r1_ordinal1(A_354, B_353) | ~v3_ordinal1(B_353) | ~v3_ordinal1(A_354))), inference(resolution, [status(thm)], [c_5771, c_2])).
% 8.42/2.69  tff(c_8832, plain, (![B_405, A_406]: (B_405=A_406 | ~r1_ordinal1(B_405, A_406) | ~r1_ordinal1(A_406, B_405) | ~v3_ordinal1(B_405) | ~v3_ordinal1(A_406))), inference(resolution, [status(thm)], [c_12, c_6538])).
% 8.42/2.69  tff(c_8880, plain, ('#skF_2'='#skF_3' | ~r1_ordinal1('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_6434, c_8832])).
% 8.42/2.69  tff(c_8971, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5677, c_44, c_5894, c_8880])).
% 8.42/2.69  tff(c_8973, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5687, c_8971])).
% 8.42/2.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.42/2.69  
% 8.42/2.69  Inference rules
% 8.42/2.69  ----------------------
% 8.42/2.69  #Ref     : 0
% 8.42/2.69  #Sup     : 1689
% 8.42/2.69  #Fact    : 26
% 8.42/2.69  #Define  : 0
% 8.42/2.69  #Split   : 8
% 8.42/2.69  #Chain   : 0
% 8.42/2.69  #Close   : 0
% 8.42/2.69  
% 8.42/2.69  Ordering : KBO
% 8.42/2.69  
% 8.42/2.69  Simplification rules
% 8.42/2.69  ----------------------
% 8.42/2.69  #Subsume      : 599
% 8.42/2.69  #Demod        : 797
% 8.42/2.69  #Tautology    : 346
% 8.42/2.69  #SimpNegUnit  : 137
% 8.42/2.69  #BackRed      : 0
% 8.42/2.69  
% 8.42/2.69  #Partial instantiations: 0
% 8.42/2.69  #Strategies tried      : 1
% 8.42/2.69  
% 8.42/2.69  Timing (in seconds)
% 8.42/2.69  ----------------------
% 8.42/2.69  Preprocessing        : 0.29
% 8.42/2.69  Parsing              : 0.16
% 8.42/2.69  CNF conversion       : 0.02
% 8.42/2.69  Main loop            : 1.69
% 8.42/2.69  Inferencing          : 0.53
% 8.42/2.69  Reduction            : 0.40
% 8.42/2.69  Demodulation         : 0.25
% 8.42/2.69  BG Simplification    : 0.06
% 8.42/2.69  Subsumption          : 0.60
% 8.42/2.69  Abstraction          : 0.08
% 8.42/2.69  MUC search           : 0.00
% 8.42/2.69  Cooper               : 0.00
% 8.42/2.69  Total                : 2.02
% 8.42/2.69  Index Insertion      : 0.00
% 8.42/2.69  Index Deletion       : 0.00
% 8.42/2.69  Index Matching       : 0.00
% 8.42/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
