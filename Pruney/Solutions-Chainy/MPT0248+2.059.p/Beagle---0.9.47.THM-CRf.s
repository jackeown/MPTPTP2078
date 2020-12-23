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
% DateTime   : Thu Dec  3 09:50:12 EST 2020

% Result     : Theorem 4.65s
% Output     : CNFRefutation 4.67s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 262 expanded)
%              Number of leaves         :   39 (  99 expanded)
%              Depth                    :   13
%              Number of atoms          :  142 ( 486 expanded)
%              Number of equality atoms :   60 ( 296 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_86,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_82,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_68,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_92,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_66,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_90,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_1157,plain,(
    ! [B_136,A_137] :
      ( k3_xboole_0(B_136,k1_tarski(A_137)) = k1_tarski(A_137)
      | ~ r2_hidden(A_137,B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_72,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_46,plain,(
    ! [A_34,B_35] : r1_tarski(A_34,k2_xboole_0(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_97,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_46])).

tff(c_387,plain,(
    ! [A_84,B_85] :
      ( k3_xboole_0(A_84,B_85) = A_84
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_407,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_97,c_387])).

tff(c_1185,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1157,c_407])).

tff(c_1221,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1185])).

tff(c_60,plain,(
    ! [A_49,B_50] :
      ( r1_xboole_0(k1_tarski(A_49),B_50)
      | r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_594,plain,(
    ! [A_102,B_103,C_104] :
      ( ~ r1_xboole_0(A_102,B_103)
      | ~ r2_hidden(C_104,k3_xboole_0(A_102,B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_633,plain,(
    ! [A_106,B_107] :
      ( ~ r1_xboole_0(A_106,B_107)
      | v1_xboole_0(k3_xboole_0(A_106,B_107)) ) ),
    inference(resolution,[status(thm)],[c_6,c_594])).

tff(c_645,plain,
    ( ~ r1_xboole_0('#skF_4',k1_tarski('#skF_3'))
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_633])).

tff(c_764,plain,(
    ~ r1_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_645])).

tff(c_1635,plain,(
    ! [A_151,B_152] :
      ( r2_hidden('#skF_2'(A_151,B_152),k3_xboole_0(A_151,B_152))
      | r1_xboole_0(A_151,B_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1659,plain,
    ( r2_hidden('#skF_2'('#skF_4',k1_tarski('#skF_3')),'#skF_4')
    | r1_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_1635])).

tff(c_1672,plain,(
    r2_hidden('#skF_2'('#skF_4',k1_tarski('#skF_3')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_764,c_1659])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1697,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1672,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2423,plain,(
    ! [B_177,A_178] :
      ( ~ r1_xboole_0(B_177,A_178)
      | v1_xboole_0(k3_xboole_0(A_178,B_177)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_633])).

tff(c_2453,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_2423])).

tff(c_2462,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1697,c_2453])).

tff(c_2468,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_2462])).

tff(c_2473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1221,c_2468])).

tff(c_2474,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_645])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2521,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2474,c_8])).

tff(c_2525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_2521])).

tff(c_2526,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_2527,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2659,plain,(
    ! [A_194,B_195] :
      ( k4_xboole_0(A_194,B_195) = '#skF_4'
      | ~ r1_tarski(A_194,B_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2527,c_28])).

tff(c_2783,plain,(
    ! [A_206,B_207] : k4_xboole_0(A_206,k2_xboole_0(A_206,B_207)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_2659])).

tff(c_42,plain,(
    ! [A_31,B_32] : r1_tarski(k4_xboole_0(A_31,B_32),A_31) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2692,plain,(
    ! [A_198,B_199] :
      ( k2_xboole_0(A_198,B_199) = B_199
      | ~ r1_tarski(A_198,B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2706,plain,(
    ! [A_31,B_32] : k2_xboole_0(k4_xboole_0(A_31,B_32),A_31) = A_31 ),
    inference(resolution,[status(thm)],[c_42,c_2692])).

tff(c_2793,plain,(
    ! [A_206] : k2_xboole_0('#skF_4',A_206) = A_206 ),
    inference(superposition,[status(thm),theory(equality)],[c_2783,c_2706])).

tff(c_2839,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2793,c_72])).

tff(c_2841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2526,c_2839])).

tff(c_2842,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_2843,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_70,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2875,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2843,c_2843,c_70])).

tff(c_3279,plain,(
    ! [A_240,B_241] :
      ( r1_xboole_0(k1_tarski(A_240),B_241)
      | r2_hidden(A_240,B_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3282,plain,(
    ! [B_241] :
      ( r1_xboole_0('#skF_4',B_241)
      | r2_hidden('#skF_3',B_241) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2843,c_3279])).

tff(c_4110,plain,(
    ! [B_285,A_286] :
      ( k3_xboole_0(B_285,k1_tarski(A_286)) = k1_tarski(A_286)
      | ~ r2_hidden(A_286,B_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4153,plain,(
    ! [B_285] :
      ( k3_xboole_0(B_285,'#skF_4') = k1_tarski('#skF_3')
      | ~ r2_hidden('#skF_3',B_285) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2843,c_4110])).

tff(c_4212,plain,(
    ! [B_288] :
      ( k3_xboole_0(B_288,'#skF_4') = '#skF_4'
      | ~ r2_hidden('#skF_3',B_288) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2843,c_4153])).

tff(c_4216,plain,(
    ! [B_241] :
      ( k3_xboole_0(B_241,'#skF_4') = '#skF_4'
      | r1_xboole_0('#skF_4',B_241) ) ),
    inference(resolution,[status(thm)],[c_3282,c_4212])).

tff(c_44,plain,(
    ! [A_33] : k5_xboole_0(A_33,k1_xboole_0) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_40,plain,(
    ! [A_30] : k3_xboole_0(A_30,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3848,plain,(
    ! [A_277,B_278] : k5_xboole_0(A_277,k3_xboole_0(A_277,B_278)) = k4_xboole_0(A_277,B_278) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3878,plain,(
    ! [A_30] : k5_xboole_0(A_30,k1_xboole_0) = k4_xboole_0(A_30,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_3848])).

tff(c_3888,plain,(
    ! [A_279] : k4_xboole_0(A_279,k1_xboole_0) = A_279 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3878])).

tff(c_2848,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2843,c_72])).

tff(c_3562,plain,(
    ! [A_261,C_262,B_263] :
      ( r1_tarski(A_261,k2_xboole_0(C_262,B_263))
      | ~ r1_tarski(A_261,B_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3617,plain,(
    ! [A_265] :
      ( r1_tarski(A_265,'#skF_4')
      | ~ r1_tarski(A_265,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2848,c_3562])).

tff(c_3633,plain,(
    ! [B_32] : r1_tarski(k4_xboole_0('#skF_5',B_32),'#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_3617])).

tff(c_3903,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3888,c_3633])).

tff(c_38,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3976,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3903,c_38])).

tff(c_4351,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3976,c_2])).

tff(c_3527,plain,(
    ! [A_258,B_259,C_260] :
      ( ~ r1_xboole_0(A_258,B_259)
      | ~ r2_hidden(C_260,k3_xboole_0(A_258,B_259)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3561,plain,(
    ! [A_258,B_259] :
      ( ~ r1_xboole_0(A_258,B_259)
      | v1_xboole_0(k3_xboole_0(A_258,B_259)) ) ),
    inference(resolution,[status(thm)],[c_6,c_3527])).

tff(c_4375,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4351,c_3561])).

tff(c_4741,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4375])).

tff(c_4751,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4216,c_4741])).

tff(c_4758,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4751,c_3976])).

tff(c_4760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2875,c_4758])).

tff(c_4761,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_4375])).

tff(c_4768,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4761,c_8])).

tff(c_4773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2842,c_4768])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.65/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.67/1.82  
% 4.67/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.67/1.83  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 4.67/1.83  
% 4.67/1.83  %Foreground sorts:
% 4.67/1.83  
% 4.67/1.83  
% 4.67/1.83  %Background operators:
% 4.67/1.83  
% 4.67/1.83  
% 4.67/1.83  %Foreground operators:
% 4.67/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.67/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.67/1.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.67/1.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.67/1.83  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.67/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.67/1.83  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.67/1.83  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.67/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.67/1.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.67/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.67/1.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.67/1.83  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.67/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.67/1.83  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.67/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.67/1.83  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.67/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.67/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.67/1.83  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.67/1.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.67/1.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.67/1.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.67/1.83  
% 4.67/1.84  tff(f_130, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.67/1.84  tff(f_109, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 4.67/1.84  tff(f_88, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.67/1.84  tff(f_80, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.67/1.84  tff(f_105, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.67/1.84  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.67/1.84  tff(f_58, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.67/1.84  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.67/1.84  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.67/1.84  tff(f_62, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.67/1.84  tff(f_84, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.67/1.84  tff(f_72, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.67/1.84  tff(f_86, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.67/1.84  tff(f_82, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.67/1.84  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.67/1.84  tff(f_68, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 4.67/1.84  tff(c_68, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.67/1.84  tff(c_92, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_68])).
% 4.67/1.84  tff(c_66, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.67/1.84  tff(c_90, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_66])).
% 4.67/1.84  tff(c_1157, plain, (![B_136, A_137]: (k3_xboole_0(B_136, k1_tarski(A_137))=k1_tarski(A_137) | ~r2_hidden(A_137, B_136))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.67/1.84  tff(c_72, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.67/1.84  tff(c_46, plain, (![A_34, B_35]: (r1_tarski(A_34, k2_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.67/1.84  tff(c_97, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_46])).
% 4.67/1.84  tff(c_387, plain, (![A_84, B_85]: (k3_xboole_0(A_84, B_85)=A_84 | ~r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.67/1.84  tff(c_407, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(resolution, [status(thm)], [c_97, c_387])).
% 4.67/1.84  tff(c_1185, plain, (k1_tarski('#skF_3')='#skF_4' | ~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1157, c_407])).
% 4.67/1.84  tff(c_1221, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_90, c_1185])).
% 4.67/1.84  tff(c_60, plain, (![A_49, B_50]: (r1_xboole_0(k1_tarski(A_49), B_50) | r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.67/1.84  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.67/1.84  tff(c_594, plain, (![A_102, B_103, C_104]: (~r1_xboole_0(A_102, B_103) | ~r2_hidden(C_104, k3_xboole_0(A_102, B_103)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.67/1.84  tff(c_633, plain, (![A_106, B_107]: (~r1_xboole_0(A_106, B_107) | v1_xboole_0(k3_xboole_0(A_106, B_107)))), inference(resolution, [status(thm)], [c_6, c_594])).
% 4.67/1.84  tff(c_645, plain, (~r1_xboole_0('#skF_4', k1_tarski('#skF_3')) | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_407, c_633])).
% 4.67/1.84  tff(c_764, plain, (~r1_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_645])).
% 4.67/1.84  tff(c_1635, plain, (![A_151, B_152]: (r2_hidden('#skF_2'(A_151, B_152), k3_xboole_0(A_151, B_152)) | r1_xboole_0(A_151, B_152))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.67/1.84  tff(c_1659, plain, (r2_hidden('#skF_2'('#skF_4', k1_tarski('#skF_3')), '#skF_4') | r1_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_407, c_1635])).
% 4.67/1.84  tff(c_1672, plain, (r2_hidden('#skF_2'('#skF_4', k1_tarski('#skF_3')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_764, c_1659])).
% 4.67/1.84  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.67/1.84  tff(c_1697, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1672, c_4])).
% 4.67/1.84  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.67/1.84  tff(c_2423, plain, (![B_177, A_178]: (~r1_xboole_0(B_177, A_178) | v1_xboole_0(k3_xboole_0(A_178, B_177)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_633])).
% 4.67/1.84  tff(c_2453, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_407, c_2423])).
% 4.67/1.84  tff(c_2462, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1697, c_2453])).
% 4.67/1.84  tff(c_2468, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_2462])).
% 4.67/1.84  tff(c_2473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1221, c_2468])).
% 4.67/1.84  tff(c_2474, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_645])).
% 4.67/1.84  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.67/1.84  tff(c_2521, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2474, c_8])).
% 4.67/1.84  tff(c_2525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_2521])).
% 4.67/1.84  tff(c_2526, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_68])).
% 4.67/1.84  tff(c_2527, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_68])).
% 4.67/1.84  tff(c_28, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.67/1.84  tff(c_2659, plain, (![A_194, B_195]: (k4_xboole_0(A_194, B_195)='#skF_4' | ~r1_tarski(A_194, B_195))), inference(demodulation, [status(thm), theory('equality')], [c_2527, c_28])).
% 4.67/1.84  tff(c_2783, plain, (![A_206, B_207]: (k4_xboole_0(A_206, k2_xboole_0(A_206, B_207))='#skF_4')), inference(resolution, [status(thm)], [c_46, c_2659])).
% 4.67/1.84  tff(c_42, plain, (![A_31, B_32]: (r1_tarski(k4_xboole_0(A_31, B_32), A_31))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.67/1.84  tff(c_2692, plain, (![A_198, B_199]: (k2_xboole_0(A_198, B_199)=B_199 | ~r1_tarski(A_198, B_199))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.67/1.84  tff(c_2706, plain, (![A_31, B_32]: (k2_xboole_0(k4_xboole_0(A_31, B_32), A_31)=A_31)), inference(resolution, [status(thm)], [c_42, c_2692])).
% 4.67/1.84  tff(c_2793, plain, (![A_206]: (k2_xboole_0('#skF_4', A_206)=A_206)), inference(superposition, [status(thm), theory('equality')], [c_2783, c_2706])).
% 4.67/1.84  tff(c_2839, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2793, c_72])).
% 4.67/1.84  tff(c_2841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2526, c_2839])).
% 4.67/1.84  tff(c_2842, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_66])).
% 4.67/1.84  tff(c_2843, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_66])).
% 4.67/1.84  tff(c_70, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.67/1.84  tff(c_2875, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2843, c_2843, c_70])).
% 4.67/1.84  tff(c_3279, plain, (![A_240, B_241]: (r1_xboole_0(k1_tarski(A_240), B_241) | r2_hidden(A_240, B_241))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.67/1.84  tff(c_3282, plain, (![B_241]: (r1_xboole_0('#skF_4', B_241) | r2_hidden('#skF_3', B_241))), inference(superposition, [status(thm), theory('equality')], [c_2843, c_3279])).
% 4.67/1.84  tff(c_4110, plain, (![B_285, A_286]: (k3_xboole_0(B_285, k1_tarski(A_286))=k1_tarski(A_286) | ~r2_hidden(A_286, B_285))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.67/1.84  tff(c_4153, plain, (![B_285]: (k3_xboole_0(B_285, '#skF_4')=k1_tarski('#skF_3') | ~r2_hidden('#skF_3', B_285))), inference(superposition, [status(thm), theory('equality')], [c_2843, c_4110])).
% 4.67/1.84  tff(c_4212, plain, (![B_288]: (k3_xboole_0(B_288, '#skF_4')='#skF_4' | ~r2_hidden('#skF_3', B_288))), inference(demodulation, [status(thm), theory('equality')], [c_2843, c_4153])).
% 4.67/1.84  tff(c_4216, plain, (![B_241]: (k3_xboole_0(B_241, '#skF_4')='#skF_4' | r1_xboole_0('#skF_4', B_241))), inference(resolution, [status(thm)], [c_3282, c_4212])).
% 4.67/1.84  tff(c_44, plain, (![A_33]: (k5_xboole_0(A_33, k1_xboole_0)=A_33)), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.67/1.84  tff(c_40, plain, (![A_30]: (k3_xboole_0(A_30, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.67/1.84  tff(c_3848, plain, (![A_277, B_278]: (k5_xboole_0(A_277, k3_xboole_0(A_277, B_278))=k4_xboole_0(A_277, B_278))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.67/1.84  tff(c_3878, plain, (![A_30]: (k5_xboole_0(A_30, k1_xboole_0)=k4_xboole_0(A_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_3848])).
% 4.67/1.84  tff(c_3888, plain, (![A_279]: (k4_xboole_0(A_279, k1_xboole_0)=A_279)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3878])).
% 4.67/1.84  tff(c_2848, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2843, c_72])).
% 4.67/1.84  tff(c_3562, plain, (![A_261, C_262, B_263]: (r1_tarski(A_261, k2_xboole_0(C_262, B_263)) | ~r1_tarski(A_261, B_263))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.67/1.84  tff(c_3617, plain, (![A_265]: (r1_tarski(A_265, '#skF_4') | ~r1_tarski(A_265, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2848, c_3562])).
% 4.67/1.84  tff(c_3633, plain, (![B_32]: (r1_tarski(k4_xboole_0('#skF_5', B_32), '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_3617])).
% 4.67/1.84  tff(c_3903, plain, (r1_tarski('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3888, c_3633])).
% 4.67/1.84  tff(c_38, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.67/1.84  tff(c_3976, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_3903, c_38])).
% 4.67/1.84  tff(c_4351, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3976, c_2])).
% 4.67/1.84  tff(c_3527, plain, (![A_258, B_259, C_260]: (~r1_xboole_0(A_258, B_259) | ~r2_hidden(C_260, k3_xboole_0(A_258, B_259)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.67/1.84  tff(c_3561, plain, (![A_258, B_259]: (~r1_xboole_0(A_258, B_259) | v1_xboole_0(k3_xboole_0(A_258, B_259)))), inference(resolution, [status(thm)], [c_6, c_3527])).
% 4.67/1.84  tff(c_4375, plain, (~r1_xboole_0('#skF_4', '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4351, c_3561])).
% 4.67/1.84  tff(c_4741, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_4375])).
% 4.67/1.84  tff(c_4751, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_4216, c_4741])).
% 4.67/1.84  tff(c_4758, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4751, c_3976])).
% 4.67/1.84  tff(c_4760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2875, c_4758])).
% 4.67/1.84  tff(c_4761, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_4375])).
% 4.67/1.84  tff(c_4768, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_4761, c_8])).
% 4.67/1.84  tff(c_4773, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2842, c_4768])).
% 4.67/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.67/1.84  
% 4.67/1.84  Inference rules
% 4.67/1.84  ----------------------
% 4.67/1.84  #Ref     : 1
% 4.67/1.84  #Sup     : 1167
% 4.67/1.84  #Fact    : 0
% 4.67/1.84  #Define  : 0
% 4.67/1.84  #Split   : 11
% 4.67/1.84  #Chain   : 0
% 4.67/1.84  #Close   : 0
% 4.67/1.84  
% 4.67/1.84  Ordering : KBO
% 4.67/1.84  
% 4.67/1.84  Simplification rules
% 4.67/1.84  ----------------------
% 4.67/1.84  #Subsume      : 84
% 4.67/1.84  #Demod        : 424
% 4.67/1.84  #Tautology    : 772
% 4.67/1.84  #SimpNegUnit  : 21
% 4.67/1.84  #BackRed      : 19
% 4.67/1.84  
% 4.67/1.84  #Partial instantiations: 0
% 4.67/1.84  #Strategies tried      : 1
% 4.67/1.84  
% 4.67/1.84  Timing (in seconds)
% 4.67/1.84  ----------------------
% 4.67/1.85  Preprocessing        : 0.33
% 4.67/1.85  Parsing              : 0.17
% 4.67/1.85  CNF conversion       : 0.02
% 4.67/1.85  Main loop            : 0.76
% 4.67/1.85  Inferencing          : 0.26
% 4.67/1.85  Reduction            : 0.27
% 4.67/1.85  Demodulation         : 0.20
% 4.67/1.85  BG Simplification    : 0.03
% 4.67/1.85  Subsumption          : 0.13
% 4.67/1.85  Abstraction          : 0.03
% 4.67/1.85  MUC search           : 0.00
% 4.67/1.85  Cooper               : 0.00
% 4.67/1.85  Total                : 1.12
% 4.67/1.85  Index Insertion      : 0.00
% 4.67/1.85  Index Deletion       : 0.00
% 4.67/1.85  Index Matching       : 0.00
% 4.67/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
