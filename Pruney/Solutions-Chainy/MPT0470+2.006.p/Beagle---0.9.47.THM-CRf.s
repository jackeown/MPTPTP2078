%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:01 EST 2020

% Result     : Theorem 10.97s
% Output     : CNFRefutation 11.09s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 126 expanded)
%              Number of leaves         :   41 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  144 ( 203 expanded)
%              Number of equality atoms :   31 (  49 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_64,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_123,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_120,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_66,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_111,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_104,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(c_58,plain,
    ( k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_88,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_60,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,(
    ! [A_55] :
      ( v1_relat_1(A_55)
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_93,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_44,plain,(
    ! [A_40,B_41] :
      ( v1_relat_1(k5_relat_1(A_40,B_41))
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_56,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_54,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_760,plain,(
    ! [A_143,B_144] :
      ( k1_relat_1(k5_relat_1(A_143,B_144)) = k1_relat_1(A_143)
      | ~ r1_tarski(k2_relat_1(A_143),k1_relat_1(B_144))
      | ~ v1_relat_1(B_144)
      | ~ v1_relat_1(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_769,plain,(
    ! [B_144] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_144)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_144))
      | ~ v1_relat_1(B_144)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_760])).

tff(c_776,plain,(
    ! [B_145] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_145)) = k1_xboole_0
      | ~ v1_relat_1(B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_24,c_56,c_769])).

tff(c_46,plain,(
    ! [A_42] :
      ( ~ v1_xboole_0(k1_relat_1(A_42))
      | ~ v1_relat_1(A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_788,plain,(
    ! [B_145] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_145))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_145))
      | ~ v1_relat_1(B_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_776,c_46])).

tff(c_2720,plain,(
    ! [B_247] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_247))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_247))
      | ~ v1_relat_1(B_247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_788])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3006,plain,(
    ! [B_262] :
      ( k5_relat_1(k1_xboole_0,B_262) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_262))
      | ~ v1_relat_1(B_262) ) ),
    inference(resolution,[status(thm)],[c_2720,c_10])).

tff(c_3013,plain,(
    ! [B_41] :
      ( k5_relat_1(k1_xboole_0,B_41) = k1_xboole_0
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_44,c_3006])).

tff(c_3045,plain,(
    ! [B_264] :
      ( k5_relat_1(k1_xboole_0,B_264) = k1_xboole_0
      | ~ v1_relat_1(B_264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_3013])).

tff(c_3081,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_3045])).

tff(c_3097,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_3081])).

tff(c_3098,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_3100,plain,(
    ! [A_265] :
      ( v1_relat_1(A_265)
      | ~ v1_xboole_0(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3104,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_3100])).

tff(c_26,plain,(
    ! [A_18] : r1_xboole_0(A_18,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3110,plain,(
    ! [B_268,A_269] :
      ( r1_xboole_0(B_268,A_269)
      | ~ r1_xboole_0(A_269,B_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3113,plain,(
    ! [A_18] : r1_xboole_0(k1_xboole_0,A_18) ),
    inference(resolution,[status(thm)],[c_26,c_3110])).

tff(c_3348,plain,(
    ! [C_302,D_303,A_304,B_305] :
      ( ~ r1_xboole_0(C_302,D_303)
      | r1_xboole_0(k2_zfmisc_1(A_304,C_302),k2_zfmisc_1(B_305,D_303)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3148,plain,(
    ! [A_277,B_278,C_279] :
      ( ~ r1_xboole_0(A_277,B_278)
      | ~ r2_hidden(C_279,k3_xboole_0(A_277,B_278)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3179,plain,(
    ! [A_285,B_286] :
      ( ~ r1_xboole_0(A_285,B_286)
      | v1_xboole_0(k3_xboole_0(A_285,B_286)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3148])).

tff(c_3188,plain,(
    ! [A_5] :
      ( ~ r1_xboole_0(A_5,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_3179])).

tff(c_3392,plain,(
    ! [B_310,D_311] :
      ( v1_xboole_0(k2_zfmisc_1(B_310,D_311))
      | ~ r1_xboole_0(D_311,D_311) ) ),
    inference(resolution,[status(thm)],[c_3348,c_3188])).

tff(c_3409,plain,(
    ! [B_312] : v1_xboole_0(k2_zfmisc_1(B_312,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_3113,c_3392])).

tff(c_3417,plain,(
    ! [B_312] : k2_zfmisc_1(B_312,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3409,c_10])).

tff(c_3526,plain,(
    ! [A_322,B_323] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_322,B_323)),k2_relat_1(B_323))
      | ~ v1_relat_1(B_323)
      | ~ v1_relat_1(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3534,plain,(
    ! [A_322] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_322,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_322) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_3526])).

tff(c_3789,plain,(
    ! [A_355] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_355,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_355) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3104,c_3534])).

tff(c_3204,plain,(
    ! [B_288,A_289] :
      ( B_288 = A_289
      | ~ r1_tarski(B_288,A_289)
      | ~ r1_tarski(A_289,B_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3213,plain,(
    ! [A_17] :
      ( k1_xboole_0 = A_17
      | ~ r1_tarski(A_17,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_3204])).

tff(c_3799,plain,(
    ! [A_356] :
      ( k2_relat_1(k5_relat_1(A_356,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_356) ) ),
    inference(resolution,[status(thm)],[c_3789,c_3213])).

tff(c_48,plain,(
    ! [A_43] :
      ( r1_tarski(A_43,k2_zfmisc_1(k1_relat_1(A_43),k2_relat_1(A_43)))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3817,plain,(
    ! [A_356] :
      ( r1_tarski(k5_relat_1(A_356,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(A_356,k1_xboole_0)),k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_356,k1_xboole_0))
      | ~ v1_relat_1(A_356) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3799,c_48])).

tff(c_14180,plain,(
    ! [A_642] :
      ( r1_tarski(k5_relat_1(A_642,k1_xboole_0),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_642,k1_xboole_0))
      | ~ v1_relat_1(A_642) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3417,c_3817])).

tff(c_14195,plain,(
    ! [A_643] :
      ( k5_relat_1(A_643,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_643,k1_xboole_0))
      | ~ v1_relat_1(A_643) ) ),
    inference(resolution,[status(thm)],[c_14180,c_3213])).

tff(c_14202,plain,(
    ! [A_40] :
      ( k5_relat_1(A_40,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_40) ) ),
    inference(resolution,[status(thm)],[c_44,c_14195])).

tff(c_14208,plain,(
    ! [A_644] :
      ( k5_relat_1(A_644,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_644) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3104,c_14202])).

tff(c_14265,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_14208])).

tff(c_14288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3098,c_14265])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:15:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.97/4.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.97/4.03  
% 10.97/4.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.97/4.04  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 10.97/4.04  
% 10.97/4.04  %Foreground sorts:
% 10.97/4.04  
% 10.97/4.04  
% 10.97/4.04  %Background operators:
% 10.97/4.04  
% 10.97/4.04  
% 10.97/4.04  %Foreground operators:
% 10.97/4.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.97/4.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.97/4.04  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.97/4.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.97/4.04  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.97/4.04  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.97/4.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.97/4.04  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.97/4.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.97/4.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.97/4.04  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.97/4.04  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.97/4.04  tff('#skF_3', type, '#skF_3': $i).
% 10.97/4.04  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.97/4.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.97/4.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.97/4.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.97/4.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.97/4.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.97/4.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.97/4.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.97/4.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.97/4.04  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.97/4.04  
% 11.09/4.06  tff(f_130, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 11.09/4.06  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.09/4.06  tff(f_86, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 11.09/4.06  tff(f_92, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 11.09/4.06  tff(f_64, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.09/4.06  tff(f_123, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 11.09/4.06  tff(f_120, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 11.09/4.06  tff(f_100, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 11.09/4.06  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 11.09/4.06  tff(f_66, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 11.09/4.06  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 11.09/4.06  tff(f_80, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 11.09/4.06  tff(f_34, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 11.09/4.06  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.09/4.06  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 11.09/4.06  tff(f_111, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 11.09/4.06  tff(f_62, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.09/4.06  tff(f_104, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 11.09/4.06  tff(c_58, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.09/4.06  tff(c_88, plain, (k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 11.09/4.06  tff(c_60, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.09/4.06  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.09/4.06  tff(c_89, plain, (![A_55]: (v1_relat_1(A_55) | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.09/4.06  tff(c_93, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_89])).
% 11.09/4.06  tff(c_44, plain, (![A_40, B_41]: (v1_relat_1(k5_relat_1(A_40, B_41)) | ~v1_relat_1(B_41) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.09/4.06  tff(c_24, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.09/4.06  tff(c_56, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.09/4.06  tff(c_54, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.09/4.06  tff(c_760, plain, (![A_143, B_144]: (k1_relat_1(k5_relat_1(A_143, B_144))=k1_relat_1(A_143) | ~r1_tarski(k2_relat_1(A_143), k1_relat_1(B_144)) | ~v1_relat_1(B_144) | ~v1_relat_1(A_143))), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.09/4.06  tff(c_769, plain, (![B_144]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_144))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_144)) | ~v1_relat_1(B_144) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_54, c_760])).
% 11.09/4.06  tff(c_776, plain, (![B_145]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_145))=k1_xboole_0 | ~v1_relat_1(B_145))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_24, c_56, c_769])).
% 11.09/4.06  tff(c_46, plain, (![A_42]: (~v1_xboole_0(k1_relat_1(A_42)) | ~v1_relat_1(A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.09/4.06  tff(c_788, plain, (![B_145]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_145)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_145)) | ~v1_relat_1(B_145))), inference(superposition, [status(thm), theory('equality')], [c_776, c_46])).
% 11.09/4.06  tff(c_2720, plain, (![B_247]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_247)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_247)) | ~v1_relat_1(B_247))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_788])).
% 11.09/4.06  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.09/4.06  tff(c_3006, plain, (![B_262]: (k5_relat_1(k1_xboole_0, B_262)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_262)) | ~v1_relat_1(B_262))), inference(resolution, [status(thm)], [c_2720, c_10])).
% 11.09/4.06  tff(c_3013, plain, (![B_41]: (k5_relat_1(k1_xboole_0, B_41)=k1_xboole_0 | ~v1_relat_1(B_41) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_44, c_3006])).
% 11.09/4.06  tff(c_3045, plain, (![B_264]: (k5_relat_1(k1_xboole_0, B_264)=k1_xboole_0 | ~v1_relat_1(B_264))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_3013])).
% 11.09/4.06  tff(c_3081, plain, (k5_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_3045])).
% 11.09/4.06  tff(c_3097, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_3081])).
% 11.09/4.06  tff(c_3098, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 11.09/4.06  tff(c_3100, plain, (![A_265]: (v1_relat_1(A_265) | ~v1_xboole_0(A_265))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.09/4.06  tff(c_3104, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_3100])).
% 11.09/4.06  tff(c_26, plain, (![A_18]: (r1_xboole_0(A_18, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.09/4.06  tff(c_3110, plain, (![B_268, A_269]: (r1_xboole_0(B_268, A_269) | ~r1_xboole_0(A_269, B_268))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.09/4.06  tff(c_3113, plain, (![A_18]: (r1_xboole_0(k1_xboole_0, A_18))), inference(resolution, [status(thm)], [c_26, c_3110])).
% 11.09/4.06  tff(c_3348, plain, (![C_302, D_303, A_304, B_305]: (~r1_xboole_0(C_302, D_303) | r1_xboole_0(k2_zfmisc_1(A_304, C_302), k2_zfmisc_1(B_305, D_303)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.09/4.06  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.09/4.06  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.09/4.06  tff(c_3148, plain, (![A_277, B_278, C_279]: (~r1_xboole_0(A_277, B_278) | ~r2_hidden(C_279, k3_xboole_0(A_277, B_278)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.09/4.06  tff(c_3179, plain, (![A_285, B_286]: (~r1_xboole_0(A_285, B_286) | v1_xboole_0(k3_xboole_0(A_285, B_286)))), inference(resolution, [status(thm)], [c_4, c_3148])).
% 11.09/4.06  tff(c_3188, plain, (![A_5]: (~r1_xboole_0(A_5, A_5) | v1_xboole_0(A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_3179])).
% 11.09/4.06  tff(c_3392, plain, (![B_310, D_311]: (v1_xboole_0(k2_zfmisc_1(B_310, D_311)) | ~r1_xboole_0(D_311, D_311))), inference(resolution, [status(thm)], [c_3348, c_3188])).
% 11.09/4.06  tff(c_3409, plain, (![B_312]: (v1_xboole_0(k2_zfmisc_1(B_312, k1_xboole_0)))), inference(resolution, [status(thm)], [c_3113, c_3392])).
% 11.09/4.06  tff(c_3417, plain, (![B_312]: (k2_zfmisc_1(B_312, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3409, c_10])).
% 11.09/4.06  tff(c_3526, plain, (![A_322, B_323]: (r1_tarski(k2_relat_1(k5_relat_1(A_322, B_323)), k2_relat_1(B_323)) | ~v1_relat_1(B_323) | ~v1_relat_1(A_322))), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.09/4.06  tff(c_3534, plain, (![A_322]: (r1_tarski(k2_relat_1(k5_relat_1(A_322, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_322))), inference(superposition, [status(thm), theory('equality')], [c_54, c_3526])).
% 11.09/4.06  tff(c_3789, plain, (![A_355]: (r1_tarski(k2_relat_1(k5_relat_1(A_355, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_355))), inference(demodulation, [status(thm), theory('equality')], [c_3104, c_3534])).
% 11.09/4.06  tff(c_3204, plain, (![B_288, A_289]: (B_288=A_289 | ~r1_tarski(B_288, A_289) | ~r1_tarski(A_289, B_288))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.09/4.06  tff(c_3213, plain, (![A_17]: (k1_xboole_0=A_17 | ~r1_tarski(A_17, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_3204])).
% 11.09/4.06  tff(c_3799, plain, (![A_356]: (k2_relat_1(k5_relat_1(A_356, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_356))), inference(resolution, [status(thm)], [c_3789, c_3213])).
% 11.09/4.06  tff(c_48, plain, (![A_43]: (r1_tarski(A_43, k2_zfmisc_1(k1_relat_1(A_43), k2_relat_1(A_43))) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.09/4.06  tff(c_3817, plain, (![A_356]: (r1_tarski(k5_relat_1(A_356, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(A_356, k1_xboole_0)), k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_356, k1_xboole_0)) | ~v1_relat_1(A_356))), inference(superposition, [status(thm), theory('equality')], [c_3799, c_48])).
% 11.09/4.06  tff(c_14180, plain, (![A_642]: (r1_tarski(k5_relat_1(A_642, k1_xboole_0), k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_642, k1_xboole_0)) | ~v1_relat_1(A_642))), inference(demodulation, [status(thm), theory('equality')], [c_3417, c_3817])).
% 11.09/4.06  tff(c_14195, plain, (![A_643]: (k5_relat_1(A_643, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_643, k1_xboole_0)) | ~v1_relat_1(A_643))), inference(resolution, [status(thm)], [c_14180, c_3213])).
% 11.09/4.06  tff(c_14202, plain, (![A_40]: (k5_relat_1(A_40, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_40))), inference(resolution, [status(thm)], [c_44, c_14195])).
% 11.09/4.06  tff(c_14208, plain, (![A_644]: (k5_relat_1(A_644, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_644))), inference(demodulation, [status(thm), theory('equality')], [c_3104, c_14202])).
% 11.09/4.06  tff(c_14265, plain, (k5_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_14208])).
% 11.09/4.06  tff(c_14288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3098, c_14265])).
% 11.09/4.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.09/4.06  
% 11.09/4.06  Inference rules
% 11.09/4.06  ----------------------
% 11.09/4.06  #Ref     : 0
% 11.09/4.06  #Sup     : 3453
% 11.09/4.06  #Fact    : 0
% 11.09/4.06  #Define  : 0
% 11.09/4.06  #Split   : 3
% 11.09/4.06  #Chain   : 0
% 11.09/4.06  #Close   : 0
% 11.09/4.06  
% 11.09/4.06  Ordering : KBO
% 11.09/4.06  
% 11.09/4.06  Simplification rules
% 11.09/4.06  ----------------------
% 11.09/4.06  #Subsume      : 242
% 11.09/4.06  #Demod        : 3951
% 11.09/4.06  #Tautology    : 2728
% 11.09/4.06  #SimpNegUnit  : 10
% 11.09/4.06  #BackRed      : 13
% 11.09/4.06  
% 11.09/4.06  #Partial instantiations: 0
% 11.09/4.06  #Strategies tried      : 1
% 11.09/4.06  
% 11.09/4.06  Timing (in seconds)
% 11.09/4.06  ----------------------
% 11.09/4.07  Preprocessing        : 0.55
% 11.09/4.07  Parsing              : 0.28
% 11.09/4.07  CNF conversion       : 0.04
% 11.09/4.07  Main loop            : 2.56
% 11.09/4.07  Inferencing          : 0.88
% 11.09/4.07  Reduction            : 0.81
% 11.09/4.07  Demodulation         : 0.60
% 11.09/4.07  BG Simplification    : 0.09
% 11.09/4.07  Subsumption          : 0.60
% 11.09/4.07  Abstraction          : 0.11
% 11.09/4.07  MUC search           : 0.00
% 11.09/4.07  Cooper               : 0.00
% 11.09/4.07  Total                : 3.17
% 11.09/4.07  Index Insertion      : 0.00
% 11.09/4.07  Index Deletion       : 0.00
% 11.09/4.07  Index Matching       : 0.00
% 11.09/4.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
