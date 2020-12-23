%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:06 EST 2020

% Result     : Theorem 9.40s
% Output     : CNFRefutation 9.40s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 932 expanded)
%              Number of leaves         :   39 ( 332 expanded)
%              Depth                    :   22
%              Number of atoms          :  209 (1663 expanded)
%              Number of equality atoms :   73 ( 520 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_38,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_42,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_101,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_54,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_101,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_56,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_102,plain,(
    ! [A_64] :
      ( v1_relat_1(A_64)
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_106,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_102])).

tff(c_40,plain,(
    ! [A_43,B_44] :
      ( v1_relat_1(k5_relat_1(A_43,B_44))
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_148,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k4_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_160,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_148])).

tff(c_163,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_160])).

tff(c_356,plain,(
    ! [C_95,A_96,B_97] : k4_xboole_0(k2_zfmisc_1(C_95,A_96),k2_zfmisc_1(C_95,B_97)) = k2_zfmisc_1(C_95,k4_xboole_0(A_96,B_97)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_363,plain,(
    ! [C_95,B_97] : k2_zfmisc_1(C_95,k4_xboole_0(B_97,B_97)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_163])).

tff(c_372,plain,(
    ! [C_95] : k2_zfmisc_1(C_95,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_363])).

tff(c_393,plain,(
    ! [A_99,C_100,B_101] : k4_xboole_0(k2_zfmisc_1(A_99,C_100),k2_zfmisc_1(B_101,C_100)) = k2_zfmisc_1(k4_xboole_0(A_99,B_101),C_100) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    ! [C_39,A_37,B_38] : k4_xboole_0(k2_zfmisc_1(C_39,A_37),k2_zfmisc_1(C_39,B_38)) = k2_zfmisc_1(C_39,k4_xboole_0(A_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_400,plain,(
    ! [B_101,C_100] : k2_zfmisc_1(k4_xboole_0(B_101,B_101),C_100) = k2_zfmisc_1(B_101,k4_xboole_0(C_100,C_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_34])).

tff(c_423,plain,(
    ! [C_100] : k2_zfmisc_1(k1_xboole_0,C_100) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_163,c_163,c_400])).

tff(c_52,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_232,plain,(
    ! [A_82,B_83] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_82,B_83)),k1_relat_1(A_82))
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_237,plain,(
    ! [B_83] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_83)),k1_xboole_0)
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_232])).

tff(c_245,plain,(
    ! [B_84] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_84)),k1_xboole_0)
      | ~ v1_relat_1(B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_237])).

tff(c_16,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_125,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_134,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_125])).

tff(c_255,plain,(
    ! [B_85] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_85)) = k1_xboole_0
      | ~ v1_relat_1(B_85) ) ),
    inference(resolution,[status(thm)],[c_245,c_134])).

tff(c_42,plain,(
    ! [A_45] :
      ( k3_xboole_0(A_45,k2_zfmisc_1(k1_relat_1(A_45),k2_relat_1(A_45))) = A_45
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_270,plain,(
    ! [B_85] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_85),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_85)))) = k5_relat_1(k1_xboole_0,B_85)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_85))
      | ~ v1_relat_1(B_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_42])).

tff(c_3377,plain,(
    ! [B_198] :
      ( k5_relat_1(k1_xboole_0,B_198) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_198))
      | ~ v1_relat_1(B_198) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_423,c_270])).

tff(c_3385,plain,(
    ! [B_44] :
      ( k5_relat_1(k1_xboole_0,B_44) = k1_xboole_0
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_3377])).

tff(c_3392,plain,(
    ! [B_199] :
      ( k5_relat_1(k1_xboole_0,B_199) = k1_xboole_0
      | ~ v1_relat_1(B_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_3385])).

tff(c_3404,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_3392])).

tff(c_3411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_3404])).

tff(c_3412,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_3414,plain,(
    ! [A_200] :
      ( v1_relat_1(A_200)
      | ~ v1_xboole_0(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3418,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_3414])).

tff(c_50,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3571,plain,(
    ! [A_220,B_221] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_220,B_221)),k2_relat_1(B_221))
      | ~ v1_relat_1(B_221)
      | ~ v1_relat_1(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3579,plain,(
    ! [A_220] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_220,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_220) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_3571])).

tff(c_3629,plain,(
    ! [A_224] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_224,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_224) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3418,c_3579])).

tff(c_3441,plain,(
    ! [B_205,A_206] :
      ( B_205 = A_206
      | ~ r1_tarski(B_205,A_206)
      | ~ r1_tarski(A_206,B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3450,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_3441])).

tff(c_3635,plain,(
    ! [A_224] :
      ( k2_relat_1(k5_relat_1(A_224,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_224) ) ),
    inference(resolution,[status(thm)],[c_3629,c_3450])).

tff(c_3413,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_4168,plain,(
    ! [A_265,B_266,C_267] :
      ( k5_relat_1(k5_relat_1(A_265,B_266),C_267) = k5_relat_1(A_265,k5_relat_1(B_266,C_267))
      | ~ v1_relat_1(C_267)
      | ~ v1_relat_1(B_266)
      | ~ v1_relat_1(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4200,plain,(
    ! [C_267] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',C_267)) = k5_relat_1(k1_xboole_0,C_267)
      | ~ v1_relat_1(C_267)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3413,c_4168])).

tff(c_4209,plain,(
    ! [C_268] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',C_268)) = k5_relat_1(k1_xboole_0,C_268)
      | ~ v1_relat_1(C_268) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3418,c_56,c_4200])).

tff(c_46,plain,(
    ! [A_49,B_51] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_49,B_51)),k2_relat_1(B_51))
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4224,plain,(
    ! [C_268] :
      ( r1_tarski(k2_relat_1(k5_relat_1(k1_xboole_0,C_268)),k2_relat_1(k5_relat_1('#skF_1',C_268)))
      | ~ v1_relat_1(k5_relat_1('#skF_1',C_268))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(C_268) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4209,c_46])).

tff(c_4361,plain,(
    ! [C_273] :
      ( r1_tarski(k2_relat_1(k5_relat_1(k1_xboole_0,C_273)),k2_relat_1(k5_relat_1('#skF_1',C_273)))
      | ~ v1_relat_1(k5_relat_1('#skF_1',C_273))
      | ~ v1_relat_1(C_273) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3418,c_4224])).

tff(c_4374,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1('#skF_1',k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3635,c_4361])).

tff(c_4382,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1('#skF_1',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3418,c_4374])).

tff(c_4385,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_1',k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_4382])).

tff(c_4388,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_4385])).

tff(c_4392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3418,c_4388])).

tff(c_4394,plain,(
    v1_relat_1(k5_relat_1('#skF_1',k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_4382])).

tff(c_3464,plain,(
    ! [A_208,B_209] : k5_xboole_0(A_208,k3_xboole_0(A_208,B_209)) = k4_xboole_0(A_208,B_209) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3476,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3464])).

tff(c_3479,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3476])).

tff(c_3716,plain,(
    ! [C_234,A_235,B_236] : k4_xboole_0(k2_zfmisc_1(C_234,A_235),k2_zfmisc_1(C_234,B_236)) = k2_zfmisc_1(C_234,k4_xboole_0(A_235,B_236)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3727,plain,(
    ! [C_234,B_236] : k2_zfmisc_1(C_234,k4_xboole_0(B_236,B_236)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3716,c_3479])).

tff(c_3741,plain,(
    ! [C_234] : k2_zfmisc_1(C_234,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3479,c_3727])).

tff(c_4230,plain,(
    ! [C_268] :
      ( v1_relat_1(k5_relat_1(k1_xboole_0,C_268))
      | ~ v1_relat_1(k5_relat_1('#skF_1',C_268))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(C_268) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4209,c_40])).

tff(c_4242,plain,(
    ! [C_268] :
      ( v1_relat_1(k5_relat_1(k1_xboole_0,C_268))
      | ~ v1_relat_1(k5_relat_1('#skF_1',C_268))
      | ~ v1_relat_1(C_268) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3418,c_4230])).

tff(c_4393,plain,(
    r1_tarski(k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_4382])).

tff(c_4403,plain,(
    k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4393,c_3450])).

tff(c_4432,plain,
    ( k3_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4403,c_42])).

tff(c_4448,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3741,c_4432])).

tff(c_4463,plain,(
    ~ v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_4448])).

tff(c_4466,plain,
    ( ~ v1_relat_1(k5_relat_1('#skF_1',k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4242,c_4463])).

tff(c_4473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3418,c_4394,c_4466])).

tff(c_4474,plain,(
    k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4448])).

tff(c_4208,plain,(
    ! [C_267] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',C_267)) = k5_relat_1(k1_xboole_0,C_267)
      | ~ v1_relat_1(C_267) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3418,c_56,c_4200])).

tff(c_48,plain,(
    ! [A_52,B_56,C_58] :
      ( k5_relat_1(k5_relat_1(A_52,B_56),C_58) = k5_relat_1(A_52,k5_relat_1(B_56,C_58))
      | ~ v1_relat_1(C_58)
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4513,plain,(
    ! [C_58] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,C_58)) = k5_relat_1(k1_xboole_0,C_58)
      | ~ v1_relat_1(C_58)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4474,c_48])).

tff(c_4563,plain,(
    ! [C_282] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,C_282)) = k5_relat_1(k1_xboole_0,C_282)
      | ~ v1_relat_1(C_282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3418,c_3418,c_4513])).

tff(c_4786,plain,(
    ! [C_289] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,C_289)) = k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',C_289))
      | ~ v1_relat_1(k5_relat_1('#skF_1',C_289))
      | ~ v1_relat_1(C_289) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4208,c_4563])).

tff(c_4789,plain,
    ( k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4394,c_4786])).

tff(c_4796,plain,(
    k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3418,c_4474,c_4474,c_4789])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5183,plain,(
    ! [A_292,B_293] :
      ( k2_relat_1(k5_relat_1(A_292,B_293)) = k2_relat_1(B_293)
      | ~ r1_tarski(k2_relat_1(B_293),k2_relat_1(k5_relat_1(A_292,B_293)))
      | ~ v1_relat_1(B_293)
      | ~ v1_relat_1(A_292) ) ),
    inference(resolution,[status(thm)],[c_3571,c_6])).

tff(c_5213,plain,(
    ! [C_267] :
      ( k2_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',C_267))) = k2_relat_1(k5_relat_1('#skF_1',C_267))
      | ~ r1_tarski(k2_relat_1(k5_relat_1('#skF_1',C_267)),k2_relat_1(k5_relat_1(k1_xboole_0,C_267)))
      | ~ v1_relat_1(k5_relat_1('#skF_1',C_267))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(C_267) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4208,c_5183])).

tff(c_12840,plain,(
    ! [C_372] :
      ( k2_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',C_372))) = k2_relat_1(k5_relat_1('#skF_1',C_372))
      | ~ r1_tarski(k2_relat_1(k5_relat_1('#skF_1',C_372)),k2_relat_1(k5_relat_1(k1_xboole_0,C_372)))
      | ~ v1_relat_1(k5_relat_1('#skF_1',C_372))
      | ~ v1_relat_1(C_372) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3418,c_5213])).

tff(c_12929,plain,
    ( k2_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',k1_xboole_0))) = k2_relat_1(k5_relat_1('#skF_1',k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_relat_1(k5_relat_1('#skF_1',k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3635,c_12840])).

tff(c_12959,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3418,c_4394,c_16,c_4474,c_50,c_4796,c_12929])).

tff(c_13019,plain,
    ( k3_xboole_0(k5_relat_1('#skF_1',k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1('#skF_1',k1_xboole_0)),k1_xboole_0)) = k5_relat_1('#skF_1',k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1('#skF_1',k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12959,c_42])).

tff(c_13061,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4394,c_14,c_3741,c_13019])).

tff(c_13063,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3412,c_13061])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.40/3.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.40/3.20  
% 9.40/3.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.40/3.20  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 9.40/3.20  
% 9.40/3.20  %Foreground sorts:
% 9.40/3.20  
% 9.40/3.20  
% 9.40/3.20  %Background operators:
% 9.40/3.20  
% 9.40/3.20  
% 9.40/3.20  %Foreground operators:
% 9.40/3.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.40/3.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.40/3.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.40/3.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.40/3.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.40/3.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.40/3.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.40/3.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.40/3.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.40/3.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.40/3.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.40/3.20  tff('#skF_1', type, '#skF_1': $i).
% 9.40/3.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.40/3.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.40/3.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.40/3.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.40/3.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.40/3.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.40/3.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.40/3.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.40/3.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.40/3.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.40/3.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.40/3.20  
% 9.40/3.23  tff(f_108, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 9.40/3.23  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.40/3.23  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 9.40/3.23  tff(f_70, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 9.40/3.23  tff(f_38, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 9.40/3.23  tff(f_42, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 9.40/3.23  tff(f_28, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 9.40/3.23  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.40/3.23  tff(f_58, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 9.40/3.23  tff(f_101, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 9.40/3.23  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 9.40/3.23  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.40/3.23  tff(f_34, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.40/3.23  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 9.40/3.23  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 9.40/3.23  tff(f_98, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 9.40/3.23  tff(c_54, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.40/3.23  tff(c_101, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 9.40/3.23  tff(c_56, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.40/3.23  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 9.40/3.23  tff(c_102, plain, (![A_64]: (v1_relat_1(A_64) | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.40/3.23  tff(c_106, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_102])).
% 9.40/3.23  tff(c_40, plain, (![A_43, B_44]: (v1_relat_1(k5_relat_1(A_43, B_44)) | ~v1_relat_1(B_44) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.40/3.23  tff(c_14, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.40/3.23  tff(c_18, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.40/3.23  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 9.40/3.23  tff(c_148, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k4_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.40/3.23  tff(c_160, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_148])).
% 9.40/3.23  tff(c_163, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_160])).
% 9.40/3.23  tff(c_356, plain, (![C_95, A_96, B_97]: (k4_xboole_0(k2_zfmisc_1(C_95, A_96), k2_zfmisc_1(C_95, B_97))=k2_zfmisc_1(C_95, k4_xboole_0(A_96, B_97)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.40/3.23  tff(c_363, plain, (![C_95, B_97]: (k2_zfmisc_1(C_95, k4_xboole_0(B_97, B_97))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_356, c_163])).
% 9.40/3.23  tff(c_372, plain, (![C_95]: (k2_zfmisc_1(C_95, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_163, c_363])).
% 9.40/3.23  tff(c_393, plain, (![A_99, C_100, B_101]: (k4_xboole_0(k2_zfmisc_1(A_99, C_100), k2_zfmisc_1(B_101, C_100))=k2_zfmisc_1(k4_xboole_0(A_99, B_101), C_100))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.40/3.23  tff(c_34, plain, (![C_39, A_37, B_38]: (k4_xboole_0(k2_zfmisc_1(C_39, A_37), k2_zfmisc_1(C_39, B_38))=k2_zfmisc_1(C_39, k4_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.40/3.23  tff(c_400, plain, (![B_101, C_100]: (k2_zfmisc_1(k4_xboole_0(B_101, B_101), C_100)=k2_zfmisc_1(B_101, k4_xboole_0(C_100, C_100)))), inference(superposition, [status(thm), theory('equality')], [c_393, c_34])).
% 9.40/3.23  tff(c_423, plain, (![C_100]: (k2_zfmisc_1(k1_xboole_0, C_100)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_372, c_163, c_163, c_400])).
% 9.40/3.23  tff(c_52, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.40/3.23  tff(c_232, plain, (![A_82, B_83]: (r1_tarski(k1_relat_1(k5_relat_1(A_82, B_83)), k1_relat_1(A_82)) | ~v1_relat_1(B_83) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.40/3.23  tff(c_237, plain, (![B_83]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_83)), k1_xboole_0) | ~v1_relat_1(B_83) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_52, c_232])).
% 9.40/3.23  tff(c_245, plain, (![B_84]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_84)), k1_xboole_0) | ~v1_relat_1(B_84))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_237])).
% 9.40/3.23  tff(c_16, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.40/3.23  tff(c_125, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.40/3.23  tff(c_134, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_125])).
% 9.40/3.23  tff(c_255, plain, (![B_85]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_85))=k1_xboole_0 | ~v1_relat_1(B_85))), inference(resolution, [status(thm)], [c_245, c_134])).
% 9.40/3.23  tff(c_42, plain, (![A_45]: (k3_xboole_0(A_45, k2_zfmisc_1(k1_relat_1(A_45), k2_relat_1(A_45)))=A_45 | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.40/3.23  tff(c_270, plain, (![B_85]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_85), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_85))))=k5_relat_1(k1_xboole_0, B_85) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_85)) | ~v1_relat_1(B_85))), inference(superposition, [status(thm), theory('equality')], [c_255, c_42])).
% 9.40/3.23  tff(c_3377, plain, (![B_198]: (k5_relat_1(k1_xboole_0, B_198)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_198)) | ~v1_relat_1(B_198))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_423, c_270])).
% 9.40/3.23  tff(c_3385, plain, (![B_44]: (k5_relat_1(k1_xboole_0, B_44)=k1_xboole_0 | ~v1_relat_1(B_44) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_3377])).
% 9.40/3.23  tff(c_3392, plain, (![B_199]: (k5_relat_1(k1_xboole_0, B_199)=k1_xboole_0 | ~v1_relat_1(B_199))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_3385])).
% 9.40/3.23  tff(c_3404, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_3392])).
% 9.40/3.23  tff(c_3411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_3404])).
% 9.40/3.23  tff(c_3412, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 9.40/3.23  tff(c_3414, plain, (![A_200]: (v1_relat_1(A_200) | ~v1_xboole_0(A_200))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.40/3.23  tff(c_3418, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_3414])).
% 9.40/3.23  tff(c_50, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.40/3.23  tff(c_3571, plain, (![A_220, B_221]: (r1_tarski(k2_relat_1(k5_relat_1(A_220, B_221)), k2_relat_1(B_221)) | ~v1_relat_1(B_221) | ~v1_relat_1(A_220))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.40/3.23  tff(c_3579, plain, (![A_220]: (r1_tarski(k2_relat_1(k5_relat_1(A_220, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_220))), inference(superposition, [status(thm), theory('equality')], [c_50, c_3571])).
% 9.40/3.23  tff(c_3629, plain, (![A_224]: (r1_tarski(k2_relat_1(k5_relat_1(A_224, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_224))), inference(demodulation, [status(thm), theory('equality')], [c_3418, c_3579])).
% 9.40/3.23  tff(c_3441, plain, (![B_205, A_206]: (B_205=A_206 | ~r1_tarski(B_205, A_206) | ~r1_tarski(A_206, B_205))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.40/3.23  tff(c_3450, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_3441])).
% 9.40/3.23  tff(c_3635, plain, (![A_224]: (k2_relat_1(k5_relat_1(A_224, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_224))), inference(resolution, [status(thm)], [c_3629, c_3450])).
% 9.40/3.23  tff(c_3413, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 9.40/3.23  tff(c_4168, plain, (![A_265, B_266, C_267]: (k5_relat_1(k5_relat_1(A_265, B_266), C_267)=k5_relat_1(A_265, k5_relat_1(B_266, C_267)) | ~v1_relat_1(C_267) | ~v1_relat_1(B_266) | ~v1_relat_1(A_265))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.40/3.23  tff(c_4200, plain, (![C_267]: (k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', C_267))=k5_relat_1(k1_xboole_0, C_267) | ~v1_relat_1(C_267) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3413, c_4168])).
% 9.40/3.23  tff(c_4209, plain, (![C_268]: (k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', C_268))=k5_relat_1(k1_xboole_0, C_268) | ~v1_relat_1(C_268))), inference(demodulation, [status(thm), theory('equality')], [c_3418, c_56, c_4200])).
% 9.40/3.23  tff(c_46, plain, (![A_49, B_51]: (r1_tarski(k2_relat_1(k5_relat_1(A_49, B_51)), k2_relat_1(B_51)) | ~v1_relat_1(B_51) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.40/3.23  tff(c_4224, plain, (![C_268]: (r1_tarski(k2_relat_1(k5_relat_1(k1_xboole_0, C_268)), k2_relat_1(k5_relat_1('#skF_1', C_268))) | ~v1_relat_1(k5_relat_1('#skF_1', C_268)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(C_268))), inference(superposition, [status(thm), theory('equality')], [c_4209, c_46])).
% 9.40/3.23  tff(c_4361, plain, (![C_273]: (r1_tarski(k2_relat_1(k5_relat_1(k1_xboole_0, C_273)), k2_relat_1(k5_relat_1('#skF_1', C_273))) | ~v1_relat_1(k5_relat_1('#skF_1', C_273)) | ~v1_relat_1(C_273))), inference(demodulation, [status(thm), theory('equality')], [c_3418, c_4224])).
% 9.40/3.23  tff(c_4374, plain, (r1_tarski(k2_relat_1(k5_relat_1(k1_xboole_0, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k5_relat_1('#skF_1', k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3635, c_4361])).
% 9.40/3.23  tff(c_4382, plain, (r1_tarski(k2_relat_1(k5_relat_1(k1_xboole_0, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k5_relat_1('#skF_1', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3418, c_4374])).
% 9.40/3.23  tff(c_4385, plain, (~v1_relat_1(k5_relat_1('#skF_1', k1_xboole_0))), inference(splitLeft, [status(thm)], [c_4382])).
% 9.40/3.23  tff(c_4388, plain, (~v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_40, c_4385])).
% 9.40/3.23  tff(c_4392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_3418, c_4388])).
% 9.40/3.23  tff(c_4394, plain, (v1_relat_1(k5_relat_1('#skF_1', k1_xboole_0))), inference(splitRight, [status(thm)], [c_4382])).
% 9.40/3.23  tff(c_3464, plain, (![A_208, B_209]: (k5_xboole_0(A_208, k3_xboole_0(A_208, B_209))=k4_xboole_0(A_208, B_209))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.40/3.23  tff(c_3476, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_3464])).
% 9.40/3.23  tff(c_3479, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3476])).
% 9.40/3.23  tff(c_3716, plain, (![C_234, A_235, B_236]: (k4_xboole_0(k2_zfmisc_1(C_234, A_235), k2_zfmisc_1(C_234, B_236))=k2_zfmisc_1(C_234, k4_xboole_0(A_235, B_236)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.40/3.23  tff(c_3727, plain, (![C_234, B_236]: (k2_zfmisc_1(C_234, k4_xboole_0(B_236, B_236))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3716, c_3479])).
% 9.40/3.23  tff(c_3741, plain, (![C_234]: (k2_zfmisc_1(C_234, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3479, c_3727])).
% 9.40/3.23  tff(c_4230, plain, (![C_268]: (v1_relat_1(k5_relat_1(k1_xboole_0, C_268)) | ~v1_relat_1(k5_relat_1('#skF_1', C_268)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(C_268))), inference(superposition, [status(thm), theory('equality')], [c_4209, c_40])).
% 9.40/3.23  tff(c_4242, plain, (![C_268]: (v1_relat_1(k5_relat_1(k1_xboole_0, C_268)) | ~v1_relat_1(k5_relat_1('#skF_1', C_268)) | ~v1_relat_1(C_268))), inference(demodulation, [status(thm), theory('equality')], [c_3418, c_4230])).
% 9.40/3.23  tff(c_4393, plain, (r1_tarski(k2_relat_1(k5_relat_1(k1_xboole_0, k1_xboole_0)), k1_xboole_0)), inference(splitRight, [status(thm)], [c_4382])).
% 9.40/3.23  tff(c_4403, plain, (k2_relat_1(k5_relat_1(k1_xboole_0, k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_4393, c_3450])).
% 9.40/3.23  tff(c_4432, plain, (k3_xboole_0(k5_relat_1(k1_xboole_0, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0, k1_xboole_0)), k1_xboole_0))=k5_relat_1(k1_xboole_0, k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4403, c_42])).
% 9.40/3.23  tff(c_4448, plain, (k5_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3741, c_4432])).
% 9.40/3.23  tff(c_4463, plain, (~v1_relat_1(k5_relat_1(k1_xboole_0, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_4448])).
% 9.40/3.23  tff(c_4466, plain, (~v1_relat_1(k5_relat_1('#skF_1', k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_4242, c_4463])).
% 9.40/3.23  tff(c_4473, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3418, c_4394, c_4466])).
% 9.40/3.23  tff(c_4474, plain, (k5_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_4448])).
% 9.40/3.23  tff(c_4208, plain, (![C_267]: (k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', C_267))=k5_relat_1(k1_xboole_0, C_267) | ~v1_relat_1(C_267))), inference(demodulation, [status(thm), theory('equality')], [c_3418, c_56, c_4200])).
% 9.40/3.23  tff(c_48, plain, (![A_52, B_56, C_58]: (k5_relat_1(k5_relat_1(A_52, B_56), C_58)=k5_relat_1(A_52, k5_relat_1(B_56, C_58)) | ~v1_relat_1(C_58) | ~v1_relat_1(B_56) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.40/3.23  tff(c_4513, plain, (![C_58]: (k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, C_58))=k5_relat_1(k1_xboole_0, C_58) | ~v1_relat_1(C_58) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4474, c_48])).
% 9.40/3.23  tff(c_4563, plain, (![C_282]: (k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, C_282))=k5_relat_1(k1_xboole_0, C_282) | ~v1_relat_1(C_282))), inference(demodulation, [status(thm), theory('equality')], [c_3418, c_3418, c_4513])).
% 9.40/3.23  tff(c_4786, plain, (![C_289]: (k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, C_289))=k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', C_289)) | ~v1_relat_1(k5_relat_1('#skF_1', C_289)) | ~v1_relat_1(C_289))), inference(superposition, [status(thm), theory('equality')], [c_4208, c_4563])).
% 9.40/3.23  tff(c_4789, plain, (k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, k1_xboole_0))=k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_4394, c_4786])).
% 9.40/3.23  tff(c_4796, plain, (k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3418, c_4474, c_4474, c_4789])).
% 9.40/3.23  tff(c_6, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.40/3.23  tff(c_5183, plain, (![A_292, B_293]: (k2_relat_1(k5_relat_1(A_292, B_293))=k2_relat_1(B_293) | ~r1_tarski(k2_relat_1(B_293), k2_relat_1(k5_relat_1(A_292, B_293))) | ~v1_relat_1(B_293) | ~v1_relat_1(A_292))), inference(resolution, [status(thm)], [c_3571, c_6])).
% 9.40/3.23  tff(c_5213, plain, (![C_267]: (k2_relat_1(k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', C_267)))=k2_relat_1(k5_relat_1('#skF_1', C_267)) | ~r1_tarski(k2_relat_1(k5_relat_1('#skF_1', C_267)), k2_relat_1(k5_relat_1(k1_xboole_0, C_267))) | ~v1_relat_1(k5_relat_1('#skF_1', C_267)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(C_267))), inference(superposition, [status(thm), theory('equality')], [c_4208, c_5183])).
% 9.40/3.23  tff(c_12840, plain, (![C_372]: (k2_relat_1(k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', C_372)))=k2_relat_1(k5_relat_1('#skF_1', C_372)) | ~r1_tarski(k2_relat_1(k5_relat_1('#skF_1', C_372)), k2_relat_1(k5_relat_1(k1_xboole_0, C_372))) | ~v1_relat_1(k5_relat_1('#skF_1', C_372)) | ~v1_relat_1(C_372))), inference(demodulation, [status(thm), theory('equality')], [c_3418, c_5213])).
% 9.40/3.23  tff(c_12929, plain, (k2_relat_1(k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', k1_xboole_0)))=k2_relat_1(k5_relat_1('#skF_1', k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, k1_xboole_0))) | ~v1_relat_1(k5_relat_1('#skF_1', k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3635, c_12840])).
% 9.40/3.23  tff(c_12959, plain, (k2_relat_1(k5_relat_1('#skF_1', k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3418, c_4394, c_16, c_4474, c_50, c_4796, c_12929])).
% 9.40/3.23  tff(c_13019, plain, (k3_xboole_0(k5_relat_1('#skF_1', k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1('#skF_1', k1_xboole_0)), k1_xboole_0))=k5_relat_1('#skF_1', k1_xboole_0) | ~v1_relat_1(k5_relat_1('#skF_1', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12959, c_42])).
% 9.40/3.23  tff(c_13061, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4394, c_14, c_3741, c_13019])).
% 9.40/3.23  tff(c_13063, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3412, c_13061])).
% 9.40/3.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.40/3.23  
% 9.40/3.23  Inference rules
% 9.40/3.23  ----------------------
% 9.40/3.23  #Ref     : 0
% 9.40/3.23  #Sup     : 2961
% 9.40/3.23  #Fact    : 0
% 9.40/3.23  #Define  : 0
% 9.40/3.23  #Split   : 4
% 9.40/3.23  #Chain   : 0
% 9.40/3.23  #Close   : 0
% 9.40/3.23  
% 9.40/3.23  Ordering : KBO
% 9.40/3.23  
% 9.40/3.23  Simplification rules
% 9.40/3.23  ----------------------
% 9.40/3.23  #Subsume      : 463
% 9.40/3.23  #Demod        : 4300
% 9.40/3.23  #Tautology    : 1268
% 9.40/3.23  #SimpNegUnit  : 2
% 9.40/3.23  #BackRed      : 10
% 9.40/3.23  
% 9.40/3.23  #Partial instantiations: 0
% 9.40/3.23  #Strategies tried      : 1
% 9.40/3.23  
% 9.40/3.23  Timing (in seconds)
% 9.40/3.23  ----------------------
% 9.40/3.23  Preprocessing        : 0.39
% 9.40/3.23  Parsing              : 0.20
% 9.40/3.23  CNF conversion       : 0.02
% 9.40/3.23  Main loop            : 2.01
% 9.40/3.23  Inferencing          : 0.62
% 9.40/3.23  Reduction            : 0.80
% 9.40/3.23  Demodulation         : 0.65
% 9.40/3.23  BG Simplification    : 0.09
% 9.40/3.23  Subsumption          : 0.40
% 9.40/3.23  Abstraction          : 0.13
% 9.40/3.23  MUC search           : 0.00
% 9.40/3.23  Cooper               : 0.00
% 9.40/3.23  Total                : 2.44
% 9.40/3.23  Index Insertion      : 0.00
% 9.40/3.23  Index Deletion       : 0.00
% 9.40/3.23  Index Matching       : 0.00
% 9.40/3.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
