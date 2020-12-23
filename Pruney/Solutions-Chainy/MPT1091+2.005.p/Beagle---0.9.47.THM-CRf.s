%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:25 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 284 expanded)
%              Number of leaves         :   20 (  94 expanded)
%              Depth                    :   10
%              Number of atoms          :  192 ( 599 expanded)
%              Number of equality atoms :   12 (  27 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_finset_1 > k3_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_finset_1(A)
          & ! [B] :
              ( r2_hidden(B,A)
             => v1_finset_1(B) ) )
      <=> v1_finset_1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_finset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_finset_1(A)
        & ! [B] :
            ( r2_hidden(B,A)
           => v1_finset_1(B) ) )
     => v1_finset_1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_finset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_finset_1(A)
     => v1_finset_1(k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_finset_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_finset_1(B)
     => v1_finset_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_finset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(c_16,plain,
    ( v1_finset_1(k3_tarski('#skF_2'))
    | ~ v1_finset_1(k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    ~ v1_finset_1(k3_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_28,plain,
    ( v1_finset_1(k3_tarski('#skF_2'))
    | v1_finset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_33,plain,(
    v1_finset_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_164,plain,(
    ! [A_37] :
      ( ~ v1_finset_1('#skF_1'(A_37))
      | v1_finset_1(k3_tarski(A_37))
      | ~ v1_finset_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_173,plain,
    ( ~ v1_finset_1('#skF_1'('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_164,c_36])).

tff(c_178,plain,(
    ~ v1_finset_1('#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_173])).

tff(c_196,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_1'(A_42),A_42)
      | v1_finset_1(k3_tarski(A_42))
      | ~ v1_finset_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_140,plain,(
    ! [A_34] :
      ( ~ v1_finset_1('#skF_1'(A_34))
      | v1_finset_1(k3_tarski(A_34))
      | ~ v1_finset_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_146,plain,
    ( ~ v1_finset_1('#skF_1'('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_140,c_36])).

tff(c_150,plain,(
    ~ v1_finset_1('#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_146])).

tff(c_151,plain,(
    ! [A_35] :
      ( r2_hidden('#skF_1'(A_35),A_35)
      | v1_finset_1(k3_tarski(A_35))
      | ~ v1_finset_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_76,plain,(
    ! [A_25] :
      ( ~ v1_finset_1('#skF_1'(A_25))
      | v1_finset_1(k3_tarski(A_25))
      | ~ v1_finset_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_82,plain,
    ( ~ v1_finset_1('#skF_1'('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_36])).

tff(c_86,plain,(
    ~ v1_finset_1('#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_82])).

tff(c_14,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_1'(A_9),A_9)
      | v1_finset_1(k3_tarski(A_9))
      | ~ v1_finset_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    ! [B_13] :
      ( v1_finset_1(k3_tarski('#skF_2'))
      | v1_finset_1(B_13)
      | ~ r2_hidden(B_13,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_68,plain,(
    v1_finset_1(k3_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_10,plain,(
    ! [A_8] :
      ( v1_finset_1(k1_zfmisc_1(A_8))
      | ~ v1_finset_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(A_5,k1_zfmisc_1(k3_tarski(A_5))) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_39,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    ! [A_20] : k3_xboole_0(A_20,k1_zfmisc_1(k3_tarski(A_20))) = A_20 ),
    inference(resolution,[status(thm)],[c_6,c_39])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_finset_1(k3_xboole_0(A_6,B_7))
      | ~ v1_finset_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_56,plain,(
    ! [A_21] :
      ( v1_finset_1(A_21)
      | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(A_21))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_8])).

tff(c_60,plain,(
    ! [A_21] :
      ( v1_finset_1(A_21)
      | ~ v1_finset_1(k3_tarski(A_21)) ) ),
    inference(resolution,[status(thm)],[c_10,c_56])).

tff(c_72,plain,(
    v1_finset_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_60])).

tff(c_24,plain,(
    ! [B_13] :
      ( ~ v1_finset_1('#skF_3')
      | ~ v1_finset_1('#skF_2')
      | v1_finset_1(B_13)
      | ~ r2_hidden(B_13,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_74,plain,(
    ! [B_13] :
      ( ~ v1_finset_1('#skF_3')
      | v1_finset_1(B_13)
      | ~ r2_hidden(B_13,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_24])).

tff(c_75,plain,(
    ~ v1_finset_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_26,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_3','#skF_2')
      | ~ v1_finset_1('#skF_2')
      | v1_finset_1(B_13)
      | ~ r2_hidden(B_13,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_116,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_3','#skF_2')
      | v1_finset_1(B_13)
      | ~ r2_hidden(B_13,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_26])).

tff(c_117,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_63,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,k3_tarski(B_24))
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_87,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,k3_tarski(B_27)) = A_26
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_63,c_2])).

tff(c_99,plain,(
    ! [A_28,B_29] :
      ( v1_finset_1(A_28)
      | ~ v1_finset_1(k3_tarski(B_29))
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_8])).

tff(c_105,plain,(
    ! [A_28] :
      ( v1_finset_1(A_28)
      | ~ r2_hidden(A_28,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_68,c_99])).

tff(c_120,plain,(
    v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_117,c_105])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_120])).

tff(c_127,plain,(
    ! [B_32] :
      ( v1_finset_1(B_32)
      | ~ r2_hidden(B_32,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_131,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_127])).

tff(c_134,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_131])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_86,c_134])).

tff(c_137,plain,(
    ! [B_13] :
      ( v1_finset_1(B_13)
      | ~ r2_hidden(B_13,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_155,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_151,c_137])).

tff(c_158,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_155])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_150,c_158])).

tff(c_161,plain,(
    ! [B_13] :
      ( v1_finset_1(B_13)
      | ~ r2_hidden(B_13,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_200,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_196,c_161])).

tff(c_203,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_200])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_178,c_203])).

tff(c_207,plain,(
    v1_finset_1(k3_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_18,plain,
    ( ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1('#skF_2')
    | ~ v1_finset_1(k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_212,plain,
    ( ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_18])).

tff(c_213,plain,(
    ~ v1_finset_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_206,plain,(
    v1_finset_1(k3_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_215,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_226,plain,(
    ! [A_49] : k3_xboole_0(A_49,k1_zfmisc_1(k3_tarski(A_49))) = A_49 ),
    inference(resolution,[status(thm)],[c_6,c_215])).

tff(c_238,plain,(
    ! [A_50] :
      ( v1_finset_1(A_50)
      | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(A_50))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_8])).

tff(c_243,plain,(
    ! [A_51] :
      ( v1_finset_1(A_51)
      | ~ v1_finset_1(k3_tarski(A_51)) ) ),
    inference(resolution,[status(thm)],[c_10,c_238])).

tff(c_249,plain,(
    v1_finset_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_206,c_243])).

tff(c_255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_249])).

tff(c_256,plain,(
    ~ v1_finset_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_257,plain,(
    v1_finset_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_20,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | ~ v1_finset_1('#skF_2')
    | ~ v1_finset_1(k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_286,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_257,c_20])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,k3_tarski(B_4))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_259,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_306,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(A_58,k3_tarski(B_59)) = A_58
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_4,c_259])).

tff(c_318,plain,(
    ! [A_60,B_61] :
      ( v1_finset_1(A_60)
      | ~ v1_finset_1(k3_tarski(B_61))
      | ~ r2_hidden(A_60,B_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_8])).

tff(c_329,plain,(
    ! [A_63] :
      ( v1_finset_1(A_63)
      | ~ r2_hidden(A_63,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_206,c_318])).

tff(c_332,plain,(
    v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_286,c_329])).

tff(c_336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_256,c_332])).

tff(c_338,plain,(
    ~ v1_finset_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_30,plain,
    ( ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1('#skF_2')
    | v1_finset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_341,plain,
    ( ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_338,c_30])).

tff(c_342,plain,(
    ~ v1_finset_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_341])).

tff(c_337,plain,(
    v1_finset_1(k3_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_345,plain,(
    ! [A_68,B_69] :
      ( k3_xboole_0(A_68,B_69) = A_68
      | ~ r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_350,plain,(
    ! [A_70] : k3_xboole_0(A_70,k1_zfmisc_1(k3_tarski(A_70))) = A_70 ),
    inference(resolution,[status(thm)],[c_6,c_345])).

tff(c_362,plain,(
    ! [A_71] :
      ( v1_finset_1(A_71)
      | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(A_71))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_8])).

tff(c_367,plain,(
    ! [A_72] :
      ( v1_finset_1(A_72)
      | ~ v1_finset_1(k3_tarski(A_72)) ) ),
    inference(resolution,[status(thm)],[c_10,c_362])).

tff(c_370,plain,(
    v1_finset_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_337,c_367])).

tff(c_374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_370])).

tff(c_375,plain,(
    ~ v1_finset_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_376,plain,(
    v1_finset_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_32,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | ~ v1_finset_1('#skF_2')
    | v1_finset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_410,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | v1_finset_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_32])).

tff(c_411,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_338,c_410])).

tff(c_412,plain,(
    ! [A_80,B_81] :
      ( r1_tarski(A_80,k3_tarski(B_81))
      | ~ r2_hidden(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_425,plain,(
    ! [A_83,B_84] :
      ( k3_xboole_0(A_83,k3_tarski(B_84)) = A_83
      | ~ r2_hidden(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_412,c_2])).

tff(c_437,plain,(
    ! [A_85,B_86] :
      ( v1_finset_1(A_85)
      | ~ v1_finset_1(k3_tarski(B_86))
      | ~ r2_hidden(A_85,B_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_8])).

tff(c_444,plain,(
    ! [A_87] :
      ( v1_finset_1(A_87)
      | ~ r2_hidden(A_87,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_337,c_437])).

tff(c_447,plain,(
    v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_411,c_444])).

tff(c_451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_375,c_447])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:03:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.33  
% 2.28/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.33  %$ r2_hidden > r1_tarski > v1_finset_1 > k3_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.28/1.33  
% 2.28/1.33  %Foreground sorts:
% 2.28/1.33  
% 2.28/1.33  
% 2.28/1.33  %Background operators:
% 2.28/1.33  
% 2.28/1.33  
% 2.28/1.33  %Foreground operators:
% 2.28/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.28/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.28/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.28/1.33  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 2.28/1.33  
% 2.28/1.35  tff(f_62, negated_conjecture, ~(![A]: ((v1_finset_1(A) & (![B]: (r2_hidden(B, A) => v1_finset_1(B)))) <=> v1_finset_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_finset_1)).
% 2.28/1.35  tff(f_52, axiom, (![A]: ((v1_finset_1(A) & (![B]: (r2_hidden(B, A) => v1_finset_1(B)))) => v1_finset_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_finset_1)).
% 2.28/1.35  tff(f_43, axiom, (![A]: (v1_finset_1(A) => v1_finset_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc17_finset_1)).
% 2.28/1.35  tff(f_35, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 2.28/1.35  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.28/1.35  tff(f_39, axiom, (![A, B]: (v1_finset_1(B) => v1_finset_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_finset_1)).
% 2.28/1.35  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.28/1.35  tff(c_16, plain, (v1_finset_1(k3_tarski('#skF_2')) | ~v1_finset_1(k3_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.28/1.35  tff(c_36, plain, (~v1_finset_1(k3_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_16])).
% 2.28/1.35  tff(c_28, plain, (v1_finset_1(k3_tarski('#skF_2')) | v1_finset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.28/1.35  tff(c_33, plain, (v1_finset_1('#skF_4')), inference(splitLeft, [status(thm)], [c_28])).
% 2.28/1.35  tff(c_164, plain, (![A_37]: (~v1_finset_1('#skF_1'(A_37)) | v1_finset_1(k3_tarski(A_37)) | ~v1_finset_1(A_37))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.28/1.35  tff(c_173, plain, (~v1_finset_1('#skF_1'('#skF_4')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_164, c_36])).
% 2.28/1.35  tff(c_178, plain, (~v1_finset_1('#skF_1'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_173])).
% 2.28/1.35  tff(c_196, plain, (![A_42]: (r2_hidden('#skF_1'(A_42), A_42) | v1_finset_1(k3_tarski(A_42)) | ~v1_finset_1(A_42))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.28/1.35  tff(c_140, plain, (![A_34]: (~v1_finset_1('#skF_1'(A_34)) | v1_finset_1(k3_tarski(A_34)) | ~v1_finset_1(A_34))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.28/1.35  tff(c_146, plain, (~v1_finset_1('#skF_1'('#skF_4')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_140, c_36])).
% 2.28/1.35  tff(c_150, plain, (~v1_finset_1('#skF_1'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_146])).
% 2.28/1.35  tff(c_151, plain, (![A_35]: (r2_hidden('#skF_1'(A_35), A_35) | v1_finset_1(k3_tarski(A_35)) | ~v1_finset_1(A_35))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.28/1.35  tff(c_76, plain, (![A_25]: (~v1_finset_1('#skF_1'(A_25)) | v1_finset_1(k3_tarski(A_25)) | ~v1_finset_1(A_25))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.28/1.35  tff(c_82, plain, (~v1_finset_1('#skF_1'('#skF_4')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_36])).
% 2.28/1.35  tff(c_86, plain, (~v1_finset_1('#skF_1'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_82])).
% 2.28/1.35  tff(c_14, plain, (![A_9]: (r2_hidden('#skF_1'(A_9), A_9) | v1_finset_1(k3_tarski(A_9)) | ~v1_finset_1(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.28/1.35  tff(c_22, plain, (![B_13]: (v1_finset_1(k3_tarski('#skF_2')) | v1_finset_1(B_13) | ~r2_hidden(B_13, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.28/1.35  tff(c_68, plain, (v1_finset_1(k3_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_22])).
% 2.28/1.35  tff(c_10, plain, (![A_8]: (v1_finset_1(k1_zfmisc_1(A_8)) | ~v1_finset_1(A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.28/1.35  tff(c_6, plain, (![A_5]: (r1_tarski(A_5, k1_zfmisc_1(k3_tarski(A_5))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.28/1.35  tff(c_39, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.28/1.35  tff(c_44, plain, (![A_20]: (k3_xboole_0(A_20, k1_zfmisc_1(k3_tarski(A_20)))=A_20)), inference(resolution, [status(thm)], [c_6, c_39])).
% 2.28/1.35  tff(c_8, plain, (![A_6, B_7]: (v1_finset_1(k3_xboole_0(A_6, B_7)) | ~v1_finset_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.28/1.35  tff(c_56, plain, (![A_21]: (v1_finset_1(A_21) | ~v1_finset_1(k1_zfmisc_1(k3_tarski(A_21))))), inference(superposition, [status(thm), theory('equality')], [c_44, c_8])).
% 2.28/1.35  tff(c_60, plain, (![A_21]: (v1_finset_1(A_21) | ~v1_finset_1(k3_tarski(A_21)))), inference(resolution, [status(thm)], [c_10, c_56])).
% 2.28/1.35  tff(c_72, plain, (v1_finset_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_60])).
% 2.28/1.35  tff(c_24, plain, (![B_13]: (~v1_finset_1('#skF_3') | ~v1_finset_1('#skF_2') | v1_finset_1(B_13) | ~r2_hidden(B_13, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.28/1.35  tff(c_74, plain, (![B_13]: (~v1_finset_1('#skF_3') | v1_finset_1(B_13) | ~r2_hidden(B_13, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_24])).
% 2.28/1.35  tff(c_75, plain, (~v1_finset_1('#skF_3')), inference(splitLeft, [status(thm)], [c_74])).
% 2.28/1.35  tff(c_26, plain, (![B_13]: (r2_hidden('#skF_3', '#skF_2') | ~v1_finset_1('#skF_2') | v1_finset_1(B_13) | ~r2_hidden(B_13, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.28/1.35  tff(c_116, plain, (![B_13]: (r2_hidden('#skF_3', '#skF_2') | v1_finset_1(B_13) | ~r2_hidden(B_13, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_26])).
% 2.28/1.35  tff(c_117, plain, (r2_hidden('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_116])).
% 2.28/1.35  tff(c_63, plain, (![A_23, B_24]: (r1_tarski(A_23, k3_tarski(B_24)) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.28/1.35  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.28/1.35  tff(c_87, plain, (![A_26, B_27]: (k3_xboole_0(A_26, k3_tarski(B_27))=A_26 | ~r2_hidden(A_26, B_27))), inference(resolution, [status(thm)], [c_63, c_2])).
% 2.28/1.35  tff(c_99, plain, (![A_28, B_29]: (v1_finset_1(A_28) | ~v1_finset_1(k3_tarski(B_29)) | ~r2_hidden(A_28, B_29))), inference(superposition, [status(thm), theory('equality')], [c_87, c_8])).
% 2.28/1.35  tff(c_105, plain, (![A_28]: (v1_finset_1(A_28) | ~r2_hidden(A_28, '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_99])).
% 2.28/1.35  tff(c_120, plain, (v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_117, c_105])).
% 2.28/1.35  tff(c_124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_120])).
% 2.28/1.35  tff(c_127, plain, (![B_32]: (v1_finset_1(B_32) | ~r2_hidden(B_32, '#skF_4'))), inference(splitRight, [status(thm)], [c_116])).
% 2.28/1.35  tff(c_131, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_127])).
% 2.28/1.35  tff(c_134, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_131])).
% 2.28/1.35  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_86, c_134])).
% 2.28/1.35  tff(c_137, plain, (![B_13]: (v1_finset_1(B_13) | ~r2_hidden(B_13, '#skF_4'))), inference(splitRight, [status(thm)], [c_74])).
% 2.28/1.35  tff(c_155, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_151, c_137])).
% 2.28/1.35  tff(c_158, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_155])).
% 2.28/1.35  tff(c_160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_150, c_158])).
% 2.28/1.35  tff(c_161, plain, (![B_13]: (v1_finset_1(B_13) | ~r2_hidden(B_13, '#skF_4'))), inference(splitRight, [status(thm)], [c_22])).
% 2.28/1.35  tff(c_200, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_196, c_161])).
% 2.28/1.35  tff(c_203, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_200])).
% 2.28/1.35  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_178, c_203])).
% 2.28/1.35  tff(c_207, plain, (v1_finset_1(k3_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_16])).
% 2.28/1.35  tff(c_18, plain, (~v1_finset_1('#skF_3') | ~v1_finset_1('#skF_2') | ~v1_finset_1(k3_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.28/1.35  tff(c_212, plain, (~v1_finset_1('#skF_3') | ~v1_finset_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_18])).
% 2.28/1.35  tff(c_213, plain, (~v1_finset_1('#skF_2')), inference(splitLeft, [status(thm)], [c_212])).
% 2.28/1.35  tff(c_206, plain, (v1_finset_1(k3_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_16])).
% 2.28/1.35  tff(c_215, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.28/1.35  tff(c_226, plain, (![A_49]: (k3_xboole_0(A_49, k1_zfmisc_1(k3_tarski(A_49)))=A_49)), inference(resolution, [status(thm)], [c_6, c_215])).
% 2.28/1.35  tff(c_238, plain, (![A_50]: (v1_finset_1(A_50) | ~v1_finset_1(k1_zfmisc_1(k3_tarski(A_50))))), inference(superposition, [status(thm), theory('equality')], [c_226, c_8])).
% 2.28/1.35  tff(c_243, plain, (![A_51]: (v1_finset_1(A_51) | ~v1_finset_1(k3_tarski(A_51)))), inference(resolution, [status(thm)], [c_10, c_238])).
% 2.28/1.35  tff(c_249, plain, (v1_finset_1('#skF_2')), inference(resolution, [status(thm)], [c_206, c_243])).
% 2.28/1.35  tff(c_255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_213, c_249])).
% 2.28/1.35  tff(c_256, plain, (~v1_finset_1('#skF_3')), inference(splitRight, [status(thm)], [c_212])).
% 2.28/1.35  tff(c_257, plain, (v1_finset_1('#skF_2')), inference(splitRight, [status(thm)], [c_212])).
% 2.28/1.35  tff(c_20, plain, (r2_hidden('#skF_3', '#skF_2') | ~v1_finset_1('#skF_2') | ~v1_finset_1(k3_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.28/1.35  tff(c_286, plain, (r2_hidden('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_257, c_20])).
% 2.28/1.35  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k3_tarski(B_4)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.28/1.35  tff(c_259, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.28/1.35  tff(c_306, plain, (![A_58, B_59]: (k3_xboole_0(A_58, k3_tarski(B_59))=A_58 | ~r2_hidden(A_58, B_59))), inference(resolution, [status(thm)], [c_4, c_259])).
% 2.28/1.35  tff(c_318, plain, (![A_60, B_61]: (v1_finset_1(A_60) | ~v1_finset_1(k3_tarski(B_61)) | ~r2_hidden(A_60, B_61))), inference(superposition, [status(thm), theory('equality')], [c_306, c_8])).
% 2.28/1.35  tff(c_329, plain, (![A_63]: (v1_finset_1(A_63) | ~r2_hidden(A_63, '#skF_2'))), inference(resolution, [status(thm)], [c_206, c_318])).
% 2.28/1.35  tff(c_332, plain, (v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_286, c_329])).
% 2.28/1.35  tff(c_336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_256, c_332])).
% 2.28/1.35  tff(c_338, plain, (~v1_finset_1('#skF_4')), inference(splitRight, [status(thm)], [c_28])).
% 2.28/1.35  tff(c_30, plain, (~v1_finset_1('#skF_3') | ~v1_finset_1('#skF_2') | v1_finset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.28/1.35  tff(c_341, plain, (~v1_finset_1('#skF_3') | ~v1_finset_1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_338, c_30])).
% 2.28/1.35  tff(c_342, plain, (~v1_finset_1('#skF_2')), inference(splitLeft, [status(thm)], [c_341])).
% 2.28/1.35  tff(c_337, plain, (v1_finset_1(k3_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_28])).
% 2.28/1.35  tff(c_345, plain, (![A_68, B_69]: (k3_xboole_0(A_68, B_69)=A_68 | ~r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.28/1.35  tff(c_350, plain, (![A_70]: (k3_xboole_0(A_70, k1_zfmisc_1(k3_tarski(A_70)))=A_70)), inference(resolution, [status(thm)], [c_6, c_345])).
% 2.28/1.35  tff(c_362, plain, (![A_71]: (v1_finset_1(A_71) | ~v1_finset_1(k1_zfmisc_1(k3_tarski(A_71))))), inference(superposition, [status(thm), theory('equality')], [c_350, c_8])).
% 2.28/1.35  tff(c_367, plain, (![A_72]: (v1_finset_1(A_72) | ~v1_finset_1(k3_tarski(A_72)))), inference(resolution, [status(thm)], [c_10, c_362])).
% 2.28/1.35  tff(c_370, plain, (v1_finset_1('#skF_2')), inference(resolution, [status(thm)], [c_337, c_367])).
% 2.28/1.35  tff(c_374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_342, c_370])).
% 2.28/1.35  tff(c_375, plain, (~v1_finset_1('#skF_3')), inference(splitRight, [status(thm)], [c_341])).
% 2.28/1.35  tff(c_376, plain, (v1_finset_1('#skF_2')), inference(splitRight, [status(thm)], [c_341])).
% 2.28/1.35  tff(c_32, plain, (r2_hidden('#skF_3', '#skF_2') | ~v1_finset_1('#skF_2') | v1_finset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.28/1.35  tff(c_410, plain, (r2_hidden('#skF_3', '#skF_2') | v1_finset_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_376, c_32])).
% 2.28/1.35  tff(c_411, plain, (r2_hidden('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_338, c_410])).
% 2.28/1.35  tff(c_412, plain, (![A_80, B_81]: (r1_tarski(A_80, k3_tarski(B_81)) | ~r2_hidden(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.28/1.35  tff(c_425, plain, (![A_83, B_84]: (k3_xboole_0(A_83, k3_tarski(B_84))=A_83 | ~r2_hidden(A_83, B_84))), inference(resolution, [status(thm)], [c_412, c_2])).
% 2.28/1.35  tff(c_437, plain, (![A_85, B_86]: (v1_finset_1(A_85) | ~v1_finset_1(k3_tarski(B_86)) | ~r2_hidden(A_85, B_86))), inference(superposition, [status(thm), theory('equality')], [c_425, c_8])).
% 2.28/1.35  tff(c_444, plain, (![A_87]: (v1_finset_1(A_87) | ~r2_hidden(A_87, '#skF_2'))), inference(resolution, [status(thm)], [c_337, c_437])).
% 2.28/1.35  tff(c_447, plain, (v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_411, c_444])).
% 2.28/1.35  tff(c_451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_375, c_447])).
% 2.28/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.35  
% 2.28/1.35  Inference rules
% 2.28/1.35  ----------------------
% 2.28/1.35  #Ref     : 0
% 2.28/1.35  #Sup     : 72
% 2.28/1.35  #Fact    : 0
% 2.28/1.35  #Define  : 0
% 2.28/1.35  #Split   : 8
% 2.28/1.35  #Chain   : 0
% 2.28/1.35  #Close   : 0
% 2.28/1.35  
% 2.28/1.35  Ordering : KBO
% 2.28/1.35  
% 2.28/1.35  Simplification rules
% 2.28/1.35  ----------------------
% 2.28/1.35  #Subsume      : 8
% 2.28/1.35  #Demod        : 32
% 2.28/1.35  #Tautology    : 37
% 2.28/1.35  #SimpNegUnit  : 10
% 2.28/1.35  #BackRed      : 0
% 2.28/1.35  
% 2.28/1.35  #Partial instantiations: 0
% 2.28/1.35  #Strategies tried      : 1
% 2.28/1.35  
% 2.28/1.35  Timing (in seconds)
% 2.28/1.35  ----------------------
% 2.28/1.35  Preprocessing        : 0.30
% 2.28/1.35  Parsing              : 0.16
% 2.28/1.35  CNF conversion       : 0.02
% 2.28/1.35  Main loop            : 0.23
% 2.28/1.35  Inferencing          : 0.10
% 2.28/1.35  Reduction            : 0.06
% 2.28/1.35  Demodulation         : 0.04
% 2.28/1.35  BG Simplification    : 0.01
% 2.28/1.35  Subsumption          : 0.04
% 2.28/1.35  Abstraction          : 0.01
% 2.28/1.35  MUC search           : 0.00
% 2.28/1.35  Cooper               : 0.00
% 2.28/1.35  Total                : 0.57
% 2.28/1.36  Index Insertion      : 0.00
% 2.28/1.36  Index Deletion       : 0.00
% 2.28/1.36  Index Matching       : 0.00
% 2.28/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
