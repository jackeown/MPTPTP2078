%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:27 EST 2020

% Result     : Theorem 8.93s
% Output     : CNFRefutation 9.35s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 427 expanded)
%              Number of leaves         :   38 ( 157 expanded)
%              Depth                    :   16
%              Number of atoms          :  187 ( 879 expanded)
%              Number of equality atoms :   53 ( 191 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k1_relset_1(B,A,k3_relset_1(A,B,C)) = k2_relset_1(A,B,C)
        & k2_relset_1(B,A,k3_relset_1(A,B,C)) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_69,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_8849,plain,(
    ! [A_398,B_399,C_400] :
      ( k2_relset_1(A_398,B_399,C_400) = k2_relat_1(C_400)
      | ~ m1_subset_1(C_400,k1_zfmisc_1(k2_zfmisc_1(A_398,B_399))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_8858,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_8849])).

tff(c_44,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_8859,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8858,c_44])).

tff(c_9178,plain,(
    ! [B_430,A_431,C_432] :
      ( k1_relset_1(B_430,A_431,k3_relset_1(A_431,B_430,C_432)) = k2_relset_1(A_431,B_430,C_432)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(k2_zfmisc_1(A_431,B_430))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_9188,plain,(
    k1_relset_1('#skF_2','#skF_3',k3_relset_1('#skF_3','#skF_2','#skF_4')) = k2_relset_1('#skF_3','#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_9178])).

tff(c_9193,plain,(
    k1_relset_1('#skF_2','#skF_3',k3_relset_1('#skF_3','#skF_2','#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8858,c_9188])).

tff(c_8917,plain,(
    ! [A_409,B_410,C_411] :
      ( m1_subset_1(k3_relset_1(A_409,B_410,C_411),k1_zfmisc_1(k2_zfmisc_1(B_410,A_409)))
      | ~ m1_subset_1(C_411,k1_zfmisc_1(k2_zfmisc_1(A_409,B_410))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    ! [A_27,B_28,C_29] :
      ( k1_relset_1(A_27,B_28,C_29) = k1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14253,plain,(
    ! [B_540,A_541,C_542] :
      ( k1_relset_1(B_540,A_541,k3_relset_1(A_541,B_540,C_542)) = k1_relat_1(k3_relset_1(A_541,B_540,C_542))
      | ~ m1_subset_1(C_542,k1_zfmisc_1(k2_zfmisc_1(A_541,B_540))) ) ),
    inference(resolution,[status(thm)],[c_8917,c_34])).

tff(c_14263,plain,(
    k1_relset_1('#skF_2','#skF_3',k3_relset_1('#skF_3','#skF_2','#skF_4')) = k1_relat_1(k3_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_14253])).

tff(c_14268,plain,(
    k1_relat_1(k3_relset_1('#skF_3','#skF_2','#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9193,c_14263])).

tff(c_22,plain,(
    ! [A_17] :
      ( v1_xboole_0(k1_relat_1(A_17))
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14344,plain,
    ( v1_xboole_0(k2_relat_1('#skF_4'))
    | ~ v1_xboole_0(k3_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14268,c_22])).

tff(c_14356,plain,(
    ~ v1_xboole_0(k3_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_14344])).

tff(c_24,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16,plain,(
    ! [B_14,A_12] :
      ( v1_relat_1(B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_12))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8934,plain,(
    ! [A_409,B_410,C_411] :
      ( v1_relat_1(k3_relset_1(A_409,B_410,C_411))
      | ~ v1_relat_1(k2_zfmisc_1(B_410,A_409))
      | ~ m1_subset_1(C_411,k1_zfmisc_1(k2_zfmisc_1(A_409,B_410))) ) ),
    inference(resolution,[status(thm)],[c_8917,c_16])).

tff(c_9198,plain,(
    ! [A_433,B_434,C_435] :
      ( v1_relat_1(k3_relset_1(A_433,B_434,C_435))
      | ~ m1_subset_1(C_435,k1_zfmisc_1(k2_zfmisc_1(A_433,B_434))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_8934])).

tff(c_9216,plain,(
    v1_relat_1(k3_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_9198])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4871,plain,(
    ! [A_242,B_243,C_244] :
      ( k2_relset_1(A_242,B_243,C_244) = k2_relat_1(C_244)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4885,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_4871])).

tff(c_4920,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4885,c_44])).

tff(c_65,plain,(
    ! [B_55,A_56] :
      ( ~ v1_xboole_0(B_55)
      | B_55 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_72,plain,(
    ! [A_57] :
      ( k1_xboole_0 = A_57
      | ~ v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_6,c_65])).

tff(c_82,plain,(
    ! [A_58] :
      ( k1_relat_1(A_58) = k1_xboole_0
      | ~ v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_22,c_72])).

tff(c_90,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_4943,plain,(
    ! [A_246,B_247,C_248] :
      ( m1_subset_1(k3_relset_1(A_246,B_247,C_248),k1_zfmisc_1(k2_zfmisc_1(B_247,A_246)))
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4960,plain,(
    ! [A_246,B_247,C_248] :
      ( v1_relat_1(k3_relset_1(A_246,B_247,C_248))
      | ~ v1_relat_1(k2_zfmisc_1(B_247,A_246))
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247))) ) ),
    inference(resolution,[status(thm)],[c_4943,c_16])).

tff(c_5165,plain,(
    ! [A_263,B_264,C_265] :
      ( v1_relat_1(k3_relset_1(A_263,B_264,C_265))
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(A_263,B_264))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4960])).

tff(c_5183,plain,(
    v1_relat_1(k3_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_5165])).

tff(c_145,plain,(
    ! [B_67,A_68] :
      ( v1_relat_1(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68))
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_151,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_145])).

tff(c_155,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_151])).

tff(c_163,plain,(
    ! [C_71,A_72,B_73] :
      ( v4_relat_1(C_71,A_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_172,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_163])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4773,plain,(
    ! [A_229,C_230,B_231] :
      ( m1_subset_1(A_229,C_230)
      | ~ m1_subset_1(B_231,k1_zfmisc_1(C_230))
      | ~ r2_hidden(A_229,B_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4803,plain,(
    ! [A_237,B_238,A_239] :
      ( m1_subset_1(A_237,B_238)
      | ~ r2_hidden(A_237,A_239)
      | ~ r1_tarski(A_239,B_238) ) ),
    inference(resolution,[status(thm)],[c_12,c_4773])).

tff(c_4807,plain,(
    ! [A_240,B_241] :
      ( m1_subset_1('#skF_1'(A_240),B_241)
      | ~ r1_tarski(A_240,B_241)
      | v1_xboole_0(A_240) ) ),
    inference(resolution,[status(thm)],[c_4,c_4803])).

tff(c_4780,plain,(
    ! [A_232,B_233,C_234] :
      ( k1_relset_1(A_232,B_233,C_234) = k1_relat_1(C_234)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4789,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_4780])).

tff(c_59,plain,(
    ! [D_54] :
      ( ~ r2_hidden(D_54,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_54,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_64,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3')
    | v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_59])).

tff(c_137,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_4790,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4789,c_137])).

tff(c_4834,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4807,c_4790])).

tff(c_4841,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4834])).

tff(c_4844,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_4841])).

tff(c_4848,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_172,c_4844])).

tff(c_4849,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4834])).

tff(c_71,plain,(
    ! [A_56] :
      ( k1_xboole_0 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_65])).

tff(c_4869,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4849,c_71])).

tff(c_4889,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4869,c_4789])).

tff(c_5184,plain,(
    ! [B_266,A_267,C_268] :
      ( k2_relset_1(B_266,A_267,k3_relset_1(A_267,B_266,C_268)) = k1_relset_1(A_267,B_266,C_268)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_267,B_266))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5194,plain,(
    k2_relset_1('#skF_2','#skF_3',k3_relset_1('#skF_3','#skF_2','#skF_4')) = k1_relset_1('#skF_3','#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_5184])).

tff(c_5199,plain,(
    k2_relset_1('#skF_2','#skF_3',k3_relset_1('#skF_3','#skF_2','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4889,c_5194])).

tff(c_36,plain,(
    ! [A_30,B_31,C_32] :
      ( k2_relset_1(A_30,B_31,C_32) = k2_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_8516,plain,(
    ! [B_361,A_362,C_363] :
      ( k2_relset_1(B_361,A_362,k3_relset_1(A_362,B_361,C_363)) = k2_relat_1(k3_relset_1(A_362,B_361,C_363))
      | ~ m1_subset_1(C_363,k1_zfmisc_1(k2_zfmisc_1(A_362,B_361))) ) ),
    inference(resolution,[status(thm)],[c_4943,c_36])).

tff(c_8526,plain,(
    k2_relset_1('#skF_2','#skF_3',k3_relset_1('#skF_3','#skF_2','#skF_4')) = k2_relat_1(k3_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_8516])).

tff(c_8531,plain,(
    k2_relat_1(k3_relset_1('#skF_3','#skF_2','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5199,c_8526])).

tff(c_26,plain,(
    ! [A_20] :
      ( ~ v1_xboole_0(k2_relat_1(A_20))
      | ~ v1_relat_1(A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8535,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k3_relset_1('#skF_3','#skF_2','#skF_4'))
    | v1_xboole_0(k3_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8531,c_26])).

tff(c_8539,plain,(
    v1_xboole_0(k3_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5183,c_6,c_8535])).

tff(c_8577,plain,(
    k3_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8539,c_71])).

tff(c_8641,plain,(
    ! [B_364,A_365,C_366] :
      ( k1_relset_1(B_364,A_365,k3_relset_1(A_365,B_364,C_366)) = k1_relat_1(k3_relset_1(A_365,B_364,C_366))
      | ~ m1_subset_1(C_366,k1_zfmisc_1(k2_zfmisc_1(A_365,B_364))) ) ),
    inference(resolution,[status(thm)],[c_4943,c_34])).

tff(c_8651,plain,(
    k1_relset_1('#skF_2','#skF_3',k3_relset_1('#skF_3','#skF_2','#skF_4')) = k1_relat_1(k3_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_8641])).

tff(c_8656,plain,(
    k1_relset_1('#skF_2','#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_8577,c_8577,c_8651])).

tff(c_5145,plain,(
    ! [B_260,A_261,C_262] :
      ( k1_relset_1(B_260,A_261,k3_relset_1(A_261,B_260,C_262)) = k2_relset_1(A_261,B_260,C_262)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_261,B_260))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5155,plain,(
    k1_relset_1('#skF_2','#skF_3',k3_relset_1('#skF_3','#skF_2','#skF_4')) = k2_relset_1('#skF_3','#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_5145])).

tff(c_5160,plain,(
    k1_relset_1('#skF_2','#skF_3',k3_relset_1('#skF_3','#skF_2','#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4885,c_5155])).

tff(c_8585,plain,(
    k1_relset_1('#skF_2','#skF_3',k1_xboole_0) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8577,c_5160])).

tff(c_8703,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8656,c_8585])).

tff(c_8704,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4920,c_8703])).

tff(c_8705,plain,(
    v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_8716,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8705,c_71])).

tff(c_9000,plain,(
    ! [B_417,A_418,C_419] :
      ( k2_relset_1(B_417,A_418,k3_relset_1(A_418,B_417,C_419)) = k1_relset_1(A_418,B_417,C_419)
      | ~ m1_subset_1(C_419,k1_zfmisc_1(k2_zfmisc_1(A_418,B_417))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_9010,plain,(
    k2_relset_1('#skF_2','#skF_3',k3_relset_1('#skF_3','#skF_2','#skF_4')) = k1_relset_1('#skF_3','#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_9000])).

tff(c_9015,plain,(
    k2_relset_1('#skF_2','#skF_3',k3_relset_1('#skF_3','#skF_2','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8716,c_9010])).

tff(c_14396,plain,(
    ! [B_545,A_546,C_547] :
      ( k2_relset_1(B_545,A_546,k3_relset_1(A_546,B_545,C_547)) = k2_relat_1(k3_relset_1(A_546,B_545,C_547))
      | ~ m1_subset_1(C_547,k1_zfmisc_1(k2_zfmisc_1(A_546,B_545))) ) ),
    inference(resolution,[status(thm)],[c_8917,c_36])).

tff(c_14406,plain,(
    k2_relset_1('#skF_2','#skF_3',k3_relset_1('#skF_3','#skF_2','#skF_4')) = k2_relat_1(k3_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_14396])).

tff(c_14411,plain,(
    k2_relat_1(k3_relset_1('#skF_3','#skF_2','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9015,c_14406])).

tff(c_14415,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k3_relset_1('#skF_3','#skF_2','#skF_4'))
    | v1_xboole_0(k3_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14411,c_26])).

tff(c_14419,plain,(
    v1_xboole_0(k3_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9216,c_6,c_14415])).

tff(c_14421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14356,c_14419])).

tff(c_14422,plain,(
    v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_14344])).

tff(c_14454,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14422,c_71])).

tff(c_14475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8859,c_14454])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:26:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.93/2.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.93/2.98  
% 8.93/2.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.93/2.99  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 8.93/2.99  
% 8.93/2.99  %Foreground sorts:
% 8.93/2.99  
% 8.93/2.99  
% 8.93/2.99  %Background operators:
% 8.93/2.99  
% 8.93/2.99  
% 8.93/2.99  %Foreground operators:
% 8.93/2.99  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.93/2.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.93/2.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.93/2.99  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.93/2.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.93/2.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.93/2.99  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 8.93/2.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.93/2.99  tff('#skF_2', type, '#skF_2': $i).
% 8.93/2.99  tff('#skF_3', type, '#skF_3': $i).
% 8.93/2.99  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.93/2.99  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.93/2.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.93/2.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.93/2.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.93/2.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.93/2.99  tff('#skF_4', type, '#skF_4': $i).
% 8.93/2.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.93/2.99  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.93/2.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.93/2.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.93/2.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.93/2.99  
% 9.35/3.01  tff(f_122, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 9.35/3.01  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.35/3.01  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k1_relset_1(B, A, k3_relset_1(A, B, C)) = k2_relset_1(A, B, C)) & (k2_relset_1(B, A, k3_relset_1(A, B, C)) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_relset_1)).
% 9.35/3.01  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 9.35/3.01  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.35/3.01  tff(f_67, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 9.35/3.01  tff(f_69, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.35/3.01  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.35/3.01  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.35/3.01  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 9.35/3.01  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.35/3.01  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 9.35/3.01  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.35/3.01  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.35/3.01  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 9.35/3.01  tff(f_77, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 9.35/3.01  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.35/3.01  tff(c_8849, plain, (![A_398, B_399, C_400]: (k2_relset_1(A_398, B_399, C_400)=k2_relat_1(C_400) | ~m1_subset_1(C_400, k1_zfmisc_1(k2_zfmisc_1(A_398, B_399))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.35/3.01  tff(c_8858, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_8849])).
% 9.35/3.01  tff(c_44, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.35/3.01  tff(c_8859, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8858, c_44])).
% 9.35/3.01  tff(c_9178, plain, (![B_430, A_431, C_432]: (k1_relset_1(B_430, A_431, k3_relset_1(A_431, B_430, C_432))=k2_relset_1(A_431, B_430, C_432) | ~m1_subset_1(C_432, k1_zfmisc_1(k2_zfmisc_1(A_431, B_430))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.35/3.01  tff(c_9188, plain, (k1_relset_1('#skF_2', '#skF_3', k3_relset_1('#skF_3', '#skF_2', '#skF_4'))=k2_relset_1('#skF_3', '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_9178])).
% 9.35/3.01  tff(c_9193, plain, (k1_relset_1('#skF_2', '#skF_3', k3_relset_1('#skF_3', '#skF_2', '#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8858, c_9188])).
% 9.35/3.01  tff(c_8917, plain, (![A_409, B_410, C_411]: (m1_subset_1(k3_relset_1(A_409, B_410, C_411), k1_zfmisc_1(k2_zfmisc_1(B_410, A_409))) | ~m1_subset_1(C_411, k1_zfmisc_1(k2_zfmisc_1(A_409, B_410))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.35/3.01  tff(c_34, plain, (![A_27, B_28, C_29]: (k1_relset_1(A_27, B_28, C_29)=k1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.35/3.01  tff(c_14253, plain, (![B_540, A_541, C_542]: (k1_relset_1(B_540, A_541, k3_relset_1(A_541, B_540, C_542))=k1_relat_1(k3_relset_1(A_541, B_540, C_542)) | ~m1_subset_1(C_542, k1_zfmisc_1(k2_zfmisc_1(A_541, B_540))))), inference(resolution, [status(thm)], [c_8917, c_34])).
% 9.35/3.01  tff(c_14263, plain, (k1_relset_1('#skF_2', '#skF_3', k3_relset_1('#skF_3', '#skF_2', '#skF_4'))=k1_relat_1(k3_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_14253])).
% 9.35/3.01  tff(c_14268, plain, (k1_relat_1(k3_relset_1('#skF_3', '#skF_2', '#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9193, c_14263])).
% 9.35/3.01  tff(c_22, plain, (![A_17]: (v1_xboole_0(k1_relat_1(A_17)) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.35/3.01  tff(c_14344, plain, (v1_xboole_0(k2_relat_1('#skF_4')) | ~v1_xboole_0(k3_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14268, c_22])).
% 9.35/3.01  tff(c_14356, plain, (~v1_xboole_0(k3_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_14344])).
% 9.35/3.01  tff(c_24, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.35/3.01  tff(c_16, plain, (![B_14, A_12]: (v1_relat_1(B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(A_12)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.35/3.01  tff(c_8934, plain, (![A_409, B_410, C_411]: (v1_relat_1(k3_relset_1(A_409, B_410, C_411)) | ~v1_relat_1(k2_zfmisc_1(B_410, A_409)) | ~m1_subset_1(C_411, k1_zfmisc_1(k2_zfmisc_1(A_409, B_410))))), inference(resolution, [status(thm)], [c_8917, c_16])).
% 9.35/3.01  tff(c_9198, plain, (![A_433, B_434, C_435]: (v1_relat_1(k3_relset_1(A_433, B_434, C_435)) | ~m1_subset_1(C_435, k1_zfmisc_1(k2_zfmisc_1(A_433, B_434))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_8934])).
% 9.35/3.01  tff(c_9216, plain, (v1_relat_1(k3_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_9198])).
% 9.35/3.01  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.35/3.01  tff(c_4871, plain, (![A_242, B_243, C_244]: (k2_relset_1(A_242, B_243, C_244)=k2_relat_1(C_244) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.35/3.01  tff(c_4885, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_4871])).
% 9.35/3.01  tff(c_4920, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4885, c_44])).
% 9.35/3.01  tff(c_65, plain, (![B_55, A_56]: (~v1_xboole_0(B_55) | B_55=A_56 | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.35/3.01  tff(c_72, plain, (![A_57]: (k1_xboole_0=A_57 | ~v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_6, c_65])).
% 9.35/3.01  tff(c_82, plain, (![A_58]: (k1_relat_1(A_58)=k1_xboole_0 | ~v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_22, c_72])).
% 9.35/3.01  tff(c_90, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_82])).
% 9.35/3.01  tff(c_4943, plain, (![A_246, B_247, C_248]: (m1_subset_1(k3_relset_1(A_246, B_247, C_248), k1_zfmisc_1(k2_zfmisc_1(B_247, A_246))) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.35/3.01  tff(c_4960, plain, (![A_246, B_247, C_248]: (v1_relat_1(k3_relset_1(A_246, B_247, C_248)) | ~v1_relat_1(k2_zfmisc_1(B_247, A_246)) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))))), inference(resolution, [status(thm)], [c_4943, c_16])).
% 9.35/3.01  tff(c_5165, plain, (![A_263, B_264, C_265]: (v1_relat_1(k3_relset_1(A_263, B_264, C_265)) | ~m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1(A_263, B_264))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4960])).
% 9.35/3.01  tff(c_5183, plain, (v1_relat_1(k3_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_5165])).
% 9.35/3.01  tff(c_145, plain, (![B_67, A_68]: (v1_relat_1(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.35/3.01  tff(c_151, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_145])).
% 9.35/3.01  tff(c_155, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_151])).
% 9.35/3.01  tff(c_163, plain, (![C_71, A_72, B_73]: (v4_relat_1(C_71, A_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.35/3.01  tff(c_172, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_163])).
% 9.35/3.01  tff(c_20, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.35/3.01  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.35/3.01  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.35/3.01  tff(c_4773, plain, (![A_229, C_230, B_231]: (m1_subset_1(A_229, C_230) | ~m1_subset_1(B_231, k1_zfmisc_1(C_230)) | ~r2_hidden(A_229, B_231))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.35/3.01  tff(c_4803, plain, (![A_237, B_238, A_239]: (m1_subset_1(A_237, B_238) | ~r2_hidden(A_237, A_239) | ~r1_tarski(A_239, B_238))), inference(resolution, [status(thm)], [c_12, c_4773])).
% 9.35/3.01  tff(c_4807, plain, (![A_240, B_241]: (m1_subset_1('#skF_1'(A_240), B_241) | ~r1_tarski(A_240, B_241) | v1_xboole_0(A_240))), inference(resolution, [status(thm)], [c_4, c_4803])).
% 9.35/3.01  tff(c_4780, plain, (![A_232, B_233, C_234]: (k1_relset_1(A_232, B_233, C_234)=k1_relat_1(C_234) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.35/3.01  tff(c_4789, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_4780])).
% 9.35/3.01  tff(c_59, plain, (![D_54]: (~r2_hidden(D_54, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_54, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.35/3.01  tff(c_64, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3') | v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_59])).
% 9.35/3.01  tff(c_137, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_64])).
% 9.35/3.01  tff(c_4790, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4789, c_137])).
% 9.35/3.01  tff(c_4834, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | v1_xboole_0(k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4807, c_4790])).
% 9.35/3.01  tff(c_4841, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_4834])).
% 9.35/3.01  tff(c_4844, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_4841])).
% 9.35/3.01  tff(c_4848, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_172, c_4844])).
% 9.35/3.01  tff(c_4849, plain, (v1_xboole_0(k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4834])).
% 9.35/3.01  tff(c_71, plain, (![A_56]: (k1_xboole_0=A_56 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_6, c_65])).
% 9.35/3.01  tff(c_4869, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_4849, c_71])).
% 9.35/3.01  tff(c_4889, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4869, c_4789])).
% 9.35/3.01  tff(c_5184, plain, (![B_266, A_267, C_268]: (k2_relset_1(B_266, A_267, k3_relset_1(A_267, B_266, C_268))=k1_relset_1(A_267, B_266, C_268) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(A_267, B_266))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.35/3.01  tff(c_5194, plain, (k2_relset_1('#skF_2', '#skF_3', k3_relset_1('#skF_3', '#skF_2', '#skF_4'))=k1_relset_1('#skF_3', '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_5184])).
% 9.35/3.01  tff(c_5199, plain, (k2_relset_1('#skF_2', '#skF_3', k3_relset_1('#skF_3', '#skF_2', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4889, c_5194])).
% 9.35/3.01  tff(c_36, plain, (![A_30, B_31, C_32]: (k2_relset_1(A_30, B_31, C_32)=k2_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.35/3.01  tff(c_8516, plain, (![B_361, A_362, C_363]: (k2_relset_1(B_361, A_362, k3_relset_1(A_362, B_361, C_363))=k2_relat_1(k3_relset_1(A_362, B_361, C_363)) | ~m1_subset_1(C_363, k1_zfmisc_1(k2_zfmisc_1(A_362, B_361))))), inference(resolution, [status(thm)], [c_4943, c_36])).
% 9.35/3.01  tff(c_8526, plain, (k2_relset_1('#skF_2', '#skF_3', k3_relset_1('#skF_3', '#skF_2', '#skF_4'))=k2_relat_1(k3_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_8516])).
% 9.35/3.01  tff(c_8531, plain, (k2_relat_1(k3_relset_1('#skF_3', '#skF_2', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5199, c_8526])).
% 9.35/3.01  tff(c_26, plain, (![A_20]: (~v1_xboole_0(k2_relat_1(A_20)) | ~v1_relat_1(A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.35/3.01  tff(c_8535, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k3_relset_1('#skF_3', '#skF_2', '#skF_4')) | v1_xboole_0(k3_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8531, c_26])).
% 9.35/3.01  tff(c_8539, plain, (v1_xboole_0(k3_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5183, c_6, c_8535])).
% 9.35/3.01  tff(c_8577, plain, (k3_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_8539, c_71])).
% 9.35/3.01  tff(c_8641, plain, (![B_364, A_365, C_366]: (k1_relset_1(B_364, A_365, k3_relset_1(A_365, B_364, C_366))=k1_relat_1(k3_relset_1(A_365, B_364, C_366)) | ~m1_subset_1(C_366, k1_zfmisc_1(k2_zfmisc_1(A_365, B_364))))), inference(resolution, [status(thm)], [c_4943, c_34])).
% 9.35/3.01  tff(c_8651, plain, (k1_relset_1('#skF_2', '#skF_3', k3_relset_1('#skF_3', '#skF_2', '#skF_4'))=k1_relat_1(k3_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_8641])).
% 9.35/3.01  tff(c_8656, plain, (k1_relset_1('#skF_2', '#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_90, c_8577, c_8577, c_8651])).
% 9.35/3.01  tff(c_5145, plain, (![B_260, A_261, C_262]: (k1_relset_1(B_260, A_261, k3_relset_1(A_261, B_260, C_262))=k2_relset_1(A_261, B_260, C_262) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_261, B_260))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.35/3.01  tff(c_5155, plain, (k1_relset_1('#skF_2', '#skF_3', k3_relset_1('#skF_3', '#skF_2', '#skF_4'))=k2_relset_1('#skF_3', '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_5145])).
% 9.35/3.01  tff(c_5160, plain, (k1_relset_1('#skF_2', '#skF_3', k3_relset_1('#skF_3', '#skF_2', '#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4885, c_5155])).
% 9.35/3.01  tff(c_8585, plain, (k1_relset_1('#skF_2', '#skF_3', k1_xboole_0)=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8577, c_5160])).
% 9.35/3.01  tff(c_8703, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8656, c_8585])).
% 9.35/3.01  tff(c_8704, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4920, c_8703])).
% 9.35/3.01  tff(c_8705, plain, (v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_64])).
% 9.35/3.01  tff(c_8716, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_8705, c_71])).
% 9.35/3.01  tff(c_9000, plain, (![B_417, A_418, C_419]: (k2_relset_1(B_417, A_418, k3_relset_1(A_418, B_417, C_419))=k1_relset_1(A_418, B_417, C_419) | ~m1_subset_1(C_419, k1_zfmisc_1(k2_zfmisc_1(A_418, B_417))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.35/3.01  tff(c_9010, plain, (k2_relset_1('#skF_2', '#skF_3', k3_relset_1('#skF_3', '#skF_2', '#skF_4'))=k1_relset_1('#skF_3', '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_9000])).
% 9.35/3.01  tff(c_9015, plain, (k2_relset_1('#skF_2', '#skF_3', k3_relset_1('#skF_3', '#skF_2', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8716, c_9010])).
% 9.35/3.01  tff(c_14396, plain, (![B_545, A_546, C_547]: (k2_relset_1(B_545, A_546, k3_relset_1(A_546, B_545, C_547))=k2_relat_1(k3_relset_1(A_546, B_545, C_547)) | ~m1_subset_1(C_547, k1_zfmisc_1(k2_zfmisc_1(A_546, B_545))))), inference(resolution, [status(thm)], [c_8917, c_36])).
% 9.35/3.01  tff(c_14406, plain, (k2_relset_1('#skF_2', '#skF_3', k3_relset_1('#skF_3', '#skF_2', '#skF_4'))=k2_relat_1(k3_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_14396])).
% 9.35/3.01  tff(c_14411, plain, (k2_relat_1(k3_relset_1('#skF_3', '#skF_2', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9015, c_14406])).
% 9.35/3.01  tff(c_14415, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k3_relset_1('#skF_3', '#skF_2', '#skF_4')) | v1_xboole_0(k3_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14411, c_26])).
% 9.35/3.01  tff(c_14419, plain, (v1_xboole_0(k3_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9216, c_6, c_14415])).
% 9.35/3.01  tff(c_14421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14356, c_14419])).
% 9.35/3.01  tff(c_14422, plain, (v1_xboole_0(k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_14344])).
% 9.35/3.01  tff(c_14454, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_14422, c_71])).
% 9.35/3.01  tff(c_14475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8859, c_14454])).
% 9.35/3.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.35/3.01  
% 9.35/3.01  Inference rules
% 9.35/3.01  ----------------------
% 9.35/3.01  #Ref     : 0
% 9.35/3.01  #Sup     : 4212
% 9.35/3.01  #Fact    : 0
% 9.35/3.01  #Define  : 0
% 9.35/3.01  #Split   : 20
% 9.35/3.01  #Chain   : 0
% 9.35/3.01  #Close   : 0
% 9.35/3.01  
% 9.35/3.01  Ordering : KBO
% 9.35/3.01  
% 9.35/3.01  Simplification rules
% 9.35/3.01  ----------------------
% 9.35/3.01  #Subsume      : 1937
% 9.35/3.01  #Demod        : 1763
% 9.35/3.01  #Tautology    : 567
% 9.35/3.01  #SimpNegUnit  : 10
% 9.35/3.01  #BackRed      : 31
% 9.35/3.01  
% 9.35/3.01  #Partial instantiations: 0
% 9.35/3.01  #Strategies tried      : 1
% 9.35/3.01  
% 9.35/3.01  Timing (in seconds)
% 9.35/3.01  ----------------------
% 9.36/3.01  Preprocessing        : 0.34
% 9.36/3.01  Parsing              : 0.19
% 9.36/3.01  CNF conversion       : 0.02
% 9.36/3.01  Main loop            : 1.87
% 9.36/3.01  Inferencing          : 0.55
% 9.36/3.01  Reduction            : 0.52
% 9.36/3.01  Demodulation         : 0.37
% 9.36/3.01  BG Simplification    : 0.07
% 9.36/3.01  Subsumption          : 0.60
% 9.36/3.01  Abstraction          : 0.10
% 9.36/3.01  MUC search           : 0.00
% 9.36/3.01  Cooper               : 0.00
% 9.36/3.01  Total                : 2.24
% 9.36/3.01  Index Insertion      : 0.00
% 9.36/3.01  Index Deletion       : 0.00
% 9.36/3.01  Index Matching       : 0.00
% 9.36/3.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
