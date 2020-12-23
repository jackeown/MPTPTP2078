%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:16 EST 2020

% Result     : Theorem 7.72s
% Output     : CNFRefutation 7.88s
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
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

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
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

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
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_6845,plain,(
    ! [A_401,B_402,C_403] :
      ( k1_relset_1(A_401,B_402,C_403) = k1_relat_1(C_403)
      | ~ m1_subset_1(C_403,k1_zfmisc_1(k2_zfmisc_1(A_401,B_402))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6859,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_6845])).

tff(c_44,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_6860,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6859,c_44])).

tff(c_7072,plain,(
    ! [B_420,A_421,C_422] :
      ( k2_relset_1(B_420,A_421,k3_relset_1(A_421,B_420,C_422)) = k1_relset_1(A_421,B_420,C_422)
      | ~ m1_subset_1(C_422,k1_zfmisc_1(k2_zfmisc_1(A_421,B_420))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_7082,plain,(
    k2_relset_1('#skF_3','#skF_2',k3_relset_1('#skF_2','#skF_3','#skF_4')) = k1_relset_1('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_7072])).

tff(c_7087,plain,(
    k2_relset_1('#skF_3','#skF_2',k3_relset_1('#skF_2','#skF_3','#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6859,c_7082])).

tff(c_6880,plain,(
    ! [A_406,B_407,C_408] :
      ( m1_subset_1(k3_relset_1(A_406,B_407,C_408),k1_zfmisc_1(k2_zfmisc_1(B_407,A_406)))
      | ~ m1_subset_1(C_408,k1_zfmisc_1(k2_zfmisc_1(A_406,B_407))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36,plain,(
    ! [A_30,B_31,C_32] :
      ( k2_relset_1(A_30,B_31,C_32) = k2_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_12151,plain,(
    ! [B_530,A_531,C_532] :
      ( k2_relset_1(B_530,A_531,k3_relset_1(A_531,B_530,C_532)) = k2_relat_1(k3_relset_1(A_531,B_530,C_532))
      | ~ m1_subset_1(C_532,k1_zfmisc_1(k2_zfmisc_1(A_531,B_530))) ) ),
    inference(resolution,[status(thm)],[c_6880,c_36])).

tff(c_12161,plain,(
    k2_relset_1('#skF_3','#skF_2',k3_relset_1('#skF_2','#skF_3','#skF_4')) = k2_relat_1(k3_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_12151])).

tff(c_12166,plain,(
    k2_relat_1(k3_relset_1('#skF_2','#skF_3','#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7087,c_12161])).

tff(c_22,plain,(
    ! [A_17] :
      ( v1_xboole_0(k2_relat_1(A_17))
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12242,plain,
    ( v1_xboole_0(k1_relat_1('#skF_4'))
    | ~ v1_xboole_0(k3_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12166,c_22])).

tff(c_12254,plain,(
    ~ v1_xboole_0(k3_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_12242])).

tff(c_24,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16,plain,(
    ! [B_14,A_12] :
      ( v1_relat_1(B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_12))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6897,plain,(
    ! [A_406,B_407,C_408] :
      ( v1_relat_1(k3_relset_1(A_406,B_407,C_408))
      | ~ v1_relat_1(k2_zfmisc_1(B_407,A_406))
      | ~ m1_subset_1(C_408,k1_zfmisc_1(k2_zfmisc_1(A_406,B_407))) ) ),
    inference(resolution,[status(thm)],[c_6880,c_16])).

tff(c_7053,plain,(
    ! [A_417,B_418,C_419] :
      ( v1_relat_1(k3_relset_1(A_417,B_418,C_419))
      | ~ m1_subset_1(C_419,k1_zfmisc_1(k2_zfmisc_1(A_417,B_418))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_6897])).

tff(c_7071,plain,(
    v1_relat_1(k3_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_7053])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3374,plain,(
    ! [A_228,B_229,C_230] :
      ( k1_relset_1(A_228,B_229,C_230) = k1_relat_1(C_230)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3383,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_3374])).

tff(c_3384,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3383,c_44])).

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
      ( k2_relat_1(A_58) = k1_xboole_0
      | ~ v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_22,c_72])).

tff(c_90,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_3455,plain,(
    ! [A_241,B_242,C_243] :
      ( m1_subset_1(k3_relset_1(A_241,B_242,C_243),k1_zfmisc_1(k2_zfmisc_1(B_242,A_241)))
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3472,plain,(
    ! [A_241,B_242,C_243] :
      ( v1_relat_1(k3_relset_1(A_241,B_242,C_243))
      | ~ v1_relat_1(k2_zfmisc_1(B_242,A_241))
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242))) ) ),
    inference(resolution,[status(thm)],[c_3455,c_16])).

tff(c_3790,plain,(
    ! [A_262,B_263,C_264] :
      ( v1_relat_1(k3_relset_1(A_262,B_263,C_264))
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_262,B_263))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3472])).

tff(c_3808,plain,(
    v1_relat_1(k3_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_3790])).

tff(c_145,plain,(
    ! [B_67,A_68] :
      ( v1_relat_1(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68))
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_151,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_145])).

tff(c_155,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_151])).

tff(c_187,plain,(
    ! [C_79,B_80,A_81] :
      ( v5_relat_1(C_79,B_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_196,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_187])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v5_relat_1(B_16,A_15)
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

tff(c_3367,plain,(
    ! [A_225,C_226,B_227] :
      ( m1_subset_1(A_225,C_226)
      | ~ m1_subset_1(B_227,k1_zfmisc_1(C_226))
      | ~ r2_hidden(A_225,B_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3412,plain,(
    ! [A_236,B_237,A_238] :
      ( m1_subset_1(A_236,B_237)
      | ~ r2_hidden(A_236,A_238)
      | ~ r1_tarski(A_238,B_237) ) ),
    inference(resolution,[status(thm)],[c_12,c_3367])).

tff(c_3416,plain,(
    ! [A_239,B_240] :
      ( m1_subset_1('#skF_1'(A_239),B_240)
      | ~ r1_tarski(A_239,B_240)
      | v1_xboole_0(A_239) ) ),
    inference(resolution,[status(thm)],[c_4,c_3412])).

tff(c_3390,plain,(
    ! [A_232,B_233,C_234] :
      ( k2_relset_1(A_232,B_233,C_234) = k2_relat_1(C_234)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3399,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_3390])).

tff(c_59,plain,(
    ! [D_54] :
      ( ~ r2_hidden(D_54,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_54,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_64,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3')
    | v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_59])).

tff(c_137,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_3400,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3399,c_137])).

tff(c_3447,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_3416,c_3400])).

tff(c_3485,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3447])).

tff(c_3488,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_3485])).

tff(c_3492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_196,c_3488])).

tff(c_3493,plain,(
    v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3447])).

tff(c_71,plain,(
    ! [A_56] :
      ( k1_xboole_0 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_65])).

tff(c_3513,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3493,c_71])).

tff(c_3529,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3513,c_3399])).

tff(c_3566,plain,(
    ! [B_244,A_245,C_246] :
      ( k1_relset_1(B_244,A_245,k3_relset_1(A_245,B_244,C_246)) = k2_relset_1(A_245,B_244,C_246)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_245,B_244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3580,plain,(
    k1_relset_1('#skF_3','#skF_2',k3_relset_1('#skF_2','#skF_3','#skF_4')) = k2_relset_1('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_3566])).

tff(c_3587,plain,(
    k1_relset_1('#skF_3','#skF_2',k3_relset_1('#skF_2','#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3529,c_3580])).

tff(c_34,plain,(
    ! [A_27,B_28,C_29] :
      ( k1_relset_1(A_27,B_28,C_29) = k1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6411,plain,(
    ! [B_351,A_352,C_353] :
      ( k1_relset_1(B_351,A_352,k3_relset_1(A_352,B_351,C_353)) = k1_relat_1(k3_relset_1(A_352,B_351,C_353))
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_zfmisc_1(A_352,B_351))) ) ),
    inference(resolution,[status(thm)],[c_3455,c_34])).

tff(c_6421,plain,(
    k1_relset_1('#skF_3','#skF_2',k3_relset_1('#skF_2','#skF_3','#skF_4')) = k1_relat_1(k3_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_6411])).

tff(c_6426,plain,(
    k1_relat_1(k3_relset_1('#skF_2','#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3587,c_6421])).

tff(c_26,plain,(
    ! [A_20] :
      ( ~ v1_xboole_0(k1_relat_1(A_20))
      | ~ v1_relat_1(A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6430,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k3_relset_1('#skF_2','#skF_3','#skF_4'))
    | v1_xboole_0(k3_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6426,c_26])).

tff(c_6434,plain,(
    v1_xboole_0(k3_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3808,c_6,c_6430])).

tff(c_6472,plain,(
    k3_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6434,c_71])).

tff(c_6536,plain,(
    ! [B_354,A_355,C_356] :
      ( k2_relset_1(B_354,A_355,k3_relset_1(A_355,B_354,C_356)) = k2_relat_1(k3_relset_1(A_355,B_354,C_356))
      | ~ m1_subset_1(C_356,k1_zfmisc_1(k2_zfmisc_1(A_355,B_354))) ) ),
    inference(resolution,[status(thm)],[c_3455,c_36])).

tff(c_6546,plain,(
    k2_relset_1('#skF_3','#skF_2',k3_relset_1('#skF_2','#skF_3','#skF_4')) = k2_relat_1(k3_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_6536])).

tff(c_6551,plain,(
    k2_relset_1('#skF_3','#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_6472,c_6472,c_6546])).

tff(c_3612,plain,(
    ! [B_250,A_251,C_252] :
      ( k2_relset_1(B_250,A_251,k3_relset_1(A_251,B_250,C_252)) = k1_relset_1(A_251,B_250,C_252)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_251,B_250))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3622,plain,(
    k2_relset_1('#skF_3','#skF_2',k3_relset_1('#skF_2','#skF_3','#skF_4')) = k1_relset_1('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_3612])).

tff(c_3627,plain,(
    k2_relset_1('#skF_3','#skF_2',k3_relset_1('#skF_2','#skF_3','#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3383,c_3622])).

tff(c_6479,plain,(
    k2_relset_1('#skF_3','#skF_2',k1_xboole_0) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6472,c_3627])).

tff(c_6598,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6551,c_6479])).

tff(c_6599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3384,c_6598])).

tff(c_6600,plain,(
    v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_6611,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6600,c_71])).

tff(c_7116,plain,(
    ! [B_429,A_430,C_431] :
      ( k1_relset_1(B_429,A_430,k3_relset_1(A_430,B_429,C_431)) = k2_relset_1(A_430,B_429,C_431)
      | ~ m1_subset_1(C_431,k1_zfmisc_1(k2_zfmisc_1(A_430,B_429))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_7126,plain,(
    k1_relset_1('#skF_3','#skF_2',k3_relset_1('#skF_2','#skF_3','#skF_4')) = k2_relset_1('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_7116])).

tff(c_7131,plain,(
    k1_relset_1('#skF_3','#skF_2',k3_relset_1('#skF_2','#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6611,c_7126])).

tff(c_12295,plain,(
    ! [B_535,A_536,C_537] :
      ( k1_relset_1(B_535,A_536,k3_relset_1(A_536,B_535,C_537)) = k1_relat_1(k3_relset_1(A_536,B_535,C_537))
      | ~ m1_subset_1(C_537,k1_zfmisc_1(k2_zfmisc_1(A_536,B_535))) ) ),
    inference(resolution,[status(thm)],[c_6880,c_34])).

tff(c_12305,plain,(
    k1_relset_1('#skF_3','#skF_2',k3_relset_1('#skF_2','#skF_3','#skF_4')) = k1_relat_1(k3_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_12295])).

tff(c_12310,plain,(
    k1_relat_1(k3_relset_1('#skF_2','#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7131,c_12305])).

tff(c_12314,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k3_relset_1('#skF_2','#skF_3','#skF_4'))
    | v1_xboole_0(k3_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12310,c_26])).

tff(c_12318,plain,(
    v1_xboole_0(k3_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7071,c_6,c_12314])).

tff(c_12320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12254,c_12318])).

tff(c_12321,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_12242])).

tff(c_12353,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12321,c_71])).

tff(c_12374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6860,c_12353])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.72/2.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.72/2.71  
% 7.72/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.72/2.72  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 7.72/2.72  
% 7.72/2.72  %Foreground sorts:
% 7.72/2.72  
% 7.72/2.72  
% 7.72/2.72  %Background operators:
% 7.72/2.72  
% 7.72/2.72  
% 7.72/2.72  %Foreground operators:
% 7.72/2.72  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.72/2.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.72/2.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.72/2.72  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.72/2.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.72/2.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.72/2.72  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 7.72/2.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.72/2.72  tff('#skF_2', type, '#skF_2': $i).
% 7.72/2.72  tff('#skF_3', type, '#skF_3': $i).
% 7.72/2.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.72/2.72  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.72/2.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.72/2.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.72/2.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.72/2.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.72/2.72  tff('#skF_4', type, '#skF_4': $i).
% 7.72/2.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.72/2.72  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.72/2.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.72/2.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.72/2.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.72/2.72  
% 7.88/2.74  tff(f_122, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 7.88/2.74  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.88/2.74  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k1_relset_1(B, A, k3_relset_1(A, B, C)) = k2_relset_1(A, B, C)) & (k2_relset_1(B, A, k3_relset_1(A, B, C)) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_relset_1)).
% 7.88/2.74  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 7.88/2.74  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.88/2.74  tff(f_67, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 7.88/2.74  tff(f_69, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.88/2.74  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.88/2.74  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.88/2.74  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 7.88/2.74  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.88/2.74  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.88/2.74  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.88/2.74  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.88/2.74  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 7.88/2.74  tff(f_77, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 7.88/2.74  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.88/2.74  tff(c_6845, plain, (![A_401, B_402, C_403]: (k1_relset_1(A_401, B_402, C_403)=k1_relat_1(C_403) | ~m1_subset_1(C_403, k1_zfmisc_1(k2_zfmisc_1(A_401, B_402))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.88/2.74  tff(c_6859, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_6845])).
% 7.88/2.74  tff(c_44, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.88/2.74  tff(c_6860, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6859, c_44])).
% 7.88/2.74  tff(c_7072, plain, (![B_420, A_421, C_422]: (k2_relset_1(B_420, A_421, k3_relset_1(A_421, B_420, C_422))=k1_relset_1(A_421, B_420, C_422) | ~m1_subset_1(C_422, k1_zfmisc_1(k2_zfmisc_1(A_421, B_420))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.88/2.74  tff(c_7082, plain, (k2_relset_1('#skF_3', '#skF_2', k3_relset_1('#skF_2', '#skF_3', '#skF_4'))=k1_relset_1('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_7072])).
% 7.88/2.74  tff(c_7087, plain, (k2_relset_1('#skF_3', '#skF_2', k3_relset_1('#skF_2', '#skF_3', '#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6859, c_7082])).
% 7.88/2.74  tff(c_6880, plain, (![A_406, B_407, C_408]: (m1_subset_1(k3_relset_1(A_406, B_407, C_408), k1_zfmisc_1(k2_zfmisc_1(B_407, A_406))) | ~m1_subset_1(C_408, k1_zfmisc_1(k2_zfmisc_1(A_406, B_407))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.88/2.74  tff(c_36, plain, (![A_30, B_31, C_32]: (k2_relset_1(A_30, B_31, C_32)=k2_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.88/2.74  tff(c_12151, plain, (![B_530, A_531, C_532]: (k2_relset_1(B_530, A_531, k3_relset_1(A_531, B_530, C_532))=k2_relat_1(k3_relset_1(A_531, B_530, C_532)) | ~m1_subset_1(C_532, k1_zfmisc_1(k2_zfmisc_1(A_531, B_530))))), inference(resolution, [status(thm)], [c_6880, c_36])).
% 7.88/2.74  tff(c_12161, plain, (k2_relset_1('#skF_3', '#skF_2', k3_relset_1('#skF_2', '#skF_3', '#skF_4'))=k2_relat_1(k3_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_12151])).
% 7.88/2.74  tff(c_12166, plain, (k2_relat_1(k3_relset_1('#skF_2', '#skF_3', '#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7087, c_12161])).
% 7.88/2.74  tff(c_22, plain, (![A_17]: (v1_xboole_0(k2_relat_1(A_17)) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.88/2.74  tff(c_12242, plain, (v1_xboole_0(k1_relat_1('#skF_4')) | ~v1_xboole_0(k3_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12166, c_22])).
% 7.88/2.74  tff(c_12254, plain, (~v1_xboole_0(k3_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_12242])).
% 7.88/2.74  tff(c_24, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.88/2.74  tff(c_16, plain, (![B_14, A_12]: (v1_relat_1(B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(A_12)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.88/2.74  tff(c_6897, plain, (![A_406, B_407, C_408]: (v1_relat_1(k3_relset_1(A_406, B_407, C_408)) | ~v1_relat_1(k2_zfmisc_1(B_407, A_406)) | ~m1_subset_1(C_408, k1_zfmisc_1(k2_zfmisc_1(A_406, B_407))))), inference(resolution, [status(thm)], [c_6880, c_16])).
% 7.88/2.74  tff(c_7053, plain, (![A_417, B_418, C_419]: (v1_relat_1(k3_relset_1(A_417, B_418, C_419)) | ~m1_subset_1(C_419, k1_zfmisc_1(k2_zfmisc_1(A_417, B_418))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_6897])).
% 7.88/2.74  tff(c_7071, plain, (v1_relat_1(k3_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_7053])).
% 7.88/2.74  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.88/2.74  tff(c_3374, plain, (![A_228, B_229, C_230]: (k1_relset_1(A_228, B_229, C_230)=k1_relat_1(C_230) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.88/2.74  tff(c_3383, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_3374])).
% 7.88/2.74  tff(c_3384, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3383, c_44])).
% 7.88/2.74  tff(c_65, plain, (![B_55, A_56]: (~v1_xboole_0(B_55) | B_55=A_56 | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.88/2.74  tff(c_72, plain, (![A_57]: (k1_xboole_0=A_57 | ~v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_6, c_65])).
% 7.88/2.74  tff(c_82, plain, (![A_58]: (k2_relat_1(A_58)=k1_xboole_0 | ~v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_22, c_72])).
% 7.88/2.74  tff(c_90, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_82])).
% 7.88/2.74  tff(c_3455, plain, (![A_241, B_242, C_243]: (m1_subset_1(k3_relset_1(A_241, B_242, C_243), k1_zfmisc_1(k2_zfmisc_1(B_242, A_241))) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_241, B_242))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.88/2.74  tff(c_3472, plain, (![A_241, B_242, C_243]: (v1_relat_1(k3_relset_1(A_241, B_242, C_243)) | ~v1_relat_1(k2_zfmisc_1(B_242, A_241)) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_241, B_242))))), inference(resolution, [status(thm)], [c_3455, c_16])).
% 7.88/2.74  tff(c_3790, plain, (![A_262, B_263, C_264]: (v1_relat_1(k3_relset_1(A_262, B_263, C_264)) | ~m1_subset_1(C_264, k1_zfmisc_1(k2_zfmisc_1(A_262, B_263))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3472])).
% 7.88/2.74  tff(c_3808, plain, (v1_relat_1(k3_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_3790])).
% 7.88/2.74  tff(c_145, plain, (![B_67, A_68]: (v1_relat_1(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.88/2.74  tff(c_151, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_145])).
% 7.88/2.74  tff(c_155, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_151])).
% 7.88/2.74  tff(c_187, plain, (![C_79, B_80, A_81]: (v5_relat_1(C_79, B_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.88/2.74  tff(c_196, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_187])).
% 7.88/2.74  tff(c_20, plain, (![B_16, A_15]: (r1_tarski(k2_relat_1(B_16), A_15) | ~v5_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.88/2.74  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.88/2.74  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.88/2.74  tff(c_3367, plain, (![A_225, C_226, B_227]: (m1_subset_1(A_225, C_226) | ~m1_subset_1(B_227, k1_zfmisc_1(C_226)) | ~r2_hidden(A_225, B_227))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.88/2.74  tff(c_3412, plain, (![A_236, B_237, A_238]: (m1_subset_1(A_236, B_237) | ~r2_hidden(A_236, A_238) | ~r1_tarski(A_238, B_237))), inference(resolution, [status(thm)], [c_12, c_3367])).
% 7.88/2.74  tff(c_3416, plain, (![A_239, B_240]: (m1_subset_1('#skF_1'(A_239), B_240) | ~r1_tarski(A_239, B_240) | v1_xboole_0(A_239))), inference(resolution, [status(thm)], [c_4, c_3412])).
% 7.88/2.74  tff(c_3390, plain, (![A_232, B_233, C_234]: (k2_relset_1(A_232, B_233, C_234)=k2_relat_1(C_234) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.88/2.74  tff(c_3399, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_3390])).
% 7.88/2.74  tff(c_59, plain, (![D_54]: (~r2_hidden(D_54, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_54, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.88/2.74  tff(c_64, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3') | v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_59])).
% 7.88/2.74  tff(c_137, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_64])).
% 7.88/2.74  tff(c_3400, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3399, c_137])).
% 7.88/2.74  tff(c_3447, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | v1_xboole_0(k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_3416, c_3400])).
% 7.88/2.74  tff(c_3485, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_3447])).
% 7.88/2.74  tff(c_3488, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_3485])).
% 7.88/2.74  tff(c_3492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_196, c_3488])).
% 7.88/2.74  tff(c_3493, plain, (v1_xboole_0(k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3447])).
% 7.88/2.74  tff(c_71, plain, (![A_56]: (k1_xboole_0=A_56 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_6, c_65])).
% 7.88/2.74  tff(c_3513, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_3493, c_71])).
% 7.88/2.74  tff(c_3529, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3513, c_3399])).
% 7.88/2.74  tff(c_3566, plain, (![B_244, A_245, C_246]: (k1_relset_1(B_244, A_245, k3_relset_1(A_245, B_244, C_246))=k2_relset_1(A_245, B_244, C_246) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_245, B_244))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.88/2.74  tff(c_3580, plain, (k1_relset_1('#skF_3', '#skF_2', k3_relset_1('#skF_2', '#skF_3', '#skF_4'))=k2_relset_1('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_3566])).
% 7.88/2.74  tff(c_3587, plain, (k1_relset_1('#skF_3', '#skF_2', k3_relset_1('#skF_2', '#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3529, c_3580])).
% 7.88/2.74  tff(c_34, plain, (![A_27, B_28, C_29]: (k1_relset_1(A_27, B_28, C_29)=k1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.88/2.74  tff(c_6411, plain, (![B_351, A_352, C_353]: (k1_relset_1(B_351, A_352, k3_relset_1(A_352, B_351, C_353))=k1_relat_1(k3_relset_1(A_352, B_351, C_353)) | ~m1_subset_1(C_353, k1_zfmisc_1(k2_zfmisc_1(A_352, B_351))))), inference(resolution, [status(thm)], [c_3455, c_34])).
% 7.88/2.74  tff(c_6421, plain, (k1_relset_1('#skF_3', '#skF_2', k3_relset_1('#skF_2', '#skF_3', '#skF_4'))=k1_relat_1(k3_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_6411])).
% 7.88/2.74  tff(c_6426, plain, (k1_relat_1(k3_relset_1('#skF_2', '#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3587, c_6421])).
% 7.88/2.74  tff(c_26, plain, (![A_20]: (~v1_xboole_0(k1_relat_1(A_20)) | ~v1_relat_1(A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.88/2.74  tff(c_6430, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k3_relset_1('#skF_2', '#skF_3', '#skF_4')) | v1_xboole_0(k3_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6426, c_26])).
% 7.88/2.74  tff(c_6434, plain, (v1_xboole_0(k3_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3808, c_6, c_6430])).
% 7.88/2.74  tff(c_6472, plain, (k3_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_6434, c_71])).
% 7.88/2.74  tff(c_6536, plain, (![B_354, A_355, C_356]: (k2_relset_1(B_354, A_355, k3_relset_1(A_355, B_354, C_356))=k2_relat_1(k3_relset_1(A_355, B_354, C_356)) | ~m1_subset_1(C_356, k1_zfmisc_1(k2_zfmisc_1(A_355, B_354))))), inference(resolution, [status(thm)], [c_3455, c_36])).
% 7.88/2.74  tff(c_6546, plain, (k2_relset_1('#skF_3', '#skF_2', k3_relset_1('#skF_2', '#skF_3', '#skF_4'))=k2_relat_1(k3_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_6536])).
% 7.88/2.74  tff(c_6551, plain, (k2_relset_1('#skF_3', '#skF_2', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_90, c_6472, c_6472, c_6546])).
% 7.88/2.74  tff(c_3612, plain, (![B_250, A_251, C_252]: (k2_relset_1(B_250, A_251, k3_relset_1(A_251, B_250, C_252))=k1_relset_1(A_251, B_250, C_252) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_251, B_250))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.88/2.74  tff(c_3622, plain, (k2_relset_1('#skF_3', '#skF_2', k3_relset_1('#skF_2', '#skF_3', '#skF_4'))=k1_relset_1('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_3612])).
% 7.88/2.74  tff(c_3627, plain, (k2_relset_1('#skF_3', '#skF_2', k3_relset_1('#skF_2', '#skF_3', '#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3383, c_3622])).
% 7.88/2.74  tff(c_6479, plain, (k2_relset_1('#skF_3', '#skF_2', k1_xboole_0)=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6472, c_3627])).
% 7.88/2.74  tff(c_6598, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6551, c_6479])).
% 7.88/2.74  tff(c_6599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3384, c_6598])).
% 7.88/2.74  tff(c_6600, plain, (v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_64])).
% 7.88/2.74  tff(c_6611, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_6600, c_71])).
% 7.88/2.74  tff(c_7116, plain, (![B_429, A_430, C_431]: (k1_relset_1(B_429, A_430, k3_relset_1(A_430, B_429, C_431))=k2_relset_1(A_430, B_429, C_431) | ~m1_subset_1(C_431, k1_zfmisc_1(k2_zfmisc_1(A_430, B_429))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.88/2.74  tff(c_7126, plain, (k1_relset_1('#skF_3', '#skF_2', k3_relset_1('#skF_2', '#skF_3', '#skF_4'))=k2_relset_1('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_7116])).
% 7.88/2.74  tff(c_7131, plain, (k1_relset_1('#skF_3', '#skF_2', k3_relset_1('#skF_2', '#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6611, c_7126])).
% 7.88/2.74  tff(c_12295, plain, (![B_535, A_536, C_537]: (k1_relset_1(B_535, A_536, k3_relset_1(A_536, B_535, C_537))=k1_relat_1(k3_relset_1(A_536, B_535, C_537)) | ~m1_subset_1(C_537, k1_zfmisc_1(k2_zfmisc_1(A_536, B_535))))), inference(resolution, [status(thm)], [c_6880, c_34])).
% 7.88/2.74  tff(c_12305, plain, (k1_relset_1('#skF_3', '#skF_2', k3_relset_1('#skF_2', '#skF_3', '#skF_4'))=k1_relat_1(k3_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_12295])).
% 7.88/2.74  tff(c_12310, plain, (k1_relat_1(k3_relset_1('#skF_2', '#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7131, c_12305])).
% 7.88/2.74  tff(c_12314, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k3_relset_1('#skF_2', '#skF_3', '#skF_4')) | v1_xboole_0(k3_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12310, c_26])).
% 7.88/2.74  tff(c_12318, plain, (v1_xboole_0(k3_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7071, c_6, c_12314])).
% 7.88/2.74  tff(c_12320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12254, c_12318])).
% 7.88/2.74  tff(c_12321, plain, (v1_xboole_0(k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_12242])).
% 7.88/2.74  tff(c_12353, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_12321, c_71])).
% 7.88/2.74  tff(c_12374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6860, c_12353])).
% 7.88/2.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.88/2.74  
% 7.88/2.74  Inference rules
% 7.88/2.74  ----------------------
% 7.88/2.74  #Ref     : 0
% 7.88/2.74  #Sup     : 3534
% 7.88/2.74  #Fact    : 0
% 7.88/2.74  #Define  : 0
% 7.88/2.74  #Split   : 21
% 7.88/2.74  #Chain   : 0
% 7.88/2.74  #Close   : 0
% 7.88/2.74  
% 7.88/2.74  Ordering : KBO
% 7.88/2.74  
% 7.88/2.74  Simplification rules
% 7.88/2.74  ----------------------
% 7.88/2.74  #Subsume      : 1541
% 7.88/2.74  #Demod        : 1632
% 7.88/2.74  #Tautology    : 570
% 7.88/2.74  #SimpNegUnit  : 9
% 7.88/2.74  #BackRed      : 32
% 7.88/2.74  
% 7.88/2.74  #Partial instantiations: 0
% 7.88/2.74  #Strategies tried      : 1
% 7.88/2.74  
% 7.88/2.74  Timing (in seconds)
% 7.88/2.74  ----------------------
% 7.88/2.74  Preprocessing        : 0.32
% 7.88/2.74  Parsing              : 0.18
% 7.88/2.74  CNF conversion       : 0.02
% 7.88/2.74  Main loop            : 1.62
% 7.88/2.74  Inferencing          : 0.47
% 7.88/2.74  Reduction            : 0.47
% 7.88/2.74  Demodulation         : 0.33
% 7.88/2.74  BG Simplification    : 0.06
% 7.88/2.74  Subsumption          : 0.51
% 7.88/2.74  Abstraction          : 0.09
% 7.88/2.74  MUC search           : 0.00
% 7.88/2.74  Cooper               : 0.00
% 7.88/2.74  Total                : 1.99
% 7.88/2.74  Index Insertion      : 0.00
% 7.88/2.74  Index Deletion       : 0.00
% 7.88/2.74  Index Matching       : 0.00
% 7.88/2.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
