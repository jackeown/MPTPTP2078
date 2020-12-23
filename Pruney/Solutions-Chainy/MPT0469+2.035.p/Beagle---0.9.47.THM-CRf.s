%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:56 EST 2020

% Result     : Theorem 16.86s
% Output     : CNFRefutation 16.86s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 230 expanded)
%              Number of leaves         :   46 (  98 expanded)
%              Depth                    :   10
%              Number of atoms          :  150 ( 366 expanded)
%              Number of equality atoms :   58 ( 151 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_1 > #skF_3 > #skF_10 > #skF_8 > #skF_11 > #skF_2 > #skF_7 > #skF_9

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_77,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_83,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_119,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_133,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_127,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_137,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_22,plain,(
    ! [A_19] : k2_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_814,plain,(
    ! [A_182,B_183] : k4_xboole_0(A_182,k2_xboole_0(A_182,B_183)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_821,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_814])).

tff(c_30,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(A_24,B_25)
      | k4_xboole_0(A_24,B_25) != A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_886,plain,(
    ! [A_204,B_205] :
      ( k3_xboole_0(A_204,B_205) = A_204
      | ~ r1_tarski(A_204,B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1000,plain,(
    ! [A_242,B_243] :
      ( k3_xboole_0(A_242,B_243) = A_242
      | k4_xboole_0(A_242,B_243) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_886])).

tff(c_1009,plain,(
    ! [A_244] : k3_xboole_0(A_244,A_244) = A_244 ),
    inference(superposition,[status(thm),theory(equality)],[c_821,c_1000])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_896,plain,(
    ! [A_208,B_209,C_210] :
      ( ~ r1_xboole_0(A_208,B_209)
      | ~ r2_hidden(C_210,k3_xboole_0(A_208,B_209)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_911,plain,(
    ! [A_208,B_209] :
      ( ~ r1_xboole_0(A_208,B_209)
      | v1_xboole_0(k3_xboole_0(A_208,B_209)) ) ),
    inference(resolution,[status(thm)],[c_4,c_896])).

tff(c_1033,plain,(
    ! [A_245] :
      ( ~ r1_xboole_0(A_245,A_245)
      | v1_xboole_0(A_245) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1009,c_911])).

tff(c_1053,plain,(
    ! [B_25] :
      ( v1_xboole_0(B_25)
      | k4_xboole_0(B_25,B_25) != B_25 ) ),
    inference(resolution,[status(thm)],[c_30,c_1033])).

tff(c_1082,plain,(
    ! [B_247] :
      ( v1_xboole_0(B_247)
      | k1_xboole_0 != B_247 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_1053])).

tff(c_832,plain,(
    ! [A_186] :
      ( r2_hidden('#skF_5'(A_186),A_186)
      | v1_relat_1(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_836,plain,(
    ! [A_186] :
      ( ~ v1_xboole_0(A_186)
      | v1_relat_1(A_186) ) ),
    inference(resolution,[status(thm)],[c_832,c_2])).

tff(c_1104,plain,(
    ! [B_247] :
      ( v1_relat_1(B_247)
      | k1_xboole_0 != B_247 ) ),
    inference(resolution,[status(thm)],[c_1082,c_836])).

tff(c_1059,plain,(
    ! [B_25] :
      ( v1_xboole_0(B_25)
      | k1_xboole_0 != B_25 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_1053])).

tff(c_58,plain,(
    ! [A_71] :
      ( v1_relat_1(k4_relat_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1658,plain,(
    ! [C_285,A_286] :
      ( r2_hidden(k4_tarski(C_285,'#skF_11'(A_286,k1_relat_1(A_286),C_285)),A_286)
      | ~ r2_hidden(C_285,k1_relat_1(A_286)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1690,plain,(
    ! [A_287,C_288] :
      ( ~ v1_xboole_0(A_287)
      | ~ r2_hidden(C_288,k1_relat_1(A_287)) ) ),
    inference(resolution,[status(thm)],[c_1658,c_2])).

tff(c_1733,plain,(
    ! [A_287] :
      ( ~ v1_xboole_0(A_287)
      | v1_xboole_0(k1_relat_1(A_287)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1690])).

tff(c_848,plain,(
    ! [A_191] :
      ( k2_relat_1(k4_relat_1(A_191)) = k1_relat_1(A_191)
      | ~ v1_relat_1(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_60,plain,(
    ! [A_72] :
      ( ~ v1_xboole_0(k2_relat_1(A_72))
      | ~ v1_relat_1(A_72)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_4984,plain,(
    ! [A_401] :
      ( ~ v1_xboole_0(k1_relat_1(A_401))
      | ~ v1_relat_1(k4_relat_1(A_401))
      | v1_xboole_0(k4_relat_1(A_401))
      | ~ v1_relat_1(A_401) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_848,c_60])).

tff(c_809,plain,(
    ! [A_181] :
      ( r2_hidden('#skF_4'(A_181),A_181)
      | k1_xboole_0 = A_181 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_813,plain,(
    ! [A_181] :
      ( ~ v1_xboole_0(A_181)
      | k1_xboole_0 = A_181 ) ),
    inference(resolution,[status(thm)],[c_809,c_2])).

tff(c_21158,plain,(
    ! [A_706] :
      ( k4_relat_1(A_706) = k1_xboole_0
      | ~ v1_xboole_0(k1_relat_1(A_706))
      | ~ v1_relat_1(k4_relat_1(A_706))
      | ~ v1_relat_1(A_706) ) ),
    inference(resolution,[status(thm)],[c_4984,c_813])).

tff(c_56849,plain,(
    ! [A_1098] :
      ( k4_relat_1(A_1098) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_1098))
      | ~ v1_relat_1(A_1098)
      | ~ v1_xboole_0(A_1098) ) ),
    inference(resolution,[status(thm)],[c_1733,c_21158])).

tff(c_56858,plain,(
    ! [A_1099] :
      ( k4_relat_1(A_1099) = k1_xboole_0
      | ~ v1_xboole_0(A_1099)
      | ~ v1_relat_1(A_1099) ) ),
    inference(resolution,[status(thm)],[c_58,c_56849])).

tff(c_56952,plain,(
    ! [B_1100] :
      ( k4_relat_1(B_1100) = k1_xboole_0
      | ~ v1_relat_1(B_1100)
      | k1_xboole_0 != B_1100 ) ),
    inference(resolution,[status(thm)],[c_1059,c_56858])).

tff(c_57147,plain,(
    ! [B_1104] :
      ( k4_relat_1(B_1104) = k1_xboole_0
      | k1_xboole_0 != B_1104 ) ),
    inference(resolution,[status(thm)],[c_1104,c_56952])).

tff(c_16,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_4'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_64,plain,(
    ! [A_73] :
      ( k1_relat_1(k4_relat_1(A_73)) = k2_relat_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_10052,plain,(
    ! [A_531,C_532] :
      ( ~ v1_xboole_0(k4_relat_1(A_531))
      | ~ r2_hidden(C_532,k2_relat_1(A_531))
      | ~ v1_relat_1(A_531) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1690])).

tff(c_10151,plain,(
    ! [A_533] :
      ( ~ v1_xboole_0(k4_relat_1(A_533))
      | ~ v1_relat_1(A_533)
      | k2_relat_1(A_533) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_10052])).

tff(c_10168,plain,(
    ! [A_534] :
      ( ~ v1_relat_1(A_534)
      | k2_relat_1(A_534) = k1_xboole_0
      | k4_relat_1(A_534) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1059,c_10151])).

tff(c_10214,plain,(
    ! [B_247] :
      ( k2_relat_1(B_247) = k1_xboole_0
      | k4_relat_1(B_247) != k1_xboole_0
      | k1_xboole_0 != B_247 ) ),
    inference(resolution,[status(thm)],[c_1104,c_10168])).

tff(c_57272,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_57147,c_10214])).

tff(c_95,plain,(
    ! [A_82,B_83] : k4_xboole_0(A_82,k2_xboole_0(A_82,B_83)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_102,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_95])).

tff(c_166,plain,(
    ! [A_104,B_105] :
      ( k3_xboole_0(A_104,B_105) = A_104
      | ~ r1_tarski(A_104,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_266,plain,(
    ! [A_134,B_135] :
      ( k3_xboole_0(A_134,B_135) = A_134
      | k4_xboole_0(A_134,B_135) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_166])).

tff(c_275,plain,(
    ! [A_136] : k3_xboole_0(A_136,A_136) = A_136 ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_266])).

tff(c_181,plain,(
    ! [A_110,B_111,C_112] :
      ( ~ r1_xboole_0(A_110,B_111)
      | ~ r2_hidden(C_112,k3_xboole_0(A_110,B_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_201,plain,(
    ! [A_110,B_111] :
      ( ~ r1_xboole_0(A_110,B_111)
      | v1_xboole_0(k3_xboole_0(A_110,B_111)) ) ),
    inference(resolution,[status(thm)],[c_4,c_181])).

tff(c_330,plain,(
    ! [A_140] :
      ( ~ r1_xboole_0(A_140,A_140)
      | v1_xboole_0(A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_201])).

tff(c_342,plain,(
    ! [B_25] :
      ( v1_xboole_0(B_25)
      | k4_xboole_0(B_25,B_25) != B_25 ) ),
    inference(resolution,[status(thm)],[c_30,c_330])).

tff(c_346,plain,(
    ! [B_25] :
      ( v1_xboole_0(B_25)
      | k1_xboole_0 != B_25 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_342])).

tff(c_685,plain,(
    ! [C_172,A_173] :
      ( r2_hidden(k4_tarski(C_172,'#skF_11'(A_173,k1_relat_1(A_173),C_172)),A_173)
      | ~ r2_hidden(C_172,k1_relat_1(A_173)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_706,plain,(
    ! [A_174,C_175] :
      ( ~ v1_xboole_0(A_174)
      | ~ r2_hidden(C_175,k1_relat_1(A_174)) ) ),
    inference(resolution,[status(thm)],[c_685,c_2])).

tff(c_745,plain,(
    ! [A_176] :
      ( ~ v1_xboole_0(A_176)
      | k1_relat_1(A_176) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_706])).

tff(c_799,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_346,c_745])).

tff(c_66,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_83,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_802,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_83])).

tff(c_803,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_57277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57272,c_803])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:37:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.86/9.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.86/9.85  
% 16.86/9.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.86/9.86  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_1 > #skF_3 > #skF_10 > #skF_8 > #skF_11 > #skF_2 > #skF_7 > #skF_9
% 16.86/9.86  
% 16.86/9.86  %Foreground sorts:
% 16.86/9.86  
% 16.86/9.86  
% 16.86/9.86  %Background operators:
% 16.86/9.86  
% 16.86/9.86  
% 16.86/9.86  %Foreground operators:
% 16.86/9.86  tff('#skF_5', type, '#skF_5': $i > $i).
% 16.86/9.86  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 16.86/9.86  tff('#skF_4', type, '#skF_4': $i > $i).
% 16.86/9.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.86/9.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.86/9.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.86/9.86  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 16.86/9.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 16.86/9.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.86/9.86  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 16.86/9.86  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 16.86/9.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.86/9.86  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.86/9.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 16.86/9.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.86/9.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.86/9.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.86/9.86  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 16.86/9.86  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 16.86/9.86  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 16.86/9.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.86/9.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.86/9.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.86/9.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 16.86/9.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.86/9.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.86/9.86  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 16.86/9.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.86/9.86  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 16.86/9.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.86/9.86  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 16.86/9.86  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 16.86/9.86  
% 16.86/9.87  tff(f_77, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 16.86/9.87  tff(f_83, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 16.86/9.87  tff(f_87, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 16.86/9.87  tff(f_75, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 16.86/9.87  tff(f_81, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 16.86/9.87  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 16.86/9.87  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 16.86/9.87  tff(f_103, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 16.86/9.87  tff(f_119, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 16.86/9.87  tff(f_111, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 16.86/9.87  tff(f_133, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 16.86/9.87  tff(f_127, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 16.86/9.87  tff(f_71, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 16.86/9.87  tff(f_137, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 16.86/9.87  tff(c_22, plain, (![A_19]: (k2_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_77])).
% 16.86/9.87  tff(c_814, plain, (![A_182, B_183]: (k4_xboole_0(A_182, k2_xboole_0(A_182, B_183))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_83])).
% 16.86/9.87  tff(c_821, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_814])).
% 16.86/9.87  tff(c_30, plain, (![A_24, B_25]: (r1_xboole_0(A_24, B_25) | k4_xboole_0(A_24, B_25)!=A_24)), inference(cnfTransformation, [status(thm)], [f_87])).
% 16.86/9.87  tff(c_18, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | k4_xboole_0(A_17, B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.86/9.87  tff(c_886, plain, (![A_204, B_205]: (k3_xboole_0(A_204, B_205)=A_204 | ~r1_tarski(A_204, B_205))), inference(cnfTransformation, [status(thm)], [f_81])).
% 16.86/9.87  tff(c_1000, plain, (![A_242, B_243]: (k3_xboole_0(A_242, B_243)=A_242 | k4_xboole_0(A_242, B_243)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_886])).
% 16.86/9.87  tff(c_1009, plain, (![A_244]: (k3_xboole_0(A_244, A_244)=A_244)), inference(superposition, [status(thm), theory('equality')], [c_821, c_1000])).
% 16.86/9.87  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.86/9.87  tff(c_896, plain, (![A_208, B_209, C_210]: (~r1_xboole_0(A_208, B_209) | ~r2_hidden(C_210, k3_xboole_0(A_208, B_209)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.86/9.87  tff(c_911, plain, (![A_208, B_209]: (~r1_xboole_0(A_208, B_209) | v1_xboole_0(k3_xboole_0(A_208, B_209)))), inference(resolution, [status(thm)], [c_4, c_896])).
% 16.86/9.87  tff(c_1033, plain, (![A_245]: (~r1_xboole_0(A_245, A_245) | v1_xboole_0(A_245))), inference(superposition, [status(thm), theory('equality')], [c_1009, c_911])).
% 16.86/9.87  tff(c_1053, plain, (![B_25]: (v1_xboole_0(B_25) | k4_xboole_0(B_25, B_25)!=B_25)), inference(resolution, [status(thm)], [c_30, c_1033])).
% 16.86/9.87  tff(c_1082, plain, (![B_247]: (v1_xboole_0(B_247) | k1_xboole_0!=B_247)), inference(demodulation, [status(thm), theory('equality')], [c_821, c_1053])).
% 16.86/9.87  tff(c_832, plain, (![A_186]: (r2_hidden('#skF_5'(A_186), A_186) | v1_relat_1(A_186))), inference(cnfTransformation, [status(thm)], [f_103])).
% 16.86/9.87  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.86/9.87  tff(c_836, plain, (![A_186]: (~v1_xboole_0(A_186) | v1_relat_1(A_186))), inference(resolution, [status(thm)], [c_832, c_2])).
% 16.86/9.87  tff(c_1104, plain, (![B_247]: (v1_relat_1(B_247) | k1_xboole_0!=B_247)), inference(resolution, [status(thm)], [c_1082, c_836])).
% 16.86/9.87  tff(c_1059, plain, (![B_25]: (v1_xboole_0(B_25) | k1_xboole_0!=B_25)), inference(demodulation, [status(thm), theory('equality')], [c_821, c_1053])).
% 16.86/9.87  tff(c_58, plain, (![A_71]: (v1_relat_1(k4_relat_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_119])).
% 16.86/9.87  tff(c_1658, plain, (![C_285, A_286]: (r2_hidden(k4_tarski(C_285, '#skF_11'(A_286, k1_relat_1(A_286), C_285)), A_286) | ~r2_hidden(C_285, k1_relat_1(A_286)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 16.86/9.87  tff(c_1690, plain, (![A_287, C_288]: (~v1_xboole_0(A_287) | ~r2_hidden(C_288, k1_relat_1(A_287)))), inference(resolution, [status(thm)], [c_1658, c_2])).
% 16.86/9.87  tff(c_1733, plain, (![A_287]: (~v1_xboole_0(A_287) | v1_xboole_0(k1_relat_1(A_287)))), inference(resolution, [status(thm)], [c_4, c_1690])).
% 16.86/9.87  tff(c_848, plain, (![A_191]: (k2_relat_1(k4_relat_1(A_191))=k1_relat_1(A_191) | ~v1_relat_1(A_191))), inference(cnfTransformation, [status(thm)], [f_133])).
% 16.86/9.87  tff(c_60, plain, (![A_72]: (~v1_xboole_0(k2_relat_1(A_72)) | ~v1_relat_1(A_72) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_127])).
% 16.86/9.87  tff(c_4984, plain, (![A_401]: (~v1_xboole_0(k1_relat_1(A_401)) | ~v1_relat_1(k4_relat_1(A_401)) | v1_xboole_0(k4_relat_1(A_401)) | ~v1_relat_1(A_401))), inference(superposition, [status(thm), theory('equality')], [c_848, c_60])).
% 16.86/9.87  tff(c_809, plain, (![A_181]: (r2_hidden('#skF_4'(A_181), A_181) | k1_xboole_0=A_181)), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.86/9.87  tff(c_813, plain, (![A_181]: (~v1_xboole_0(A_181) | k1_xboole_0=A_181)), inference(resolution, [status(thm)], [c_809, c_2])).
% 16.86/9.87  tff(c_21158, plain, (![A_706]: (k4_relat_1(A_706)=k1_xboole_0 | ~v1_xboole_0(k1_relat_1(A_706)) | ~v1_relat_1(k4_relat_1(A_706)) | ~v1_relat_1(A_706))), inference(resolution, [status(thm)], [c_4984, c_813])).
% 16.86/9.87  tff(c_56849, plain, (![A_1098]: (k4_relat_1(A_1098)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_1098)) | ~v1_relat_1(A_1098) | ~v1_xboole_0(A_1098))), inference(resolution, [status(thm)], [c_1733, c_21158])).
% 16.86/9.87  tff(c_56858, plain, (![A_1099]: (k4_relat_1(A_1099)=k1_xboole_0 | ~v1_xboole_0(A_1099) | ~v1_relat_1(A_1099))), inference(resolution, [status(thm)], [c_58, c_56849])).
% 16.86/9.87  tff(c_56952, plain, (![B_1100]: (k4_relat_1(B_1100)=k1_xboole_0 | ~v1_relat_1(B_1100) | k1_xboole_0!=B_1100)), inference(resolution, [status(thm)], [c_1059, c_56858])).
% 16.86/9.87  tff(c_57147, plain, (![B_1104]: (k4_relat_1(B_1104)=k1_xboole_0 | k1_xboole_0!=B_1104)), inference(resolution, [status(thm)], [c_1104, c_56952])).
% 16.86/9.87  tff(c_16, plain, (![A_15]: (r2_hidden('#skF_4'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.86/9.87  tff(c_64, plain, (![A_73]: (k1_relat_1(k4_relat_1(A_73))=k2_relat_1(A_73) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_133])).
% 16.86/9.87  tff(c_10052, plain, (![A_531, C_532]: (~v1_xboole_0(k4_relat_1(A_531)) | ~r2_hidden(C_532, k2_relat_1(A_531)) | ~v1_relat_1(A_531))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1690])).
% 16.86/9.87  tff(c_10151, plain, (![A_533]: (~v1_xboole_0(k4_relat_1(A_533)) | ~v1_relat_1(A_533) | k2_relat_1(A_533)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_10052])).
% 16.86/9.87  tff(c_10168, plain, (![A_534]: (~v1_relat_1(A_534) | k2_relat_1(A_534)=k1_xboole_0 | k4_relat_1(A_534)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1059, c_10151])).
% 16.86/9.87  tff(c_10214, plain, (![B_247]: (k2_relat_1(B_247)=k1_xboole_0 | k4_relat_1(B_247)!=k1_xboole_0 | k1_xboole_0!=B_247)), inference(resolution, [status(thm)], [c_1104, c_10168])).
% 16.86/9.87  tff(c_57272, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_57147, c_10214])).
% 16.86/9.87  tff(c_95, plain, (![A_82, B_83]: (k4_xboole_0(A_82, k2_xboole_0(A_82, B_83))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_83])).
% 16.86/9.87  tff(c_102, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_95])).
% 16.86/9.87  tff(c_166, plain, (![A_104, B_105]: (k3_xboole_0(A_104, B_105)=A_104 | ~r1_tarski(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_81])).
% 16.86/9.87  tff(c_266, plain, (![A_134, B_135]: (k3_xboole_0(A_134, B_135)=A_134 | k4_xboole_0(A_134, B_135)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_166])).
% 16.86/9.87  tff(c_275, plain, (![A_136]: (k3_xboole_0(A_136, A_136)=A_136)), inference(superposition, [status(thm), theory('equality')], [c_102, c_266])).
% 16.86/9.87  tff(c_181, plain, (![A_110, B_111, C_112]: (~r1_xboole_0(A_110, B_111) | ~r2_hidden(C_112, k3_xboole_0(A_110, B_111)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.86/9.87  tff(c_201, plain, (![A_110, B_111]: (~r1_xboole_0(A_110, B_111) | v1_xboole_0(k3_xboole_0(A_110, B_111)))), inference(resolution, [status(thm)], [c_4, c_181])).
% 16.86/9.87  tff(c_330, plain, (![A_140]: (~r1_xboole_0(A_140, A_140) | v1_xboole_0(A_140))), inference(superposition, [status(thm), theory('equality')], [c_275, c_201])).
% 16.86/9.87  tff(c_342, plain, (![B_25]: (v1_xboole_0(B_25) | k4_xboole_0(B_25, B_25)!=B_25)), inference(resolution, [status(thm)], [c_30, c_330])).
% 16.86/9.87  tff(c_346, plain, (![B_25]: (v1_xboole_0(B_25) | k1_xboole_0!=B_25)), inference(demodulation, [status(thm), theory('equality')], [c_102, c_342])).
% 16.86/9.87  tff(c_685, plain, (![C_172, A_173]: (r2_hidden(k4_tarski(C_172, '#skF_11'(A_173, k1_relat_1(A_173), C_172)), A_173) | ~r2_hidden(C_172, k1_relat_1(A_173)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 16.86/9.87  tff(c_706, plain, (![A_174, C_175]: (~v1_xboole_0(A_174) | ~r2_hidden(C_175, k1_relat_1(A_174)))), inference(resolution, [status(thm)], [c_685, c_2])).
% 16.86/9.87  tff(c_745, plain, (![A_176]: (~v1_xboole_0(A_176) | k1_relat_1(A_176)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_706])).
% 16.86/9.87  tff(c_799, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_346, c_745])).
% 16.86/9.87  tff(c_66, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_137])).
% 16.86/9.87  tff(c_83, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_66])).
% 16.86/9.87  tff(c_802, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_799, c_83])).
% 16.86/9.87  tff(c_803, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_66])).
% 16.86/9.87  tff(c_57277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57272, c_803])).
% 16.86/9.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.86/9.87  
% 16.86/9.87  Inference rules
% 16.86/9.87  ----------------------
% 16.86/9.87  #Ref     : 11
% 16.86/9.87  #Sup     : 16308
% 16.86/9.87  #Fact    : 0
% 16.86/9.87  #Define  : 0
% 16.86/9.87  #Split   : 1
% 16.86/9.87  #Chain   : 0
% 16.86/9.87  #Close   : 0
% 16.86/9.87  
% 16.86/9.87  Ordering : KBO
% 16.86/9.87  
% 16.86/9.87  Simplification rules
% 16.86/9.87  ----------------------
% 17.05/9.87  #Subsume      : 6333
% 17.05/9.87  #Demod        : 5893
% 17.05/9.87  #Tautology    : 3533
% 17.05/9.87  #SimpNegUnit  : 107
% 17.05/9.87  #BackRed      : 3
% 17.05/9.87  
% 17.05/9.87  #Partial instantiations: 0
% 17.05/9.87  #Strategies tried      : 1
% 17.05/9.87  
% 17.05/9.87  Timing (in seconds)
% 17.05/9.87  ----------------------
% 17.05/9.87  Preprocessing        : 0.34
% 17.05/9.87  Parsing              : 0.18
% 17.05/9.87  CNF conversion       : 0.03
% 17.05/9.87  Main loop            : 8.76
% 17.05/9.87  Inferencing          : 1.20
% 17.05/9.87  Reduction            : 2.24
% 17.05/9.87  Demodulation         : 1.66
% 17.05/9.88  BG Simplification    : 0.15
% 17.05/9.88  Subsumption          : 4.75
% 17.05/9.88  Abstraction          : 0.23
% 17.05/9.88  MUC search           : 0.00
% 17.05/9.88  Cooper               : 0.00
% 17.05/9.88  Total                : 9.13
% 17.05/9.88  Index Insertion      : 0.00
% 17.05/9.88  Index Deletion       : 0.00
% 17.05/9.88  Index Matching       : 0.00
% 17.05/9.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
