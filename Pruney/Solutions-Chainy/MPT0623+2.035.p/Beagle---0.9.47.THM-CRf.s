%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:10 EST 2020

% Result     : Theorem 8.06s
% Output     : CNFRefutation 8.06s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 517 expanded)
%              Number of leaves         :   39 ( 178 expanded)
%              Depth                    :   15
%              Number of atoms          :  225 (1316 expanded)
%              Number of equality atoms :  112 ( 749 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_126,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_108,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_95,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_75,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_59,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_78,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_108,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_361,plain,(
    ! [A_103,B_104] :
      ( r2_hidden('#skF_4'(A_103,B_104),k3_xboole_0(A_103,B_104))
      | r1_xboole_0(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_412,plain,(
    ! [A_107,B_108] :
      ( r2_hidden('#skF_4'(A_107,B_108),A_107)
      | r1_xboole_0(A_107,B_108) ) ),
    inference(resolution,[status(thm)],[c_361,c_12])).

tff(c_34,plain,(
    ! [A_19] : r1_xboole_0(A_19,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_30,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_258,plain,(
    ! [A_74,B_75,C_76] :
      ( ~ r1_xboole_0(A_74,B_75)
      | ~ r2_hidden(C_76,k3_xboole_0(A_74,B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_265,plain,(
    ! [A_17,C_76] :
      ( ~ r1_xboole_0(A_17,k1_xboole_0)
      | ~ r2_hidden(C_76,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_258])).

tff(c_268,plain,(
    ! [C_76] : ~ r2_hidden(C_76,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_265])).

tff(c_438,plain,(
    ! [B_108] : r1_xboole_0(k1_xboole_0,B_108) ),
    inference(resolution,[status(thm)],[c_412,c_268])).

tff(c_10729,plain,(
    ! [A_4051,B_4052,C_4053] :
      ( r2_hidden('#skF_2'(A_4051,B_4052,C_4053),B_4052)
      | r2_hidden('#skF_3'(A_4051,B_4052,C_4053),C_4053)
      | k3_xboole_0(A_4051,B_4052) = C_4053 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10750,plain,(
    ! [A_4051,C_4053] :
      ( r2_hidden('#skF_3'(A_4051,k1_xboole_0,C_4053),C_4053)
      | k3_xboole_0(A_4051,k1_xboole_0) = C_4053 ) ),
    inference(resolution,[status(thm)],[c_10729,c_268])).

tff(c_10797,plain,(
    ! [A_4054,C_4055] :
      ( r2_hidden('#skF_3'(A_4054,k1_xboole_0,C_4055),C_4055)
      | k1_xboole_0 = C_4055 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_10750])).

tff(c_28,plain,(
    ! [A_12,B_13,C_16] :
      ( ~ r1_xboole_0(A_12,B_13)
      | ~ r2_hidden(C_16,k3_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10831,plain,(
    ! [A_4056,B_4057] :
      ( ~ r1_xboole_0(A_4056,B_4057)
      | k3_xboole_0(A_4056,B_4057) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10797,c_28])).

tff(c_10854,plain,(
    ! [B_108] : k3_xboole_0(k1_xboole_0,B_108) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_438,c_10831])).

tff(c_11074,plain,(
    ! [A_4067,B_4068,C_4069] :
      ( r2_hidden('#skF_2'(A_4067,B_4068,C_4069),A_4067)
      | r2_hidden('#skF_3'(A_4067,B_4068,C_4069),C_4069)
      | k3_xboole_0(A_4067,B_4068) = C_4069 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11095,plain,(
    ! [B_4068,C_4069] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_4068,C_4069),C_4069)
      | k3_xboole_0(k1_xboole_0,B_4068) = C_4069 ) ),
    inference(resolution,[status(thm)],[c_11074,c_268])).

tff(c_11136,plain,(
    ! [B_4068,C_4069] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_4068,C_4069),C_4069)
      | k1_xboole_0 = C_4069 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10854,c_11095])).

tff(c_70,plain,(
    ! [A_36,B_40] :
      ( k1_relat_1('#skF_8'(A_36,B_40)) = A_36
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_72,plain,(
    ! [A_36,B_40] :
      ( v1_funct_1('#skF_8'(A_36,B_40))
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_74,plain,(
    ! [A_36,B_40] :
      ( v1_relat_1('#skF_8'(A_36,B_40))
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_234,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_1'(A_69,B_70),A_69)
      | r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    ! [C_24,A_20] :
      ( C_24 = A_20
      | ~ r2_hidden(C_24,k1_tarski(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_336,plain,(
    ! [A_99,B_100] :
      ( '#skF_1'(k1_tarski(A_99),B_100) = A_99
      | r1_tarski(k1_tarski(A_99),B_100) ) ),
    inference(resolution,[status(thm)],[c_234,c_36])).

tff(c_277,plain,(
    ! [A_78,B_79] :
      ( k2_relat_1('#skF_8'(A_78,B_79)) = k1_tarski(B_79)
      | k1_xboole_0 = A_78 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_76,plain,(
    ! [C_43] :
      ( ~ r1_tarski(k2_relat_1(C_43),'#skF_9')
      | k1_relat_1(C_43) != '#skF_10'
      | ~ v1_funct_1(C_43)
      | ~ v1_relat_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_283,plain,(
    ! [B_79,A_78] :
      ( ~ r1_tarski(k1_tarski(B_79),'#skF_9')
      | k1_relat_1('#skF_8'(A_78,B_79)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_78,B_79))
      | ~ v1_relat_1('#skF_8'(A_78,B_79))
      | k1_xboole_0 = A_78 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_76])).

tff(c_442,plain,(
    ! [A_110,A_111] :
      ( k1_relat_1('#skF_8'(A_110,A_111)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_110,A_111))
      | ~ v1_relat_1('#skF_8'(A_110,A_111))
      | k1_xboole_0 = A_110
      | '#skF_1'(k1_tarski(A_111),'#skF_9') = A_111 ) ),
    inference(resolution,[status(thm)],[c_336,c_283])).

tff(c_541,plain,(
    ! [A_133,B_134] :
      ( k1_relat_1('#skF_8'(A_133,B_134)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_133,B_134))
      | '#skF_1'(k1_tarski(B_134),'#skF_9') = B_134
      | k1_xboole_0 = A_133 ) ),
    inference(resolution,[status(thm)],[c_74,c_442])).

tff(c_12334,plain,(
    ! [A_4138,B_4139] :
      ( k1_relat_1('#skF_8'(A_4138,B_4139)) != '#skF_10'
      | '#skF_1'(k1_tarski(B_4139),'#skF_9') = B_4139
      | k1_xboole_0 = A_4138 ) ),
    inference(resolution,[status(thm)],[c_72,c_541])).

tff(c_12337,plain,(
    ! [A_36,B_40] :
      ( A_36 != '#skF_10'
      | '#skF_1'(k1_tarski(B_40),'#skF_9') = B_40
      | k1_xboole_0 = A_36
      | k1_xboole_0 = A_36 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_12334])).

tff(c_14052,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_12337])).

tff(c_62,plain,(
    ! [A_30] : k1_relat_1('#skF_7'(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_66,plain,(
    ! [A_30] : v1_relat_1('#skF_7'(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_154,plain,(
    ! [A_64] :
      ( k1_relat_1(A_64) != k1_xboole_0
      | k1_xboole_0 = A_64
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_160,plain,(
    ! [A_30] :
      ( k1_relat_1('#skF_7'(A_30)) != k1_xboole_0
      | '#skF_7'(A_30) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_66,c_154])).

tff(c_171,plain,(
    ! [A_66] :
      ( k1_xboole_0 != A_66
      | '#skF_7'(A_66) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_160])).

tff(c_181,plain,(
    ! [A_66] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_66 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_66])).

tff(c_200,plain,(
    ! [A_66] : k1_xboole_0 != A_66 ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_30])).

tff(c_217,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_64,plain,(
    ! [A_30] : v1_funct_1('#skF_7'(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_179,plain,(
    ! [A_66] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_66 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_64])).

tff(c_188,plain,(
    ! [A_66] : k1_xboole_0 != A_66 ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_30])).

tff(c_199,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_54,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,A_18) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_164,plain,(
    ! [C_65] :
      ( ~ r1_tarski(k2_relat_1(C_65),'#skF_9')
      | k1_relat_1(C_65) != '#skF_10'
      | ~ v1_funct_1(C_65)
      | ~ v1_relat_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_167,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_9')
    | k1_relat_1(k1_xboole_0) != '#skF_10'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_164])).

tff(c_169,plain,
    ( k1_xboole_0 != '#skF_10'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_32,c_167])).

tff(c_233,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_199,c_169])).

tff(c_14117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14052,c_233])).

tff(c_14120,plain,(
    ! [B_4202] : '#skF_1'(k1_tarski(B_4202),'#skF_9') = B_4202 ),
    inference(splitRight,[status(thm)],[c_12337])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14148,plain,(
    ! [B_4203] :
      ( ~ r2_hidden(B_4203,'#skF_9')
      | r1_tarski(k1_tarski(B_4203),'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14120,c_4])).

tff(c_14542,plain,(
    ! [A_4218,B_4219] :
      ( k1_relat_1('#skF_8'(A_4218,B_4219)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_4218,B_4219))
      | ~ v1_relat_1('#skF_8'(A_4218,B_4219))
      | k1_xboole_0 = A_4218
      | ~ r2_hidden(B_4219,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_14148,c_283])).

tff(c_15240,plain,(
    ! [A_4238,B_4239] :
      ( k1_relat_1('#skF_8'(A_4238,B_4239)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_4238,B_4239))
      | ~ r2_hidden(B_4239,'#skF_9')
      | k1_xboole_0 = A_4238 ) ),
    inference(resolution,[status(thm)],[c_74,c_14542])).

tff(c_15700,plain,(
    ! [A_4258,B_4259] :
      ( k1_relat_1('#skF_8'(A_4258,B_4259)) != '#skF_10'
      | ~ r2_hidden(B_4259,'#skF_9')
      | k1_xboole_0 = A_4258 ) ),
    inference(resolution,[status(thm)],[c_72,c_15240])).

tff(c_15703,plain,(
    ! [A_36,B_40] :
      ( A_36 != '#skF_10'
      | ~ r2_hidden(B_40,'#skF_9')
      | k1_xboole_0 = A_36
      | k1_xboole_0 = A_36 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_15700])).

tff(c_16236,plain,(
    ! [B_4279] : ~ r2_hidden(B_4279,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_15703])).

tff(c_16284,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_11136,c_16236])).

tff(c_16339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_16284])).

tff(c_16341,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_15703])).

tff(c_16418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16341,c_233])).

tff(c_16420,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_16419,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_16430,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16420,c_16419])).

tff(c_16424,plain,(
    k1_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16419,c_16419,c_54])).

tff(c_16446,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16430,c_16430,c_16424])).

tff(c_16423,plain,(
    ! [A_18] : r1_tarski('#skF_10',A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16419,c_32])).

tff(c_16451,plain,(
    ! [A_18] : r1_tarski('#skF_9',A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16430,c_16423])).

tff(c_16422,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16419,c_16419,c_52])).

tff(c_16439,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16430,c_16430,c_16422])).

tff(c_16454,plain,(
    ! [C_4282] :
      ( ~ r1_tarski(k2_relat_1(C_4282),'#skF_9')
      | k1_relat_1(C_4282) != '#skF_9'
      | ~ v1_funct_1(C_4282)
      | ~ v1_relat_1(C_4282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16430,c_76])).

tff(c_16457,plain,
    ( ~ r1_tarski('#skF_9','#skF_9')
    | k1_relat_1('#skF_9') != '#skF_9'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_16439,c_16454])).

tff(c_16459,plain,
    ( ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16446,c_16451,c_16457])).

tff(c_16468,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_16459])).

tff(c_58,plain,(
    ! [A_29] :
      ( k1_relat_1(A_29) != k1_xboole_0
      | k1_xboole_0 = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_16480,plain,(
    ! [A_4290] :
      ( k1_relat_1(A_4290) != '#skF_9'
      | A_4290 = '#skF_9'
      | ~ v1_relat_1(A_4290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16420,c_16420,c_58])).

tff(c_16486,plain,(
    ! [A_30] :
      ( k1_relat_1('#skF_7'(A_30)) != '#skF_9'
      | '#skF_7'(A_30) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_66,c_16480])).

tff(c_16491,plain,(
    ! [A_4291] :
      ( A_4291 != '#skF_9'
      | '#skF_7'(A_4291) = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_16486])).

tff(c_16501,plain,(
    ! [A_4291] :
      ( v1_relat_1('#skF_9')
      | A_4291 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16491,c_66])).

tff(c_16507,plain,(
    ! [A_4291] : A_4291 != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_16468,c_16501])).

tff(c_16421,plain,(
    ! [A_17] : k3_xboole_0(A_17,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16419,c_16419,c_30])).

tff(c_16460,plain,(
    ! [A_17] : k3_xboole_0(A_17,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16430,c_16430,c_16421])).

tff(c_16518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16507,c_16460])).

tff(c_16519,plain,(
    ~ v1_funct_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_16459])).

tff(c_16569,plain,(
    ! [A_4303] :
      ( k1_relat_1(A_4303) != '#skF_9'
      | A_4303 = '#skF_9'
      | ~ v1_relat_1(A_4303) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16420,c_16420,c_58])).

tff(c_16578,plain,(
    ! [A_30] :
      ( k1_relat_1('#skF_7'(A_30)) != '#skF_9'
      | '#skF_7'(A_30) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_66,c_16569])).

tff(c_16587,plain,(
    ! [A_4304] :
      ( A_4304 != '#skF_9'
      | '#skF_7'(A_4304) = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_16578])).

tff(c_16595,plain,(
    ! [A_4304] :
      ( v1_funct_1('#skF_9')
      | A_4304 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16587,c_64])).

tff(c_16603,plain,(
    ! [A_4304] : A_4304 != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_16519,c_16595])).

tff(c_16617,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16603,c_16460])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.06/2.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.06/2.82  
% 8.06/2.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.06/2.82  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 8.06/2.82  
% 8.06/2.82  %Foreground sorts:
% 8.06/2.82  
% 8.06/2.82  
% 8.06/2.82  %Background operators:
% 8.06/2.82  
% 8.06/2.82  
% 8.06/2.82  %Foreground operators:
% 8.06/2.82  tff('#skF_7', type, '#skF_7': $i > $i).
% 8.06/2.82  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.06/2.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.06/2.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.06/2.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.06/2.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.06/2.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.06/2.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.06/2.82  tff('#skF_10', type, '#skF_10': $i).
% 8.06/2.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.06/2.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.06/2.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.06/2.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.06/2.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.06/2.82  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 8.06/2.82  tff('#skF_9', type, '#skF_9': $i).
% 8.06/2.82  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.06/2.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.06/2.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.06/2.82  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.06/2.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.06/2.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.06/2.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.06/2.82  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.06/2.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.06/2.82  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.06/2.82  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.06/2.82  
% 8.06/2.84  tff(f_126, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 8.06/2.84  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.06/2.84  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 8.06/2.84  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.06/2.84  tff(f_57, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 8.06/2.84  tff(f_108, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 8.06/2.84  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.06/2.84  tff(f_68, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 8.06/2.84  tff(f_95, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 8.06/2.84  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 8.06/2.84  tff(f_75, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 8.06/2.84  tff(f_59, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.06/2.84  tff(c_78, plain, (k1_xboole_0='#skF_10' | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.06/2.84  tff(c_108, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_78])).
% 8.06/2.84  tff(c_361, plain, (![A_103, B_104]: (r2_hidden('#skF_4'(A_103, B_104), k3_xboole_0(A_103, B_104)) | r1_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.06/2.84  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.06/2.84  tff(c_412, plain, (![A_107, B_108]: (r2_hidden('#skF_4'(A_107, B_108), A_107) | r1_xboole_0(A_107, B_108))), inference(resolution, [status(thm)], [c_361, c_12])).
% 8.06/2.84  tff(c_34, plain, (![A_19]: (r1_xboole_0(A_19, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.06/2.84  tff(c_30, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.06/2.84  tff(c_258, plain, (![A_74, B_75, C_76]: (~r1_xboole_0(A_74, B_75) | ~r2_hidden(C_76, k3_xboole_0(A_74, B_75)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.06/2.84  tff(c_265, plain, (![A_17, C_76]: (~r1_xboole_0(A_17, k1_xboole_0) | ~r2_hidden(C_76, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_258])).
% 8.06/2.84  tff(c_268, plain, (![C_76]: (~r2_hidden(C_76, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_265])).
% 8.06/2.84  tff(c_438, plain, (![B_108]: (r1_xboole_0(k1_xboole_0, B_108))), inference(resolution, [status(thm)], [c_412, c_268])).
% 8.06/2.84  tff(c_10729, plain, (![A_4051, B_4052, C_4053]: (r2_hidden('#skF_2'(A_4051, B_4052, C_4053), B_4052) | r2_hidden('#skF_3'(A_4051, B_4052, C_4053), C_4053) | k3_xboole_0(A_4051, B_4052)=C_4053)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.06/2.84  tff(c_10750, plain, (![A_4051, C_4053]: (r2_hidden('#skF_3'(A_4051, k1_xboole_0, C_4053), C_4053) | k3_xboole_0(A_4051, k1_xboole_0)=C_4053)), inference(resolution, [status(thm)], [c_10729, c_268])).
% 8.06/2.84  tff(c_10797, plain, (![A_4054, C_4055]: (r2_hidden('#skF_3'(A_4054, k1_xboole_0, C_4055), C_4055) | k1_xboole_0=C_4055)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_10750])).
% 8.06/2.84  tff(c_28, plain, (![A_12, B_13, C_16]: (~r1_xboole_0(A_12, B_13) | ~r2_hidden(C_16, k3_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.06/2.84  tff(c_10831, plain, (![A_4056, B_4057]: (~r1_xboole_0(A_4056, B_4057) | k3_xboole_0(A_4056, B_4057)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10797, c_28])).
% 8.06/2.84  tff(c_10854, plain, (![B_108]: (k3_xboole_0(k1_xboole_0, B_108)=k1_xboole_0)), inference(resolution, [status(thm)], [c_438, c_10831])).
% 8.06/2.84  tff(c_11074, plain, (![A_4067, B_4068, C_4069]: (r2_hidden('#skF_2'(A_4067, B_4068, C_4069), A_4067) | r2_hidden('#skF_3'(A_4067, B_4068, C_4069), C_4069) | k3_xboole_0(A_4067, B_4068)=C_4069)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.06/2.84  tff(c_11095, plain, (![B_4068, C_4069]: (r2_hidden('#skF_3'(k1_xboole_0, B_4068, C_4069), C_4069) | k3_xboole_0(k1_xboole_0, B_4068)=C_4069)), inference(resolution, [status(thm)], [c_11074, c_268])).
% 8.06/2.84  tff(c_11136, plain, (![B_4068, C_4069]: (r2_hidden('#skF_3'(k1_xboole_0, B_4068, C_4069), C_4069) | k1_xboole_0=C_4069)), inference(demodulation, [status(thm), theory('equality')], [c_10854, c_11095])).
% 8.06/2.84  tff(c_70, plain, (![A_36, B_40]: (k1_relat_1('#skF_8'(A_36, B_40))=A_36 | k1_xboole_0=A_36)), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.06/2.84  tff(c_72, plain, (![A_36, B_40]: (v1_funct_1('#skF_8'(A_36, B_40)) | k1_xboole_0=A_36)), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.06/2.84  tff(c_74, plain, (![A_36, B_40]: (v1_relat_1('#skF_8'(A_36, B_40)) | k1_xboole_0=A_36)), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.06/2.84  tff(c_234, plain, (![A_69, B_70]: (r2_hidden('#skF_1'(A_69, B_70), A_69) | r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.06/2.84  tff(c_36, plain, (![C_24, A_20]: (C_24=A_20 | ~r2_hidden(C_24, k1_tarski(A_20)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.06/2.84  tff(c_336, plain, (![A_99, B_100]: ('#skF_1'(k1_tarski(A_99), B_100)=A_99 | r1_tarski(k1_tarski(A_99), B_100))), inference(resolution, [status(thm)], [c_234, c_36])).
% 8.06/2.84  tff(c_277, plain, (![A_78, B_79]: (k2_relat_1('#skF_8'(A_78, B_79))=k1_tarski(B_79) | k1_xboole_0=A_78)), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.06/2.84  tff(c_76, plain, (![C_43]: (~r1_tarski(k2_relat_1(C_43), '#skF_9') | k1_relat_1(C_43)!='#skF_10' | ~v1_funct_1(C_43) | ~v1_relat_1(C_43))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.06/2.84  tff(c_283, plain, (![B_79, A_78]: (~r1_tarski(k1_tarski(B_79), '#skF_9') | k1_relat_1('#skF_8'(A_78, B_79))!='#skF_10' | ~v1_funct_1('#skF_8'(A_78, B_79)) | ~v1_relat_1('#skF_8'(A_78, B_79)) | k1_xboole_0=A_78)), inference(superposition, [status(thm), theory('equality')], [c_277, c_76])).
% 8.06/2.84  tff(c_442, plain, (![A_110, A_111]: (k1_relat_1('#skF_8'(A_110, A_111))!='#skF_10' | ~v1_funct_1('#skF_8'(A_110, A_111)) | ~v1_relat_1('#skF_8'(A_110, A_111)) | k1_xboole_0=A_110 | '#skF_1'(k1_tarski(A_111), '#skF_9')=A_111)), inference(resolution, [status(thm)], [c_336, c_283])).
% 8.06/2.84  tff(c_541, plain, (![A_133, B_134]: (k1_relat_1('#skF_8'(A_133, B_134))!='#skF_10' | ~v1_funct_1('#skF_8'(A_133, B_134)) | '#skF_1'(k1_tarski(B_134), '#skF_9')=B_134 | k1_xboole_0=A_133)), inference(resolution, [status(thm)], [c_74, c_442])).
% 8.06/2.84  tff(c_12334, plain, (![A_4138, B_4139]: (k1_relat_1('#skF_8'(A_4138, B_4139))!='#skF_10' | '#skF_1'(k1_tarski(B_4139), '#skF_9')=B_4139 | k1_xboole_0=A_4138)), inference(resolution, [status(thm)], [c_72, c_541])).
% 8.06/2.84  tff(c_12337, plain, (![A_36, B_40]: (A_36!='#skF_10' | '#skF_1'(k1_tarski(B_40), '#skF_9')=B_40 | k1_xboole_0=A_36 | k1_xboole_0=A_36)), inference(superposition, [status(thm), theory('equality')], [c_70, c_12334])).
% 8.06/2.84  tff(c_14052, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_12337])).
% 8.06/2.84  tff(c_62, plain, (![A_30]: (k1_relat_1('#skF_7'(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.06/2.84  tff(c_66, plain, (![A_30]: (v1_relat_1('#skF_7'(A_30)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.06/2.84  tff(c_154, plain, (![A_64]: (k1_relat_1(A_64)!=k1_xboole_0 | k1_xboole_0=A_64 | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.06/2.84  tff(c_160, plain, (![A_30]: (k1_relat_1('#skF_7'(A_30))!=k1_xboole_0 | '#skF_7'(A_30)=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_154])).
% 8.06/2.84  tff(c_171, plain, (![A_66]: (k1_xboole_0!=A_66 | '#skF_7'(A_66)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_160])).
% 8.06/2.84  tff(c_181, plain, (![A_66]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_66)), inference(superposition, [status(thm), theory('equality')], [c_171, c_66])).
% 8.06/2.84  tff(c_200, plain, (![A_66]: (k1_xboole_0!=A_66)), inference(splitLeft, [status(thm)], [c_181])).
% 8.06/2.84  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_200, c_30])).
% 8.06/2.84  tff(c_217, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_181])).
% 8.06/2.84  tff(c_64, plain, (![A_30]: (v1_funct_1('#skF_7'(A_30)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.06/2.84  tff(c_179, plain, (![A_66]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=A_66)), inference(superposition, [status(thm), theory('equality')], [c_171, c_64])).
% 8.06/2.84  tff(c_188, plain, (![A_66]: (k1_xboole_0!=A_66)), inference(splitLeft, [status(thm)], [c_179])).
% 8.06/2.84  tff(c_198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_30])).
% 8.06/2.84  tff(c_199, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_179])).
% 8.06/2.84  tff(c_54, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.06/2.84  tff(c_32, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.06/2.84  tff(c_52, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.06/2.84  tff(c_164, plain, (![C_65]: (~r1_tarski(k2_relat_1(C_65), '#skF_9') | k1_relat_1(C_65)!='#skF_10' | ~v1_funct_1(C_65) | ~v1_relat_1(C_65))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.06/2.84  tff(c_167, plain, (~r1_tarski(k1_xboole_0, '#skF_9') | k1_relat_1(k1_xboole_0)!='#skF_10' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_52, c_164])).
% 8.06/2.84  tff(c_169, plain, (k1_xboole_0!='#skF_10' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_32, c_167])).
% 8.06/2.84  tff(c_233, plain, (k1_xboole_0!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_217, c_199, c_169])).
% 8.06/2.84  tff(c_14117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14052, c_233])).
% 8.06/2.84  tff(c_14120, plain, (![B_4202]: ('#skF_1'(k1_tarski(B_4202), '#skF_9')=B_4202)), inference(splitRight, [status(thm)], [c_12337])).
% 8.06/2.84  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.06/2.84  tff(c_14148, plain, (![B_4203]: (~r2_hidden(B_4203, '#skF_9') | r1_tarski(k1_tarski(B_4203), '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_14120, c_4])).
% 8.06/2.84  tff(c_14542, plain, (![A_4218, B_4219]: (k1_relat_1('#skF_8'(A_4218, B_4219))!='#skF_10' | ~v1_funct_1('#skF_8'(A_4218, B_4219)) | ~v1_relat_1('#skF_8'(A_4218, B_4219)) | k1_xboole_0=A_4218 | ~r2_hidden(B_4219, '#skF_9'))), inference(resolution, [status(thm)], [c_14148, c_283])).
% 8.06/2.84  tff(c_15240, plain, (![A_4238, B_4239]: (k1_relat_1('#skF_8'(A_4238, B_4239))!='#skF_10' | ~v1_funct_1('#skF_8'(A_4238, B_4239)) | ~r2_hidden(B_4239, '#skF_9') | k1_xboole_0=A_4238)), inference(resolution, [status(thm)], [c_74, c_14542])).
% 8.06/2.84  tff(c_15700, plain, (![A_4258, B_4259]: (k1_relat_1('#skF_8'(A_4258, B_4259))!='#skF_10' | ~r2_hidden(B_4259, '#skF_9') | k1_xboole_0=A_4258)), inference(resolution, [status(thm)], [c_72, c_15240])).
% 8.06/2.84  tff(c_15703, plain, (![A_36, B_40]: (A_36!='#skF_10' | ~r2_hidden(B_40, '#skF_9') | k1_xboole_0=A_36 | k1_xboole_0=A_36)), inference(superposition, [status(thm), theory('equality')], [c_70, c_15700])).
% 8.06/2.84  tff(c_16236, plain, (![B_4279]: (~r2_hidden(B_4279, '#skF_9'))), inference(splitLeft, [status(thm)], [c_15703])).
% 8.06/2.84  tff(c_16284, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_11136, c_16236])).
% 8.06/2.84  tff(c_16339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_16284])).
% 8.06/2.84  tff(c_16341, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_15703])).
% 8.06/2.84  tff(c_16418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16341, c_233])).
% 8.06/2.84  tff(c_16420, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_78])).
% 8.06/2.84  tff(c_16419, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_78])).
% 8.06/2.84  tff(c_16430, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_16420, c_16419])).
% 8.06/2.84  tff(c_16424, plain, (k1_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_16419, c_16419, c_54])).
% 8.06/2.84  tff(c_16446, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_16430, c_16430, c_16424])).
% 8.06/2.84  tff(c_16423, plain, (![A_18]: (r1_tarski('#skF_10', A_18))), inference(demodulation, [status(thm), theory('equality')], [c_16419, c_32])).
% 8.06/2.84  tff(c_16451, plain, (![A_18]: (r1_tarski('#skF_9', A_18))), inference(demodulation, [status(thm), theory('equality')], [c_16430, c_16423])).
% 8.06/2.84  tff(c_16422, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_16419, c_16419, c_52])).
% 8.06/2.84  tff(c_16439, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_16430, c_16430, c_16422])).
% 8.06/2.84  tff(c_16454, plain, (![C_4282]: (~r1_tarski(k2_relat_1(C_4282), '#skF_9') | k1_relat_1(C_4282)!='#skF_9' | ~v1_funct_1(C_4282) | ~v1_relat_1(C_4282))), inference(demodulation, [status(thm), theory('equality')], [c_16430, c_76])).
% 8.06/2.84  tff(c_16457, plain, (~r1_tarski('#skF_9', '#skF_9') | k1_relat_1('#skF_9')!='#skF_9' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_16439, c_16454])).
% 8.06/2.84  tff(c_16459, plain, (~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_16446, c_16451, c_16457])).
% 8.06/2.84  tff(c_16468, plain, (~v1_relat_1('#skF_9')), inference(splitLeft, [status(thm)], [c_16459])).
% 8.06/2.84  tff(c_58, plain, (![A_29]: (k1_relat_1(A_29)!=k1_xboole_0 | k1_xboole_0=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.06/2.84  tff(c_16480, plain, (![A_4290]: (k1_relat_1(A_4290)!='#skF_9' | A_4290='#skF_9' | ~v1_relat_1(A_4290))), inference(demodulation, [status(thm), theory('equality')], [c_16420, c_16420, c_58])).
% 8.06/2.84  tff(c_16486, plain, (![A_30]: (k1_relat_1('#skF_7'(A_30))!='#skF_9' | '#skF_7'(A_30)='#skF_9')), inference(resolution, [status(thm)], [c_66, c_16480])).
% 8.06/2.84  tff(c_16491, plain, (![A_4291]: (A_4291!='#skF_9' | '#skF_7'(A_4291)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_16486])).
% 8.06/2.84  tff(c_16501, plain, (![A_4291]: (v1_relat_1('#skF_9') | A_4291!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_16491, c_66])).
% 8.06/2.84  tff(c_16507, plain, (![A_4291]: (A_4291!='#skF_9')), inference(negUnitSimplification, [status(thm)], [c_16468, c_16501])).
% 8.06/2.84  tff(c_16421, plain, (![A_17]: (k3_xboole_0(A_17, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_16419, c_16419, c_30])).
% 8.06/2.84  tff(c_16460, plain, (![A_17]: (k3_xboole_0(A_17, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_16430, c_16430, c_16421])).
% 8.06/2.84  tff(c_16518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16507, c_16460])).
% 8.06/2.84  tff(c_16519, plain, (~v1_funct_1('#skF_9')), inference(splitRight, [status(thm)], [c_16459])).
% 8.06/2.84  tff(c_16569, plain, (![A_4303]: (k1_relat_1(A_4303)!='#skF_9' | A_4303='#skF_9' | ~v1_relat_1(A_4303))), inference(demodulation, [status(thm), theory('equality')], [c_16420, c_16420, c_58])).
% 8.06/2.84  tff(c_16578, plain, (![A_30]: (k1_relat_1('#skF_7'(A_30))!='#skF_9' | '#skF_7'(A_30)='#skF_9')), inference(resolution, [status(thm)], [c_66, c_16569])).
% 8.06/2.84  tff(c_16587, plain, (![A_4304]: (A_4304!='#skF_9' | '#skF_7'(A_4304)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_16578])).
% 8.06/2.84  tff(c_16595, plain, (![A_4304]: (v1_funct_1('#skF_9') | A_4304!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_16587, c_64])).
% 8.06/2.84  tff(c_16603, plain, (![A_4304]: (A_4304!='#skF_9')), inference(negUnitSimplification, [status(thm)], [c_16519, c_16595])).
% 8.06/2.84  tff(c_16617, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16603, c_16460])).
% 8.06/2.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.06/2.84  
% 8.06/2.84  Inference rules
% 8.06/2.84  ----------------------
% 8.06/2.84  #Ref     : 0
% 8.06/2.84  #Sup     : 3115
% 8.06/2.84  #Fact    : 2
% 8.06/2.84  #Define  : 0
% 8.06/2.84  #Split   : 6
% 8.06/2.84  #Chain   : 0
% 8.06/2.84  #Close   : 0
% 8.06/2.84  
% 8.06/2.84  Ordering : KBO
% 8.06/2.84  
% 8.06/2.84  Simplification rules
% 8.06/2.84  ----------------------
% 8.06/2.84  #Subsume      : 1026
% 8.06/2.84  #Demod        : 1054
% 8.06/2.84  #Tautology    : 619
% 8.06/2.84  #SimpNegUnit  : 90
% 8.06/2.84  #BackRed      : 171
% 8.06/2.84  
% 8.06/2.84  #Partial instantiations: 2432
% 8.06/2.84  #Strategies tried      : 1
% 8.06/2.84  
% 8.06/2.84  Timing (in seconds)
% 8.06/2.84  ----------------------
% 8.45/2.85  Preprocessing        : 0.32
% 8.45/2.85  Parsing              : 0.16
% 8.45/2.85  CNF conversion       : 0.03
% 8.45/2.85  Main loop            : 1.74
% 8.45/2.85  Inferencing          : 0.56
% 8.45/2.85  Reduction            : 0.53
% 8.45/2.85  Demodulation         : 0.36
% 8.45/2.85  BG Simplification    : 0.09
% 8.45/2.85  Subsumption          : 0.41
% 8.45/2.85  Abstraction          : 0.09
% 8.45/2.85  MUC search           : 0.00
% 8.45/2.85  Cooper               : 0.00
% 8.45/2.85  Total                : 2.11
% 8.45/2.85  Index Insertion      : 0.00
% 8.45/2.85  Index Deletion       : 0.00
% 8.45/2.85  Index Matching       : 0.00
% 8.45/2.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
