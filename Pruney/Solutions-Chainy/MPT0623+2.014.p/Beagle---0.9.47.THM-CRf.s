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
% DateTime   : Thu Dec  3 10:03:08 EST 2020

% Result     : Theorem 4.73s
% Output     : CNFRefutation 5.07s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 501 expanded)
%              Number of leaves         :   36 ( 172 expanded)
%              Depth                    :   16
%              Number of atoms          :  215 (1257 expanded)
%              Number of equality atoms :  123 ( 728 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff(f_136,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_118,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_97,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(c_86,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_98,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_2699,plain,(
    ! [A_3995,B_3996,C_3997] :
      ( r2_hidden('#skF_2'(A_3995,B_3996,C_3997),B_3996)
      | r2_hidden('#skF_3'(A_3995,B_3996,C_3997),C_3997)
      | k3_xboole_0(A_3995,B_3996) = C_3997 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),C_10)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k3_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2740,plain,(
    ! [A_3995,B_3996] :
      ( r2_hidden('#skF_3'(A_3995,B_3996,B_3996),B_3996)
      | k3_xboole_0(A_3995,B_3996) = B_3996 ) ),
    inference(resolution,[status(thm)],[c_2699,c_22])).

tff(c_78,plain,(
    ! [A_40,B_44] :
      ( k1_relat_1('#skF_8'(A_40,B_44)) = A_40
      | k1_xboole_0 = A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_80,plain,(
    ! [A_40,B_44] :
      ( v1_funct_1('#skF_8'(A_40,B_44))
      | k1_xboole_0 = A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_82,plain,(
    ! [A_40,B_44] :
      ( v1_relat_1('#skF_8'(A_40,B_44))
      | k1_xboole_0 = A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_471,plain,(
    ! [A_96,B_97] :
      ( r2_hidden('#skF_1'(A_96,B_97),A_96)
      | r1_tarski(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_32,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_653,plain,(
    ! [A_127,B_128] :
      ( '#skF_1'(k1_tarski(A_127),B_128) = A_127
      | r1_tarski(k1_tarski(A_127),B_128) ) ),
    inference(resolution,[status(thm)],[c_471,c_32])).

tff(c_525,plain,(
    ! [A_103,B_104] :
      ( k2_relat_1('#skF_8'(A_103,B_104)) = k1_tarski(B_104)
      | k1_xboole_0 = A_103 ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_84,plain,(
    ! [C_47] :
      ( ~ r1_tarski(k2_relat_1(C_47),'#skF_9')
      | k1_relat_1(C_47) != '#skF_10'
      | ~ v1_funct_1(C_47)
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_531,plain,(
    ! [B_104,A_103] :
      ( ~ r1_tarski(k1_tarski(B_104),'#skF_9')
      | k1_relat_1('#skF_8'(A_103,B_104)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_103,B_104))
      | ~ v1_relat_1('#skF_8'(A_103,B_104))
      | k1_xboole_0 = A_103 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_525,c_84])).

tff(c_688,plain,(
    ! [A_133,A_134] :
      ( k1_relat_1('#skF_8'(A_133,A_134)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_133,A_134))
      | ~ v1_relat_1('#skF_8'(A_133,A_134))
      | k1_xboole_0 = A_133
      | '#skF_1'(k1_tarski(A_134),'#skF_9') = A_134 ) ),
    inference(resolution,[status(thm)],[c_653,c_531])).

tff(c_2820,plain,(
    ! [A_4004,B_4005] :
      ( k1_relat_1('#skF_8'(A_4004,B_4005)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_4004,B_4005))
      | '#skF_1'(k1_tarski(B_4005),'#skF_9') = B_4005
      | k1_xboole_0 = A_4004 ) ),
    inference(resolution,[status(thm)],[c_82,c_688])).

tff(c_2936,plain,(
    ! [A_4021,B_4022] :
      ( k1_relat_1('#skF_8'(A_4021,B_4022)) != '#skF_10'
      | '#skF_1'(k1_tarski(B_4022),'#skF_9') = B_4022
      | k1_xboole_0 = A_4021 ) ),
    inference(resolution,[status(thm)],[c_80,c_2820])).

tff(c_2939,plain,(
    ! [A_40,B_44] :
      ( A_40 != '#skF_10'
      | '#skF_1'(k1_tarski(B_44),'#skF_9') = B_44
      | k1_xboole_0 = A_40
      | k1_xboole_0 = A_40 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_2936])).

tff(c_3161,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_2939])).

tff(c_48,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_107,plain,(
    ! [C_54] :
      ( ~ r1_tarski(k2_relat_1(C_54),'#skF_9')
      | k1_relat_1(C_54) != '#skF_10'
      | ~ v1_funct_1(C_54)
      | ~ v1_relat_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_110,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_9')
    | k1_relat_1(k1_xboole_0) != '#skF_10'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_107])).

tff(c_112,plain,
    ( k1_xboole_0 != '#skF_10'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_30,c_110])).

tff(c_216,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_68,plain,(
    ! [A_32] : k1_relat_1('#skF_7'(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_72,plain,(
    ! [A_32] : v1_relat_1('#skF_7'(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_235,plain,(
    ! [A_72] :
      ( k1_relat_1(A_72) != k1_xboole_0
      | k1_xboole_0 = A_72
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_244,plain,(
    ! [A_32] :
      ( k1_relat_1('#skF_7'(A_32)) != k1_xboole_0
      | '#skF_7'(A_32) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_72,c_235])).

tff(c_251,plain,(
    ! [A_73] :
      ( k1_xboole_0 != A_73
      | '#skF_7'(A_73) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_244])).

tff(c_261,plain,(
    ! [A_73] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_73 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_72])).

tff(c_267,plain,(
    ! [A_73] : k1_xboole_0 != A_73 ),
    inference(negUnitSimplification,[status(thm)],[c_216,c_261])).

tff(c_134,plain,(
    ! [B_63,A_64] : k3_xboole_0(B_63,A_64) = k3_xboole_0(A_64,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_150,plain,(
    ! [A_64] : k3_xboole_0(k1_xboole_0,A_64) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_28])).

tff(c_278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_267,c_150])).

tff(c_279,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_281,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_279])).

tff(c_3208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3161,c_281])).

tff(c_3212,plain,(
    ! [B_4047] : '#skF_1'(k1_tarski(B_4047),'#skF_9') = B_4047 ),
    inference(splitRight,[status(thm)],[c_2939])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3243,plain,(
    ! [B_4048] :
      ( ~ r2_hidden(B_4048,'#skF_9')
      | r1_tarski(k1_tarski(B_4048),'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3212,c_6])).

tff(c_3340,plain,(
    ! [A_4056,B_4057] :
      ( k1_relat_1('#skF_8'(A_4056,B_4057)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_4056,B_4057))
      | ~ v1_relat_1('#skF_8'(A_4056,B_4057))
      | k1_xboole_0 = A_4056
      | ~ r2_hidden(B_4057,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_3243,c_531])).

tff(c_3428,plain,(
    ! [A_4064,B_4065] :
      ( k1_relat_1('#skF_8'(A_4064,B_4065)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_4064,B_4065))
      | ~ r2_hidden(B_4065,'#skF_9')
      | k1_xboole_0 = A_4064 ) ),
    inference(resolution,[status(thm)],[c_82,c_3340])).

tff(c_3486,plain,(
    ! [A_4069,B_4070] :
      ( k1_relat_1('#skF_8'(A_4069,B_4070)) != '#skF_10'
      | ~ r2_hidden(B_4070,'#skF_9')
      | k1_xboole_0 = A_4069 ) ),
    inference(resolution,[status(thm)],[c_80,c_3428])).

tff(c_3489,plain,(
    ! [A_40,B_44] :
      ( A_40 != '#skF_10'
      | ~ r2_hidden(B_44,'#skF_9')
      | k1_xboole_0 = A_40
      | k1_xboole_0 = A_40 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_3486])).

tff(c_3491,plain,(
    ! [B_4071] : ~ r2_hidden(B_4071,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_3489])).

tff(c_3547,plain,(
    ! [A_4073] : k3_xboole_0(A_4073,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2740,c_3491])).

tff(c_3573,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_3547,c_150])).

tff(c_3602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_3573])).

tff(c_3604,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_3489])).

tff(c_3650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3604,c_281])).

tff(c_3652,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_3651,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_3654,plain,(
    ~ v1_funct_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3652,c_3651])).

tff(c_52,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3762,plain,(
    ! [A_4087] :
      ( k1_relat_1(A_4087) != '#skF_10'
      | A_4087 = '#skF_10'
      | ~ v1_relat_1(A_4087) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3652,c_3652,c_52])).

tff(c_3774,plain,(
    ! [A_32] :
      ( k1_relat_1('#skF_7'(A_32)) != '#skF_10'
      | '#skF_7'(A_32) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_72,c_3762])).

tff(c_3785,plain,(
    ! [A_4088] :
      ( A_4088 != '#skF_10'
      | '#skF_7'(A_4088) = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3774])).

tff(c_70,plain,(
    ! [A_32] : v1_funct_1('#skF_7'(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3793,plain,(
    ! [A_4088] :
      ( v1_funct_1('#skF_10')
      | A_4088 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3785,c_70])).

tff(c_3801,plain,(
    ! [A_4088] : A_4088 != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_3654,c_3793])).

tff(c_3659,plain,(
    ! [A_14] : k3_xboole_0(A_14,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3652,c_3652,c_28])).

tff(c_3814,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3801,c_3659])).

tff(c_3816,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_3815,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_3825,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3816,c_3815])).

tff(c_3819,plain,(
    k1_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3815,c_3815,c_48])).

tff(c_3835,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3825,c_3825,c_3819])).

tff(c_3817,plain,(
    ! [A_15] : r1_tarski('#skF_10',A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3815,c_30])).

tff(c_3845,plain,(
    ! [A_15] : r1_tarski('#skF_9',A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3825,c_3817])).

tff(c_3818,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3815,c_3815,c_46])).

tff(c_3840,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3825,c_3825,c_3818])).

tff(c_3859,plain,(
    ! [C_4097] :
      ( ~ r1_tarski(k2_relat_1(C_4097),'#skF_9')
      | k1_relat_1(C_4097) != '#skF_9'
      | ~ v1_funct_1(C_4097)
      | ~ v1_relat_1(C_4097) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3825,c_84])).

tff(c_3862,plain,
    ( ~ r1_tarski('#skF_9','#skF_9')
    | k1_relat_1('#skF_9') != '#skF_9'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_3840,c_3859])).

tff(c_3864,plain,
    ( ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3835,c_3845,c_3862])).

tff(c_3873,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_3864])).

tff(c_4002,plain,(
    ! [A_4113] :
      ( k1_relat_1(A_4113) != '#skF_9'
      | A_4113 = '#skF_9'
      | ~ v1_relat_1(A_4113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3816,c_3816,c_52])).

tff(c_4011,plain,(
    ! [A_32] :
      ( k1_relat_1('#skF_7'(A_32)) != '#skF_9'
      | '#skF_7'(A_32) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_72,c_4002])).

tff(c_4027,plain,(
    ! [A_4116] :
      ( A_4116 != '#skF_9'
      | '#skF_7'(A_4116) = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4011])).

tff(c_4037,plain,(
    ! [A_4116] :
      ( v1_relat_1('#skF_9')
      | A_4116 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4027,c_72])).

tff(c_4043,plain,(
    ! [A_4116] : A_4116 != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_3873,c_4037])).

tff(c_3893,plain,(
    ! [B_4107,A_4108] : k3_xboole_0(B_4107,A_4108) = k3_xboole_0(A_4108,B_4107) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3865,plain,(
    ! [A_14] : k3_xboole_0(A_14,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3816,c_3816,c_28])).

tff(c_3909,plain,(
    ! [A_4108] : k3_xboole_0('#skF_9',A_4108) = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_3893,c_3865])).

tff(c_4057,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4043,c_3909])).

tff(c_4058,plain,(
    ~ v1_funct_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_3864])).

tff(c_4172,plain,(
    ! [A_4130] :
      ( k1_relat_1(A_4130) != '#skF_9'
      | A_4130 = '#skF_9'
      | ~ v1_relat_1(A_4130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3816,c_3816,c_52])).

tff(c_4184,plain,(
    ! [A_32] :
      ( k1_relat_1('#skF_7'(A_32)) != '#skF_9'
      | '#skF_7'(A_32) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_72,c_4172])).

tff(c_4195,plain,(
    ! [A_4131] :
      ( A_4131 != '#skF_9'
      | '#skF_7'(A_4131) = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4184])).

tff(c_4203,plain,(
    ! [A_4131] :
      ( v1_funct_1('#skF_9')
      | A_4131 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4195,c_70])).

tff(c_4211,plain,(
    ! [A_4131] : A_4131 != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_4058,c_4203])).

tff(c_4077,plain,(
    ! [B_4123,A_4124] : k3_xboole_0(B_4123,A_4124) = k3_xboole_0(A_4124,B_4123) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4093,plain,(
    ! [A_4124] : k3_xboole_0('#skF_9',A_4124) = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_4077,c_3865])).

tff(c_4224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4211,c_4093])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.73/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.07/1.93  
% 5.07/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.07/1.93  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 5.07/1.93  
% 5.07/1.93  %Foreground sorts:
% 5.07/1.93  
% 5.07/1.93  
% 5.07/1.93  %Background operators:
% 5.07/1.93  
% 5.07/1.93  
% 5.07/1.93  %Foreground operators:
% 5.07/1.93  tff('#skF_7', type, '#skF_7': $i > $i).
% 5.07/1.93  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.07/1.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.07/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.07/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.07/1.93  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.07/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.07/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.07/1.93  tff('#skF_10', type, '#skF_10': $i).
% 5.07/1.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.07/1.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.07/1.93  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.07/1.93  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 5.07/1.93  tff('#skF_9', type, '#skF_9': $i).
% 5.07/1.93  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.07/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.07/1.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.07/1.93  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.07/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.07/1.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.07/1.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.07/1.93  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.07/1.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.07/1.93  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.07/1.93  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.07/1.93  
% 5.07/1.95  tff(f_136, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 5.07/1.95  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.07/1.95  tff(f_118, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 5.07/1.95  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.07/1.95  tff(f_54, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 5.07/1.95  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.07/1.95  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.07/1.95  tff(f_97, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 5.07/1.95  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.07/1.95  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.07/1.95  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.07/1.95  tff(c_86, plain, (k1_xboole_0='#skF_10' | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.07/1.95  tff(c_98, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_86])).
% 5.07/1.95  tff(c_2699, plain, (![A_3995, B_3996, C_3997]: (r2_hidden('#skF_2'(A_3995, B_3996, C_3997), B_3996) | r2_hidden('#skF_3'(A_3995, B_3996, C_3997), C_3997) | k3_xboole_0(A_3995, B_3996)=C_3997)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.07/1.95  tff(c_22, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), C_10) | r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | k3_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.07/1.95  tff(c_2740, plain, (![A_3995, B_3996]: (r2_hidden('#skF_3'(A_3995, B_3996, B_3996), B_3996) | k3_xboole_0(A_3995, B_3996)=B_3996)), inference(resolution, [status(thm)], [c_2699, c_22])).
% 5.07/1.95  tff(c_78, plain, (![A_40, B_44]: (k1_relat_1('#skF_8'(A_40, B_44))=A_40 | k1_xboole_0=A_40)), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.07/1.95  tff(c_80, plain, (![A_40, B_44]: (v1_funct_1('#skF_8'(A_40, B_44)) | k1_xboole_0=A_40)), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.07/1.95  tff(c_82, plain, (![A_40, B_44]: (v1_relat_1('#skF_8'(A_40, B_44)) | k1_xboole_0=A_40)), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.07/1.95  tff(c_471, plain, (![A_96, B_97]: (r2_hidden('#skF_1'(A_96, B_97), A_96) | r1_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.07/1.95  tff(c_32, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.07/1.95  tff(c_653, plain, (![A_127, B_128]: ('#skF_1'(k1_tarski(A_127), B_128)=A_127 | r1_tarski(k1_tarski(A_127), B_128))), inference(resolution, [status(thm)], [c_471, c_32])).
% 5.07/1.95  tff(c_525, plain, (![A_103, B_104]: (k2_relat_1('#skF_8'(A_103, B_104))=k1_tarski(B_104) | k1_xboole_0=A_103)), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.07/1.95  tff(c_84, plain, (![C_47]: (~r1_tarski(k2_relat_1(C_47), '#skF_9') | k1_relat_1(C_47)!='#skF_10' | ~v1_funct_1(C_47) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.07/1.95  tff(c_531, plain, (![B_104, A_103]: (~r1_tarski(k1_tarski(B_104), '#skF_9') | k1_relat_1('#skF_8'(A_103, B_104))!='#skF_10' | ~v1_funct_1('#skF_8'(A_103, B_104)) | ~v1_relat_1('#skF_8'(A_103, B_104)) | k1_xboole_0=A_103)), inference(superposition, [status(thm), theory('equality')], [c_525, c_84])).
% 5.07/1.95  tff(c_688, plain, (![A_133, A_134]: (k1_relat_1('#skF_8'(A_133, A_134))!='#skF_10' | ~v1_funct_1('#skF_8'(A_133, A_134)) | ~v1_relat_1('#skF_8'(A_133, A_134)) | k1_xboole_0=A_133 | '#skF_1'(k1_tarski(A_134), '#skF_9')=A_134)), inference(resolution, [status(thm)], [c_653, c_531])).
% 5.07/1.95  tff(c_2820, plain, (![A_4004, B_4005]: (k1_relat_1('#skF_8'(A_4004, B_4005))!='#skF_10' | ~v1_funct_1('#skF_8'(A_4004, B_4005)) | '#skF_1'(k1_tarski(B_4005), '#skF_9')=B_4005 | k1_xboole_0=A_4004)), inference(resolution, [status(thm)], [c_82, c_688])).
% 5.07/1.95  tff(c_2936, plain, (![A_4021, B_4022]: (k1_relat_1('#skF_8'(A_4021, B_4022))!='#skF_10' | '#skF_1'(k1_tarski(B_4022), '#skF_9')=B_4022 | k1_xboole_0=A_4021)), inference(resolution, [status(thm)], [c_80, c_2820])).
% 5.07/1.95  tff(c_2939, plain, (![A_40, B_44]: (A_40!='#skF_10' | '#skF_1'(k1_tarski(B_44), '#skF_9')=B_44 | k1_xboole_0=A_40 | k1_xboole_0=A_40)), inference(superposition, [status(thm), theory('equality')], [c_78, c_2936])).
% 5.07/1.95  tff(c_3161, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_2939])).
% 5.07/1.95  tff(c_48, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.07/1.95  tff(c_30, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.07/1.95  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.07/1.95  tff(c_107, plain, (![C_54]: (~r1_tarski(k2_relat_1(C_54), '#skF_9') | k1_relat_1(C_54)!='#skF_10' | ~v1_funct_1(C_54) | ~v1_relat_1(C_54))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.07/1.95  tff(c_110, plain, (~r1_tarski(k1_xboole_0, '#skF_9') | k1_relat_1(k1_xboole_0)!='#skF_10' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_107])).
% 5.07/1.95  tff(c_112, plain, (k1_xboole_0!='#skF_10' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_30, c_110])).
% 5.07/1.95  tff(c_216, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_112])).
% 5.07/1.95  tff(c_68, plain, (![A_32]: (k1_relat_1('#skF_7'(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.07/1.95  tff(c_72, plain, (![A_32]: (v1_relat_1('#skF_7'(A_32)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.07/1.95  tff(c_235, plain, (![A_72]: (k1_relat_1(A_72)!=k1_xboole_0 | k1_xboole_0=A_72 | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.07/1.95  tff(c_244, plain, (![A_32]: (k1_relat_1('#skF_7'(A_32))!=k1_xboole_0 | '#skF_7'(A_32)=k1_xboole_0)), inference(resolution, [status(thm)], [c_72, c_235])).
% 5.07/1.95  tff(c_251, plain, (![A_73]: (k1_xboole_0!=A_73 | '#skF_7'(A_73)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_244])).
% 5.07/1.95  tff(c_261, plain, (![A_73]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_73)), inference(superposition, [status(thm), theory('equality')], [c_251, c_72])).
% 5.07/1.95  tff(c_267, plain, (![A_73]: (k1_xboole_0!=A_73)), inference(negUnitSimplification, [status(thm)], [c_216, c_261])).
% 5.07/1.95  tff(c_134, plain, (![B_63, A_64]: (k3_xboole_0(B_63, A_64)=k3_xboole_0(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.07/1.95  tff(c_28, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.07/1.95  tff(c_150, plain, (![A_64]: (k3_xboole_0(k1_xboole_0, A_64)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_134, c_28])).
% 5.07/1.95  tff(c_278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_267, c_150])).
% 5.07/1.95  tff(c_279, plain, (~v1_funct_1(k1_xboole_0) | k1_xboole_0!='#skF_10'), inference(splitRight, [status(thm)], [c_112])).
% 5.07/1.95  tff(c_281, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_279])).
% 5.07/1.95  tff(c_3208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3161, c_281])).
% 5.07/1.95  tff(c_3212, plain, (![B_4047]: ('#skF_1'(k1_tarski(B_4047), '#skF_9')=B_4047)), inference(splitRight, [status(thm)], [c_2939])).
% 5.07/1.95  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.07/1.95  tff(c_3243, plain, (![B_4048]: (~r2_hidden(B_4048, '#skF_9') | r1_tarski(k1_tarski(B_4048), '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_3212, c_6])).
% 5.07/1.95  tff(c_3340, plain, (![A_4056, B_4057]: (k1_relat_1('#skF_8'(A_4056, B_4057))!='#skF_10' | ~v1_funct_1('#skF_8'(A_4056, B_4057)) | ~v1_relat_1('#skF_8'(A_4056, B_4057)) | k1_xboole_0=A_4056 | ~r2_hidden(B_4057, '#skF_9'))), inference(resolution, [status(thm)], [c_3243, c_531])).
% 5.07/1.95  tff(c_3428, plain, (![A_4064, B_4065]: (k1_relat_1('#skF_8'(A_4064, B_4065))!='#skF_10' | ~v1_funct_1('#skF_8'(A_4064, B_4065)) | ~r2_hidden(B_4065, '#skF_9') | k1_xboole_0=A_4064)), inference(resolution, [status(thm)], [c_82, c_3340])).
% 5.07/1.95  tff(c_3486, plain, (![A_4069, B_4070]: (k1_relat_1('#skF_8'(A_4069, B_4070))!='#skF_10' | ~r2_hidden(B_4070, '#skF_9') | k1_xboole_0=A_4069)), inference(resolution, [status(thm)], [c_80, c_3428])).
% 5.07/1.95  tff(c_3489, plain, (![A_40, B_44]: (A_40!='#skF_10' | ~r2_hidden(B_44, '#skF_9') | k1_xboole_0=A_40 | k1_xboole_0=A_40)), inference(superposition, [status(thm), theory('equality')], [c_78, c_3486])).
% 5.07/1.95  tff(c_3491, plain, (![B_4071]: (~r2_hidden(B_4071, '#skF_9'))), inference(splitLeft, [status(thm)], [c_3489])).
% 5.07/1.95  tff(c_3547, plain, (![A_4073]: (k3_xboole_0(A_4073, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_2740, c_3491])).
% 5.07/1.95  tff(c_3573, plain, (k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_3547, c_150])).
% 5.07/1.95  tff(c_3602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_3573])).
% 5.07/1.95  tff(c_3604, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_3489])).
% 5.07/1.95  tff(c_3650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3604, c_281])).
% 5.07/1.95  tff(c_3652, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_279])).
% 5.07/1.95  tff(c_3651, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_279])).
% 5.07/1.95  tff(c_3654, plain, (~v1_funct_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_3652, c_3651])).
% 5.07/1.95  tff(c_52, plain, (![A_23]: (k1_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.07/1.95  tff(c_3762, plain, (![A_4087]: (k1_relat_1(A_4087)!='#skF_10' | A_4087='#skF_10' | ~v1_relat_1(A_4087))), inference(demodulation, [status(thm), theory('equality')], [c_3652, c_3652, c_52])).
% 5.07/1.95  tff(c_3774, plain, (![A_32]: (k1_relat_1('#skF_7'(A_32))!='#skF_10' | '#skF_7'(A_32)='#skF_10')), inference(resolution, [status(thm)], [c_72, c_3762])).
% 5.07/1.95  tff(c_3785, plain, (![A_4088]: (A_4088!='#skF_10' | '#skF_7'(A_4088)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3774])).
% 5.07/1.95  tff(c_70, plain, (![A_32]: (v1_funct_1('#skF_7'(A_32)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.07/1.95  tff(c_3793, plain, (![A_4088]: (v1_funct_1('#skF_10') | A_4088!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_3785, c_70])).
% 5.07/1.95  tff(c_3801, plain, (![A_4088]: (A_4088!='#skF_10')), inference(negUnitSimplification, [status(thm)], [c_3654, c_3793])).
% 5.07/1.95  tff(c_3659, plain, (![A_14]: (k3_xboole_0(A_14, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_3652, c_3652, c_28])).
% 5.07/1.95  tff(c_3814, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3801, c_3659])).
% 5.07/1.95  tff(c_3816, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_86])).
% 5.07/1.95  tff(c_3815, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_86])).
% 5.07/1.95  tff(c_3825, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_3816, c_3815])).
% 5.07/1.95  tff(c_3819, plain, (k1_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_3815, c_3815, c_48])).
% 5.07/1.95  tff(c_3835, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_3825, c_3825, c_3819])).
% 5.07/1.95  tff(c_3817, plain, (![A_15]: (r1_tarski('#skF_10', A_15))), inference(demodulation, [status(thm), theory('equality')], [c_3815, c_30])).
% 5.07/1.95  tff(c_3845, plain, (![A_15]: (r1_tarski('#skF_9', A_15))), inference(demodulation, [status(thm), theory('equality')], [c_3825, c_3817])).
% 5.07/1.95  tff(c_3818, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_3815, c_3815, c_46])).
% 5.07/1.95  tff(c_3840, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_3825, c_3825, c_3818])).
% 5.07/1.95  tff(c_3859, plain, (![C_4097]: (~r1_tarski(k2_relat_1(C_4097), '#skF_9') | k1_relat_1(C_4097)!='#skF_9' | ~v1_funct_1(C_4097) | ~v1_relat_1(C_4097))), inference(demodulation, [status(thm), theory('equality')], [c_3825, c_84])).
% 5.07/1.95  tff(c_3862, plain, (~r1_tarski('#skF_9', '#skF_9') | k1_relat_1('#skF_9')!='#skF_9' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_3840, c_3859])).
% 5.07/1.95  tff(c_3864, plain, (~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3835, c_3845, c_3862])).
% 5.07/1.95  tff(c_3873, plain, (~v1_relat_1('#skF_9')), inference(splitLeft, [status(thm)], [c_3864])).
% 5.07/1.95  tff(c_4002, plain, (![A_4113]: (k1_relat_1(A_4113)!='#skF_9' | A_4113='#skF_9' | ~v1_relat_1(A_4113))), inference(demodulation, [status(thm), theory('equality')], [c_3816, c_3816, c_52])).
% 5.07/1.95  tff(c_4011, plain, (![A_32]: (k1_relat_1('#skF_7'(A_32))!='#skF_9' | '#skF_7'(A_32)='#skF_9')), inference(resolution, [status(thm)], [c_72, c_4002])).
% 5.07/1.95  tff(c_4027, plain, (![A_4116]: (A_4116!='#skF_9' | '#skF_7'(A_4116)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4011])).
% 5.07/1.95  tff(c_4037, plain, (![A_4116]: (v1_relat_1('#skF_9') | A_4116!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_4027, c_72])).
% 5.07/1.95  tff(c_4043, plain, (![A_4116]: (A_4116!='#skF_9')), inference(negUnitSimplification, [status(thm)], [c_3873, c_4037])).
% 5.07/1.95  tff(c_3893, plain, (![B_4107, A_4108]: (k3_xboole_0(B_4107, A_4108)=k3_xboole_0(A_4108, B_4107))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.07/1.95  tff(c_3865, plain, (![A_14]: (k3_xboole_0(A_14, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3816, c_3816, c_28])).
% 5.07/1.95  tff(c_3909, plain, (![A_4108]: (k3_xboole_0('#skF_9', A_4108)='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_3893, c_3865])).
% 5.07/1.95  tff(c_4057, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4043, c_3909])).
% 5.07/1.95  tff(c_4058, plain, (~v1_funct_1('#skF_9')), inference(splitRight, [status(thm)], [c_3864])).
% 5.07/1.95  tff(c_4172, plain, (![A_4130]: (k1_relat_1(A_4130)!='#skF_9' | A_4130='#skF_9' | ~v1_relat_1(A_4130))), inference(demodulation, [status(thm), theory('equality')], [c_3816, c_3816, c_52])).
% 5.07/1.95  tff(c_4184, plain, (![A_32]: (k1_relat_1('#skF_7'(A_32))!='#skF_9' | '#skF_7'(A_32)='#skF_9')), inference(resolution, [status(thm)], [c_72, c_4172])).
% 5.07/1.95  tff(c_4195, plain, (![A_4131]: (A_4131!='#skF_9' | '#skF_7'(A_4131)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4184])).
% 5.07/1.95  tff(c_4203, plain, (![A_4131]: (v1_funct_1('#skF_9') | A_4131!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_4195, c_70])).
% 5.07/1.95  tff(c_4211, plain, (![A_4131]: (A_4131!='#skF_9')), inference(negUnitSimplification, [status(thm)], [c_4058, c_4203])).
% 5.07/1.95  tff(c_4077, plain, (![B_4123, A_4124]: (k3_xboole_0(B_4123, A_4124)=k3_xboole_0(A_4124, B_4123))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.07/1.95  tff(c_4093, plain, (![A_4124]: (k3_xboole_0('#skF_9', A_4124)='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_4077, c_3865])).
% 5.07/1.95  tff(c_4224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4211, c_4093])).
% 5.07/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.07/1.95  
% 5.07/1.95  Inference rules
% 5.07/1.95  ----------------------
% 5.07/1.95  #Ref     : 1
% 5.07/1.95  #Sup     : 908
% 5.07/1.95  #Fact    : 0
% 5.07/1.95  #Define  : 0
% 5.07/1.95  #Split   : 13
% 5.07/1.95  #Chain   : 0
% 5.07/1.95  #Close   : 0
% 5.07/1.95  
% 5.07/1.95  Ordering : KBO
% 5.07/1.95  
% 5.07/1.95  Simplification rules
% 5.07/1.95  ----------------------
% 5.07/1.95  #Subsume      : 379
% 5.07/1.95  #Demod        : 441
% 5.07/1.95  #Tautology    : 235
% 5.07/1.95  #SimpNegUnit  : 88
% 5.07/1.95  #BackRed      : 142
% 5.07/1.95  
% 5.07/1.95  #Partial instantiations: 2520
% 5.07/1.95  #Strategies tried      : 1
% 5.07/1.95  
% 5.07/1.95  Timing (in seconds)
% 5.07/1.95  ----------------------
% 5.07/1.95  Preprocessing        : 0.33
% 5.07/1.95  Parsing              : 0.17
% 5.07/1.96  CNF conversion       : 0.03
% 5.07/1.96  Main loop            : 0.84
% 5.07/1.96  Inferencing          : 0.31
% 5.07/1.96  Reduction            : 0.27
% 5.07/1.96  Demodulation         : 0.19
% 5.07/1.96  BG Simplification    : 0.04
% 5.07/1.96  Subsumption          : 0.15
% 5.07/1.96  Abstraction          : 0.04
% 5.07/1.96  MUC search           : 0.00
% 5.07/1.96  Cooper               : 0.00
% 5.07/1.96  Total                : 1.21
% 5.07/1.96  Index Insertion      : 0.00
% 5.07/1.96  Index Deletion       : 0.00
% 5.07/1.96  Index Matching       : 0.00
% 5.07/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
