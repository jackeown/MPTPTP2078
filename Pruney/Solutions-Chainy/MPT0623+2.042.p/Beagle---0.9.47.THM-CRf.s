%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:11 EST 2020

% Result     : Theorem 8.67s
% Output     : CNFRefutation 9.08s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 401 expanded)
%              Number of leaves         :   34 ( 149 expanded)
%              Depth                    :   19
%              Number of atoms          :  218 (1098 expanded)
%              Number of equality atoms :  106 ( 500 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > np__1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_8 > #skF_10 > #skF_2 > #skF_3 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(np__1,type,(
    np__1: $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_78,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_91,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_51,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_60,plain,(
    ! [A_23] : v1_relat_1('#skF_8'(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_58,plain,(
    ! [A_23] : v1_funct_1('#skF_8'(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_56,plain,(
    ! [A_23] : k1_relat_1('#skF_8'(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_72,plain,
    ( k1_xboole_0 = '#skF_11'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_95,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8153,plain,(
    ! [A_4237,B_4238,C_4239] :
      ( ~ r2_hidden('#skF_2'(A_4237,B_4238,C_4239),C_4239)
      | r2_hidden('#skF_3'(A_4237,B_4238,C_4239),C_4239)
      | k4_xboole_0(A_4237,B_4238) = C_4239 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8179,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_3'(A_6,B_7,A_6),A_6)
      | k4_xboole_0(A_6,B_7) = A_6 ) ),
    inference(resolution,[status(thm)],[c_24,c_8153])).

tff(c_8185,plain,(
    ! [A_4266,B_4267] :
      ( r2_hidden('#skF_3'(A_4266,B_4267,A_4266),A_4266)
      | k4_xboole_0(A_4266,B_4267) = A_4266 ) ),
    inference(resolution,[status(thm)],[c_24,c_8153])).

tff(c_36,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_115,plain,(
    ! [D_52,B_53,A_54] :
      ( ~ r2_hidden(D_52,B_53)
      | ~ r2_hidden(D_52,k4_xboole_0(A_54,B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_118,plain,(
    ! [D_52,A_16] :
      ( ~ r2_hidden(D_52,k1_xboole_0)
      | ~ r2_hidden(D_52,A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_115])).

tff(c_8213,plain,(
    ! [B_4294,A_4295] :
      ( ~ r2_hidden('#skF_3'(k1_xboole_0,B_4294,k1_xboole_0),A_4295)
      | k4_xboole_0(k1_xboole_0,B_4294) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8185,c_118])).

tff(c_8244,plain,(
    ! [B_7] : k4_xboole_0(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8179,c_8213])).

tff(c_64,plain,(
    ! [A_29,B_33] :
      ( k1_relat_1('#skF_9'(A_29,B_33)) = A_29
      | k1_xboole_0 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_66,plain,(
    ! [A_29,B_33] :
      ( v1_funct_1('#skF_9'(A_29,B_33))
      | k1_xboole_0 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_68,plain,(
    ! [A_29,B_33] :
      ( v1_relat_1('#skF_9'(A_29,B_33))
      | k1_xboole_0 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_146,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_1'(A_65,B_66),A_65)
      | r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [C_21,A_17] :
      ( C_21 = A_17
      | ~ r2_hidden(C_21,k1_tarski(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_166,plain,(
    ! [A_17,B_66] :
      ( '#skF_1'(k1_tarski(A_17),B_66) = A_17
      | r1_tarski(k1_tarski(A_17),B_66) ) ),
    inference(resolution,[status(thm)],[c_146,c_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_220,plain,(
    ! [C_76,B_77,A_78] :
      ( r2_hidden(C_76,B_77)
      | ~ r2_hidden(C_76,A_78)
      | ~ r1_tarski(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_609,plain,(
    ! [A_1015,B_1016,B_1017] :
      ( r2_hidden('#skF_1'(A_1015,B_1016),B_1017)
      | ~ r1_tarski(A_1015,B_1017)
      | r1_tarski(A_1015,B_1016) ) ),
    inference(resolution,[status(thm)],[c_6,c_220])).

tff(c_771,plain,(
    ! [A_1237,B_1238,A_1239] :
      ( ~ r2_hidden('#skF_1'(A_1237,B_1238),A_1239)
      | ~ r1_tarski(A_1237,k1_xboole_0)
      | r1_tarski(A_1237,B_1238) ) ),
    inference(resolution,[status(thm)],[c_609,c_118])).

tff(c_813,plain,(
    ! [A_1266,B_1267] :
      ( ~ r1_tarski(A_1266,k1_xboole_0)
      | r1_tarski(A_1266,B_1267) ) ),
    inference(resolution,[status(thm)],[c_6,c_771])).

tff(c_850,plain,(
    ! [A_1322,B_1323] :
      ( r1_tarski(k1_tarski(A_1322),B_1323)
      | '#skF_1'(k1_tarski(A_1322),k1_xboole_0) = A_1322 ) ),
    inference(resolution,[status(thm)],[c_166,c_813])).

tff(c_40,plain,(
    ! [C_21] : r2_hidden(C_21,k1_tarski(C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_226,plain,(
    ! [C_21,B_77] :
      ( r2_hidden(C_21,B_77)
      | ~ r1_tarski(k1_tarski(C_21),B_77) ) ),
    inference(resolution,[status(thm)],[c_40,c_220])).

tff(c_935,plain,(
    ! [A_1350,B_1351] :
      ( r2_hidden(A_1350,B_1351)
      | '#skF_1'(k1_tarski(A_1350),k1_xboole_0) = A_1350 ) ),
    inference(resolution,[status(thm)],[c_850,c_226])).

tff(c_1040,plain,(
    ! [A_17,A_1350] :
      ( A_17 = A_1350
      | '#skF_1'(k1_tarski(A_1350),k1_xboole_0) = A_1350 ) ),
    inference(resolution,[status(thm)],[c_935,c_38])).

tff(c_7620,plain,(
    ! [A_3930] : '#skF_1'(k1_tarski(A_3930),k1_xboole_0) = A_3930 ),
    inference(factorization,[status(thm),theory(equality)],[c_1040])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7783,plain,(
    ! [A_4013] :
      ( ~ r2_hidden(A_4013,k1_xboole_0)
      | r1_tarski(k1_tarski(A_4013),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7620,c_4])).

tff(c_811,plain,(
    ! [A_1,B_2] :
      ( ~ r1_tarski(A_1,k1_xboole_0)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_771])).

tff(c_7841,plain,(
    ! [A_4040,B_4041] :
      ( r1_tarski(k1_tarski(A_4040),B_4041)
      | ~ r2_hidden(A_4040,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_7783,c_811])).

tff(c_122,plain,(
    ! [A_59,B_60] :
      ( k2_relat_1('#skF_9'(A_59,B_60)) = k1_tarski(B_60)
      | k1_xboole_0 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_70,plain,(
    ! [C_36] :
      ( ~ r1_tarski(k2_relat_1(C_36),'#skF_10')
      | k1_relat_1(C_36) != '#skF_11'
      | ~ v1_funct_1(C_36)
      | ~ v1_relat_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_128,plain,(
    ! [B_60,A_59] :
      ( ~ r1_tarski(k1_tarski(B_60),'#skF_10')
      | k1_relat_1('#skF_9'(A_59,B_60)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_59,B_60))
      | ~ v1_relat_1('#skF_9'(A_59,B_60))
      | k1_xboole_0 = A_59 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_70])).

tff(c_8028,plain,(
    ! [A_4152,A_4153] :
      ( k1_relat_1('#skF_9'(A_4152,A_4153)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_4152,A_4153))
      | ~ v1_relat_1('#skF_9'(A_4152,A_4153))
      | k1_xboole_0 = A_4152
      | ~ r2_hidden(A_4153,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_7841,c_128])).

tff(c_8654,plain,(
    ! [A_4603,B_4604] :
      ( k1_relat_1('#skF_9'(A_4603,B_4604)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_4603,B_4604))
      | ~ r2_hidden(B_4604,k1_xboole_0)
      | k1_xboole_0 = A_4603 ) ),
    inference(resolution,[status(thm)],[c_68,c_8028])).

tff(c_17337,plain,(
    ! [A_8072,B_8073] :
      ( k1_relat_1('#skF_9'(A_8072,B_8073)) != '#skF_11'
      | ~ r2_hidden(B_8073,k1_xboole_0)
      | k1_xboole_0 = A_8072 ) ),
    inference(resolution,[status(thm)],[c_66,c_8654])).

tff(c_17342,plain,(
    ! [A_29,B_33] :
      ( A_29 != '#skF_11'
      | ~ r2_hidden(B_33,k1_xboole_0)
      | k1_xboole_0 = A_29
      | k1_xboole_0 = A_29 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_17337])).

tff(c_17419,plain,(
    ! [B_8157] : ~ r2_hidden(B_8157,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_17342])).

tff(c_17441,plain,(
    ! [B_7,C_8] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_7,C_8),C_8)
      | k4_xboole_0(k1_xboole_0,B_7) = C_8 ) ),
    inference(resolution,[status(thm)],[c_24,c_17419])).

tff(c_17475,plain,(
    ! [B_7,C_8] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_7,C_8),C_8)
      | k1_xboole_0 = C_8 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8244,c_17441])).

tff(c_445,plain,(
    ! [A_930,B_931] :
      ( '#skF_1'(k1_tarski(A_930),B_931) = A_930
      | r1_tarski(k1_tarski(A_930),B_931) ) ),
    inference(resolution,[status(thm)],[c_146,c_38])).

tff(c_711,plain,(
    ! [A_1153,A_1154] :
      ( k1_relat_1('#skF_9'(A_1153,A_1154)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_1153,A_1154))
      | ~ v1_relat_1('#skF_9'(A_1153,A_1154))
      | k1_xboole_0 = A_1153
      | '#skF_1'(k1_tarski(A_1154),'#skF_10') = A_1154 ) ),
    inference(resolution,[status(thm)],[c_445,c_128])).

tff(c_18310,plain,(
    ! [A_8660,B_8661] :
      ( k1_relat_1('#skF_9'(A_8660,B_8661)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_8660,B_8661))
      | '#skF_1'(k1_tarski(B_8661),'#skF_10') = B_8661
      | k1_xboole_0 = A_8660 ) ),
    inference(resolution,[status(thm)],[c_68,c_711])).

tff(c_20108,plain,(
    ! [A_9533,B_9534] :
      ( k1_relat_1('#skF_9'(A_9533,B_9534)) != '#skF_11'
      | '#skF_1'(k1_tarski(B_9534),'#skF_10') = B_9534
      | k1_xboole_0 = A_9533 ) ),
    inference(resolution,[status(thm)],[c_66,c_18310])).

tff(c_20131,plain,(
    ! [A_29,B_33] :
      ( A_29 != '#skF_11'
      | '#skF_1'(k1_tarski(B_33),'#skF_10') = B_33
      | k1_xboole_0 = A_29
      | k1_xboole_0 = A_29 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_20108])).

tff(c_20133,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_20131])).

tff(c_34,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_177,plain,(
    ! [A_70] :
      ( k2_relat_1(A_70) = k1_xboole_0
      | k1_relat_1(A_70) != k1_xboole_0
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_183,plain,(
    ! [A_23] :
      ( k2_relat_1('#skF_8'(A_23)) = k1_xboole_0
      | k1_relat_1('#skF_8'(A_23)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_60,c_177])).

tff(c_188,plain,(
    ! [A_71] :
      ( k2_relat_1('#skF_8'(A_71)) = k1_xboole_0
      | k1_xboole_0 != A_71 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_183])).

tff(c_197,plain,(
    ! [A_71] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_10')
      | k1_relat_1('#skF_8'(A_71)) != '#skF_11'
      | ~ v1_funct_1('#skF_8'(A_71))
      | ~ v1_relat_1('#skF_8'(A_71))
      | k1_xboole_0 != A_71 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_70])).

tff(c_204,plain,(
    ! [A_71] :
      ( A_71 != '#skF_11'
      | k1_xboole_0 != A_71 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_34,c_197])).

tff(c_218,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_204])).

tff(c_20183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20133,c_218])).

tff(c_20186,plain,(
    ! [B_9561] : '#skF_1'(k1_tarski(B_9561),'#skF_10') = B_9561 ),
    inference(splitRight,[status(thm)],[c_20131])).

tff(c_20318,plain,(
    ! [B_9616] :
      ( ~ r2_hidden(B_9616,'#skF_10')
      | r1_tarski(k1_tarski(B_9616),'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20186,c_4])).

tff(c_20623,plain,(
    ! [A_9699,B_9700] :
      ( k1_relat_1('#skF_9'(A_9699,B_9700)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_9699,B_9700))
      | ~ v1_relat_1('#skF_9'(A_9699,B_9700))
      | k1_xboole_0 = A_9699
      | ~ r2_hidden(B_9700,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_20318,c_128])).

tff(c_20915,plain,(
    ! [A_9813,B_9814] :
      ( k1_relat_1('#skF_9'(A_9813,B_9814)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_9813,B_9814))
      | ~ r2_hidden(B_9814,'#skF_10')
      | k1_xboole_0 = A_9813 ) ),
    inference(resolution,[status(thm)],[c_68,c_20623])).

tff(c_20921,plain,(
    ! [A_9841,B_9842] :
      ( k1_relat_1('#skF_9'(A_9841,B_9842)) != '#skF_11'
      | ~ r2_hidden(B_9842,'#skF_10')
      | k1_xboole_0 = A_9841 ) ),
    inference(resolution,[status(thm)],[c_66,c_20915])).

tff(c_20926,plain,(
    ! [A_29,B_33] :
      ( A_29 != '#skF_11'
      | ~ r2_hidden(B_33,'#skF_10')
      | k1_xboole_0 = A_29
      | k1_xboole_0 = A_29 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_20921])).

tff(c_20929,plain,(
    ! [B_9869] : ~ r2_hidden(B_9869,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_20926])).

tff(c_20989,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_17475,c_20929])).

tff(c_21056,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_20989])).

tff(c_21058,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_20926])).

tff(c_21110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21058,c_218])).

tff(c_21112,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_17342])).

tff(c_21141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21112,c_218])).

tff(c_21143,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_21142,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_21150,plain,(
    '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21143,c_21142])).

tff(c_21145,plain,(
    ! [A_15] : r1_tarski('#skF_11',A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21142,c_34])).

tff(c_21159,plain,(
    ! [A_15] : r1_tarski('#skF_10',A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21150,c_21145])).

tff(c_52,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) = k1_xboole_0
      | k1_relat_1(A_22) != k1_xboole_0
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_21247,plain,(
    ! [A_9924] :
      ( k2_relat_1(A_9924) = '#skF_10'
      | k1_relat_1(A_9924) != '#skF_10'
      | ~ v1_relat_1(A_9924) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21143,c_21143,c_52])).

tff(c_21253,plain,(
    ! [A_23] :
      ( k2_relat_1('#skF_8'(A_23)) = '#skF_10'
      | k1_relat_1('#skF_8'(A_23)) != '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_60,c_21247])).

tff(c_21258,plain,(
    ! [A_9925] :
      ( k2_relat_1('#skF_8'(A_9925)) = '#skF_10'
      | A_9925 != '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_21253])).

tff(c_21161,plain,(
    ! [C_36] :
      ( ~ r1_tarski(k2_relat_1(C_36),'#skF_10')
      | k1_relat_1(C_36) != '#skF_10'
      | ~ v1_funct_1(C_36)
      | ~ v1_relat_1(C_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21150,c_70])).

tff(c_21264,plain,(
    ! [A_9925] :
      ( ~ r1_tarski('#skF_10','#skF_10')
      | k1_relat_1('#skF_8'(A_9925)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_9925))
      | ~ v1_relat_1('#skF_8'(A_9925))
      | A_9925 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21258,c_21161])).

tff(c_21270,plain,(
    ! [A_9925] : A_9925 != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_21159,c_21264])).

tff(c_21293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21270,c_21150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n018.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 19:17:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.67/2.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.67/2.97  
% 8.67/2.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.67/2.97  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > np__1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_8 > #skF_10 > #skF_2 > #skF_3 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_4
% 8.67/2.97  
% 8.67/2.97  %Foreground sorts:
% 8.67/2.97  
% 8.67/2.97  
% 8.67/2.97  %Background operators:
% 8.67/2.97  
% 8.67/2.97  
% 8.67/2.97  %Foreground operators:
% 8.67/2.97  tff(np__1, type, np__1: $i).
% 8.67/2.97  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.67/2.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.67/2.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.67/2.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.67/2.97  tff('#skF_11', type, '#skF_11': $i).
% 8.67/2.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.67/2.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.67/2.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.67/2.97  tff('#skF_8', type, '#skF_8': $i > $i).
% 8.67/2.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.67/2.97  tff('#skF_10', type, '#skF_10': $i).
% 8.67/2.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.67/2.97  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.67/2.97  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.67/2.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.67/2.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.67/2.97  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.67/2.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.67/2.97  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 8.67/2.97  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.67/2.97  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 8.67/2.97  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.67/2.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.67/2.97  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.67/2.97  
% 9.08/2.99  tff(f_78, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 9.08/2.99  tff(f_109, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 9.08/2.99  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 9.08/2.99  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 9.08/2.99  tff(f_91, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 9.08/2.99  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.08/2.99  tff(f_60, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 9.08/2.99  tff(f_51, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.08/2.99  tff(f_66, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 9.08/2.99  tff(c_60, plain, (![A_23]: (v1_relat_1('#skF_8'(A_23)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.08/2.99  tff(c_58, plain, (![A_23]: (v1_funct_1('#skF_8'(A_23)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.08/2.99  tff(c_56, plain, (![A_23]: (k1_relat_1('#skF_8'(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.08/2.99  tff(c_72, plain, (k1_xboole_0='#skF_11' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.08/2.99  tff(c_95, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_72])).
% 9.08/2.99  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.08/2.99  tff(c_8153, plain, (![A_4237, B_4238, C_4239]: (~r2_hidden('#skF_2'(A_4237, B_4238, C_4239), C_4239) | r2_hidden('#skF_3'(A_4237, B_4238, C_4239), C_4239) | k4_xboole_0(A_4237, B_4238)=C_4239)), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.08/2.99  tff(c_8179, plain, (![A_6, B_7]: (r2_hidden('#skF_3'(A_6, B_7, A_6), A_6) | k4_xboole_0(A_6, B_7)=A_6)), inference(resolution, [status(thm)], [c_24, c_8153])).
% 9.08/2.99  tff(c_8185, plain, (![A_4266, B_4267]: (r2_hidden('#skF_3'(A_4266, B_4267, A_4266), A_4266) | k4_xboole_0(A_4266, B_4267)=A_4266)), inference(resolution, [status(thm)], [c_24, c_8153])).
% 9.08/2.99  tff(c_36, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.08/2.99  tff(c_115, plain, (![D_52, B_53, A_54]: (~r2_hidden(D_52, B_53) | ~r2_hidden(D_52, k4_xboole_0(A_54, B_53)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.08/2.99  tff(c_118, plain, (![D_52, A_16]: (~r2_hidden(D_52, k1_xboole_0) | ~r2_hidden(D_52, A_16))), inference(superposition, [status(thm), theory('equality')], [c_36, c_115])).
% 9.08/2.99  tff(c_8213, plain, (![B_4294, A_4295]: (~r2_hidden('#skF_3'(k1_xboole_0, B_4294, k1_xboole_0), A_4295) | k4_xboole_0(k1_xboole_0, B_4294)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8185, c_118])).
% 9.08/2.99  tff(c_8244, plain, (![B_7]: (k4_xboole_0(k1_xboole_0, B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8179, c_8213])).
% 9.08/2.99  tff(c_64, plain, (![A_29, B_33]: (k1_relat_1('#skF_9'(A_29, B_33))=A_29 | k1_xboole_0=A_29)), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.08/2.99  tff(c_66, plain, (![A_29, B_33]: (v1_funct_1('#skF_9'(A_29, B_33)) | k1_xboole_0=A_29)), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.08/2.99  tff(c_68, plain, (![A_29, B_33]: (v1_relat_1('#skF_9'(A_29, B_33)) | k1_xboole_0=A_29)), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.08/2.99  tff(c_146, plain, (![A_65, B_66]: (r2_hidden('#skF_1'(A_65, B_66), A_65) | r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.08/2.99  tff(c_38, plain, (![C_21, A_17]: (C_21=A_17 | ~r2_hidden(C_21, k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.08/2.99  tff(c_166, plain, (![A_17, B_66]: ('#skF_1'(k1_tarski(A_17), B_66)=A_17 | r1_tarski(k1_tarski(A_17), B_66))), inference(resolution, [status(thm)], [c_146, c_38])).
% 9.08/2.99  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.08/2.99  tff(c_220, plain, (![C_76, B_77, A_78]: (r2_hidden(C_76, B_77) | ~r2_hidden(C_76, A_78) | ~r1_tarski(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.08/2.99  tff(c_609, plain, (![A_1015, B_1016, B_1017]: (r2_hidden('#skF_1'(A_1015, B_1016), B_1017) | ~r1_tarski(A_1015, B_1017) | r1_tarski(A_1015, B_1016))), inference(resolution, [status(thm)], [c_6, c_220])).
% 9.08/2.99  tff(c_771, plain, (![A_1237, B_1238, A_1239]: (~r2_hidden('#skF_1'(A_1237, B_1238), A_1239) | ~r1_tarski(A_1237, k1_xboole_0) | r1_tarski(A_1237, B_1238))), inference(resolution, [status(thm)], [c_609, c_118])).
% 9.08/2.99  tff(c_813, plain, (![A_1266, B_1267]: (~r1_tarski(A_1266, k1_xboole_0) | r1_tarski(A_1266, B_1267))), inference(resolution, [status(thm)], [c_6, c_771])).
% 9.08/2.99  tff(c_850, plain, (![A_1322, B_1323]: (r1_tarski(k1_tarski(A_1322), B_1323) | '#skF_1'(k1_tarski(A_1322), k1_xboole_0)=A_1322)), inference(resolution, [status(thm)], [c_166, c_813])).
% 9.08/2.99  tff(c_40, plain, (![C_21]: (r2_hidden(C_21, k1_tarski(C_21)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.08/2.99  tff(c_226, plain, (![C_21, B_77]: (r2_hidden(C_21, B_77) | ~r1_tarski(k1_tarski(C_21), B_77))), inference(resolution, [status(thm)], [c_40, c_220])).
% 9.08/2.99  tff(c_935, plain, (![A_1350, B_1351]: (r2_hidden(A_1350, B_1351) | '#skF_1'(k1_tarski(A_1350), k1_xboole_0)=A_1350)), inference(resolution, [status(thm)], [c_850, c_226])).
% 9.08/2.99  tff(c_1040, plain, (![A_17, A_1350]: (A_17=A_1350 | '#skF_1'(k1_tarski(A_1350), k1_xboole_0)=A_1350)), inference(resolution, [status(thm)], [c_935, c_38])).
% 9.08/2.99  tff(c_7620, plain, (![A_3930]: ('#skF_1'(k1_tarski(A_3930), k1_xboole_0)=A_3930)), inference(factorization, [status(thm), theory('equality')], [c_1040])).
% 9.08/2.99  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.08/2.99  tff(c_7783, plain, (![A_4013]: (~r2_hidden(A_4013, k1_xboole_0) | r1_tarski(k1_tarski(A_4013), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7620, c_4])).
% 9.08/2.99  tff(c_811, plain, (![A_1, B_2]: (~r1_tarski(A_1, k1_xboole_0) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_771])).
% 9.08/2.99  tff(c_7841, plain, (![A_4040, B_4041]: (r1_tarski(k1_tarski(A_4040), B_4041) | ~r2_hidden(A_4040, k1_xboole_0))), inference(resolution, [status(thm)], [c_7783, c_811])).
% 9.08/2.99  tff(c_122, plain, (![A_59, B_60]: (k2_relat_1('#skF_9'(A_59, B_60))=k1_tarski(B_60) | k1_xboole_0=A_59)), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.08/2.99  tff(c_70, plain, (![C_36]: (~r1_tarski(k2_relat_1(C_36), '#skF_10') | k1_relat_1(C_36)!='#skF_11' | ~v1_funct_1(C_36) | ~v1_relat_1(C_36))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.08/2.99  tff(c_128, plain, (![B_60, A_59]: (~r1_tarski(k1_tarski(B_60), '#skF_10') | k1_relat_1('#skF_9'(A_59, B_60))!='#skF_11' | ~v1_funct_1('#skF_9'(A_59, B_60)) | ~v1_relat_1('#skF_9'(A_59, B_60)) | k1_xboole_0=A_59)), inference(superposition, [status(thm), theory('equality')], [c_122, c_70])).
% 9.08/2.99  tff(c_8028, plain, (![A_4152, A_4153]: (k1_relat_1('#skF_9'(A_4152, A_4153))!='#skF_11' | ~v1_funct_1('#skF_9'(A_4152, A_4153)) | ~v1_relat_1('#skF_9'(A_4152, A_4153)) | k1_xboole_0=A_4152 | ~r2_hidden(A_4153, k1_xboole_0))), inference(resolution, [status(thm)], [c_7841, c_128])).
% 9.08/2.99  tff(c_8654, plain, (![A_4603, B_4604]: (k1_relat_1('#skF_9'(A_4603, B_4604))!='#skF_11' | ~v1_funct_1('#skF_9'(A_4603, B_4604)) | ~r2_hidden(B_4604, k1_xboole_0) | k1_xboole_0=A_4603)), inference(resolution, [status(thm)], [c_68, c_8028])).
% 9.08/2.99  tff(c_17337, plain, (![A_8072, B_8073]: (k1_relat_1('#skF_9'(A_8072, B_8073))!='#skF_11' | ~r2_hidden(B_8073, k1_xboole_0) | k1_xboole_0=A_8072)), inference(resolution, [status(thm)], [c_66, c_8654])).
% 9.08/2.99  tff(c_17342, plain, (![A_29, B_33]: (A_29!='#skF_11' | ~r2_hidden(B_33, k1_xboole_0) | k1_xboole_0=A_29 | k1_xboole_0=A_29)), inference(superposition, [status(thm), theory('equality')], [c_64, c_17337])).
% 9.08/2.99  tff(c_17419, plain, (![B_8157]: (~r2_hidden(B_8157, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_17342])).
% 9.08/2.99  tff(c_17441, plain, (![B_7, C_8]: (r2_hidden('#skF_3'(k1_xboole_0, B_7, C_8), C_8) | k4_xboole_0(k1_xboole_0, B_7)=C_8)), inference(resolution, [status(thm)], [c_24, c_17419])).
% 9.08/2.99  tff(c_17475, plain, (![B_7, C_8]: (r2_hidden('#skF_3'(k1_xboole_0, B_7, C_8), C_8) | k1_xboole_0=C_8)), inference(demodulation, [status(thm), theory('equality')], [c_8244, c_17441])).
% 9.08/2.99  tff(c_445, plain, (![A_930, B_931]: ('#skF_1'(k1_tarski(A_930), B_931)=A_930 | r1_tarski(k1_tarski(A_930), B_931))), inference(resolution, [status(thm)], [c_146, c_38])).
% 9.08/2.99  tff(c_711, plain, (![A_1153, A_1154]: (k1_relat_1('#skF_9'(A_1153, A_1154))!='#skF_11' | ~v1_funct_1('#skF_9'(A_1153, A_1154)) | ~v1_relat_1('#skF_9'(A_1153, A_1154)) | k1_xboole_0=A_1153 | '#skF_1'(k1_tarski(A_1154), '#skF_10')=A_1154)), inference(resolution, [status(thm)], [c_445, c_128])).
% 9.08/2.99  tff(c_18310, plain, (![A_8660, B_8661]: (k1_relat_1('#skF_9'(A_8660, B_8661))!='#skF_11' | ~v1_funct_1('#skF_9'(A_8660, B_8661)) | '#skF_1'(k1_tarski(B_8661), '#skF_10')=B_8661 | k1_xboole_0=A_8660)), inference(resolution, [status(thm)], [c_68, c_711])).
% 9.08/2.99  tff(c_20108, plain, (![A_9533, B_9534]: (k1_relat_1('#skF_9'(A_9533, B_9534))!='#skF_11' | '#skF_1'(k1_tarski(B_9534), '#skF_10')=B_9534 | k1_xboole_0=A_9533)), inference(resolution, [status(thm)], [c_66, c_18310])).
% 9.08/2.99  tff(c_20131, plain, (![A_29, B_33]: (A_29!='#skF_11' | '#skF_1'(k1_tarski(B_33), '#skF_10')=B_33 | k1_xboole_0=A_29 | k1_xboole_0=A_29)), inference(superposition, [status(thm), theory('equality')], [c_64, c_20108])).
% 9.08/2.99  tff(c_20133, plain, (k1_xboole_0='#skF_11'), inference(splitLeft, [status(thm)], [c_20131])).
% 9.08/2.99  tff(c_34, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.08/2.99  tff(c_177, plain, (![A_70]: (k2_relat_1(A_70)=k1_xboole_0 | k1_relat_1(A_70)!=k1_xboole_0 | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.08/2.99  tff(c_183, plain, (![A_23]: (k2_relat_1('#skF_8'(A_23))=k1_xboole_0 | k1_relat_1('#skF_8'(A_23))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_177])).
% 9.08/2.99  tff(c_188, plain, (![A_71]: (k2_relat_1('#skF_8'(A_71))=k1_xboole_0 | k1_xboole_0!=A_71)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_183])).
% 9.08/2.99  tff(c_197, plain, (![A_71]: (~r1_tarski(k1_xboole_0, '#skF_10') | k1_relat_1('#skF_8'(A_71))!='#skF_11' | ~v1_funct_1('#skF_8'(A_71)) | ~v1_relat_1('#skF_8'(A_71)) | k1_xboole_0!=A_71)), inference(superposition, [status(thm), theory('equality')], [c_188, c_70])).
% 9.08/2.99  tff(c_204, plain, (![A_71]: (A_71!='#skF_11' | k1_xboole_0!=A_71)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_34, c_197])).
% 9.08/2.99  tff(c_218, plain, (k1_xboole_0!='#skF_11'), inference(reflexivity, [status(thm), theory('equality')], [c_204])).
% 9.08/2.99  tff(c_20183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20133, c_218])).
% 9.08/2.99  tff(c_20186, plain, (![B_9561]: ('#skF_1'(k1_tarski(B_9561), '#skF_10')=B_9561)), inference(splitRight, [status(thm)], [c_20131])).
% 9.08/2.99  tff(c_20318, plain, (![B_9616]: (~r2_hidden(B_9616, '#skF_10') | r1_tarski(k1_tarski(B_9616), '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_20186, c_4])).
% 9.08/2.99  tff(c_20623, plain, (![A_9699, B_9700]: (k1_relat_1('#skF_9'(A_9699, B_9700))!='#skF_11' | ~v1_funct_1('#skF_9'(A_9699, B_9700)) | ~v1_relat_1('#skF_9'(A_9699, B_9700)) | k1_xboole_0=A_9699 | ~r2_hidden(B_9700, '#skF_10'))), inference(resolution, [status(thm)], [c_20318, c_128])).
% 9.08/2.99  tff(c_20915, plain, (![A_9813, B_9814]: (k1_relat_1('#skF_9'(A_9813, B_9814))!='#skF_11' | ~v1_funct_1('#skF_9'(A_9813, B_9814)) | ~r2_hidden(B_9814, '#skF_10') | k1_xboole_0=A_9813)), inference(resolution, [status(thm)], [c_68, c_20623])).
% 9.08/2.99  tff(c_20921, plain, (![A_9841, B_9842]: (k1_relat_1('#skF_9'(A_9841, B_9842))!='#skF_11' | ~r2_hidden(B_9842, '#skF_10') | k1_xboole_0=A_9841)), inference(resolution, [status(thm)], [c_66, c_20915])).
% 9.08/2.99  tff(c_20926, plain, (![A_29, B_33]: (A_29!='#skF_11' | ~r2_hidden(B_33, '#skF_10') | k1_xboole_0=A_29 | k1_xboole_0=A_29)), inference(superposition, [status(thm), theory('equality')], [c_64, c_20921])).
% 9.08/2.99  tff(c_20929, plain, (![B_9869]: (~r2_hidden(B_9869, '#skF_10'))), inference(splitLeft, [status(thm)], [c_20926])).
% 9.08/2.99  tff(c_20989, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_17475, c_20929])).
% 9.08/2.99  tff(c_21056, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_20989])).
% 9.08/2.99  tff(c_21058, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_20926])).
% 9.08/2.99  tff(c_21110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21058, c_218])).
% 9.08/2.99  tff(c_21112, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_17342])).
% 9.08/2.99  tff(c_21141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21112, c_218])).
% 9.08/2.99  tff(c_21143, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_72])).
% 9.08/2.99  tff(c_21142, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_72])).
% 9.08/2.99  tff(c_21150, plain, ('#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_21143, c_21142])).
% 9.08/2.99  tff(c_21145, plain, (![A_15]: (r1_tarski('#skF_11', A_15))), inference(demodulation, [status(thm), theory('equality')], [c_21142, c_34])).
% 9.08/2.99  tff(c_21159, plain, (![A_15]: (r1_tarski('#skF_10', A_15))), inference(demodulation, [status(thm), theory('equality')], [c_21150, c_21145])).
% 9.08/2.99  tff(c_52, plain, (![A_22]: (k2_relat_1(A_22)=k1_xboole_0 | k1_relat_1(A_22)!=k1_xboole_0 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.08/2.99  tff(c_21247, plain, (![A_9924]: (k2_relat_1(A_9924)='#skF_10' | k1_relat_1(A_9924)!='#skF_10' | ~v1_relat_1(A_9924))), inference(demodulation, [status(thm), theory('equality')], [c_21143, c_21143, c_52])).
% 9.08/2.99  tff(c_21253, plain, (![A_23]: (k2_relat_1('#skF_8'(A_23))='#skF_10' | k1_relat_1('#skF_8'(A_23))!='#skF_10')), inference(resolution, [status(thm)], [c_60, c_21247])).
% 9.08/2.99  tff(c_21258, plain, (![A_9925]: (k2_relat_1('#skF_8'(A_9925))='#skF_10' | A_9925!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_21253])).
% 9.08/2.99  tff(c_21161, plain, (![C_36]: (~r1_tarski(k2_relat_1(C_36), '#skF_10') | k1_relat_1(C_36)!='#skF_10' | ~v1_funct_1(C_36) | ~v1_relat_1(C_36))), inference(demodulation, [status(thm), theory('equality')], [c_21150, c_70])).
% 9.08/2.99  tff(c_21264, plain, (![A_9925]: (~r1_tarski('#skF_10', '#skF_10') | k1_relat_1('#skF_8'(A_9925))!='#skF_10' | ~v1_funct_1('#skF_8'(A_9925)) | ~v1_relat_1('#skF_8'(A_9925)) | A_9925!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_21258, c_21161])).
% 9.08/2.99  tff(c_21270, plain, (![A_9925]: (A_9925!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_21159, c_21264])).
% 9.08/2.99  tff(c_21293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21270, c_21150])).
% 9.08/2.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.08/2.99  
% 9.08/2.99  Inference rules
% 9.08/2.99  ----------------------
% 9.08/2.99  #Ref     : 1
% 9.08/2.99  #Sup     : 3323
% 9.08/2.99  #Fact    : 4
% 9.08/2.99  #Define  : 0
% 9.08/2.99  #Split   : 5
% 9.08/2.99  #Chain   : 0
% 9.08/2.99  #Close   : 0
% 9.08/2.99  
% 9.08/2.99  Ordering : KBO
% 9.08/2.99  
% 9.08/2.99  Simplification rules
% 9.08/2.99  ----------------------
% 9.08/2.99  #Subsume      : 981
% 9.08/2.99  #Demod        : 924
% 9.08/2.99  #Tautology    : 452
% 9.08/2.99  #SimpNegUnit  : 79
% 9.08/2.99  #BackRed      : 140
% 9.08/2.99  
% 9.08/2.99  #Partial instantiations: 6606
% 9.08/2.99  #Strategies tried      : 1
% 9.08/2.99  
% 9.08/2.99  Timing (in seconds)
% 9.08/2.99  ----------------------
% 9.08/3.00  Preprocessing        : 0.37
% 9.08/3.00  Parsing              : 0.19
% 9.08/3.00  CNF conversion       : 0.04
% 9.08/3.00  Main loop            : 1.80
% 9.08/3.00  Inferencing          : 0.68
% 9.08/3.00  Reduction            : 0.47
% 9.08/3.00  Demodulation         : 0.32
% 9.08/3.00  BG Simplification    : 0.09
% 9.08/3.00  Subsumption          : 0.38
% 9.08/3.00  Abstraction          : 0.11
% 9.08/3.00  MUC search           : 0.00
% 9.08/3.00  Cooper               : 0.00
% 9.08/3.00  Total                : 2.22
% 9.08/3.00  Index Insertion      : 0.00
% 9.08/3.00  Index Deletion       : 0.00
% 9.08/3.00  Index Matching       : 0.00
% 9.08/3.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
