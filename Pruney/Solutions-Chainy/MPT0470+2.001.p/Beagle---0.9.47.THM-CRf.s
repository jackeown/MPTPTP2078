%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:00 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 357 expanded)
%              Number of leaves         :   29 ( 130 expanded)
%              Depth                    :   19
%              Number of atoms          :  162 ( 719 expanded)
%              Number of equality atoms :   37 ( 123 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_92,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_40,plain,
    ( k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_65,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_42,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_53,plain,(
    ! [A_26] :
      ( v1_relat_1(A_26)
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_57,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_53])).

tff(c_24,plain,(
    ! [A_14] :
      ( v1_relat_1(k4_relat_1(A_14))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k5_relat_1(A_15,B_16))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_160,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_55,B_56)),k2_relat_1(B_56))
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_171,plain,(
    ! [A_55] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_55,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_160])).

tff(c_177,plain,(
    ! [A_57] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_57,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_171])).

tff(c_106,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_2'(A_38,B_39),A_38)
      | r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [A_40,B_41] :
      ( ~ v1_xboole_0(A_40)
      | r1_tarski(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_120,plain,(
    ! [B_41,A_40] :
      ( B_41 = A_40
      | ~ r1_tarski(B_41,A_40)
      | ~ v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_117,c_16])).

tff(c_183,plain,(
    ! [A_57] :
      ( k2_relat_1(k5_relat_1(A_57,k1_xboole_0)) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(A_57) ) ),
    inference(resolution,[status(thm)],[c_177,c_120])).

tff(c_209,plain,(
    ! [A_59] :
      ( k2_relat_1(k5_relat_1(A_59,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_183])).

tff(c_28,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(k2_relat_1(A_17))
      | ~ v1_relat_1(A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_227,plain,(
    ! [A_59] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_59,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_59,k1_xboole_0))
      | ~ v1_relat_1(A_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_28])).

tff(c_272,plain,(
    ! [A_65] :
      ( ~ v1_relat_1(k5_relat_1(A_65,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_65,k1_xboole_0))
      | ~ v1_relat_1(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_227])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_401,plain,(
    ! [A_78] :
      ( k5_relat_1(A_78,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_78,k1_xboole_0))
      | ~ v1_relat_1(A_78) ) ),
    inference(resolution,[status(thm)],[c_272,c_14])).

tff(c_405,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_15) ) ),
    inference(resolution,[status(thm)],[c_26,c_401])).

tff(c_409,plain,(
    ! [A_79] :
      ( k5_relat_1(A_79,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_405])).

tff(c_427,plain,(
    ! [A_14] :
      ( k5_relat_1(k4_relat_1(A_14),k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_14) ) ),
    inference(resolution,[status(thm)],[c_24,c_409])).

tff(c_30,plain,(
    ! [A_18] :
      ( k4_relat_1(k4_relat_1(A_18)) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_239,plain,(
    ! [B_60,A_61] :
      ( k5_relat_1(k4_relat_1(B_60),k4_relat_1(A_61)) = k4_relat_1(k5_relat_1(A_61,B_60))
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1183,plain,(
    ! [A_109,B_110] :
      ( k4_relat_1(k5_relat_1(k4_relat_1(A_109),B_110)) = k5_relat_1(k4_relat_1(B_110),A_109)
      | ~ v1_relat_1(B_110)
      | ~ v1_relat_1(k4_relat_1(A_109))
      | ~ v1_relat_1(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_239])).

tff(c_1230,plain,(
    ! [A_14] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_14) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_14))
      | ~ v1_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_427,c_1183])).

tff(c_1241,plain,(
    ! [A_111] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_111) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_111))
      | ~ v1_relat_1(A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_1230])).

tff(c_1259,plain,(
    ! [A_112] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_112) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_112) ) ),
    inference(resolution,[status(thm)],[c_24,c_1241])).

tff(c_1297,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1259,c_427])).

tff(c_1352,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_57,c_1297])).

tff(c_1258,plain,(
    ! [A_14] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_14) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_14) ) ),
    inference(resolution,[status(thm)],[c_24,c_1241])).

tff(c_1474,plain,(
    ! [A_115] :
      ( k5_relat_1(k1_xboole_0,A_115) = k1_xboole_0
      | ~ v1_relat_1(A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1352,c_1352,c_1258])).

tff(c_1495,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_1474])).

tff(c_1506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_1495])).

tff(c_1507,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1612,plain,(
    ! [A_141,B_142] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_141,B_142)),k2_relat_1(B_142))
      | ~ v1_relat_1(B_142)
      | ~ v1_relat_1(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1626,plain,(
    ! [A_141] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_141,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1612])).

tff(c_1651,plain,(
    ! [A_143] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_143,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_1626])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1588,plain,(
    ! [C_134,B_135,A_136] :
      ( r2_hidden(C_134,B_135)
      | ~ r2_hidden(C_134,A_136)
      | ~ r1_tarski(A_136,B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1595,plain,(
    ! [A_137,B_138] :
      ( r2_hidden('#skF_1'(A_137),B_138)
      | ~ r1_tarski(A_137,B_138)
      | v1_xboole_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_4,c_1588])).

tff(c_1602,plain,(
    ! [B_138,A_137] :
      ( ~ v1_xboole_0(B_138)
      | ~ r1_tarski(A_137,B_138)
      | v1_xboole_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_1595,c_2])).

tff(c_1654,plain,(
    ! [A_143] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k2_relat_1(k5_relat_1(A_143,k1_xboole_0)))
      | ~ v1_relat_1(A_143) ) ),
    inference(resolution,[status(thm)],[c_1651,c_1602])).

tff(c_1667,plain,(
    ! [A_144] :
      ( v1_xboole_0(k2_relat_1(k5_relat_1(A_144,k1_xboole_0)))
      | ~ v1_relat_1(A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1654])).

tff(c_1739,plain,(
    ! [A_149] :
      ( ~ v1_relat_1(k5_relat_1(A_149,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_149,k1_xboole_0))
      | ~ v1_relat_1(A_149) ) ),
    inference(resolution,[status(thm)],[c_1667,c_28])).

tff(c_1761,plain,(
    ! [A_152] :
      ( k5_relat_1(A_152,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_152,k1_xboole_0))
      | ~ v1_relat_1(A_152) ) ),
    inference(resolution,[status(thm)],[c_1739,c_14])).

tff(c_1765,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_15) ) ),
    inference(resolution,[status(thm)],[c_26,c_1761])).

tff(c_1769,plain,(
    ! [A_153] :
      ( k5_relat_1(A_153,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_1765])).

tff(c_1784,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_1769])).

tff(c_1792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1507,c_1784])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.59  
% 3.50/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.60  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 3.50/1.60  
% 3.50/1.60  %Foreground sorts:
% 3.50/1.60  
% 3.50/1.60  
% 3.50/1.60  %Background operators:
% 3.50/1.60  
% 3.50/1.60  
% 3.50/1.60  %Foreground operators:
% 3.50/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.50/1.60  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.50/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.50/1.60  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.50/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.50/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.50/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.50/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.50/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.50/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.50/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.50/1.60  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.50/1.60  
% 3.84/1.61  tff(f_99, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.84/1.61  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.84/1.61  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.84/1.61  tff(f_57, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.84/1.61  tff(f_63, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.84/1.61  tff(f_92, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.84/1.61  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.84/1.61  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.84/1.61  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.84/1.61  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.84/1.61  tff(f_71, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.84/1.61  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.84/1.61  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 3.84/1.61  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 3.84/1.61  tff(c_40, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.84/1.61  tff(c_65, plain, (k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 3.84/1.61  tff(c_42, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.84/1.61  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.84/1.61  tff(c_53, plain, (![A_26]: (v1_relat_1(A_26) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.84/1.61  tff(c_57, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_53])).
% 3.84/1.61  tff(c_24, plain, (![A_14]: (v1_relat_1(k4_relat_1(A_14)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.84/1.61  tff(c_26, plain, (![A_15, B_16]: (v1_relat_1(k5_relat_1(A_15, B_16)) | ~v1_relat_1(B_16) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.84/1.61  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.84/1.61  tff(c_160, plain, (![A_55, B_56]: (r1_tarski(k2_relat_1(k5_relat_1(A_55, B_56)), k2_relat_1(B_56)) | ~v1_relat_1(B_56) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.84/1.61  tff(c_171, plain, (![A_55]: (r1_tarski(k2_relat_1(k5_relat_1(A_55, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_55))), inference(superposition, [status(thm), theory('equality')], [c_36, c_160])).
% 3.84/1.61  tff(c_177, plain, (![A_57]: (r1_tarski(k2_relat_1(k5_relat_1(A_57, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_57))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_171])).
% 3.84/1.61  tff(c_106, plain, (![A_38, B_39]: (r2_hidden('#skF_2'(A_38, B_39), A_38) | r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.84/1.61  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.84/1.61  tff(c_117, plain, (![A_40, B_41]: (~v1_xboole_0(A_40) | r1_tarski(A_40, B_41))), inference(resolution, [status(thm)], [c_106, c_2])).
% 3.84/1.61  tff(c_16, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.84/1.61  tff(c_120, plain, (![B_41, A_40]: (B_41=A_40 | ~r1_tarski(B_41, A_40) | ~v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_117, c_16])).
% 3.84/1.61  tff(c_183, plain, (![A_57]: (k2_relat_1(k5_relat_1(A_57, k1_xboole_0))=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(A_57))), inference(resolution, [status(thm)], [c_177, c_120])).
% 3.84/1.61  tff(c_209, plain, (![A_59]: (k2_relat_1(k5_relat_1(A_59, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_183])).
% 3.84/1.61  tff(c_28, plain, (![A_17]: (~v1_xboole_0(k2_relat_1(A_17)) | ~v1_relat_1(A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.84/1.61  tff(c_227, plain, (![A_59]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_59, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_59, k1_xboole_0)) | ~v1_relat_1(A_59))), inference(superposition, [status(thm), theory('equality')], [c_209, c_28])).
% 3.84/1.61  tff(c_272, plain, (![A_65]: (~v1_relat_1(k5_relat_1(A_65, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_65, k1_xboole_0)) | ~v1_relat_1(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_227])).
% 3.84/1.61  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.84/1.61  tff(c_401, plain, (![A_78]: (k5_relat_1(A_78, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_78, k1_xboole_0)) | ~v1_relat_1(A_78))), inference(resolution, [status(thm)], [c_272, c_14])).
% 3.84/1.61  tff(c_405, plain, (![A_15]: (k5_relat_1(A_15, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_15))), inference(resolution, [status(thm)], [c_26, c_401])).
% 3.84/1.61  tff(c_409, plain, (![A_79]: (k5_relat_1(A_79, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_79))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_405])).
% 3.84/1.61  tff(c_427, plain, (![A_14]: (k5_relat_1(k4_relat_1(A_14), k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_14))), inference(resolution, [status(thm)], [c_24, c_409])).
% 3.84/1.61  tff(c_30, plain, (![A_18]: (k4_relat_1(k4_relat_1(A_18))=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.84/1.61  tff(c_239, plain, (![B_60, A_61]: (k5_relat_1(k4_relat_1(B_60), k4_relat_1(A_61))=k4_relat_1(k5_relat_1(A_61, B_60)) | ~v1_relat_1(B_60) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.84/1.61  tff(c_1183, plain, (![A_109, B_110]: (k4_relat_1(k5_relat_1(k4_relat_1(A_109), B_110))=k5_relat_1(k4_relat_1(B_110), A_109) | ~v1_relat_1(B_110) | ~v1_relat_1(k4_relat_1(A_109)) | ~v1_relat_1(A_109))), inference(superposition, [status(thm), theory('equality')], [c_30, c_239])).
% 3.84/1.61  tff(c_1230, plain, (![A_14]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_14)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_14)) | ~v1_relat_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_427, c_1183])).
% 3.84/1.61  tff(c_1241, plain, (![A_111]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_111)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_111)) | ~v1_relat_1(A_111))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_1230])).
% 3.84/1.61  tff(c_1259, plain, (![A_112]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_112)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(A_112))), inference(resolution, [status(thm)], [c_24, c_1241])).
% 3.84/1.61  tff(c_1297, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1259, c_427])).
% 3.84/1.61  tff(c_1352, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_57, c_57, c_1297])).
% 3.84/1.61  tff(c_1258, plain, (![A_14]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_14)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(A_14))), inference(resolution, [status(thm)], [c_24, c_1241])).
% 3.84/1.61  tff(c_1474, plain, (![A_115]: (k5_relat_1(k1_xboole_0, A_115)=k1_xboole_0 | ~v1_relat_1(A_115))), inference(demodulation, [status(thm), theory('equality')], [c_1352, c_1352, c_1258])).
% 3.84/1.61  tff(c_1495, plain, (k5_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_1474])).
% 3.84/1.61  tff(c_1506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_1495])).
% 3.84/1.61  tff(c_1507, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 3.84/1.61  tff(c_1612, plain, (![A_141, B_142]: (r1_tarski(k2_relat_1(k5_relat_1(A_141, B_142)), k2_relat_1(B_142)) | ~v1_relat_1(B_142) | ~v1_relat_1(A_141))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.84/1.61  tff(c_1626, plain, (![A_141]: (r1_tarski(k2_relat_1(k5_relat_1(A_141, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_141))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1612])).
% 3.84/1.61  tff(c_1651, plain, (![A_143]: (r1_tarski(k2_relat_1(k5_relat_1(A_143, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_143))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_1626])).
% 3.84/1.61  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.84/1.61  tff(c_1588, plain, (![C_134, B_135, A_136]: (r2_hidden(C_134, B_135) | ~r2_hidden(C_134, A_136) | ~r1_tarski(A_136, B_135))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.84/1.61  tff(c_1595, plain, (![A_137, B_138]: (r2_hidden('#skF_1'(A_137), B_138) | ~r1_tarski(A_137, B_138) | v1_xboole_0(A_137))), inference(resolution, [status(thm)], [c_4, c_1588])).
% 3.84/1.61  tff(c_1602, plain, (![B_138, A_137]: (~v1_xboole_0(B_138) | ~r1_tarski(A_137, B_138) | v1_xboole_0(A_137))), inference(resolution, [status(thm)], [c_1595, c_2])).
% 3.84/1.61  tff(c_1654, plain, (![A_143]: (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_relat_1(k5_relat_1(A_143, k1_xboole_0))) | ~v1_relat_1(A_143))), inference(resolution, [status(thm)], [c_1651, c_1602])).
% 3.84/1.61  tff(c_1667, plain, (![A_144]: (v1_xboole_0(k2_relat_1(k5_relat_1(A_144, k1_xboole_0))) | ~v1_relat_1(A_144))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1654])).
% 3.84/1.61  tff(c_1739, plain, (![A_149]: (~v1_relat_1(k5_relat_1(A_149, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_149, k1_xboole_0)) | ~v1_relat_1(A_149))), inference(resolution, [status(thm)], [c_1667, c_28])).
% 3.84/1.61  tff(c_1761, plain, (![A_152]: (k5_relat_1(A_152, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_152, k1_xboole_0)) | ~v1_relat_1(A_152))), inference(resolution, [status(thm)], [c_1739, c_14])).
% 3.84/1.61  tff(c_1765, plain, (![A_15]: (k5_relat_1(A_15, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_15))), inference(resolution, [status(thm)], [c_26, c_1761])).
% 3.84/1.61  tff(c_1769, plain, (![A_153]: (k5_relat_1(A_153, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_153))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_1765])).
% 3.84/1.61  tff(c_1784, plain, (k5_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_1769])).
% 3.84/1.61  tff(c_1792, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1507, c_1784])).
% 3.84/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.61  
% 3.84/1.61  Inference rules
% 3.84/1.61  ----------------------
% 3.84/1.61  #Ref     : 0
% 3.84/1.61  #Sup     : 411
% 3.84/1.61  #Fact    : 0
% 3.84/1.61  #Define  : 0
% 3.84/1.61  #Split   : 4
% 3.84/1.61  #Chain   : 0
% 3.84/1.61  #Close   : 0
% 3.84/1.61  
% 3.84/1.61  Ordering : KBO
% 3.84/1.61  
% 3.84/1.61  Simplification rules
% 3.84/1.61  ----------------------
% 3.84/1.61  #Subsume      : 96
% 3.84/1.61  #Demod        : 343
% 3.84/1.61  #Tautology    : 156
% 3.84/1.61  #SimpNegUnit  : 11
% 3.84/1.61  #BackRed      : 8
% 3.84/1.61  
% 3.84/1.61  #Partial instantiations: 0
% 3.84/1.61  #Strategies tried      : 1
% 3.84/1.61  
% 3.84/1.61  Timing (in seconds)
% 3.84/1.61  ----------------------
% 3.84/1.62  Preprocessing        : 0.29
% 3.84/1.62  Parsing              : 0.16
% 3.84/1.62  CNF conversion       : 0.02
% 3.84/1.62  Main loop            : 0.55
% 3.84/1.62  Inferencing          : 0.21
% 3.84/1.62  Reduction            : 0.15
% 3.84/1.62  Demodulation         : 0.10
% 3.84/1.62  BG Simplification    : 0.03
% 3.84/1.62  Subsumption          : 0.12
% 3.84/1.62  Abstraction          : 0.03
% 3.84/1.62  MUC search           : 0.00
% 3.84/1.62  Cooper               : 0.00
% 3.84/1.62  Total                : 0.88
% 3.84/1.62  Index Insertion      : 0.00
% 3.84/1.62  Index Deletion       : 0.00
% 3.84/1.62  Index Matching       : 0.00
% 3.84/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
