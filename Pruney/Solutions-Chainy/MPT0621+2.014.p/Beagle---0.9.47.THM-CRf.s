%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:00 EST 2020

% Result     : Theorem 11.97s
% Output     : CNFRefutation 11.97s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 592 expanded)
%              Number of leaves         :   30 ( 219 expanded)
%              Depth                    :   19
%              Number of atoms          :  205 (1482 expanded)
%              Number of equality atoms :   94 ( 540 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k1_relat_1 > np__1 > k1_xboole_0 > #skF_9 > #skF_6 > #skF_1 > #skF_10 > #skF_2 > #skF_8 > #skF_7 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( k1_relat_1(B) = A
                    & k1_relat_1(C) = A )
                 => B = C ) ) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_73,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,(
    ! [A_30,B_31] : v1_funct_1('#skF_8'(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40,plain,(
    ! [A_30,B_31] : k1_relat_1('#skF_8'(A_30,B_31)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_44,plain,(
    ! [A_30,B_31] : v1_relat_1('#skF_8'(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_50,plain,(
    ! [A_37] : v1_funct_1('#skF_9'(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_48,plain,(
    ! [A_37] : k1_relat_1('#skF_9'(A_37)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_52,plain,(
    ! [A_37] : v1_relat_1('#skF_9'(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_76,plain,(
    ! [C_60,B_61] :
      ( C_60 = B_61
      | k1_relat_1(C_60) != '#skF_10'
      | k1_relat_1(B_61) != '#skF_10'
      | ~ v1_funct_1(C_60)
      | ~ v1_relat_1(C_60)
      | ~ v1_funct_1(B_61)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_80,plain,(
    ! [B_61,A_37] :
      ( B_61 = '#skF_9'(A_37)
      | k1_relat_1('#skF_9'(A_37)) != '#skF_10'
      | k1_relat_1(B_61) != '#skF_10'
      | ~ v1_funct_1('#skF_9'(A_37))
      | ~ v1_funct_1(B_61)
      | ~ v1_relat_1(B_61) ) ),
    inference(resolution,[status(thm)],[c_52,c_76])).

tff(c_148,plain,(
    ! [B_83,A_84] :
      ( B_83 = '#skF_9'(A_84)
      | A_84 != '#skF_10'
      | k1_relat_1(B_83) != '#skF_10'
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_80])).

tff(c_150,plain,(
    ! [A_84,A_30,B_31] :
      ( '#skF_9'(A_84) = '#skF_8'(A_30,B_31)
      | A_84 != '#skF_10'
      | k1_relat_1('#skF_8'(A_30,B_31)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_30,B_31)) ) ),
    inference(resolution,[status(thm)],[c_44,c_148])).

tff(c_246,plain,(
    ! [A_98,A_99,B_100] :
      ( '#skF_9'(A_98) = '#skF_8'(A_99,B_100)
      | A_98 != '#skF_10'
      | A_99 != '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_150])).

tff(c_38,plain,(
    ! [A_30,B_31,D_36] :
      ( k1_funct_1('#skF_8'(A_30,B_31),D_36) = B_31
      | ~ r2_hidden(D_36,A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_487,plain,(
    ! [A_129,D_130,B_131,A_132] :
      ( k1_funct_1('#skF_9'(A_129),D_130) = B_131
      | ~ r2_hidden(D_130,A_132)
      | A_129 != '#skF_10'
      | A_132 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_38])).

tff(c_24184,plain,(
    ! [A_129,A_1] :
      ( k1_funct_1('#skF_9'(A_129),'#skF_1'(A_1)) = '#skF_10'
      | A_129 != '#skF_10'
      | A_1 != '#skF_10'
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_487])).

tff(c_23103,plain,(
    ! [A_129,A_1] :
      ( k1_funct_1('#skF_9'(A_129),'#skF_1'(A_1)) = k1_xboole_0
      | A_129 != '#skF_10'
      | A_1 != '#skF_10'
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_487])).

tff(c_824,plain,(
    ! [A_141,A_142] :
      ( k1_funct_1('#skF_9'(A_141),'#skF_1'(A_142)) = '#skF_10'
      | A_141 != '#skF_10'
      | A_142 != '#skF_10'
      | v1_xboole_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_4,c_487])).

tff(c_46,plain,(
    ! [A_37,C_42] :
      ( k1_funct_1('#skF_9'(A_37),C_42) = np__1
      | ~ r2_hidden(C_42,A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_827,plain,(
    ! [A_142,A_141] :
      ( np__1 = '#skF_10'
      | ~ r2_hidden('#skF_1'(A_142),A_141)
      | A_141 != '#skF_10'
      | A_142 != '#skF_10'
      | v1_xboole_0(A_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_824,c_46])).

tff(c_23027,plain,(
    np__1 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_827])).

tff(c_23041,plain,(
    ! [A_25748,C_25749] :
      ( k1_funct_1('#skF_9'(A_25748),C_25749) = '#skF_10'
      | ~ r2_hidden(C_25749,A_25748) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23027,c_46])).

tff(c_23106,plain,(
    ! [A_1,A_129] :
      ( k1_xboole_0 = '#skF_10'
      | ~ r2_hidden('#skF_1'(A_1),A_129)
      | A_129 != '#skF_10'
      | A_1 != '#skF_10'
      | v1_xboole_0(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23103,c_23041])).

tff(c_23163,plain,(
    ! [A_25854,A_25855] :
      ( ~ r2_hidden('#skF_1'(A_25854),A_25855)
      | A_25855 != '#skF_10'
      | A_25854 != '#skF_10'
      | v1_xboole_0(A_25854) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_23106])).

tff(c_23235,plain,(
    v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_4,c_23163])).

tff(c_71,plain,(
    ! [D_58,A_59] : r2_hidden(D_58,k2_tarski(A_59,D_58)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_59,D_58] : ~ v1_xboole_0(k2_tarski(A_59,D_58)) ),
    inference(resolution,[status(thm)],[c_71,c_2])).

tff(c_227,plain,(
    ! [D_95,B_96,A_97] :
      ( D_95 = B_96
      | D_95 = A_97
      | ~ r2_hidden(D_95,k2_tarski(A_97,B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_231,plain,(
    ! [A_97,B_96] :
      ( '#skF_1'(k2_tarski(A_97,B_96)) = B_96
      | '#skF_1'(k2_tarski(A_97,B_96)) = A_97
      | v1_xboole_0(k2_tarski(A_97,B_96)) ) ),
    inference(resolution,[status(thm)],[c_4,c_227])).

tff(c_240,plain,(
    ! [A_97,B_96] :
      ( '#skF_1'(k2_tarski(A_97,B_96)) = B_96
      | '#skF_1'(k2_tarski(A_97,B_96)) = A_97 ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_231])).

tff(c_307,plain,(
    ! [B_96] : '#skF_1'(k2_tarski(B_96,B_96)) = B_96 ),
    inference(factorization,[status(thm),theory(equality)],[c_240])).

tff(c_517,plain,(
    ! [A_141,A_142,B_143] :
      ( k1_funct_1('#skF_9'(A_141),'#skF_1'(A_142)) = B_143
      | A_141 != '#skF_10'
      | A_142 != '#skF_10'
      | v1_xboole_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_4,c_487])).

tff(c_10,plain,(
    ! [D_10,A_5] : r2_hidden(D_10,k2_tarski(A_5,D_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_125,plain,(
    ! [C_74,A_75,D_76] :
      ( r2_hidden(C_74,k1_relat_1(A_75))
      | ~ r2_hidden(k4_tarski(C_74,D_76),A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_159,plain,(
    ! [C_85,A_86,D_87] : r2_hidden(C_85,k1_relat_1(k2_tarski(A_86,k4_tarski(C_85,D_87)))) ),
    inference(resolution,[status(thm)],[c_10,c_125])).

tff(c_28,plain,(
    ! [C_26,A_11,D_29] :
      ( r2_hidden(C_26,k1_relat_1(A_11))
      | ~ r2_hidden(k4_tarski(C_26,D_29),A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_465,plain,(
    ! [C_119,A_120,D_121,D_122] : r2_hidden(C_119,k1_relat_1(k1_relat_1(k2_tarski(A_120,k4_tarski(k4_tarski(C_119,D_121),D_122))))) ),
    inference(resolution,[status(thm)],[c_159,c_28])).

tff(c_474,plain,(
    ! [A_120,C_119,D_121,D_122] : ~ v1_xboole_0(k1_relat_1(k1_relat_1(k2_tarski(A_120,k4_tarski(k4_tarski(C_119,D_121),D_122))))) ),
    inference(resolution,[status(thm)],[c_465,c_2])).

tff(c_991,plain,(
    ! [A_1224,A_1225] :
      ( ~ v1_xboole_0(k1_funct_1('#skF_9'(A_1224),'#skF_1'(A_1225)))
      | A_1224 != '#skF_10'
      | A_1225 != '#skF_10'
      | v1_xboole_0(A_1225) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_474])).

tff(c_1003,plain,(
    ! [A_1224,B_96] :
      ( ~ v1_xboole_0(k1_funct_1('#skF_9'(A_1224),B_96))
      | A_1224 != '#skF_10'
      | k2_tarski(B_96,B_96) != '#skF_10'
      | v1_xboole_0(k2_tarski(B_96,B_96)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_991])).

tff(c_1027,plain,(
    ! [A_1252,B_1253] :
      ( ~ v1_xboole_0(k1_funct_1('#skF_9'(A_1252),B_1253))
      | A_1252 != '#skF_10'
      | k2_tarski(B_1253,B_1253) != '#skF_10' ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1003])).

tff(c_1041,plain,(
    ! [A_37,C_42] :
      ( ~ v1_xboole_0(np__1)
      | A_37 != '#skF_10'
      | k2_tarski(C_42,C_42) != '#skF_10'
      | ~ r2_hidden(C_42,A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1027])).

tff(c_17409,plain,(
    ~ v1_xboole_0(np__1) ),
    inference(splitLeft,[status(thm)],[c_1041])).

tff(c_23030,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23027,c_17409])).

tff(c_23238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23235,c_23030])).

tff(c_23242,plain,(
    ! [A_26064,A_26065] :
      ( ~ r2_hidden('#skF_1'(A_26064),A_26065)
      | A_26065 != '#skF_10'
      | A_26064 != '#skF_10'
      | v1_xboole_0(A_26064) ) ),
    inference(splitRight,[status(thm)],[c_827])).

tff(c_23335,plain,(
    ! [A_26170] :
      ( A_26170 != '#skF_10'
      | v1_xboole_0(A_26170) ) ),
    inference(resolution,[status(thm)],[c_4,c_23242])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1816,plain,(
    ! [A_2424,B_2425] :
      ( r2_hidden(k4_tarski('#skF_4'(A_2424,B_2425),'#skF_5'(A_2424,B_2425)),A_2424)
      | r2_hidden('#skF_6'(A_2424,B_2425),B_2425)
      | k1_relat_1(A_2424) = B_2425 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2027,plain,(
    ! [A_2621,B_2622] :
      ( ~ v1_xboole_0(A_2621)
      | r2_hidden('#skF_6'(A_2621,B_2622),B_2622)
      | k1_relat_1(A_2621) = B_2622 ) ),
    inference(resolution,[status(thm)],[c_1816,c_2])).

tff(c_2082,plain,(
    ! [B_2649,A_2650] :
      ( ~ v1_xboole_0(B_2649)
      | ~ v1_xboole_0(A_2650)
      | k1_relat_1(A_2650) = B_2649 ) ),
    inference(resolution,[status(thm)],[c_2027,c_2])).

tff(c_2963,plain,(
    ! [A_5124] :
      ( ~ v1_xboole_0(A_5124)
      | k1_relat_1(A_5124) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_2082])).

tff(c_2999,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_2963])).

tff(c_36,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(k4_tarski('#skF_4'(A_11,B_12),'#skF_5'(A_11,B_12)),A_11)
      | r2_hidden('#skF_6'(A_11,B_12),B_12)
      | k1_relat_1(A_11) = B_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [C_26,A_11] :
      ( r2_hidden(k4_tarski(C_26,'#skF_7'(A_11,k1_relat_1(A_11),C_26)),A_11)
      | ~ r2_hidden(C_26,k1_relat_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1042,plain,(
    ! [C_1280,A_1281] :
      ( r2_hidden(k4_tarski(C_1280,'#skF_7'(A_1281,k1_relat_1(A_1281),C_1280)),A_1281)
      | ~ r2_hidden(C_1280,k1_relat_1(A_1281)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1073,plain,(
    ! [A_1308,C_1309] :
      ( ~ v1_xboole_0(A_1308)
      | ~ r2_hidden(C_1309,k1_relat_1(A_1308)) ) ),
    inference(resolution,[status(thm)],[c_1042,c_2])).

tff(c_1194,plain,(
    ! [A_1502,C_1503] :
      ( ~ v1_xboole_0(A_1502)
      | ~ r2_hidden(C_1503,k1_relat_1(k1_relat_1(A_1502))) ) ),
    inference(resolution,[status(thm)],[c_26,c_1073])).

tff(c_1448,plain,(
    ! [A_1896,C_1897] :
      ( ~ v1_xboole_0(A_1896)
      | ~ r2_hidden(C_1897,k1_relat_1(k1_relat_1(k1_relat_1(A_1896)))) ) ),
    inference(resolution,[status(thm)],[c_26,c_1194])).

tff(c_1473,plain,(
    ! [A_1896,C_26] :
      ( ~ v1_xboole_0(A_1896)
      | ~ r2_hidden(C_26,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(A_1896))))) ) ),
    inference(resolution,[status(thm)],[c_26,c_1448])).

tff(c_3018,plain,(
    ! [C_26] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_26,k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2999,c_1473])).

tff(c_3079,plain,(
    ! [C_5229] : ~ r2_hidden(C_5229,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2999,c_2999,c_2999,c_6,c_3018])).

tff(c_3087,plain,(
    ! [B_12] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_12),B_12)
      | k1_relat_1(k1_xboole_0) = B_12 ) ),
    inference(resolution,[status(thm)],[c_36,c_3079])).

tff(c_4529,plain,(
    ! [B_8255] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_8255),B_8255)
      | k1_xboole_0 = B_8255 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2999,c_3087])).

tff(c_4591,plain,(
    ! [B_8255] :
      ( ~ v1_xboole_0(B_8255)
      | k1_xboole_0 = B_8255 ) ),
    inference(resolution,[status(thm)],[c_4529,c_2])).

tff(c_23767,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_23335,c_4591])).

tff(c_23807,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23767,c_54])).

tff(c_23809,plain,(
    v1_xboole_0(np__1) ),
    inference(splitRight,[status(thm)],[c_1041])).

tff(c_23878,plain,(
    np__1 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23809,c_4591])).

tff(c_24127,plain,(
    ! [A_26643,C_26644] :
      ( k1_funct_1('#skF_9'(A_26643),C_26644) = k1_xboole_0
      | ~ r2_hidden(C_26644,A_26643) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23878,c_46])).

tff(c_24187,plain,(
    ! [A_1,A_129] :
      ( k1_xboole_0 = '#skF_10'
      | ~ r2_hidden('#skF_1'(A_1),A_129)
      | A_129 != '#skF_10'
      | A_1 != '#skF_10'
      | v1_xboole_0(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24184,c_24127])).

tff(c_24338,plain,(
    ! [A_26857,A_26858] :
      ( ~ r2_hidden('#skF_1'(A_26857),A_26858)
      | A_26858 != '#skF_10'
      | A_26857 != '#skF_10'
      | v1_xboole_0(A_26857) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_24187])).

tff(c_24411,plain,(
    ! [A_26963] :
      ( A_26963 != '#skF_10'
      | v1_xboole_0(A_26963) ) ),
    inference(resolution,[status(thm)],[c_4,c_24338])).

tff(c_24767,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_24411,c_4591])).

tff(c_24802,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24767,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:05:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.97/4.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.97/4.85  
% 11.97/4.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.97/4.86  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k1_relat_1 > np__1 > k1_xboole_0 > #skF_9 > #skF_6 > #skF_1 > #skF_10 > #skF_2 > #skF_8 > #skF_7 > #skF_3 > #skF_5 > #skF_4
% 11.97/4.86  
% 11.97/4.86  %Foreground sorts:
% 11.97/4.86  
% 11.97/4.86  
% 11.97/4.86  %Background operators:
% 11.97/4.86  
% 11.97/4.86  
% 11.97/4.86  %Foreground operators:
% 11.97/4.86  tff('#skF_9', type, '#skF_9': $i > $i).
% 11.97/4.86  tff(np__1, type, np__1: $i).
% 11.97/4.86  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 11.97/4.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.97/4.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.97/4.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.97/4.86  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.97/4.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.97/4.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.97/4.86  tff('#skF_10', type, '#skF_10': $i).
% 11.97/4.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.97/4.86  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.97/4.86  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 11.97/4.86  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 11.97/4.86  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.97/4.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.97/4.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.97/4.86  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.97/4.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.97/4.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.97/4.86  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 11.97/4.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.97/4.86  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.97/4.86  
% 11.97/4.88  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.97/4.88  tff(f_92, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 11.97/4.88  tff(f_61, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 11.97/4.88  tff(f_73, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 11.97/4.88  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 11.97/4.88  tff(f_49, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 11.97/4.88  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.97/4.88  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.97/4.88  tff(c_54, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.97/4.88  tff(c_42, plain, (![A_30, B_31]: (v1_funct_1('#skF_8'(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.97/4.88  tff(c_40, plain, (![A_30, B_31]: (k1_relat_1('#skF_8'(A_30, B_31))=A_30)), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.97/4.88  tff(c_44, plain, (![A_30, B_31]: (v1_relat_1('#skF_8'(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.97/4.88  tff(c_50, plain, (![A_37]: (v1_funct_1('#skF_9'(A_37)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.97/4.88  tff(c_48, plain, (![A_37]: (k1_relat_1('#skF_9'(A_37))=A_37)), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.97/4.88  tff(c_52, plain, (![A_37]: (v1_relat_1('#skF_9'(A_37)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.97/4.88  tff(c_76, plain, (![C_60, B_61]: (C_60=B_61 | k1_relat_1(C_60)!='#skF_10' | k1_relat_1(B_61)!='#skF_10' | ~v1_funct_1(C_60) | ~v1_relat_1(C_60) | ~v1_funct_1(B_61) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.97/4.88  tff(c_80, plain, (![B_61, A_37]: (B_61='#skF_9'(A_37) | k1_relat_1('#skF_9'(A_37))!='#skF_10' | k1_relat_1(B_61)!='#skF_10' | ~v1_funct_1('#skF_9'(A_37)) | ~v1_funct_1(B_61) | ~v1_relat_1(B_61))), inference(resolution, [status(thm)], [c_52, c_76])).
% 11.97/4.88  tff(c_148, plain, (![B_83, A_84]: (B_83='#skF_9'(A_84) | A_84!='#skF_10' | k1_relat_1(B_83)!='#skF_10' | ~v1_funct_1(B_83) | ~v1_relat_1(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_80])).
% 11.97/4.88  tff(c_150, plain, (![A_84, A_30, B_31]: ('#skF_9'(A_84)='#skF_8'(A_30, B_31) | A_84!='#skF_10' | k1_relat_1('#skF_8'(A_30, B_31))!='#skF_10' | ~v1_funct_1('#skF_8'(A_30, B_31)))), inference(resolution, [status(thm)], [c_44, c_148])).
% 11.97/4.88  tff(c_246, plain, (![A_98, A_99, B_100]: ('#skF_9'(A_98)='#skF_8'(A_99, B_100) | A_98!='#skF_10' | A_99!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_150])).
% 11.97/4.88  tff(c_38, plain, (![A_30, B_31, D_36]: (k1_funct_1('#skF_8'(A_30, B_31), D_36)=B_31 | ~r2_hidden(D_36, A_30))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.97/4.88  tff(c_487, plain, (![A_129, D_130, B_131, A_132]: (k1_funct_1('#skF_9'(A_129), D_130)=B_131 | ~r2_hidden(D_130, A_132) | A_129!='#skF_10' | A_132!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_246, c_38])).
% 11.97/4.88  tff(c_24184, plain, (![A_129, A_1]: (k1_funct_1('#skF_9'(A_129), '#skF_1'(A_1))='#skF_10' | A_129!='#skF_10' | A_1!='#skF_10' | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_487])).
% 11.97/4.88  tff(c_23103, plain, (![A_129, A_1]: (k1_funct_1('#skF_9'(A_129), '#skF_1'(A_1))=k1_xboole_0 | A_129!='#skF_10' | A_1!='#skF_10' | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_487])).
% 11.97/4.88  tff(c_824, plain, (![A_141, A_142]: (k1_funct_1('#skF_9'(A_141), '#skF_1'(A_142))='#skF_10' | A_141!='#skF_10' | A_142!='#skF_10' | v1_xboole_0(A_142))), inference(resolution, [status(thm)], [c_4, c_487])).
% 11.97/4.88  tff(c_46, plain, (![A_37, C_42]: (k1_funct_1('#skF_9'(A_37), C_42)=np__1 | ~r2_hidden(C_42, A_37))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.97/4.88  tff(c_827, plain, (![A_142, A_141]: (np__1='#skF_10' | ~r2_hidden('#skF_1'(A_142), A_141) | A_141!='#skF_10' | A_142!='#skF_10' | v1_xboole_0(A_142))), inference(superposition, [status(thm), theory('equality')], [c_824, c_46])).
% 11.97/4.88  tff(c_23027, plain, (np__1='#skF_10'), inference(splitLeft, [status(thm)], [c_827])).
% 11.97/4.88  tff(c_23041, plain, (![A_25748, C_25749]: (k1_funct_1('#skF_9'(A_25748), C_25749)='#skF_10' | ~r2_hidden(C_25749, A_25748))), inference(demodulation, [status(thm), theory('equality')], [c_23027, c_46])).
% 11.97/4.88  tff(c_23106, plain, (![A_1, A_129]: (k1_xboole_0='#skF_10' | ~r2_hidden('#skF_1'(A_1), A_129) | A_129!='#skF_10' | A_1!='#skF_10' | v1_xboole_0(A_1))), inference(superposition, [status(thm), theory('equality')], [c_23103, c_23041])).
% 11.97/4.88  tff(c_23163, plain, (![A_25854, A_25855]: (~r2_hidden('#skF_1'(A_25854), A_25855) | A_25855!='#skF_10' | A_25854!='#skF_10' | v1_xboole_0(A_25854))), inference(negUnitSimplification, [status(thm)], [c_54, c_23106])).
% 11.97/4.88  tff(c_23235, plain, (v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_4, c_23163])).
% 11.97/4.88  tff(c_71, plain, (![D_58, A_59]: (r2_hidden(D_58, k2_tarski(A_59, D_58)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.97/4.88  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.97/4.88  tff(c_75, plain, (![A_59, D_58]: (~v1_xboole_0(k2_tarski(A_59, D_58)))), inference(resolution, [status(thm)], [c_71, c_2])).
% 11.97/4.88  tff(c_227, plain, (![D_95, B_96, A_97]: (D_95=B_96 | D_95=A_97 | ~r2_hidden(D_95, k2_tarski(A_97, B_96)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.97/4.88  tff(c_231, plain, (![A_97, B_96]: ('#skF_1'(k2_tarski(A_97, B_96))=B_96 | '#skF_1'(k2_tarski(A_97, B_96))=A_97 | v1_xboole_0(k2_tarski(A_97, B_96)))), inference(resolution, [status(thm)], [c_4, c_227])).
% 11.97/4.88  tff(c_240, plain, (![A_97, B_96]: ('#skF_1'(k2_tarski(A_97, B_96))=B_96 | '#skF_1'(k2_tarski(A_97, B_96))=A_97)), inference(negUnitSimplification, [status(thm)], [c_75, c_231])).
% 11.97/4.88  tff(c_307, plain, (![B_96]: ('#skF_1'(k2_tarski(B_96, B_96))=B_96)), inference(factorization, [status(thm), theory('equality')], [c_240])).
% 11.97/4.88  tff(c_517, plain, (![A_141, A_142, B_143]: (k1_funct_1('#skF_9'(A_141), '#skF_1'(A_142))=B_143 | A_141!='#skF_10' | A_142!='#skF_10' | v1_xboole_0(A_142))), inference(resolution, [status(thm)], [c_4, c_487])).
% 11.97/4.88  tff(c_10, plain, (![D_10, A_5]: (r2_hidden(D_10, k2_tarski(A_5, D_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.97/4.88  tff(c_125, plain, (![C_74, A_75, D_76]: (r2_hidden(C_74, k1_relat_1(A_75)) | ~r2_hidden(k4_tarski(C_74, D_76), A_75))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.97/4.88  tff(c_159, plain, (![C_85, A_86, D_87]: (r2_hidden(C_85, k1_relat_1(k2_tarski(A_86, k4_tarski(C_85, D_87)))))), inference(resolution, [status(thm)], [c_10, c_125])).
% 11.97/4.88  tff(c_28, plain, (![C_26, A_11, D_29]: (r2_hidden(C_26, k1_relat_1(A_11)) | ~r2_hidden(k4_tarski(C_26, D_29), A_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.97/4.88  tff(c_465, plain, (![C_119, A_120, D_121, D_122]: (r2_hidden(C_119, k1_relat_1(k1_relat_1(k2_tarski(A_120, k4_tarski(k4_tarski(C_119, D_121), D_122))))))), inference(resolution, [status(thm)], [c_159, c_28])).
% 11.97/4.88  tff(c_474, plain, (![A_120, C_119, D_121, D_122]: (~v1_xboole_0(k1_relat_1(k1_relat_1(k2_tarski(A_120, k4_tarski(k4_tarski(C_119, D_121), D_122))))))), inference(resolution, [status(thm)], [c_465, c_2])).
% 11.97/4.88  tff(c_991, plain, (![A_1224, A_1225]: (~v1_xboole_0(k1_funct_1('#skF_9'(A_1224), '#skF_1'(A_1225))) | A_1224!='#skF_10' | A_1225!='#skF_10' | v1_xboole_0(A_1225))), inference(superposition, [status(thm), theory('equality')], [c_517, c_474])).
% 11.97/4.88  tff(c_1003, plain, (![A_1224, B_96]: (~v1_xboole_0(k1_funct_1('#skF_9'(A_1224), B_96)) | A_1224!='#skF_10' | k2_tarski(B_96, B_96)!='#skF_10' | v1_xboole_0(k2_tarski(B_96, B_96)))), inference(superposition, [status(thm), theory('equality')], [c_307, c_991])).
% 11.97/4.88  tff(c_1027, plain, (![A_1252, B_1253]: (~v1_xboole_0(k1_funct_1('#skF_9'(A_1252), B_1253)) | A_1252!='#skF_10' | k2_tarski(B_1253, B_1253)!='#skF_10')), inference(negUnitSimplification, [status(thm)], [c_75, c_1003])).
% 11.97/4.88  tff(c_1041, plain, (![A_37, C_42]: (~v1_xboole_0(np__1) | A_37!='#skF_10' | k2_tarski(C_42, C_42)!='#skF_10' | ~r2_hidden(C_42, A_37))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1027])).
% 11.97/4.88  tff(c_17409, plain, (~v1_xboole_0(np__1)), inference(splitLeft, [status(thm)], [c_1041])).
% 11.97/4.88  tff(c_23030, plain, (~v1_xboole_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_23027, c_17409])).
% 11.97/4.88  tff(c_23238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23235, c_23030])).
% 11.97/4.88  tff(c_23242, plain, (![A_26064, A_26065]: (~r2_hidden('#skF_1'(A_26064), A_26065) | A_26065!='#skF_10' | A_26064!='#skF_10' | v1_xboole_0(A_26064))), inference(splitRight, [status(thm)], [c_827])).
% 11.97/4.88  tff(c_23335, plain, (![A_26170]: (A_26170!='#skF_10' | v1_xboole_0(A_26170))), inference(resolution, [status(thm)], [c_4, c_23242])).
% 11.97/4.88  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.97/4.88  tff(c_1816, plain, (![A_2424, B_2425]: (r2_hidden(k4_tarski('#skF_4'(A_2424, B_2425), '#skF_5'(A_2424, B_2425)), A_2424) | r2_hidden('#skF_6'(A_2424, B_2425), B_2425) | k1_relat_1(A_2424)=B_2425)), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.97/4.88  tff(c_2027, plain, (![A_2621, B_2622]: (~v1_xboole_0(A_2621) | r2_hidden('#skF_6'(A_2621, B_2622), B_2622) | k1_relat_1(A_2621)=B_2622)), inference(resolution, [status(thm)], [c_1816, c_2])).
% 11.97/4.88  tff(c_2082, plain, (![B_2649, A_2650]: (~v1_xboole_0(B_2649) | ~v1_xboole_0(A_2650) | k1_relat_1(A_2650)=B_2649)), inference(resolution, [status(thm)], [c_2027, c_2])).
% 11.97/4.88  tff(c_2963, plain, (![A_5124]: (~v1_xboole_0(A_5124) | k1_relat_1(A_5124)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_2082])).
% 11.97/4.88  tff(c_2999, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_2963])).
% 11.97/4.88  tff(c_36, plain, (![A_11, B_12]: (r2_hidden(k4_tarski('#skF_4'(A_11, B_12), '#skF_5'(A_11, B_12)), A_11) | r2_hidden('#skF_6'(A_11, B_12), B_12) | k1_relat_1(A_11)=B_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.97/4.88  tff(c_26, plain, (![C_26, A_11]: (r2_hidden(k4_tarski(C_26, '#skF_7'(A_11, k1_relat_1(A_11), C_26)), A_11) | ~r2_hidden(C_26, k1_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.97/4.88  tff(c_1042, plain, (![C_1280, A_1281]: (r2_hidden(k4_tarski(C_1280, '#skF_7'(A_1281, k1_relat_1(A_1281), C_1280)), A_1281) | ~r2_hidden(C_1280, k1_relat_1(A_1281)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.97/4.88  tff(c_1073, plain, (![A_1308, C_1309]: (~v1_xboole_0(A_1308) | ~r2_hidden(C_1309, k1_relat_1(A_1308)))), inference(resolution, [status(thm)], [c_1042, c_2])).
% 11.97/4.88  tff(c_1194, plain, (![A_1502, C_1503]: (~v1_xboole_0(A_1502) | ~r2_hidden(C_1503, k1_relat_1(k1_relat_1(A_1502))))), inference(resolution, [status(thm)], [c_26, c_1073])).
% 11.97/4.88  tff(c_1448, plain, (![A_1896, C_1897]: (~v1_xboole_0(A_1896) | ~r2_hidden(C_1897, k1_relat_1(k1_relat_1(k1_relat_1(A_1896)))))), inference(resolution, [status(thm)], [c_26, c_1194])).
% 11.97/4.88  tff(c_1473, plain, (![A_1896, C_26]: (~v1_xboole_0(A_1896) | ~r2_hidden(C_26, k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(A_1896))))))), inference(resolution, [status(thm)], [c_26, c_1448])).
% 11.97/4.88  tff(c_3018, plain, (![C_26]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_26, k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))))), inference(superposition, [status(thm), theory('equality')], [c_2999, c_1473])).
% 11.97/4.88  tff(c_3079, plain, (![C_5229]: (~r2_hidden(C_5229, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2999, c_2999, c_2999, c_6, c_3018])).
% 11.97/4.88  tff(c_3087, plain, (![B_12]: (r2_hidden('#skF_6'(k1_xboole_0, B_12), B_12) | k1_relat_1(k1_xboole_0)=B_12)), inference(resolution, [status(thm)], [c_36, c_3079])).
% 11.97/4.88  tff(c_4529, plain, (![B_8255]: (r2_hidden('#skF_6'(k1_xboole_0, B_8255), B_8255) | k1_xboole_0=B_8255)), inference(demodulation, [status(thm), theory('equality')], [c_2999, c_3087])).
% 11.97/4.88  tff(c_4591, plain, (![B_8255]: (~v1_xboole_0(B_8255) | k1_xboole_0=B_8255)), inference(resolution, [status(thm)], [c_4529, c_2])).
% 11.97/4.88  tff(c_23767, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_23335, c_4591])).
% 11.97/4.88  tff(c_23807, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23767, c_54])).
% 11.97/4.88  tff(c_23809, plain, (v1_xboole_0(np__1)), inference(splitRight, [status(thm)], [c_1041])).
% 11.97/4.88  tff(c_23878, plain, (np__1=k1_xboole_0), inference(resolution, [status(thm)], [c_23809, c_4591])).
% 11.97/4.88  tff(c_24127, plain, (![A_26643, C_26644]: (k1_funct_1('#skF_9'(A_26643), C_26644)=k1_xboole_0 | ~r2_hidden(C_26644, A_26643))), inference(demodulation, [status(thm), theory('equality')], [c_23878, c_46])).
% 11.97/4.88  tff(c_24187, plain, (![A_1, A_129]: (k1_xboole_0='#skF_10' | ~r2_hidden('#skF_1'(A_1), A_129) | A_129!='#skF_10' | A_1!='#skF_10' | v1_xboole_0(A_1))), inference(superposition, [status(thm), theory('equality')], [c_24184, c_24127])).
% 11.97/4.88  tff(c_24338, plain, (![A_26857, A_26858]: (~r2_hidden('#skF_1'(A_26857), A_26858) | A_26858!='#skF_10' | A_26857!='#skF_10' | v1_xboole_0(A_26857))), inference(negUnitSimplification, [status(thm)], [c_54, c_24187])).
% 11.97/4.88  tff(c_24411, plain, (![A_26963]: (A_26963!='#skF_10' | v1_xboole_0(A_26963))), inference(resolution, [status(thm)], [c_4, c_24338])).
% 11.97/4.88  tff(c_24767, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_24411, c_4591])).
% 11.97/4.88  tff(c_24802, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24767, c_54])).
% 11.97/4.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.97/4.88  
% 11.97/4.88  Inference rules
% 11.97/4.88  ----------------------
% 11.97/4.88  #Ref     : 1
% 11.97/4.88  #Sup     : 5842
% 11.97/4.88  #Fact    : 28
% 11.97/4.88  #Define  : 0
% 11.97/4.88  #Split   : 8
% 11.97/4.88  #Chain   : 0
% 11.97/4.88  #Close   : 0
% 11.97/4.88  
% 11.97/4.88  Ordering : KBO
% 11.97/4.88  
% 11.97/4.88  Simplification rules
% 11.97/4.88  ----------------------
% 11.97/4.88  #Subsume      : 2359
% 11.97/4.88  #Demod        : 4065
% 12.12/4.88  #Tautology    : 1526
% 12.12/4.88  #SimpNegUnit  : 73
% 12.12/4.88  #BackRed      : 86
% 12.12/4.88  
% 12.12/4.88  #Partial instantiations: 16272
% 12.12/4.88  #Strategies tried      : 1
% 12.12/4.88  
% 12.12/4.88  Timing (in seconds)
% 12.12/4.88  ----------------------
% 12.12/4.88  Preprocessing        : 0.33
% 12.12/4.88  Parsing              : 0.17
% 12.12/4.88  CNF conversion       : 0.03
% 12.12/4.88  Main loop            : 3.73
% 12.12/4.88  Inferencing          : 1.04
% 12.12/4.88  Reduction            : 0.95
% 12.12/4.88  Demodulation         : 0.69
% 12.12/4.88  BG Simplification    : 0.10
% 12.12/4.88  Subsumption          : 1.42
% 12.12/4.88  Abstraction          : 0.15
% 12.12/4.88  MUC search           : 0.00
% 12.12/4.88  Cooper               : 0.00
% 12.12/4.88  Total                : 4.10
% 12.12/4.88  Index Insertion      : 0.00
% 12.12/4.88  Index Deletion       : 0.00
% 12.12/4.88  Index Matching       : 0.00
% 12.12/4.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
