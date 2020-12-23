%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:12 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 311 expanded)
%              Number of leaves         :   32 ( 117 expanded)
%              Depth                    :   15
%              Number of atoms          :  190 ( 847 expanded)
%              Number of equality atoms :   87 ( 380 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_2 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_84,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_66,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_59,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_97,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_46,plain,(
    ! [A_21] : v1_relat_1('#skF_7'(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_44,plain,(
    ! [A_21] : v1_funct_1('#skF_7'(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_42,plain,(
    ! [A_21] : k1_relat_1('#skF_7'(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_964,plain,(
    ! [A_975,B_976] :
      ( r2_hidden('#skF_2'(A_975,B_976),B_976)
      | r2_hidden('#skF_3'(A_975,B_976),A_975)
      | B_976 = A_975 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ! [C_19] : r2_hidden(C_19,k1_tarski(C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_4'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_184,plain,(
    ! [C_67,B_68,A_69] :
      ( r2_hidden(C_67,B_68)
      | ~ r2_hidden(C_67,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_266,plain,(
    ! [A_92,B_93,B_94] :
      ( r2_hidden('#skF_4'(A_92,B_93),B_94)
      | ~ r1_tarski(A_92,B_94)
      | r1_xboole_0(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_20,c_184])).

tff(c_24,plain,(
    ! [C_19,A_15] :
      ( C_19 = A_15
      | ~ r2_hidden(C_19,k1_tarski(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_284,plain,(
    ! [A_98,A_99,B_100] :
      ( A_98 = '#skF_4'(A_99,B_100)
      | ~ r1_tarski(A_99,k1_tarski(A_98))
      | r1_xboole_0(A_99,B_100) ) ),
    inference(resolution,[status(thm)],[c_266,c_24])).

tff(c_490,plain,(
    ! [XT_222,B_104] :
      ( k1_relat_1(XT_222) = '#skF_4'(k1_xboole_0,B_104)
      | r1_xboole_0(k1_xboole_0,B_104) ) ),
    inference(resolution,[status(thm)],[c_22,c_284])).

tff(c_194,plain,(
    ! [A_9,B_10,B_68] :
      ( r2_hidden('#skF_4'(A_9,B_10),B_68)
      | ~ r1_tarski(A_9,B_68)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_20,c_184])).

tff(c_493,plain,(
    ! [XT_222,B_68,B_104] :
      ( r2_hidden(k1_relat_1(XT_222),B_68)
      | ~ r1_tarski(k1_xboole_0,B_68)
      | r1_xboole_0(k1_xboole_0,B_104)
      | r1_xboole_0(k1_xboole_0,B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_490,c_194])).

tff(c_837,plain,(
    ! [XT_222,B_68,B_104] :
      ( r2_hidden(k1_relat_1(XT_222),B_68)
      | r1_xboole_0(k1_xboole_0,B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_493])).

tff(c_851,plain,(
    ! [B_962] : r1_xboole_0(k1_xboole_0,B_962) ),
    inference(splitLeft,[status(thm)],[c_837])).

tff(c_16,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,B_10)
      | ~ r2_hidden(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_855,plain,(
    ! [C_963,B_964] :
      ( ~ r2_hidden(C_963,B_964)
      | ~ r2_hidden(C_963,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_851,c_16])).

tff(c_879,plain,(
    ! [C_19] : ~ r2_hidden(C_19,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_855])).

tff(c_985,plain,(
    ! [B_976] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_976),B_976)
      | k1_xboole_0 = B_976 ) ),
    inference(resolution,[status(thm)],[c_964,c_879])).

tff(c_50,plain,(
    ! [A_27,B_31] :
      ( k1_relat_1('#skF_8'(A_27,B_31)) = A_27
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_52,plain,(
    ! [A_27,B_31] :
      ( v1_funct_1('#skF_8'(A_27,B_31))
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_54,plain,(
    ! [A_27,B_31] :
      ( v1_relat_1('#skF_8'(A_27,B_31))
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_144,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_1'(A_60,B_61),A_60)
      | r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_210,plain,(
    ! [A_79,B_80] :
      ( '#skF_1'(k1_tarski(A_79),B_80) = A_79
      | r1_tarski(k1_tarski(A_79),B_80) ) ),
    inference(resolution,[status(thm)],[c_144,c_24])).

tff(c_172,plain,(
    ! [A_65,B_66] :
      ( k2_relat_1('#skF_8'(A_65,B_66)) = k1_tarski(B_66)
      | k1_xboole_0 = A_65 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_56,plain,(
    ! [C_34] :
      ( ~ r1_tarski(k2_relat_1(C_34),'#skF_9')
      | k1_relat_1(C_34) != '#skF_10'
      | ~ v1_funct_1(C_34)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_178,plain,(
    ! [B_66,A_65] :
      ( ~ r1_tarski(k1_tarski(B_66),'#skF_9')
      | k1_relat_1('#skF_8'(A_65,B_66)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_65,B_66))
      | ~ v1_relat_1('#skF_8'(A_65,B_66))
      | k1_xboole_0 = A_65 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_56])).

tff(c_297,plain,(
    ! [A_101,A_102] :
      ( k1_relat_1('#skF_8'(A_101,A_102)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_101,A_102))
      | ~ v1_relat_1('#skF_8'(A_101,A_102))
      | k1_xboole_0 = A_101
      | '#skF_1'(k1_tarski(A_102),'#skF_9') = A_102 ) ),
    inference(resolution,[status(thm)],[c_210,c_178])).

tff(c_1071,plain,(
    ! [A_982,B_983] :
      ( k1_relat_1('#skF_8'(A_982,B_983)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_982,B_983))
      | '#skF_1'(k1_tarski(B_983),'#skF_9') = B_983
      | k1_xboole_0 = A_982 ) ),
    inference(resolution,[status(thm)],[c_54,c_297])).

tff(c_1293,plain,(
    ! [A_999,B_1000] :
      ( k1_relat_1('#skF_8'(A_999,B_1000)) != '#skF_10'
      | '#skF_1'(k1_tarski(B_1000),'#skF_9') = B_1000
      | k1_xboole_0 = A_999 ) ),
    inference(resolution,[status(thm)],[c_52,c_1071])).

tff(c_1296,plain,(
    ! [A_27,B_31] :
      ( A_27 != '#skF_10'
      | '#skF_1'(k1_tarski(B_31),'#skF_9') = B_31
      | k1_xboole_0 = A_27
      | k1_xboole_0 = A_27 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1293])).

tff(c_1365,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_1296])).

tff(c_113,plain,(
    ! [A_55] :
      ( k2_relat_1(A_55) = k1_xboole_0
      | k1_relat_1(A_55) != k1_xboole_0
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_119,plain,(
    ! [A_21] :
      ( k2_relat_1('#skF_7'(A_21)) = k1_xboole_0
      | k1_relat_1('#skF_7'(A_21)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_113])).

tff(c_124,plain,(
    ! [A_56] :
      ( k2_relat_1('#skF_7'(A_56)) = k1_xboole_0
      | k1_xboole_0 != A_56 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_119])).

tff(c_130,plain,(
    ! [A_56] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_9')
      | k1_relat_1('#skF_7'(A_56)) != '#skF_10'
      | ~ v1_funct_1('#skF_7'(A_56))
      | ~ v1_relat_1('#skF_7'(A_56))
      | k1_xboole_0 != A_56 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_56])).

tff(c_136,plain,(
    ! [A_56] :
      ( A_56 != '#skF_10'
      | k1_xboole_0 != A_56 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_22,c_130])).

tff(c_141,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_136])).

tff(c_1399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1365,c_141])).

tff(c_1402,plain,(
    ! [B_1012] : '#skF_1'(k1_tarski(B_1012),'#skF_9') = B_1012 ),
    inference(splitRight,[status(thm)],[c_1296])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1430,plain,(
    ! [B_1013] :
      ( ~ r2_hidden(B_1013,'#skF_9')
      | r1_tarski(k1_tarski(B_1013),'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1402,c_4])).

tff(c_1453,plain,(
    ! [A_1016,B_1017] :
      ( k1_relat_1('#skF_8'(A_1016,B_1017)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_1016,B_1017))
      | ~ v1_relat_1('#skF_8'(A_1016,B_1017))
      | k1_xboole_0 = A_1016
      | ~ r2_hidden(B_1017,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1430,c_178])).

tff(c_1490,plain,(
    ! [A_1020,B_1021] :
      ( k1_relat_1('#skF_8'(A_1020,B_1021)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_1020,B_1021))
      | ~ r2_hidden(B_1021,'#skF_9')
      | k1_xboole_0 = A_1020 ) ),
    inference(resolution,[status(thm)],[c_54,c_1453])).

tff(c_1527,plain,(
    ! [A_1024,B_1025] :
      ( k1_relat_1('#skF_8'(A_1024,B_1025)) != '#skF_10'
      | ~ r2_hidden(B_1025,'#skF_9')
      | k1_xboole_0 = A_1024 ) ),
    inference(resolution,[status(thm)],[c_52,c_1490])).

tff(c_1530,plain,(
    ! [A_27,B_31] :
      ( A_27 != '#skF_10'
      | ~ r2_hidden(B_31,'#skF_9')
      | k1_xboole_0 = A_27
      | k1_xboole_0 = A_27 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1527])).

tff(c_1532,plain,(
    ! [B_1026] : ~ r2_hidden(B_1026,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1530])).

tff(c_1544,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_985,c_1532])).

tff(c_1588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1544])).

tff(c_1590,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_1530])).

tff(c_1625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1590,c_141])).

tff(c_1627,plain,(
    ! [XT_1027,B_1028] : r2_hidden(k1_relat_1(XT_1027),B_1028) ),
    inference(splitRight,[status(thm)],[c_837])).

tff(c_1882,plain,(
    ! [XT_1027] : k1_relat_1(XT_1027) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1627,c_24])).

tff(c_1643,plain,(
    ! [XT_1049,A_1050] : k1_relat_1(XT_1049) = A_1050 ),
    inference(resolution,[status(thm)],[c_1627,c_24])).

tff(c_2008,plain,(
    ! [A_2614] : A_2614 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_1882,c_1643])).

tff(c_2077,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_2008,c_72])).

tff(c_2079,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2078,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2086,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2079,c_2078])).

tff(c_2080,plain,(
    ! [A_14] : r1_tarski('#skF_10',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2078,c_22])).

tff(c_2096,plain,(
    ! [A_14] : r1_tarski('#skF_9',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2086,c_2080])).

tff(c_38,plain,(
    ! [A_20] :
      ( k2_relat_1(A_20) = k1_xboole_0
      | k1_relat_1(A_20) != k1_xboole_0
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2151,plain,(
    ! [A_3372] :
      ( k2_relat_1(A_3372) = '#skF_9'
      | k1_relat_1(A_3372) != '#skF_9'
      | ~ v1_relat_1(A_3372) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2079,c_2079,c_38])).

tff(c_2157,plain,(
    ! [A_21] :
      ( k2_relat_1('#skF_7'(A_21)) = '#skF_9'
      | k1_relat_1('#skF_7'(A_21)) != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_46,c_2151])).

tff(c_2162,plain,(
    ! [A_3373] :
      ( k2_relat_1('#skF_7'(A_3373)) = '#skF_9'
      | A_3373 != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2157])).

tff(c_2091,plain,(
    ! [C_34] :
      ( ~ r1_tarski(k2_relat_1(C_34),'#skF_9')
      | k1_relat_1(C_34) != '#skF_9'
      | ~ v1_funct_1(C_34)
      | ~ v1_relat_1(C_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2086,c_56])).

tff(c_2168,plain,(
    ! [A_3373] :
      ( ~ r1_tarski('#skF_9','#skF_9')
      | k1_relat_1('#skF_7'(A_3373)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_3373))
      | ~ v1_relat_1('#skF_7'(A_3373))
      | A_3373 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2162,c_2091])).

tff(c_2174,plain,(
    ! [A_3373] : A_3373 != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_2096,c_2168])).

tff(c_2185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2174,c_2086])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.60  
% 3.44/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.61  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 3.44/1.61  
% 3.44/1.61  %Foreground sorts:
% 3.44/1.61  
% 3.44/1.61  
% 3.44/1.61  %Background operators:
% 3.44/1.61  
% 3.44/1.61  
% 3.44/1.61  %Foreground operators:
% 3.44/1.61  tff('#skF_7', type, '#skF_7': $i > $i).
% 3.44/1.61  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.44/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.44/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.44/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.61  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.44/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.61  tff('#skF_10', type, '#skF_10': $i).
% 3.44/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.44/1.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.44/1.61  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.44/1.61  tff('#skF_9', type, '#skF_9': $i).
% 3.44/1.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.44/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.44/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.44/1.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.44/1.61  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.44/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.44/1.61  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.44/1.61  
% 3.77/1.62  tff(f_84, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 3.77/1.62  tff(f_115, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 3.77/1.62  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 3.77/1.62  tff(f_66, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.77/1.62  tff(f_59, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.77/1.62  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.77/1.62  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.77/1.62  tff(f_97, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 3.77/1.62  tff(f_72, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.77/1.62  tff(c_46, plain, (![A_21]: (v1_relat_1('#skF_7'(A_21)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.77/1.62  tff(c_44, plain, (![A_21]: (v1_funct_1('#skF_7'(A_21)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.77/1.62  tff(c_42, plain, (![A_21]: (k1_relat_1('#skF_7'(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.77/1.62  tff(c_58, plain, (k1_xboole_0='#skF_10' | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.77/1.62  tff(c_72, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_58])).
% 3.77/1.62  tff(c_964, plain, (![A_975, B_976]: (r2_hidden('#skF_2'(A_975, B_976), B_976) | r2_hidden('#skF_3'(A_975, B_976), A_975) | B_976=A_975)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.77/1.62  tff(c_26, plain, (![C_19]: (r2_hidden(C_19, k1_tarski(C_19)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.77/1.62  tff(c_22, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.77/1.62  tff(c_20, plain, (![A_9, B_10]: (r2_hidden('#skF_4'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.77/1.62  tff(c_184, plain, (![C_67, B_68, A_69]: (r2_hidden(C_67, B_68) | ~r2_hidden(C_67, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.77/1.62  tff(c_266, plain, (![A_92, B_93, B_94]: (r2_hidden('#skF_4'(A_92, B_93), B_94) | ~r1_tarski(A_92, B_94) | r1_xboole_0(A_92, B_93))), inference(resolution, [status(thm)], [c_20, c_184])).
% 3.77/1.62  tff(c_24, plain, (![C_19, A_15]: (C_19=A_15 | ~r2_hidden(C_19, k1_tarski(A_15)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.77/1.62  tff(c_284, plain, (![A_98, A_99, B_100]: (A_98='#skF_4'(A_99, B_100) | ~r1_tarski(A_99, k1_tarski(A_98)) | r1_xboole_0(A_99, B_100))), inference(resolution, [status(thm)], [c_266, c_24])).
% 3.77/1.62  tff(c_490, plain, (![XT_222, B_104]: (k1_relat_1(XT_222)='#skF_4'(k1_xboole_0, B_104) | r1_xboole_0(k1_xboole_0, B_104))), inference(resolution, [status(thm)], [c_22, c_284])).
% 3.77/1.62  tff(c_194, plain, (![A_9, B_10, B_68]: (r2_hidden('#skF_4'(A_9, B_10), B_68) | ~r1_tarski(A_9, B_68) | r1_xboole_0(A_9, B_10))), inference(resolution, [status(thm)], [c_20, c_184])).
% 3.77/1.62  tff(c_493, plain, (![XT_222, B_68, B_104]: (r2_hidden(k1_relat_1(XT_222), B_68) | ~r1_tarski(k1_xboole_0, B_68) | r1_xboole_0(k1_xboole_0, B_104) | r1_xboole_0(k1_xboole_0, B_104))), inference(superposition, [status(thm), theory('equality')], [c_490, c_194])).
% 3.77/1.62  tff(c_837, plain, (![XT_222, B_68, B_104]: (r2_hidden(k1_relat_1(XT_222), B_68) | r1_xboole_0(k1_xboole_0, B_104))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_493])).
% 3.77/1.62  tff(c_851, plain, (![B_962]: (r1_xboole_0(k1_xboole_0, B_962))), inference(splitLeft, [status(thm)], [c_837])).
% 3.77/1.62  tff(c_16, plain, (![A_9, B_10, C_13]: (~r1_xboole_0(A_9, B_10) | ~r2_hidden(C_13, B_10) | ~r2_hidden(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.77/1.62  tff(c_855, plain, (![C_963, B_964]: (~r2_hidden(C_963, B_964) | ~r2_hidden(C_963, k1_xboole_0))), inference(resolution, [status(thm)], [c_851, c_16])).
% 3.77/1.62  tff(c_879, plain, (![C_19]: (~r2_hidden(C_19, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_855])).
% 3.77/1.62  tff(c_985, plain, (![B_976]: (r2_hidden('#skF_2'(k1_xboole_0, B_976), B_976) | k1_xboole_0=B_976)), inference(resolution, [status(thm)], [c_964, c_879])).
% 3.77/1.62  tff(c_50, plain, (![A_27, B_31]: (k1_relat_1('#skF_8'(A_27, B_31))=A_27 | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.77/1.62  tff(c_52, plain, (![A_27, B_31]: (v1_funct_1('#skF_8'(A_27, B_31)) | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.77/1.62  tff(c_54, plain, (![A_27, B_31]: (v1_relat_1('#skF_8'(A_27, B_31)) | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.77/1.62  tff(c_144, plain, (![A_60, B_61]: (r2_hidden('#skF_1'(A_60, B_61), A_60) | r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.77/1.62  tff(c_210, plain, (![A_79, B_80]: ('#skF_1'(k1_tarski(A_79), B_80)=A_79 | r1_tarski(k1_tarski(A_79), B_80))), inference(resolution, [status(thm)], [c_144, c_24])).
% 3.77/1.62  tff(c_172, plain, (![A_65, B_66]: (k2_relat_1('#skF_8'(A_65, B_66))=k1_tarski(B_66) | k1_xboole_0=A_65)), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.77/1.62  tff(c_56, plain, (![C_34]: (~r1_tarski(k2_relat_1(C_34), '#skF_9') | k1_relat_1(C_34)!='#skF_10' | ~v1_funct_1(C_34) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.77/1.62  tff(c_178, plain, (![B_66, A_65]: (~r1_tarski(k1_tarski(B_66), '#skF_9') | k1_relat_1('#skF_8'(A_65, B_66))!='#skF_10' | ~v1_funct_1('#skF_8'(A_65, B_66)) | ~v1_relat_1('#skF_8'(A_65, B_66)) | k1_xboole_0=A_65)), inference(superposition, [status(thm), theory('equality')], [c_172, c_56])).
% 3.77/1.62  tff(c_297, plain, (![A_101, A_102]: (k1_relat_1('#skF_8'(A_101, A_102))!='#skF_10' | ~v1_funct_1('#skF_8'(A_101, A_102)) | ~v1_relat_1('#skF_8'(A_101, A_102)) | k1_xboole_0=A_101 | '#skF_1'(k1_tarski(A_102), '#skF_9')=A_102)), inference(resolution, [status(thm)], [c_210, c_178])).
% 3.77/1.62  tff(c_1071, plain, (![A_982, B_983]: (k1_relat_1('#skF_8'(A_982, B_983))!='#skF_10' | ~v1_funct_1('#skF_8'(A_982, B_983)) | '#skF_1'(k1_tarski(B_983), '#skF_9')=B_983 | k1_xboole_0=A_982)), inference(resolution, [status(thm)], [c_54, c_297])).
% 3.77/1.62  tff(c_1293, plain, (![A_999, B_1000]: (k1_relat_1('#skF_8'(A_999, B_1000))!='#skF_10' | '#skF_1'(k1_tarski(B_1000), '#skF_9')=B_1000 | k1_xboole_0=A_999)), inference(resolution, [status(thm)], [c_52, c_1071])).
% 3.77/1.62  tff(c_1296, plain, (![A_27, B_31]: (A_27!='#skF_10' | '#skF_1'(k1_tarski(B_31), '#skF_9')=B_31 | k1_xboole_0=A_27 | k1_xboole_0=A_27)), inference(superposition, [status(thm), theory('equality')], [c_50, c_1293])).
% 3.77/1.62  tff(c_1365, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_1296])).
% 3.77/1.62  tff(c_113, plain, (![A_55]: (k2_relat_1(A_55)=k1_xboole_0 | k1_relat_1(A_55)!=k1_xboole_0 | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.77/1.62  tff(c_119, plain, (![A_21]: (k2_relat_1('#skF_7'(A_21))=k1_xboole_0 | k1_relat_1('#skF_7'(A_21))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_113])).
% 3.77/1.62  tff(c_124, plain, (![A_56]: (k2_relat_1('#skF_7'(A_56))=k1_xboole_0 | k1_xboole_0!=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_119])).
% 3.77/1.62  tff(c_130, plain, (![A_56]: (~r1_tarski(k1_xboole_0, '#skF_9') | k1_relat_1('#skF_7'(A_56))!='#skF_10' | ~v1_funct_1('#skF_7'(A_56)) | ~v1_relat_1('#skF_7'(A_56)) | k1_xboole_0!=A_56)), inference(superposition, [status(thm), theory('equality')], [c_124, c_56])).
% 3.77/1.62  tff(c_136, plain, (![A_56]: (A_56!='#skF_10' | k1_xboole_0!=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_22, c_130])).
% 3.77/1.62  tff(c_141, plain, (k1_xboole_0!='#skF_10'), inference(reflexivity, [status(thm), theory('equality')], [c_136])).
% 3.77/1.62  tff(c_1399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1365, c_141])).
% 3.77/1.62  tff(c_1402, plain, (![B_1012]: ('#skF_1'(k1_tarski(B_1012), '#skF_9')=B_1012)), inference(splitRight, [status(thm)], [c_1296])).
% 3.77/1.62  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.77/1.62  tff(c_1430, plain, (![B_1013]: (~r2_hidden(B_1013, '#skF_9') | r1_tarski(k1_tarski(B_1013), '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1402, c_4])).
% 3.77/1.62  tff(c_1453, plain, (![A_1016, B_1017]: (k1_relat_1('#skF_8'(A_1016, B_1017))!='#skF_10' | ~v1_funct_1('#skF_8'(A_1016, B_1017)) | ~v1_relat_1('#skF_8'(A_1016, B_1017)) | k1_xboole_0=A_1016 | ~r2_hidden(B_1017, '#skF_9'))), inference(resolution, [status(thm)], [c_1430, c_178])).
% 3.77/1.62  tff(c_1490, plain, (![A_1020, B_1021]: (k1_relat_1('#skF_8'(A_1020, B_1021))!='#skF_10' | ~v1_funct_1('#skF_8'(A_1020, B_1021)) | ~r2_hidden(B_1021, '#skF_9') | k1_xboole_0=A_1020)), inference(resolution, [status(thm)], [c_54, c_1453])).
% 3.77/1.62  tff(c_1527, plain, (![A_1024, B_1025]: (k1_relat_1('#skF_8'(A_1024, B_1025))!='#skF_10' | ~r2_hidden(B_1025, '#skF_9') | k1_xboole_0=A_1024)), inference(resolution, [status(thm)], [c_52, c_1490])).
% 3.77/1.62  tff(c_1530, plain, (![A_27, B_31]: (A_27!='#skF_10' | ~r2_hidden(B_31, '#skF_9') | k1_xboole_0=A_27 | k1_xboole_0=A_27)), inference(superposition, [status(thm), theory('equality')], [c_50, c_1527])).
% 3.77/1.62  tff(c_1532, plain, (![B_1026]: (~r2_hidden(B_1026, '#skF_9'))), inference(splitLeft, [status(thm)], [c_1530])).
% 3.77/1.62  tff(c_1544, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_985, c_1532])).
% 3.77/1.62  tff(c_1588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1544])).
% 3.77/1.62  tff(c_1590, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_1530])).
% 3.77/1.62  tff(c_1625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1590, c_141])).
% 3.77/1.62  tff(c_1627, plain, (![XT_1027, B_1028]: (r2_hidden(k1_relat_1(XT_1027), B_1028))), inference(splitRight, [status(thm)], [c_837])).
% 3.77/1.62  tff(c_1882, plain, (![XT_1027]: (k1_relat_1(XT_1027)='#skF_9')), inference(resolution, [status(thm)], [c_1627, c_24])).
% 3.77/1.62  tff(c_1643, plain, (![XT_1049, A_1050]: (k1_relat_1(XT_1049)=A_1050)), inference(resolution, [status(thm)], [c_1627, c_24])).
% 3.77/1.62  tff(c_2008, plain, (![A_2614]: (A_2614='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1882, c_1643])).
% 3.77/1.62  tff(c_2077, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_2008, c_72])).
% 3.77/1.62  tff(c_2079, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_58])).
% 3.77/1.62  tff(c_2078, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_58])).
% 3.77/1.62  tff(c_2086, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2079, c_2078])).
% 3.77/1.62  tff(c_2080, plain, (![A_14]: (r1_tarski('#skF_10', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_2078, c_22])).
% 3.77/1.62  tff(c_2096, plain, (![A_14]: (r1_tarski('#skF_9', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_2086, c_2080])).
% 3.77/1.62  tff(c_38, plain, (![A_20]: (k2_relat_1(A_20)=k1_xboole_0 | k1_relat_1(A_20)!=k1_xboole_0 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.77/1.62  tff(c_2151, plain, (![A_3372]: (k2_relat_1(A_3372)='#skF_9' | k1_relat_1(A_3372)!='#skF_9' | ~v1_relat_1(A_3372))), inference(demodulation, [status(thm), theory('equality')], [c_2079, c_2079, c_38])).
% 3.77/1.62  tff(c_2157, plain, (![A_21]: (k2_relat_1('#skF_7'(A_21))='#skF_9' | k1_relat_1('#skF_7'(A_21))!='#skF_9')), inference(resolution, [status(thm)], [c_46, c_2151])).
% 3.77/1.62  tff(c_2162, plain, (![A_3373]: (k2_relat_1('#skF_7'(A_3373))='#skF_9' | A_3373!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2157])).
% 3.77/1.62  tff(c_2091, plain, (![C_34]: (~r1_tarski(k2_relat_1(C_34), '#skF_9') | k1_relat_1(C_34)!='#skF_9' | ~v1_funct_1(C_34) | ~v1_relat_1(C_34))), inference(demodulation, [status(thm), theory('equality')], [c_2086, c_56])).
% 3.77/1.62  tff(c_2168, plain, (![A_3373]: (~r1_tarski('#skF_9', '#skF_9') | k1_relat_1('#skF_7'(A_3373))!='#skF_9' | ~v1_funct_1('#skF_7'(A_3373)) | ~v1_relat_1('#skF_7'(A_3373)) | A_3373!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_2162, c_2091])).
% 3.77/1.62  tff(c_2174, plain, (![A_3373]: (A_3373!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_2096, c_2168])).
% 3.77/1.62  tff(c_2185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2174, c_2086])).
% 3.77/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.62  
% 3.77/1.62  Inference rules
% 3.77/1.62  ----------------------
% 3.77/1.62  #Ref     : 1
% 3.77/1.62  #Sup     : 488
% 3.77/1.62  #Fact    : 0
% 3.77/1.62  #Define  : 0
% 3.77/1.62  #Split   : 4
% 3.77/1.62  #Chain   : 0
% 3.77/1.62  #Close   : 0
% 3.77/1.62  
% 3.77/1.62  Ordering : KBO
% 3.77/1.62  
% 3.77/1.62  Simplification rules
% 3.77/1.62  ----------------------
% 3.77/1.62  #Subsume      : 81
% 3.77/1.62  #Demod        : 242
% 3.77/1.62  #Tautology    : 144
% 3.77/1.62  #SimpNegUnit  : 21
% 3.77/1.62  #BackRed      : 75
% 3.77/1.62  
% 3.77/1.62  #Partial instantiations: 1403
% 3.77/1.62  #Strategies tried      : 1
% 3.77/1.62  
% 3.77/1.62  Timing (in seconds)
% 3.77/1.62  ----------------------
% 3.77/1.63  Preprocessing        : 0.32
% 3.77/1.63  Parsing              : 0.17
% 3.77/1.63  CNF conversion       : 0.03
% 3.77/1.63  Main loop            : 0.53
% 3.77/1.63  Inferencing          : 0.22
% 3.77/1.63  Reduction            : 0.14
% 3.77/1.63  Demodulation         : 0.09
% 3.77/1.63  BG Simplification    : 0.03
% 3.77/1.63  Subsumption          : 0.09
% 3.77/1.63  Abstraction          : 0.02
% 3.77/1.63  MUC search           : 0.00
% 3.77/1.63  Cooper               : 0.00
% 3.77/1.63  Total                : 0.89
% 3.77/1.63  Index Insertion      : 0.00
% 3.77/1.63  Index Deletion       : 0.00
% 3.77/1.63  Index Matching       : 0.00
% 3.77/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
