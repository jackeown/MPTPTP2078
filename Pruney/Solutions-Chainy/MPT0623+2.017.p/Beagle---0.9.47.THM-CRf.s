%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:08 EST 2020

% Result     : Theorem 19.86s
% Output     : CNFRefutation 19.86s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 489 expanded)
%              Number of leaves         :   28 ( 164 expanded)
%              Depth                    :   16
%              Number of atoms          :  207 (1268 expanded)
%              Number of equality atoms :  113 ( 733 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_83,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_50,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_70,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    ! [A_21,B_25] :
      ( k1_relat_1('#skF_5'(A_21,B_25)) = A_21
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_48,plain,(
    ! [A_21,B_25] :
      ( v1_funct_1('#skF_5'(A_21,B_25))
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_50,plain,(
    ! [A_21,B_25] :
      ( v1_relat_1('#skF_5'(A_21,B_25))
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_176,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48,B_49),A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_181,plain,(
    ! [A_9,B_49] :
      ( '#skF_1'(k1_tarski(A_9),B_49) = A_9
      | r1_tarski(k1_tarski(A_9),B_49) ) ),
    inference(resolution,[status(thm)],[c_176,c_16])).

tff(c_226,plain,(
    ! [A_54,B_55] :
      ( k2_relat_1('#skF_5'(A_54,B_55)) = k1_tarski(B_55)
      | k1_xboole_0 = A_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_52,plain,(
    ! [C_28] :
      ( ~ r1_tarski(k2_relat_1(C_28),'#skF_6')
      | k1_relat_1(C_28) != '#skF_7'
      | ~ v1_funct_1(C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_300,plain,(
    ! [B_68,A_69] :
      ( ~ r1_tarski(k1_tarski(B_68),'#skF_6')
      | k1_relat_1('#skF_5'(A_69,B_68)) != '#skF_7'
      | ~ v1_funct_1('#skF_5'(A_69,B_68))
      | ~ v1_relat_1('#skF_5'(A_69,B_68))
      | k1_xboole_0 = A_69 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_52])).

tff(c_392,plain,(
    ! [A_82,A_83] :
      ( k1_relat_1('#skF_5'(A_82,A_83)) != '#skF_7'
      | ~ v1_funct_1('#skF_5'(A_82,A_83))
      | ~ v1_relat_1('#skF_5'(A_82,A_83))
      | k1_xboole_0 = A_82
      | '#skF_1'(k1_tarski(A_83),'#skF_6') = A_83 ) ),
    inference(resolution,[status(thm)],[c_181,c_300])).

tff(c_559,plain,(
    ! [A_105,B_106] :
      ( k1_relat_1('#skF_5'(A_105,B_106)) != '#skF_7'
      | ~ v1_funct_1('#skF_5'(A_105,B_106))
      | '#skF_1'(k1_tarski(B_106),'#skF_6') = B_106
      | k1_xboole_0 = A_105 ) ),
    inference(resolution,[status(thm)],[c_50,c_392])).

tff(c_17897,plain,(
    ! [A_7706,B_7707] :
      ( k1_relat_1('#skF_5'(A_7706,B_7707)) != '#skF_7'
      | '#skF_1'(k1_tarski(B_7707),'#skF_6') = B_7707
      | k1_xboole_0 = A_7706 ) ),
    inference(resolution,[status(thm)],[c_48,c_559])).

tff(c_17942,plain,(
    ! [A_21,B_25] :
      ( A_21 != '#skF_7'
      | '#skF_1'(k1_tarski(B_25),'#skF_6') = B_25
      | k1_xboole_0 = A_21
      | k1_xboole_0 = A_21 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_17897])).

tff(c_17944,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_17942])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_70,plain,(
    ! [C_34] :
      ( ~ r1_tarski(k2_relat_1(C_34),'#skF_6')
      | k1_relat_1(C_34) != '#skF_7'
      | ~ v1_funct_1(C_34)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_73,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_6')
    | k1_relat_1(k1_xboole_0) != '#skF_7'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_70])).

tff(c_75,plain,
    ( k1_xboole_0 != '#skF_7'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_14,c_73])).

tff(c_93,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_38,plain,(
    ! [A_15] : k1_relat_1('#skF_4'(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_42,plain,(
    ! [A_15] : v1_relat_1('#skF_4'(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_94,plain,(
    ! [A_42] :
      ( k1_relat_1(A_42) != k1_xboole_0
      | k1_xboole_0 = A_42
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_100,plain,(
    ! [A_15] :
      ( k1_relat_1('#skF_4'(A_15)) != k1_xboole_0
      | '#skF_4'(A_15) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_94])).

tff(c_105,plain,(
    ! [A_43] :
      ( k1_xboole_0 != A_43
      | '#skF_4'(A_43) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_100])).

tff(c_115,plain,(
    ! [A_43] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_43 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_42])).

tff(c_121,plain,(
    ! [A_43] : k1_xboole_0 != A_43 ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_115])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_28])).

tff(c_130,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_132,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_17987,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17944,c_132])).

tff(c_17990,plain,(
    ! [B_7750] : '#skF_1'(k1_tarski(B_7750),'#skF_6') = B_7750 ),
    inference(splitRight,[status(thm)],[c_17942])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18414,plain,(
    ! [B_7837] :
      ( ~ r2_hidden(B_7837,'#skF_6')
      | r1_tarski(k1_tarski(B_7837),'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17990,c_4])).

tff(c_232,plain,(
    ! [B_55,A_54] :
      ( ~ r1_tarski(k1_tarski(B_55),'#skF_6')
      | k1_relat_1('#skF_5'(A_54,B_55)) != '#skF_7'
      | ~ v1_funct_1('#skF_5'(A_54,B_55))
      | ~ v1_relat_1('#skF_5'(A_54,B_55))
      | k1_xboole_0 = A_54 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_52])).

tff(c_18463,plain,(
    ! [A_7923,B_7924] :
      ( k1_relat_1('#skF_5'(A_7923,B_7924)) != '#skF_7'
      | ~ v1_funct_1('#skF_5'(A_7923,B_7924))
      | ~ v1_relat_1('#skF_5'(A_7923,B_7924))
      | k1_xboole_0 = A_7923
      | ~ r2_hidden(B_7924,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_18414,c_232])).

tff(c_71547,plain,(
    ! [A_20685,B_20686] :
      ( k1_relat_1('#skF_5'(A_20685,B_20686)) != '#skF_7'
      | ~ v1_funct_1('#skF_5'(A_20685,B_20686))
      | ~ r2_hidden(B_20686,'#skF_6')
      | k1_xboole_0 = A_20685 ) ),
    inference(resolution,[status(thm)],[c_50,c_18463])).

tff(c_71576,plain,(
    ! [A_20799,B_20800] :
      ( k1_relat_1('#skF_5'(A_20799,B_20800)) != '#skF_7'
      | ~ r2_hidden(B_20800,'#skF_6')
      | k1_xboole_0 = A_20799 ) ),
    inference(resolution,[status(thm)],[c_48,c_71547])).

tff(c_71627,plain,(
    ! [A_21,B_25] :
      ( A_21 != '#skF_7'
      | ~ r2_hidden(B_25,'#skF_6')
      | k1_xboole_0 = A_21
      | k1_xboole_0 = A_21 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_71576])).

tff(c_71630,plain,(
    ! [B_20913] : ~ r2_hidden(B_20913,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_71627])).

tff(c_71675,plain,(
    ! [B_21026] : r1_tarski('#skF_6',B_21026) ),
    inference(resolution,[status(thm)],[c_6,c_71630])).

tff(c_250,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_259,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_250])).

tff(c_71713,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_71675,c_259])).

tff(c_71736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_71713])).

tff(c_71738,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_71627])).

tff(c_71786,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71738,c_132])).

tff(c_71788,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_71787,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_71789,plain,(
    ~ v1_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71788,c_71787])).

tff(c_34,plain,(
    ! [A_14] :
      ( k1_relat_1(A_14) != k1_xboole_0
      | k1_xboole_0 = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_71815,plain,(
    ! [A_21139] :
      ( k1_relat_1(A_21139) != '#skF_7'
      | A_21139 = '#skF_7'
      | ~ v1_relat_1(A_21139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71788,c_71788,c_34])).

tff(c_71821,plain,(
    ! [A_15] :
      ( k1_relat_1('#skF_4'(A_15)) != '#skF_7'
      | '#skF_4'(A_15) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_42,c_71815])).

tff(c_71830,plain,(
    ! [A_21141] :
      ( A_21141 != '#skF_7'
      | '#skF_4'(A_21141) = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_71821])).

tff(c_40,plain,(
    ! [A_15] : v1_funct_1('#skF_4'(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_71838,plain,(
    ! [A_21141] :
      ( v1_funct_1('#skF_7')
      | A_21141 != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71830,c_40])).

tff(c_71846,plain,(
    ! [A_21141] : A_21141 != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_71789,c_71838])).

tff(c_71795,plain,(
    k1_relat_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71788,c_71788,c_30])).

tff(c_71854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71846,c_71795])).

tff(c_71856,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_71855,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_71870,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71856,c_71855])).

tff(c_71864,plain,(
    k1_relat_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71855,c_71855,c_30])).

tff(c_71885,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71870,c_71870,c_71864])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_71863,plain,(
    k2_relat_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71855,c_71855,c_28])).

tff(c_71880,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71870,c_71870,c_71863])).

tff(c_71904,plain,(
    ! [C_21148] :
      ( ~ r1_tarski(k2_relat_1(C_21148),'#skF_6')
      | k1_relat_1(C_21148) != '#skF_6'
      | ~ v1_funct_1(C_21148)
      | ~ v1_relat_1(C_21148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71870,c_52])).

tff(c_71907,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | k1_relat_1('#skF_6') != '#skF_6'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_71880,c_71904])).

tff(c_71909,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71885,c_12,c_71907])).

tff(c_71910,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_71909])).

tff(c_71943,plain,(
    ! [A_21156] :
      ( k1_relat_1(A_21156) != '#skF_6'
      | A_21156 = '#skF_6'
      | ~ v1_relat_1(A_21156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71856,c_71856,c_34])).

tff(c_71949,plain,(
    ! [A_15] :
      ( k1_relat_1('#skF_4'(A_15)) != '#skF_6'
      | '#skF_4'(A_15) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_42,c_71943])).

tff(c_71954,plain,(
    ! [A_21157] :
      ( A_21157 != '#skF_6'
      | '#skF_4'(A_21157) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_71949])).

tff(c_71964,plain,(
    ! [A_21157] :
      ( v1_relat_1('#skF_6')
      | A_21157 != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71954,c_42])).

tff(c_71970,plain,(
    ! [A_21157] : A_21157 != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_71910,c_71964])).

tff(c_71982,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71970,c_71885])).

tff(c_71983,plain,(
    ~ v1_funct_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_71909])).

tff(c_72024,plain,(
    ! [A_21165] :
      ( k1_relat_1(A_21165) != '#skF_6'
      | A_21165 = '#skF_6'
      | ~ v1_relat_1(A_21165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71856,c_71856,c_34])).

tff(c_72033,plain,(
    ! [A_15] :
      ( k1_relat_1('#skF_4'(A_15)) != '#skF_6'
      | '#skF_4'(A_15) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_42,c_72024])).

tff(c_72042,plain,(
    ! [A_21166] :
      ( A_21166 != '#skF_6'
      | '#skF_4'(A_21166) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_72033])).

tff(c_72050,plain,(
    ! [A_21166] :
      ( v1_funct_1('#skF_6')
      | A_21166 != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72042,c_40])).

tff(c_72058,plain,(
    ! [A_21166] : A_21166 != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_71983,c_72050])).

tff(c_72071,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72058,c_71885])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:29:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.86/11.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.86/11.41  
% 19.86/11.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.86/11.41  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5
% 19.86/11.41  
% 19.86/11.41  %Foreground sorts:
% 19.86/11.41  
% 19.86/11.41  
% 19.86/11.41  %Background operators:
% 19.86/11.41  
% 19.86/11.41  
% 19.86/11.41  %Foreground operators:
% 19.86/11.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 19.86/11.41  tff('#skF_4', type, '#skF_4': $i > $i).
% 19.86/11.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.86/11.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.86/11.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 19.86/11.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 19.86/11.41  tff('#skF_7', type, '#skF_7': $i).
% 19.86/11.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 19.86/11.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.86/11.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 19.86/11.41  tff('#skF_6', type, '#skF_6': $i).
% 19.86/11.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 19.86/11.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.86/11.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 19.86/11.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.86/11.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 19.86/11.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 19.86/11.41  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 19.86/11.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 19.86/11.41  
% 19.86/11.43  tff(f_101, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 19.86/11.43  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 19.86/11.43  tff(f_83, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 19.86/11.43  tff(f_47, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 19.86/11.43  tff(f_50, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 19.86/11.43  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 19.86/11.43  tff(f_70, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 19.86/11.43  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 19.86/11.43  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 19.86/11.43  tff(c_54, plain, (k1_xboole_0='#skF_7' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_101])).
% 19.86/11.43  tff(c_68, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_54])).
% 19.86/11.43  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.86/11.43  tff(c_46, plain, (![A_21, B_25]: (k1_relat_1('#skF_5'(A_21, B_25))=A_21 | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_83])).
% 19.86/11.43  tff(c_48, plain, (![A_21, B_25]: (v1_funct_1('#skF_5'(A_21, B_25)) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_83])).
% 19.86/11.43  tff(c_50, plain, (![A_21, B_25]: (v1_relat_1('#skF_5'(A_21, B_25)) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_83])).
% 19.86/11.43  tff(c_176, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48, B_49), A_48) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.86/11.43  tff(c_16, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 19.86/11.43  tff(c_181, plain, (![A_9, B_49]: ('#skF_1'(k1_tarski(A_9), B_49)=A_9 | r1_tarski(k1_tarski(A_9), B_49))), inference(resolution, [status(thm)], [c_176, c_16])).
% 19.86/11.43  tff(c_226, plain, (![A_54, B_55]: (k2_relat_1('#skF_5'(A_54, B_55))=k1_tarski(B_55) | k1_xboole_0=A_54)), inference(cnfTransformation, [status(thm)], [f_83])).
% 19.86/11.43  tff(c_52, plain, (![C_28]: (~r1_tarski(k2_relat_1(C_28), '#skF_6') | k1_relat_1(C_28)!='#skF_7' | ~v1_funct_1(C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_101])).
% 19.86/11.43  tff(c_300, plain, (![B_68, A_69]: (~r1_tarski(k1_tarski(B_68), '#skF_6') | k1_relat_1('#skF_5'(A_69, B_68))!='#skF_7' | ~v1_funct_1('#skF_5'(A_69, B_68)) | ~v1_relat_1('#skF_5'(A_69, B_68)) | k1_xboole_0=A_69)), inference(superposition, [status(thm), theory('equality')], [c_226, c_52])).
% 19.86/11.43  tff(c_392, plain, (![A_82, A_83]: (k1_relat_1('#skF_5'(A_82, A_83))!='#skF_7' | ~v1_funct_1('#skF_5'(A_82, A_83)) | ~v1_relat_1('#skF_5'(A_82, A_83)) | k1_xboole_0=A_82 | '#skF_1'(k1_tarski(A_83), '#skF_6')=A_83)), inference(resolution, [status(thm)], [c_181, c_300])).
% 19.86/11.43  tff(c_559, plain, (![A_105, B_106]: (k1_relat_1('#skF_5'(A_105, B_106))!='#skF_7' | ~v1_funct_1('#skF_5'(A_105, B_106)) | '#skF_1'(k1_tarski(B_106), '#skF_6')=B_106 | k1_xboole_0=A_105)), inference(resolution, [status(thm)], [c_50, c_392])).
% 19.86/11.43  tff(c_17897, plain, (![A_7706, B_7707]: (k1_relat_1('#skF_5'(A_7706, B_7707))!='#skF_7' | '#skF_1'(k1_tarski(B_7707), '#skF_6')=B_7707 | k1_xboole_0=A_7706)), inference(resolution, [status(thm)], [c_48, c_559])).
% 19.86/11.43  tff(c_17942, plain, (![A_21, B_25]: (A_21!='#skF_7' | '#skF_1'(k1_tarski(B_25), '#skF_6')=B_25 | k1_xboole_0=A_21 | k1_xboole_0=A_21)), inference(superposition, [status(thm), theory('equality')], [c_46, c_17897])).
% 19.86/11.43  tff(c_17944, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_17942])).
% 19.86/11.43  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 19.86/11.43  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 19.86/11.43  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 19.86/11.43  tff(c_70, plain, (![C_34]: (~r1_tarski(k2_relat_1(C_34), '#skF_6') | k1_relat_1(C_34)!='#skF_7' | ~v1_funct_1(C_34) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_101])).
% 19.86/11.43  tff(c_73, plain, (~r1_tarski(k1_xboole_0, '#skF_6') | k1_relat_1(k1_xboole_0)!='#skF_7' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_70])).
% 19.86/11.43  tff(c_75, plain, (k1_xboole_0!='#skF_7' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_14, c_73])).
% 19.86/11.43  tff(c_93, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_75])).
% 19.86/11.43  tff(c_38, plain, (![A_15]: (k1_relat_1('#skF_4'(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_70])).
% 19.86/11.43  tff(c_42, plain, (![A_15]: (v1_relat_1('#skF_4'(A_15)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 19.86/11.43  tff(c_94, plain, (![A_42]: (k1_relat_1(A_42)!=k1_xboole_0 | k1_xboole_0=A_42 | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_58])).
% 19.86/11.43  tff(c_100, plain, (![A_15]: (k1_relat_1('#skF_4'(A_15))!=k1_xboole_0 | '#skF_4'(A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_94])).
% 19.86/11.43  tff(c_105, plain, (![A_43]: (k1_xboole_0!=A_43 | '#skF_4'(A_43)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_100])).
% 19.86/11.43  tff(c_115, plain, (![A_43]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_43)), inference(superposition, [status(thm), theory('equality')], [c_105, c_42])).
% 19.86/11.43  tff(c_121, plain, (![A_43]: (k1_xboole_0!=A_43)), inference(negUnitSimplification, [status(thm)], [c_93, c_115])).
% 19.86/11.43  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_28])).
% 19.86/11.43  tff(c_130, plain, (~v1_funct_1(k1_xboole_0) | k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_75])).
% 19.86/11.43  tff(c_132, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_130])).
% 19.86/11.43  tff(c_17987, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17944, c_132])).
% 19.86/11.43  tff(c_17990, plain, (![B_7750]: ('#skF_1'(k1_tarski(B_7750), '#skF_6')=B_7750)), inference(splitRight, [status(thm)], [c_17942])).
% 19.86/11.43  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.86/11.43  tff(c_18414, plain, (![B_7837]: (~r2_hidden(B_7837, '#skF_6') | r1_tarski(k1_tarski(B_7837), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_17990, c_4])).
% 19.86/11.43  tff(c_232, plain, (![B_55, A_54]: (~r1_tarski(k1_tarski(B_55), '#skF_6') | k1_relat_1('#skF_5'(A_54, B_55))!='#skF_7' | ~v1_funct_1('#skF_5'(A_54, B_55)) | ~v1_relat_1('#skF_5'(A_54, B_55)) | k1_xboole_0=A_54)), inference(superposition, [status(thm), theory('equality')], [c_226, c_52])).
% 19.86/11.43  tff(c_18463, plain, (![A_7923, B_7924]: (k1_relat_1('#skF_5'(A_7923, B_7924))!='#skF_7' | ~v1_funct_1('#skF_5'(A_7923, B_7924)) | ~v1_relat_1('#skF_5'(A_7923, B_7924)) | k1_xboole_0=A_7923 | ~r2_hidden(B_7924, '#skF_6'))), inference(resolution, [status(thm)], [c_18414, c_232])).
% 19.86/11.43  tff(c_71547, plain, (![A_20685, B_20686]: (k1_relat_1('#skF_5'(A_20685, B_20686))!='#skF_7' | ~v1_funct_1('#skF_5'(A_20685, B_20686)) | ~r2_hidden(B_20686, '#skF_6') | k1_xboole_0=A_20685)), inference(resolution, [status(thm)], [c_50, c_18463])).
% 19.86/11.43  tff(c_71576, plain, (![A_20799, B_20800]: (k1_relat_1('#skF_5'(A_20799, B_20800))!='#skF_7' | ~r2_hidden(B_20800, '#skF_6') | k1_xboole_0=A_20799)), inference(resolution, [status(thm)], [c_48, c_71547])).
% 19.86/11.43  tff(c_71627, plain, (![A_21, B_25]: (A_21!='#skF_7' | ~r2_hidden(B_25, '#skF_6') | k1_xboole_0=A_21 | k1_xboole_0=A_21)), inference(superposition, [status(thm), theory('equality')], [c_46, c_71576])).
% 19.86/11.43  tff(c_71630, plain, (![B_20913]: (~r2_hidden(B_20913, '#skF_6'))), inference(splitLeft, [status(thm)], [c_71627])).
% 19.86/11.43  tff(c_71675, plain, (![B_21026]: (r1_tarski('#skF_6', B_21026))), inference(resolution, [status(thm)], [c_6, c_71630])).
% 19.86/11.43  tff(c_250, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_38])).
% 19.86/11.43  tff(c_259, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_250])).
% 19.86/11.43  tff(c_71713, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_71675, c_259])).
% 19.86/11.43  tff(c_71736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_71713])).
% 19.86/11.43  tff(c_71738, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_71627])).
% 19.86/11.43  tff(c_71786, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71738, c_132])).
% 19.86/11.43  tff(c_71788, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_130])).
% 19.86/11.43  tff(c_71787, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_130])).
% 19.86/11.43  tff(c_71789, plain, (~v1_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_71788, c_71787])).
% 19.86/11.43  tff(c_34, plain, (![A_14]: (k1_relat_1(A_14)!=k1_xboole_0 | k1_xboole_0=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 19.86/11.43  tff(c_71815, plain, (![A_21139]: (k1_relat_1(A_21139)!='#skF_7' | A_21139='#skF_7' | ~v1_relat_1(A_21139))), inference(demodulation, [status(thm), theory('equality')], [c_71788, c_71788, c_34])).
% 19.86/11.43  tff(c_71821, plain, (![A_15]: (k1_relat_1('#skF_4'(A_15))!='#skF_7' | '#skF_4'(A_15)='#skF_7')), inference(resolution, [status(thm)], [c_42, c_71815])).
% 19.86/11.43  tff(c_71830, plain, (![A_21141]: (A_21141!='#skF_7' | '#skF_4'(A_21141)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_71821])).
% 19.86/11.43  tff(c_40, plain, (![A_15]: (v1_funct_1('#skF_4'(A_15)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 19.86/11.43  tff(c_71838, plain, (![A_21141]: (v1_funct_1('#skF_7') | A_21141!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_71830, c_40])).
% 19.86/11.43  tff(c_71846, plain, (![A_21141]: (A_21141!='#skF_7')), inference(negUnitSimplification, [status(thm)], [c_71789, c_71838])).
% 19.86/11.43  tff(c_71795, plain, (k1_relat_1('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_71788, c_71788, c_30])).
% 19.86/11.43  tff(c_71854, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71846, c_71795])).
% 19.86/11.43  tff(c_71856, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_54])).
% 19.86/11.43  tff(c_71855, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_54])).
% 19.86/11.43  tff(c_71870, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_71856, c_71855])).
% 19.86/11.43  tff(c_71864, plain, (k1_relat_1('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_71855, c_71855, c_30])).
% 19.86/11.43  tff(c_71885, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_71870, c_71870, c_71864])).
% 19.86/11.43  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 19.86/11.43  tff(c_71863, plain, (k2_relat_1('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_71855, c_71855, c_28])).
% 19.86/11.43  tff(c_71880, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_71870, c_71870, c_71863])).
% 19.86/11.43  tff(c_71904, plain, (![C_21148]: (~r1_tarski(k2_relat_1(C_21148), '#skF_6') | k1_relat_1(C_21148)!='#skF_6' | ~v1_funct_1(C_21148) | ~v1_relat_1(C_21148))), inference(demodulation, [status(thm), theory('equality')], [c_71870, c_52])).
% 19.86/11.43  tff(c_71907, plain, (~r1_tarski('#skF_6', '#skF_6') | k1_relat_1('#skF_6')!='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_71880, c_71904])).
% 19.86/11.43  tff(c_71909, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_71885, c_12, c_71907])).
% 19.86/11.43  tff(c_71910, plain, (~v1_relat_1('#skF_6')), inference(splitLeft, [status(thm)], [c_71909])).
% 19.86/11.43  tff(c_71943, plain, (![A_21156]: (k1_relat_1(A_21156)!='#skF_6' | A_21156='#skF_6' | ~v1_relat_1(A_21156))), inference(demodulation, [status(thm), theory('equality')], [c_71856, c_71856, c_34])).
% 19.86/11.43  tff(c_71949, plain, (![A_15]: (k1_relat_1('#skF_4'(A_15))!='#skF_6' | '#skF_4'(A_15)='#skF_6')), inference(resolution, [status(thm)], [c_42, c_71943])).
% 19.86/11.43  tff(c_71954, plain, (![A_21157]: (A_21157!='#skF_6' | '#skF_4'(A_21157)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_71949])).
% 19.86/11.43  tff(c_71964, plain, (![A_21157]: (v1_relat_1('#skF_6') | A_21157!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_71954, c_42])).
% 19.86/11.43  tff(c_71970, plain, (![A_21157]: (A_21157!='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_71910, c_71964])).
% 19.86/11.43  tff(c_71982, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71970, c_71885])).
% 19.86/11.43  tff(c_71983, plain, (~v1_funct_1('#skF_6')), inference(splitRight, [status(thm)], [c_71909])).
% 19.86/11.43  tff(c_72024, plain, (![A_21165]: (k1_relat_1(A_21165)!='#skF_6' | A_21165='#skF_6' | ~v1_relat_1(A_21165))), inference(demodulation, [status(thm), theory('equality')], [c_71856, c_71856, c_34])).
% 19.86/11.43  tff(c_72033, plain, (![A_15]: (k1_relat_1('#skF_4'(A_15))!='#skF_6' | '#skF_4'(A_15)='#skF_6')), inference(resolution, [status(thm)], [c_42, c_72024])).
% 19.86/11.43  tff(c_72042, plain, (![A_21166]: (A_21166!='#skF_6' | '#skF_4'(A_21166)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_72033])).
% 19.86/11.43  tff(c_72050, plain, (![A_21166]: (v1_funct_1('#skF_6') | A_21166!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_72042, c_40])).
% 19.86/11.43  tff(c_72058, plain, (![A_21166]: (A_21166!='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_71983, c_72050])).
% 19.86/11.43  tff(c_72071, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72058, c_71885])).
% 19.86/11.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.86/11.43  
% 19.86/11.43  Inference rules
% 19.86/11.43  ----------------------
% 19.86/11.43  #Ref     : 0
% 19.86/11.43  #Sup     : 13416
% 19.86/11.43  #Fact    : 38
% 19.86/11.43  #Define  : 0
% 19.86/11.43  #Split   : 7
% 19.86/11.43  #Chain   : 0
% 19.86/11.43  #Close   : 0
% 19.86/11.43  
% 19.86/11.43  Ordering : KBO
% 19.86/11.43  
% 19.86/11.43  Simplification rules
% 19.86/11.43  ----------------------
% 19.86/11.43  #Subsume      : 3933
% 19.86/11.43  #Demod        : 1344
% 19.86/11.43  #Tautology    : 1986
% 19.86/11.43  #SimpNegUnit  : 77
% 19.86/11.43  #BackRed      : 127
% 19.86/11.43  
% 19.86/11.43  #Partial instantiations: 17808
% 19.86/11.43  #Strategies tried      : 1
% 19.86/11.43  
% 19.86/11.43  Timing (in seconds)
% 19.86/11.43  ----------------------
% 19.86/11.43  Preprocessing        : 0.34
% 19.86/11.43  Parsing              : 0.17
% 19.86/11.43  CNF conversion       : 0.03
% 19.86/11.43  Main loop            : 10.17
% 19.86/11.43  Inferencing          : 1.68
% 19.86/11.43  Reduction            : 1.48
% 19.86/11.43  Demodulation         : 1.06
% 19.86/11.43  BG Simplification    : 0.27
% 19.86/11.43  Subsumption          : 6.31
% 19.86/11.43  Abstraction          : 0.38
% 19.86/11.43  MUC search           : 0.00
% 19.86/11.43  Cooper               : 0.00
% 19.86/11.43  Total                : 10.55
% 19.86/11.43  Index Insertion      : 0.00
% 19.86/11.43  Index Deletion       : 0.00
% 19.86/11.43  Index Matching       : 0.00
% 19.86/11.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
