%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:14 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 449 expanded)
%              Number of leaves         :   38 ( 155 expanded)
%              Depth                    :   11
%              Number of atoms          :  186 (1079 expanded)
%              Number of equality atoms :   97 ( 631 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(np__1,type,(
    np__1: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_62,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_95,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_82,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_518,plain,(
    ! [A_141,B_142] :
      ( r2_hidden(k4_tarski('#skF_2'(A_141,B_142),'#skF_3'(A_141,B_142)),A_141)
      | r2_hidden('#skF_4'(A_141,B_142),B_142)
      | k1_relat_1(A_141) = B_142 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_286,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,k3_xboole_0(A_83,B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_289,plain,(
    ! [A_6,C_85] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_85,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_286])).

tff(c_291,plain,(
    ! [C_85] : ~ r2_hidden(C_85,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_289])).

tff(c_559,plain,(
    ! [B_142] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_142),B_142)
      | k1_relat_1(k1_xboole_0) = B_142 ) ),
    inference(resolution,[status(thm)],[c_518,c_291])).

tff(c_575,plain,(
    ! [B_142] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_142),B_142)
      | k1_xboole_0 = B_142 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_559])).

tff(c_48,plain,(
    ! [A_39,B_43] :
      ( k1_relat_1('#skF_7'(A_39,B_43)) = A_39
      | k1_xboole_0 = A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_50,plain,(
    ! [A_39,B_43] :
      ( v1_funct_1('#skF_7'(A_39,B_43))
      | k1_xboole_0 = A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_52,plain,(
    ! [A_39,B_43] :
      ( v1_relat_1('#skF_7'(A_39,B_43))
      | k1_xboole_0 = A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(k1_tarski(A_9),B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_274,plain,(
    ! [A_81,B_82] :
      ( k2_relat_1('#skF_7'(A_81,B_82)) = k1_tarski(B_82)
      | k1_xboole_0 = A_81 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_54,plain,(
    ! [C_46] :
      ( ~ r1_tarski(k2_relat_1(C_46),'#skF_8')
      | k1_relat_1(C_46) != '#skF_9'
      | ~ v1_funct_1(C_46)
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_292,plain,(
    ! [B_86,A_87] :
      ( ~ r1_tarski(k1_tarski(B_86),'#skF_8')
      | k1_relat_1('#skF_7'(A_87,B_86)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_87,B_86))
      | ~ v1_relat_1('#skF_7'(A_87,B_86))
      | k1_xboole_0 = A_87 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_54])).

tff(c_377,plain,(
    ! [A_108,A_109] :
      ( k1_relat_1('#skF_7'(A_108,A_109)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_108,A_109))
      | ~ v1_relat_1('#skF_7'(A_108,A_109))
      | k1_xboole_0 = A_108
      | ~ r2_hidden(A_109,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_14,c_292])).

tff(c_468,plain,(
    ! [A_131,B_132] :
      ( k1_relat_1('#skF_7'(A_131,B_132)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_131,B_132))
      | ~ r2_hidden(B_132,'#skF_8')
      | k1_xboole_0 = A_131 ) ),
    inference(resolution,[status(thm)],[c_52,c_377])).

tff(c_716,plain,(
    ! [A_146,B_147] :
      ( k1_relat_1('#skF_7'(A_146,B_147)) != '#skF_9'
      | ~ r2_hidden(B_147,'#skF_8')
      | k1_xboole_0 = A_146 ) ),
    inference(resolution,[status(thm)],[c_50,c_468])).

tff(c_722,plain,(
    ! [A_39,B_43] :
      ( A_39 != '#skF_9'
      | ~ r2_hidden(B_43,'#skF_8')
      | k1_xboole_0 = A_39
      | k1_xboole_0 = A_39 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_716])).

tff(c_927,plain,(
    ! [B_156] : ~ r2_hidden(B_156,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_722])).

tff(c_931,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_575,c_927])).

tff(c_943,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_931])).

tff(c_945,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_722])).

tff(c_8,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_77,plain,(
    ! [C_52] :
      ( ~ r1_tarski(k2_relat_1(C_52),'#skF_8')
      | k1_relat_1(C_52) != '#skF_9'
      | ~ v1_funct_1(C_52)
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_80,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_8')
    | k1_relat_1(k1_xboole_0) != '#skF_9'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_77])).

tff(c_82,plain,
    ( k1_xboole_0 != '#skF_9'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8,c_80])).

tff(c_94,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_40,plain,(
    ! [A_33] : k1_relat_1('#skF_6'(A_33)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_44,plain,(
    ! [A_33] : v1_relat_1('#skF_6'(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_114,plain,(
    ! [A_63] :
      ( k1_relat_1(A_63) != k1_xboole_0
      | k1_xboole_0 = A_63
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_120,plain,(
    ! [A_33] :
      ( k1_relat_1('#skF_6'(A_33)) != k1_xboole_0
      | '#skF_6'(A_33) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_114])).

tff(c_135,plain,(
    ! [A_66] :
      ( k1_xboole_0 != A_66
      | '#skF_6'(A_66) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_120])).

tff(c_145,plain,(
    ! [A_66] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_66 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_44])).

tff(c_151,plain,(
    ! [A_66] : k1_xboole_0 != A_66 ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_145])).

tff(c_162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_6])).

tff(c_163,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_165,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_945,c_165])).

tff(c_985,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_984,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_986,plain,(
    ~ v1_funct_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_984])).

tff(c_36,plain,(
    ! [A_32] :
      ( k1_relat_1(A_32) != k1_xboole_0
      | k1_xboole_0 = A_32
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1060,plain,(
    ! [A_169] :
      ( k1_relat_1(A_169) != '#skF_9'
      | A_169 = '#skF_9'
      | ~ v1_relat_1(A_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_985,c_36])).

tff(c_1069,plain,(
    ! [A_33] :
      ( k1_relat_1('#skF_6'(A_33)) != '#skF_9'
      | '#skF_6'(A_33) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_44,c_1060])).

tff(c_1078,plain,(
    ! [A_170] :
      ( A_170 != '#skF_9'
      | '#skF_6'(A_170) = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1069])).

tff(c_42,plain,(
    ! [A_33] : v1_funct_1('#skF_6'(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1086,plain,(
    ! [A_170] :
      ( v1_funct_1('#skF_9')
      | A_170 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1078,c_42])).

tff(c_1094,plain,(
    ! [A_170] : A_170 != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_986,c_1086])).

tff(c_991,plain,(
    ! [A_6] : k3_xboole_0(A_6,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_985,c_6])).

tff(c_1107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1094,c_991])).

tff(c_1109,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1108,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1119,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1109,c_1108])).

tff(c_1114,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1108,c_1108,c_32])).

tff(c_1128,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1119,c_1119,c_1114])).

tff(c_1112,plain,(
    ! [A_7] : r1_tarski('#skF_9',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1108,c_8])).

tff(c_1138,plain,(
    ! [A_7] : r1_tarski('#skF_8',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1119,c_1112])).

tff(c_1111,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1108,c_1108,c_30])).

tff(c_1133,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1119,c_1119,c_1111])).

tff(c_1160,plain,(
    ! [C_175] :
      ( ~ r1_tarski(k2_relat_1(C_175),'#skF_8')
      | k1_relat_1(C_175) != '#skF_8'
      | ~ v1_funct_1(C_175)
      | ~ v1_relat_1(C_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1119,c_54])).

tff(c_1163,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | k1_relat_1('#skF_8') != '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1133,c_1160])).

tff(c_1165,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1128,c_1138,c_1163])).

tff(c_1166,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1165])).

tff(c_1172,plain,(
    ! [A_180] :
      ( k1_relat_1(A_180) != '#skF_8'
      | A_180 = '#skF_8'
      | ~ v1_relat_1(A_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1109,c_1109,c_36])).

tff(c_1178,plain,(
    ! [A_33] :
      ( k1_relat_1('#skF_6'(A_33)) != '#skF_8'
      | '#skF_6'(A_33) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_44,c_1172])).

tff(c_1193,plain,(
    ! [A_182] :
      ( A_182 != '#skF_8'
      | '#skF_6'(A_182) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1178])).

tff(c_1203,plain,(
    ! [A_182] :
      ( v1_relat_1('#skF_8')
      | A_182 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1193,c_44])).

tff(c_1209,plain,(
    ! [A_182] : A_182 != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1166,c_1203])).

tff(c_1110,plain,(
    ! [A_6] : k3_xboole_0(A_6,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1108,c_1108,c_6])).

tff(c_1142,plain,(
    ! [A_6] : k3_xboole_0(A_6,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1119,c_1119,c_1110])).

tff(c_1221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1209,c_1142])).

tff(c_1222,plain,(
    ~ v1_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1165])).

tff(c_1247,plain,(
    ! [A_190] :
      ( k1_relat_1(A_190) != '#skF_8'
      | A_190 = '#skF_8'
      | ~ v1_relat_1(A_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1109,c_1109,c_36])).

tff(c_1256,plain,(
    ! [A_33] :
      ( k1_relat_1('#skF_6'(A_33)) != '#skF_8'
      | '#skF_6'(A_33) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_44,c_1247])).

tff(c_1270,plain,(
    ! [A_193] :
      ( A_193 != '#skF_8'
      | '#skF_6'(A_193) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1256])).

tff(c_1278,plain,(
    ! [A_193] :
      ( v1_funct_1('#skF_8')
      | A_193 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1270,c_42])).

tff(c_1286,plain,(
    ! [A_193] : A_193 != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1222,c_1278])).

tff(c_1299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1286,c_1142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:47:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.77  
% 3.55/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.77  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_6 > #skF_4
% 3.55/1.77  
% 3.55/1.77  %Foreground sorts:
% 3.55/1.77  
% 3.55/1.77  
% 3.55/1.77  %Background operators:
% 3.55/1.77  
% 3.55/1.77  
% 3.55/1.77  %Foreground operators:
% 3.55/1.77  tff(np__1, type, np__1: $i).
% 3.55/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.55/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.55/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.55/1.77  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.55/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.55/1.77  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.55/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.55/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.55/1.77  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.55/1.77  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.55/1.77  tff('#skF_9', type, '#skF_9': $i).
% 3.55/1.77  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.55/1.77  tff('#skF_8', type, '#skF_8': $i).
% 3.55/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.55/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.77  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.55/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.55/1.77  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.55/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.55/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.55/1.77  tff('#skF_6', type, '#skF_6': $i > $i).
% 3.55/1.77  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.55/1.77  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.55/1.77  
% 3.94/1.79  tff(f_113, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 3.94/1.79  tff(f_62, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.94/1.79  tff(f_59, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.94/1.79  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.94/1.79  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.94/1.79  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.94/1.79  tff(f_95, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 3.94/1.79  tff(f_49, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.94/1.79  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.94/1.79  tff(f_82, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 3.94/1.79  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.94/1.79  tff(c_56, plain, (k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.94/1.79  tff(c_76, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_56])).
% 3.94/1.79  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.94/1.79  tff(c_518, plain, (![A_141, B_142]: (r2_hidden(k4_tarski('#skF_2'(A_141, B_142), '#skF_3'(A_141, B_142)), A_141) | r2_hidden('#skF_4'(A_141, B_142), B_142) | k1_relat_1(A_141)=B_142)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.94/1.79  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.94/1.79  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.94/1.79  tff(c_286, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, k3_xboole_0(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.94/1.79  tff(c_289, plain, (![A_6, C_85]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_85, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_286])).
% 3.94/1.79  tff(c_291, plain, (![C_85]: (~r2_hidden(C_85, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_289])).
% 3.94/1.79  tff(c_559, plain, (![B_142]: (r2_hidden('#skF_4'(k1_xboole_0, B_142), B_142) | k1_relat_1(k1_xboole_0)=B_142)), inference(resolution, [status(thm)], [c_518, c_291])).
% 3.94/1.79  tff(c_575, plain, (![B_142]: (r2_hidden('#skF_4'(k1_xboole_0, B_142), B_142) | k1_xboole_0=B_142)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_559])).
% 3.94/1.79  tff(c_48, plain, (![A_39, B_43]: (k1_relat_1('#skF_7'(A_39, B_43))=A_39 | k1_xboole_0=A_39)), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.94/1.79  tff(c_50, plain, (![A_39, B_43]: (v1_funct_1('#skF_7'(A_39, B_43)) | k1_xboole_0=A_39)), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.94/1.79  tff(c_52, plain, (![A_39, B_43]: (v1_relat_1('#skF_7'(A_39, B_43)) | k1_xboole_0=A_39)), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.94/1.79  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k1_tarski(A_9), B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.94/1.79  tff(c_274, plain, (![A_81, B_82]: (k2_relat_1('#skF_7'(A_81, B_82))=k1_tarski(B_82) | k1_xboole_0=A_81)), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.94/1.79  tff(c_54, plain, (![C_46]: (~r1_tarski(k2_relat_1(C_46), '#skF_8') | k1_relat_1(C_46)!='#skF_9' | ~v1_funct_1(C_46) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.94/1.79  tff(c_292, plain, (![B_86, A_87]: (~r1_tarski(k1_tarski(B_86), '#skF_8') | k1_relat_1('#skF_7'(A_87, B_86))!='#skF_9' | ~v1_funct_1('#skF_7'(A_87, B_86)) | ~v1_relat_1('#skF_7'(A_87, B_86)) | k1_xboole_0=A_87)), inference(superposition, [status(thm), theory('equality')], [c_274, c_54])).
% 3.94/1.79  tff(c_377, plain, (![A_108, A_109]: (k1_relat_1('#skF_7'(A_108, A_109))!='#skF_9' | ~v1_funct_1('#skF_7'(A_108, A_109)) | ~v1_relat_1('#skF_7'(A_108, A_109)) | k1_xboole_0=A_108 | ~r2_hidden(A_109, '#skF_8'))), inference(resolution, [status(thm)], [c_14, c_292])).
% 3.94/1.79  tff(c_468, plain, (![A_131, B_132]: (k1_relat_1('#skF_7'(A_131, B_132))!='#skF_9' | ~v1_funct_1('#skF_7'(A_131, B_132)) | ~r2_hidden(B_132, '#skF_8') | k1_xboole_0=A_131)), inference(resolution, [status(thm)], [c_52, c_377])).
% 3.94/1.79  tff(c_716, plain, (![A_146, B_147]: (k1_relat_1('#skF_7'(A_146, B_147))!='#skF_9' | ~r2_hidden(B_147, '#skF_8') | k1_xboole_0=A_146)), inference(resolution, [status(thm)], [c_50, c_468])).
% 3.94/1.79  tff(c_722, plain, (![A_39, B_43]: (A_39!='#skF_9' | ~r2_hidden(B_43, '#skF_8') | k1_xboole_0=A_39 | k1_xboole_0=A_39)), inference(superposition, [status(thm), theory('equality')], [c_48, c_716])).
% 3.94/1.79  tff(c_927, plain, (![B_156]: (~r2_hidden(B_156, '#skF_8'))), inference(splitLeft, [status(thm)], [c_722])).
% 3.94/1.79  tff(c_931, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_575, c_927])).
% 3.94/1.79  tff(c_943, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_931])).
% 3.94/1.79  tff(c_945, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_722])).
% 3.94/1.79  tff(c_8, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.94/1.79  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.94/1.79  tff(c_77, plain, (![C_52]: (~r1_tarski(k2_relat_1(C_52), '#skF_8') | k1_relat_1(C_52)!='#skF_9' | ~v1_funct_1(C_52) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.94/1.79  tff(c_80, plain, (~r1_tarski(k1_xboole_0, '#skF_8') | k1_relat_1(k1_xboole_0)!='#skF_9' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_77])).
% 3.94/1.79  tff(c_82, plain, (k1_xboole_0!='#skF_9' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8, c_80])).
% 3.94/1.79  tff(c_94, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_82])).
% 3.94/1.79  tff(c_40, plain, (![A_33]: (k1_relat_1('#skF_6'(A_33))=A_33)), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.94/1.79  tff(c_44, plain, (![A_33]: (v1_relat_1('#skF_6'(A_33)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.94/1.79  tff(c_114, plain, (![A_63]: (k1_relat_1(A_63)!=k1_xboole_0 | k1_xboole_0=A_63 | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.94/1.79  tff(c_120, plain, (![A_33]: (k1_relat_1('#skF_6'(A_33))!=k1_xboole_0 | '#skF_6'(A_33)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_114])).
% 3.94/1.79  tff(c_135, plain, (![A_66]: (k1_xboole_0!=A_66 | '#skF_6'(A_66)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_120])).
% 3.94/1.79  tff(c_145, plain, (![A_66]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_66)), inference(superposition, [status(thm), theory('equality')], [c_135, c_44])).
% 3.94/1.79  tff(c_151, plain, (![A_66]: (k1_xboole_0!=A_66)), inference(negUnitSimplification, [status(thm)], [c_94, c_145])).
% 3.94/1.79  tff(c_162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_6])).
% 3.94/1.79  tff(c_163, plain, (~v1_funct_1(k1_xboole_0) | k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_82])).
% 3.94/1.79  tff(c_165, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_163])).
% 3.94/1.79  tff(c_983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_945, c_165])).
% 3.94/1.79  tff(c_985, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_163])).
% 3.94/1.79  tff(c_984, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_163])).
% 3.94/1.79  tff(c_986, plain, (~v1_funct_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_985, c_984])).
% 3.94/1.79  tff(c_36, plain, (![A_32]: (k1_relat_1(A_32)!=k1_xboole_0 | k1_xboole_0=A_32 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.94/1.79  tff(c_1060, plain, (![A_169]: (k1_relat_1(A_169)!='#skF_9' | A_169='#skF_9' | ~v1_relat_1(A_169))), inference(demodulation, [status(thm), theory('equality')], [c_985, c_985, c_36])).
% 3.94/1.79  tff(c_1069, plain, (![A_33]: (k1_relat_1('#skF_6'(A_33))!='#skF_9' | '#skF_6'(A_33)='#skF_9')), inference(resolution, [status(thm)], [c_44, c_1060])).
% 3.94/1.79  tff(c_1078, plain, (![A_170]: (A_170!='#skF_9' | '#skF_6'(A_170)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1069])).
% 3.94/1.79  tff(c_42, plain, (![A_33]: (v1_funct_1('#skF_6'(A_33)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.94/1.79  tff(c_1086, plain, (![A_170]: (v1_funct_1('#skF_9') | A_170!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1078, c_42])).
% 3.94/1.79  tff(c_1094, plain, (![A_170]: (A_170!='#skF_9')), inference(negUnitSimplification, [status(thm)], [c_986, c_1086])).
% 3.94/1.79  tff(c_991, plain, (![A_6]: (k3_xboole_0(A_6, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_985, c_985, c_6])).
% 3.94/1.79  tff(c_1107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1094, c_991])).
% 3.94/1.79  tff(c_1109, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_56])).
% 3.94/1.79  tff(c_1108, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_56])).
% 3.94/1.79  tff(c_1119, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1109, c_1108])).
% 3.94/1.79  tff(c_1114, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1108, c_1108, c_32])).
% 3.94/1.79  tff(c_1128, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1119, c_1119, c_1114])).
% 3.94/1.79  tff(c_1112, plain, (![A_7]: (r1_tarski('#skF_9', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1108, c_8])).
% 3.94/1.79  tff(c_1138, plain, (![A_7]: (r1_tarski('#skF_8', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1119, c_1112])).
% 3.94/1.79  tff(c_1111, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1108, c_1108, c_30])).
% 3.94/1.79  tff(c_1133, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1119, c_1119, c_1111])).
% 3.94/1.79  tff(c_1160, plain, (![C_175]: (~r1_tarski(k2_relat_1(C_175), '#skF_8') | k1_relat_1(C_175)!='#skF_8' | ~v1_funct_1(C_175) | ~v1_relat_1(C_175))), inference(demodulation, [status(thm), theory('equality')], [c_1119, c_54])).
% 3.94/1.79  tff(c_1163, plain, (~r1_tarski('#skF_8', '#skF_8') | k1_relat_1('#skF_8')!='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1133, c_1160])).
% 3.94/1.79  tff(c_1165, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1128, c_1138, c_1163])).
% 3.94/1.79  tff(c_1166, plain, (~v1_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_1165])).
% 3.94/1.79  tff(c_1172, plain, (![A_180]: (k1_relat_1(A_180)!='#skF_8' | A_180='#skF_8' | ~v1_relat_1(A_180))), inference(demodulation, [status(thm), theory('equality')], [c_1109, c_1109, c_36])).
% 3.94/1.79  tff(c_1178, plain, (![A_33]: (k1_relat_1('#skF_6'(A_33))!='#skF_8' | '#skF_6'(A_33)='#skF_8')), inference(resolution, [status(thm)], [c_44, c_1172])).
% 3.94/1.79  tff(c_1193, plain, (![A_182]: (A_182!='#skF_8' | '#skF_6'(A_182)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1178])).
% 3.94/1.79  tff(c_1203, plain, (![A_182]: (v1_relat_1('#skF_8') | A_182!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1193, c_44])).
% 3.94/1.79  tff(c_1209, plain, (![A_182]: (A_182!='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1166, c_1203])).
% 3.94/1.79  tff(c_1110, plain, (![A_6]: (k3_xboole_0(A_6, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1108, c_1108, c_6])).
% 3.94/1.79  tff(c_1142, plain, (![A_6]: (k3_xboole_0(A_6, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1119, c_1119, c_1110])).
% 3.94/1.79  tff(c_1221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1209, c_1142])).
% 3.94/1.79  tff(c_1222, plain, (~v1_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_1165])).
% 3.94/1.79  tff(c_1247, plain, (![A_190]: (k1_relat_1(A_190)!='#skF_8' | A_190='#skF_8' | ~v1_relat_1(A_190))), inference(demodulation, [status(thm), theory('equality')], [c_1109, c_1109, c_36])).
% 3.94/1.79  tff(c_1256, plain, (![A_33]: (k1_relat_1('#skF_6'(A_33))!='#skF_8' | '#skF_6'(A_33)='#skF_8')), inference(resolution, [status(thm)], [c_44, c_1247])).
% 3.94/1.79  tff(c_1270, plain, (![A_193]: (A_193!='#skF_8' | '#skF_6'(A_193)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1256])).
% 3.94/1.79  tff(c_1278, plain, (![A_193]: (v1_funct_1('#skF_8') | A_193!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1270, c_42])).
% 3.94/1.79  tff(c_1286, plain, (![A_193]: (A_193!='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1222, c_1278])).
% 3.94/1.79  tff(c_1299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1286, c_1142])).
% 3.94/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/1.79  
% 3.94/1.79  Inference rules
% 3.94/1.79  ----------------------
% 3.94/1.79  #Ref     : 0
% 3.94/1.79  #Sup     : 258
% 3.94/1.79  #Fact    : 0
% 3.94/1.79  #Define  : 0
% 3.94/1.79  #Split   : 6
% 3.94/1.79  #Chain   : 0
% 3.94/1.79  #Close   : 0
% 3.94/1.79  
% 3.94/1.79  Ordering : KBO
% 3.94/1.79  
% 3.94/1.79  Simplification rules
% 3.94/1.79  ----------------------
% 3.94/1.79  #Subsume      : 90
% 3.94/1.79  #Demod        : 183
% 3.94/1.79  #Tautology    : 101
% 3.94/1.79  #SimpNegUnit  : 56
% 3.94/1.79  #BackRed      : 85
% 3.94/1.79  
% 3.94/1.79  #Partial instantiations: 0
% 3.94/1.79  #Strategies tried      : 1
% 3.94/1.79  
% 3.94/1.79  Timing (in seconds)
% 3.94/1.79  ----------------------
% 3.94/1.80  Preprocessing        : 0.42
% 3.94/1.80  Parsing              : 0.22
% 3.94/1.80  CNF conversion       : 0.04
% 3.94/1.80  Main loop            : 0.52
% 3.94/1.80  Inferencing          : 0.19
% 3.94/1.80  Reduction            : 0.16
% 3.94/1.80  Demodulation         : 0.11
% 3.94/1.80  BG Simplification    : 0.03
% 3.94/1.80  Subsumption          : 0.10
% 3.94/1.80  Abstraction          : 0.03
% 3.94/1.80  MUC search           : 0.00
% 3.94/1.80  Cooper               : 0.00
% 3.94/1.80  Total                : 0.99
% 3.94/1.80  Index Insertion      : 0.00
% 3.94/1.80  Index Deletion       : 0.00
% 3.94/1.80  Index Matching       : 0.00
% 3.94/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
