%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:42 EST 2020

% Result     : Theorem 8.13s
% Output     : CNFRefutation 8.29s
% Verified   : 
% Statistics : Number of formulae       :  176 (1109 expanded)
%              Number of leaves         :   34 ( 332 expanded)
%              Depth                    :   13
%              Number of atoms          :  216 (2050 expanded)
%              Number of equality atoms :  120 (1734 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_15 > #skF_4 > #skF_14 > #skF_13 > #skF_5 > #skF_10 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_11 > #skF_3 > #skF_1 > #skF_9 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_68,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(c_17936,plain,(
    ! [A_1151,B_1152,C_1153] :
      ( r2_hidden('#skF_4'(A_1151,B_1152,C_1153),B_1152)
      | r2_hidden('#skF_5'(A_1151,B_1152,C_1153),C_1153)
      | k2_zfmisc_1(A_1151,B_1152) = C_1153 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14792,plain,(
    ! [A_973,B_974,C_975] :
      ( r2_hidden('#skF_4'(A_973,B_974,C_975),B_974)
      | r2_hidden('#skF_5'(A_973,B_974,C_975),C_975)
      | k2_zfmisc_1(A_973,B_974) = C_975 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_11808,plain,(
    ! [A_794,B_795,C_796] :
      ( r2_hidden('#skF_3'(A_794,B_795,C_796),A_794)
      | r2_hidden('#skF_5'(A_794,B_795,C_796),C_796)
      | k2_zfmisc_1(A_794,B_795) = C_796 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8716,plain,(
    ! [A_602,B_603,C_604] :
      ( r2_hidden('#skF_4'(A_602,B_603,C_604),B_603)
      | r2_hidden('#skF_5'(A_602,B_603,C_604),C_604)
      | k2_zfmisc_1(A_602,B_603) = C_604 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 != '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_15' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_810,plain,(
    ! [A_124,B_125] :
      ( r2_hidden('#skF_9'(A_124,B_125),A_124)
      | r2_hidden('#skF_10'(A_124,B_125),B_125)
      | k3_tarski(A_124) = B_125 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_60,plain,
    ( k2_zfmisc_1('#skF_12','#skF_13') != k1_xboole_0
    | k1_xboole_0 != '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_81,plain,(
    k1_xboole_0 != '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_519,plain,(
    ! [A_115,B_116] :
      ( r2_hidden('#skF_9'(A_115,B_116),A_115)
      | r2_hidden('#skF_10'(A_115,B_116),B_116)
      | k3_tarski(A_115) = B_116 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_88,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k4_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_106,plain,(
    ! [A_67] : k4_xboole_0(A_67,A_67) = k3_xboole_0(A_67,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_88])).

tff(c_116,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_6])).

tff(c_132,plain,(
    ! [A_68,B_69,C_70] :
      ( ~ r1_xboole_0(A_68,B_69)
      | ~ r2_hidden(C_70,k3_xboole_0(A_68,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_135,plain,(
    ! [C_70] :
      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(C_70,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_132])).

tff(c_137,plain,(
    ! [C_70] : ~ r2_hidden(C_70,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_135])).

tff(c_66,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 = '#skF_12'
    | k2_zfmisc_1('#skF_14','#skF_15') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_83,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_291,plain,(
    ! [E_94,F_95,A_96,B_97] :
      ( r2_hidden(k4_tarski(E_94,F_95),k2_zfmisc_1(A_96,B_97))
      | ~ r2_hidden(F_95,B_97)
      | ~ r2_hidden(E_94,A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_296,plain,(
    ! [E_94,F_95] :
      ( r2_hidden(k4_tarski(E_94,F_95),k1_xboole_0)
      | ~ r2_hidden(F_95,'#skF_15')
      | ~ r2_hidden(E_94,'#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_291])).

tff(c_298,plain,(
    ! [F_95,E_94] :
      ( ~ r2_hidden(F_95,'#skF_15')
      | ~ r2_hidden(E_94,'#skF_14') ) ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_296])).

tff(c_299,plain,(
    ! [E_94] : ~ r2_hidden(E_94,'#skF_14') ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_670,plain,(
    ! [A_117] :
      ( r2_hidden('#skF_9'(A_117,'#skF_14'),A_117)
      | k3_tarski(A_117) = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_519,c_299])).

tff(c_747,plain,(
    k3_tarski(k1_xboole_0) = '#skF_14' ),
    inference(resolution,[status(thm)],[c_670,c_137])).

tff(c_54,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_770,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_747,c_54])).

tff(c_772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_770])).

tff(c_773,plain,(
    ! [F_95] : ~ r2_hidden(F_95,'#skF_15') ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_921,plain,(
    ! [A_126] :
      ( r2_hidden('#skF_9'(A_126,'#skF_15'),A_126)
      | k3_tarski(A_126) = '#skF_15' ) ),
    inference(resolution,[status(thm)],[c_810,c_773])).

tff(c_978,plain,(
    k3_tarski(k1_xboole_0) = '#skF_15' ),
    inference(resolution,[status(thm)],[c_921,c_137])).

tff(c_998,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_978,c_54])).

tff(c_1000,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_998])).

tff(c_1001,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_6995,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_1001])).

tff(c_5692,plain,(
    ! [A_430,B_431,C_432] :
      ( r2_hidden('#skF_3'(A_430,B_431,C_432),A_430)
      | r2_hidden('#skF_5'(A_430,B_431,C_432),C_432)
      | k2_zfmisc_1(A_430,B_431) = C_432 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2919,plain,(
    ! [A_268,B_269,C_270] :
      ( r2_hidden('#skF_4'(A_268,B_269,C_270),B_269)
      | r2_hidden('#skF_5'(A_268,B_269,C_270),C_270)
      | k2_zfmisc_1(A_268,B_269) = C_270 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1004,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_1001])).

tff(c_1009,plain,(
    ! [A_9] : r1_xboole_0(A_9,'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_10])).

tff(c_1008,plain,(
    ! [A_6] : k4_xboole_0(A_6,'#skF_13') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_6])).

tff(c_1031,plain,(
    ! [A_132,B_133] : k4_xboole_0(A_132,k4_xboole_0(A_132,B_133)) = k3_xboole_0(A_132,B_133) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1049,plain,(
    ! [A_134] : k4_xboole_0(A_134,A_134) = k3_xboole_0(A_134,'#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_1008,c_1031])).

tff(c_1059,plain,(
    k3_xboole_0('#skF_13','#skF_13') = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_1049,c_1008])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1072,plain,(
    ! [C_5] :
      ( ~ r1_xboole_0('#skF_13','#skF_13')
      | ~ r2_hidden(C_5,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1059,c_4])).

tff(c_1076,plain,(
    ! [C_5] : ~ r2_hidden(C_5,'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1009,c_1072])).

tff(c_3716,plain,(
    ! [A_297,C_298] :
      ( r2_hidden('#skF_5'(A_297,'#skF_13',C_298),C_298)
      | k2_zfmisc_1(A_297,'#skF_13') = C_298 ) ),
    inference(resolution,[status(thm)],[c_2919,c_1076])).

tff(c_3828,plain,(
    ! [A_297] : k2_zfmisc_1(A_297,'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_3716,c_1076])).

tff(c_64,plain,
    ( k2_zfmisc_1('#skF_12','#skF_13') != k1_xboole_0
    | k2_zfmisc_1('#skF_14','#skF_15') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1003,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_1005,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_1003])).

tff(c_3866,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3828,c_1005])).

tff(c_3867,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_1001])).

tff(c_3874,plain,(
    ! [A_9] : r1_xboole_0(A_9,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3867,c_10])).

tff(c_3873,plain,(
    ! [A_6] : k4_xboole_0(A_6,'#skF_12') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3867,c_6])).

tff(c_3895,plain,(
    ! [A_304,B_305] : k4_xboole_0(A_304,k4_xboole_0(A_304,B_305)) = k3_xboole_0(A_304,B_305) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3913,plain,(
    ! [A_306] : k4_xboole_0(A_306,A_306) = k3_xboole_0(A_306,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_3873,c_3895])).

tff(c_3923,plain,(
    k3_xboole_0('#skF_12','#skF_12') = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_3913,c_3873])).

tff(c_3937,plain,(
    ! [C_5] :
      ( ~ r1_xboole_0('#skF_12','#skF_12')
      | ~ r2_hidden(C_5,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3923,c_4])).

tff(c_3941,plain,(
    ! [C_5] : ~ r2_hidden(C_5,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3874,c_3937])).

tff(c_6838,plain,(
    ! [A_479,B_480] :
      ( r2_hidden('#skF_3'(A_479,B_480,'#skF_12'),A_479)
      | k2_zfmisc_1(A_479,B_480) = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_5692,c_3941])).

tff(c_6955,plain,(
    ! [B_480] : k2_zfmisc_1('#skF_12',B_480) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_6838,c_3941])).

tff(c_3870,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3867,c_1003])).

tff(c_6992,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6955,c_3870])).

tff(c_6993,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_7005,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6995,c_6993])).

tff(c_1002,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_7030,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7005,c_6995,c_1002])).

tff(c_7031,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_1001])).

tff(c_7043,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7031,c_1002])).

tff(c_7049,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7031,c_6993])).

tff(c_7050,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7043,c_7049])).

tff(c_7052,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_7051,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_7067,plain,
    ( '#skF_15' = '#skF_12'
    | '#skF_15' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7052,c_7052,c_7051])).

tff(c_7068,plain,(
    '#skF_15' = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_7067])).

tff(c_7055,plain,(
    ! [A_9] : r1_xboole_0(A_9,'#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7052,c_10])).

tff(c_7070,plain,(
    ! [A_9] : r1_xboole_0(A_9,'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7068,c_7055])).

tff(c_7054,plain,(
    ! [A_6] : k4_xboole_0(A_6,'#skF_15') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7052,c_6])).

tff(c_7086,plain,(
    ! [A_6] : k4_xboole_0(A_6,'#skF_13') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7068,c_7054])).

tff(c_7100,plain,(
    ! [A_490,B_491] : k4_xboole_0(A_490,k4_xboole_0(A_490,B_491)) = k3_xboole_0(A_490,B_491) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7118,plain,(
    ! [A_492] : k4_xboole_0(A_492,A_492) = k3_xboole_0(A_492,'#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_7086,c_7100])).

tff(c_7128,plain,(
    k3_xboole_0('#skF_13','#skF_13') = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_7118,c_7086])).

tff(c_7143,plain,(
    ! [A_493,B_494,C_495] :
      ( ~ r1_xboole_0(A_493,B_494)
      | ~ r2_hidden(C_495,k3_xboole_0(A_493,B_494)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7146,plain,(
    ! [C_495] :
      ( ~ r1_xboole_0('#skF_13','#skF_13')
      | ~ r2_hidden(C_495,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7128,c_7143])).

tff(c_7148,plain,(
    ! [C_495] : ~ r2_hidden(C_495,'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7070,c_7146])).

tff(c_10101,plain,(
    ! [A_675,C_676] :
      ( r2_hidden('#skF_5'(A_675,'#skF_13',C_676),C_676)
      | k2_zfmisc_1(A_675,'#skF_13') = C_676 ) ),
    inference(resolution,[status(thm)],[c_8716,c_7148])).

tff(c_10218,plain,(
    ! [A_675] : k2_zfmisc_1(A_675,'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_10101,c_7148])).

tff(c_7072,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7068,c_7052])).

tff(c_56,plain,
    ( k2_zfmisc_1('#skF_12','#skF_13') != k1_xboole_0
    | k1_xboole_0 != '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_7097,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7072,c_7068,c_7072,c_56])).

tff(c_10244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10218,c_7097])).

tff(c_10245,plain,(
    '#skF_15' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_7067])).

tff(c_10248,plain,(
    ! [A_9] : r1_xboole_0(A_9,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10245,c_7055])).

tff(c_10265,plain,(
    ! [A_6] : k4_xboole_0(A_6,'#skF_12') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10245,c_7054])).

tff(c_10277,plain,(
    ! [A_679,B_680] : k4_xboole_0(A_679,k4_xboole_0(A_679,B_680)) = k3_xboole_0(A_679,B_680) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10295,plain,(
    ! [A_681] : k4_xboole_0(A_681,A_681) = k3_xboole_0(A_681,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_10265,c_10277])).

tff(c_10305,plain,(
    k3_xboole_0('#skF_12','#skF_12') = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_10295,c_10265])).

tff(c_10322,plain,(
    ! [A_682,B_683,C_684] :
      ( ~ r1_xboole_0(A_682,B_683)
      | ~ r2_hidden(C_684,k3_xboole_0(A_682,B_683)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10325,plain,(
    ! [C_684] :
      ( ~ r1_xboole_0('#skF_12','#skF_12')
      | ~ r2_hidden(C_684,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10305,c_10322])).

tff(c_10327,plain,(
    ! [C_684] : ~ r2_hidden(C_684,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10248,c_10325])).

tff(c_12896,plain,(
    ! [A_843,B_844] :
      ( r2_hidden('#skF_3'(A_843,B_844,'#skF_12'),A_843)
      | k2_zfmisc_1(A_843,B_844) = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_11808,c_10327])).

tff(c_13008,plain,(
    ! [B_844] : k2_zfmisc_1('#skF_12',B_844) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_12896,c_10327])).

tff(c_10250,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10245,c_7052])).

tff(c_10276,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10250,c_10245,c_10250,c_56])).

tff(c_13045,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13008,c_10276])).

tff(c_13047,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 != '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_13073,plain,
    ( '#skF_14' = '#skF_13'
    | '#skF_14' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13047,c_13047,c_13047,c_62])).

tff(c_13074,plain,(
    '#skF_14' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_13073])).

tff(c_13049,plain,(
    ! [A_9] : r1_xboole_0(A_9,'#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13047,c_10])).

tff(c_13079,plain,(
    ! [A_9] : r1_xboole_0(A_9,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13074,c_13049])).

tff(c_13048,plain,(
    ! [A_6] : k4_xboole_0(A_6,'#skF_14') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13047,c_6])).

tff(c_13075,plain,(
    ! [A_6] : k4_xboole_0(A_6,'#skF_12') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13074,c_13048])).

tff(c_13107,plain,(
    ! [A_855,B_856] : k4_xboole_0(A_855,k4_xboole_0(A_855,B_856)) = k3_xboole_0(A_855,B_856) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_13125,plain,(
    ! [A_857] : k4_xboole_0(A_857,A_857) = k3_xboole_0(A_857,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_13075,c_13107])).

tff(c_13135,plain,(
    k3_xboole_0('#skF_12','#skF_12') = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_13125,c_13075])).

tff(c_13148,plain,(
    ! [C_5] :
      ( ~ r1_xboole_0('#skF_12','#skF_12')
      | ~ r2_hidden(C_5,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13135,c_4])).

tff(c_13152,plain,(
    ! [C_5] : ~ r2_hidden(C_5,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13079,c_13148])).

tff(c_15930,plain,(
    ! [A_1025,C_1026] :
      ( r2_hidden('#skF_5'(A_1025,'#skF_12',C_1026),C_1026)
      | k2_zfmisc_1(A_1025,'#skF_12') = C_1026 ) ),
    inference(resolution,[status(thm)],[c_14792,c_13152])).

tff(c_16042,plain,(
    ! [A_1025] : k2_zfmisc_1(A_1025,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_15930,c_13152])).

tff(c_13807,plain,(
    ! [A_912,B_913,D_914] :
      ( r2_hidden('#skF_6'(A_912,B_913,k2_zfmisc_1(A_912,B_913),D_914),A_912)
      | ~ r2_hidden(D_914,k2_zfmisc_1(A_912,B_913)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_13844,plain,(
    ! [D_914,B_913] : ~ r2_hidden(D_914,k2_zfmisc_1('#skF_12',B_913)) ),
    inference(resolution,[status(thm)],[c_13807,c_13152])).

tff(c_16035,plain,(
    ! [A_1025,B_913] : k2_zfmisc_1(A_1025,'#skF_12') = k2_zfmisc_1('#skF_12',B_913) ),
    inference(resolution,[status(thm)],[c_15930,c_13844])).

tff(c_16185,plain,(
    ! [B_913] : k2_zfmisc_1('#skF_12',B_913) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16042,c_16035])).

tff(c_13046,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_13062,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13047,c_13046])).

tff(c_13076,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13074,c_13062])).

tff(c_16213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16185,c_13076])).

tff(c_16214,plain,(
    '#skF_14' = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_13073])).

tff(c_16220,plain,(
    ! [A_9] : r1_xboole_0(A_9,'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16214,c_13049])).

tff(c_16216,plain,(
    ! [A_6] : k4_xboole_0(A_6,'#skF_13') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16214,c_13048])).

tff(c_16251,plain,(
    ! [A_1033,B_1034] : k4_xboole_0(A_1033,k4_xboole_0(A_1033,B_1034)) = k3_xboole_0(A_1033,B_1034) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16269,plain,(
    ! [A_1035] : k4_xboole_0(A_1035,A_1035) = k3_xboole_0(A_1035,'#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_16216,c_16251])).

tff(c_16279,plain,(
    k3_xboole_0('#skF_13','#skF_13') = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_16269,c_16216])).

tff(c_16292,plain,(
    ! [C_5] :
      ( ~ r1_xboole_0('#skF_13','#skF_13')
      | ~ r2_hidden(C_5,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16279,c_4])).

tff(c_16296,plain,(
    ! [C_5] : ~ r2_hidden(C_5,'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16220,c_16292])).

tff(c_19074,plain,(
    ! [A_1203,C_1204] :
      ( r2_hidden('#skF_5'(A_1203,'#skF_13',C_1204),C_1204)
      | k2_zfmisc_1(A_1203,'#skF_13') = C_1204 ) ),
    inference(resolution,[status(thm)],[c_17936,c_16296])).

tff(c_19186,plain,(
    ! [A_1203] : k2_zfmisc_1(A_1203,'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_19074,c_16296])).

tff(c_16217,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16214,c_13062])).

tff(c_19212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19186,c_16217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:24:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.13/2.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.13/2.75  
% 8.13/2.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.13/2.75  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_15 > #skF_4 > #skF_14 > #skF_13 > #skF_5 > #skF_10 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_11 > #skF_3 > #skF_1 > #skF_9 > #skF_12
% 8.13/2.75  
% 8.13/2.75  %Foreground sorts:
% 8.13/2.75  
% 8.13/2.75  
% 8.13/2.75  %Background operators:
% 8.13/2.75  
% 8.13/2.75  
% 8.13/2.75  %Foreground operators:
% 8.13/2.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.13/2.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.13/2.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.13/2.75  tff('#skF_15', type, '#skF_15': $i).
% 8.13/2.75  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.13/2.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.13/2.75  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.13/2.75  tff('#skF_14', type, '#skF_14': $i).
% 8.13/2.75  tff('#skF_13', type, '#skF_13': $i).
% 8.13/2.75  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.13/2.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.13/2.75  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 8.13/2.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.13/2.75  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 8.13/2.75  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 8.13/2.75  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 8.13/2.75  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 8.13/2.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.13/2.75  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.13/2.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.13/2.75  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.13/2.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.13/2.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.13/2.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.13/2.75  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 8.13/2.75  tff('#skF_12', type, '#skF_12': $i).
% 8.13/2.75  
% 8.29/2.77  tff(f_57, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 8.29/2.77  tff(f_75, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.29/2.77  tff(f_67, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 8.29/2.77  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.29/2.77  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.29/2.77  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.29/2.77  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.29/2.77  tff(f_68, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 8.29/2.77  tff(c_17936, plain, (![A_1151, B_1152, C_1153]: (r2_hidden('#skF_4'(A_1151, B_1152, C_1153), B_1152) | r2_hidden('#skF_5'(A_1151, B_1152, C_1153), C_1153) | k2_zfmisc_1(A_1151, B_1152)=C_1153)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.29/2.77  tff(c_14792, plain, (![A_973, B_974, C_975]: (r2_hidden('#skF_4'(A_973, B_974, C_975), B_974) | r2_hidden('#skF_5'(A_973, B_974, C_975), C_975) | k2_zfmisc_1(A_973, B_974)=C_975)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.29/2.77  tff(c_11808, plain, (![A_794, B_795, C_796]: (r2_hidden('#skF_3'(A_794, B_795, C_796), A_794) | r2_hidden('#skF_5'(A_794, B_795, C_796), C_796) | k2_zfmisc_1(A_794, B_795)=C_796)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.29/2.77  tff(c_8716, plain, (![A_602, B_603, C_604]: (r2_hidden('#skF_4'(A_602, B_603, C_604), B_603) | r2_hidden('#skF_5'(A_602, B_603, C_604), C_604) | k2_zfmisc_1(A_602, B_603)=C_604)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.29/2.77  tff(c_58, plain, (k1_xboole_0='#skF_13' | k1_xboole_0='#skF_12' | k1_xboole_0!='#skF_15'), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.29/2.77  tff(c_82, plain, (k1_xboole_0!='#skF_15'), inference(splitLeft, [status(thm)], [c_58])).
% 8.29/2.77  tff(c_810, plain, (![A_124, B_125]: (r2_hidden('#skF_9'(A_124, B_125), A_124) | r2_hidden('#skF_10'(A_124, B_125), B_125) | k3_tarski(A_124)=B_125)), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.29/2.77  tff(c_60, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!=k1_xboole_0 | k1_xboole_0!='#skF_14'), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.29/2.77  tff(c_81, plain, (k1_xboole_0!='#skF_14'), inference(splitLeft, [status(thm)], [c_60])).
% 8.29/2.77  tff(c_519, plain, (![A_115, B_116]: (r2_hidden('#skF_9'(A_115, B_116), A_115) | r2_hidden('#skF_10'(A_115, B_116), B_116) | k3_tarski(A_115)=B_116)), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.29/2.77  tff(c_10, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.29/2.77  tff(c_6, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.29/2.77  tff(c_88, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k4_xboole_0(A_65, B_66))=k3_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.29/2.77  tff(c_106, plain, (![A_67]: (k4_xboole_0(A_67, A_67)=k3_xboole_0(A_67, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_88])).
% 8.29/2.77  tff(c_116, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_106, c_6])).
% 8.29/2.77  tff(c_132, plain, (![A_68, B_69, C_70]: (~r1_xboole_0(A_68, B_69) | ~r2_hidden(C_70, k3_xboole_0(A_68, B_69)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.29/2.77  tff(c_135, plain, (![C_70]: (~r1_xboole_0(k1_xboole_0, k1_xboole_0) | ~r2_hidden(C_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_116, c_132])).
% 8.29/2.77  tff(c_137, plain, (![C_70]: (~r2_hidden(C_70, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_135])).
% 8.29/2.77  tff(c_66, plain, (k1_xboole_0='#skF_13' | k1_xboole_0='#skF_12' | k2_zfmisc_1('#skF_14', '#skF_15')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.29/2.77  tff(c_83, plain, (k2_zfmisc_1('#skF_14', '#skF_15')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_66])).
% 8.29/2.77  tff(c_291, plain, (![E_94, F_95, A_96, B_97]: (r2_hidden(k4_tarski(E_94, F_95), k2_zfmisc_1(A_96, B_97)) | ~r2_hidden(F_95, B_97) | ~r2_hidden(E_94, A_96))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.29/2.77  tff(c_296, plain, (![E_94, F_95]: (r2_hidden(k4_tarski(E_94, F_95), k1_xboole_0) | ~r2_hidden(F_95, '#skF_15') | ~r2_hidden(E_94, '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_83, c_291])).
% 8.29/2.77  tff(c_298, plain, (![F_95, E_94]: (~r2_hidden(F_95, '#skF_15') | ~r2_hidden(E_94, '#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_137, c_296])).
% 8.29/2.77  tff(c_299, plain, (![E_94]: (~r2_hidden(E_94, '#skF_14'))), inference(splitLeft, [status(thm)], [c_298])).
% 8.29/2.77  tff(c_670, plain, (![A_117]: (r2_hidden('#skF_9'(A_117, '#skF_14'), A_117) | k3_tarski(A_117)='#skF_14')), inference(resolution, [status(thm)], [c_519, c_299])).
% 8.29/2.77  tff(c_747, plain, (k3_tarski(k1_xboole_0)='#skF_14'), inference(resolution, [status(thm)], [c_670, c_137])).
% 8.29/2.77  tff(c_54, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.29/2.77  tff(c_770, plain, (k1_xboole_0='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_747, c_54])).
% 8.29/2.77  tff(c_772, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_770])).
% 8.29/2.77  tff(c_773, plain, (![F_95]: (~r2_hidden(F_95, '#skF_15'))), inference(splitRight, [status(thm)], [c_298])).
% 8.29/2.77  tff(c_921, plain, (![A_126]: (r2_hidden('#skF_9'(A_126, '#skF_15'), A_126) | k3_tarski(A_126)='#skF_15')), inference(resolution, [status(thm)], [c_810, c_773])).
% 8.29/2.77  tff(c_978, plain, (k3_tarski(k1_xboole_0)='#skF_15'), inference(resolution, [status(thm)], [c_921, c_137])).
% 8.29/2.77  tff(c_998, plain, (k1_xboole_0='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_978, c_54])).
% 8.29/2.77  tff(c_1000, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_998])).
% 8.29/2.77  tff(c_1001, plain, (k1_xboole_0='#skF_12' | k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_66])).
% 8.29/2.77  tff(c_6995, plain, (k1_xboole_0='#skF_13'), inference(splitLeft, [status(thm)], [c_1001])).
% 8.29/2.77  tff(c_5692, plain, (![A_430, B_431, C_432]: (r2_hidden('#skF_3'(A_430, B_431, C_432), A_430) | r2_hidden('#skF_5'(A_430, B_431, C_432), C_432) | k2_zfmisc_1(A_430, B_431)=C_432)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.29/2.77  tff(c_2919, plain, (![A_268, B_269, C_270]: (r2_hidden('#skF_4'(A_268, B_269, C_270), B_269) | r2_hidden('#skF_5'(A_268, B_269, C_270), C_270) | k2_zfmisc_1(A_268, B_269)=C_270)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.29/2.77  tff(c_1004, plain, (k1_xboole_0='#skF_13'), inference(splitLeft, [status(thm)], [c_1001])).
% 8.29/2.77  tff(c_1009, plain, (![A_9]: (r1_xboole_0(A_9, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_10])).
% 8.29/2.77  tff(c_1008, plain, (![A_6]: (k4_xboole_0(A_6, '#skF_13')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_6])).
% 8.29/2.77  tff(c_1031, plain, (![A_132, B_133]: (k4_xboole_0(A_132, k4_xboole_0(A_132, B_133))=k3_xboole_0(A_132, B_133))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.29/2.77  tff(c_1049, plain, (![A_134]: (k4_xboole_0(A_134, A_134)=k3_xboole_0(A_134, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_1008, c_1031])).
% 8.29/2.77  tff(c_1059, plain, (k3_xboole_0('#skF_13', '#skF_13')='#skF_13'), inference(superposition, [status(thm), theory('equality')], [c_1049, c_1008])).
% 8.29/2.77  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.29/2.77  tff(c_1072, plain, (![C_5]: (~r1_xboole_0('#skF_13', '#skF_13') | ~r2_hidden(C_5, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_1059, c_4])).
% 8.29/2.77  tff(c_1076, plain, (![C_5]: (~r2_hidden(C_5, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_1009, c_1072])).
% 8.29/2.77  tff(c_3716, plain, (![A_297, C_298]: (r2_hidden('#skF_5'(A_297, '#skF_13', C_298), C_298) | k2_zfmisc_1(A_297, '#skF_13')=C_298)), inference(resolution, [status(thm)], [c_2919, c_1076])).
% 8.29/2.77  tff(c_3828, plain, (![A_297]: (k2_zfmisc_1(A_297, '#skF_13')='#skF_13')), inference(resolution, [status(thm)], [c_3716, c_1076])).
% 8.29/2.77  tff(c_64, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!=k1_xboole_0 | k2_zfmisc_1('#skF_14', '#skF_15')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.29/2.77  tff(c_1003, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_64])).
% 8.29/2.77  tff(c_1005, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_1003])).
% 8.29/2.77  tff(c_3866, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3828, c_1005])).
% 8.29/2.77  tff(c_3867, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_1001])).
% 8.29/2.77  tff(c_3874, plain, (![A_9]: (r1_xboole_0(A_9, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_3867, c_10])).
% 8.29/2.77  tff(c_3873, plain, (![A_6]: (k4_xboole_0(A_6, '#skF_12')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_3867, c_6])).
% 8.29/2.77  tff(c_3895, plain, (![A_304, B_305]: (k4_xboole_0(A_304, k4_xboole_0(A_304, B_305))=k3_xboole_0(A_304, B_305))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.29/2.77  tff(c_3913, plain, (![A_306]: (k4_xboole_0(A_306, A_306)=k3_xboole_0(A_306, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_3873, c_3895])).
% 8.29/2.77  tff(c_3923, plain, (k3_xboole_0('#skF_12', '#skF_12')='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_3913, c_3873])).
% 8.29/2.77  tff(c_3937, plain, (![C_5]: (~r1_xboole_0('#skF_12', '#skF_12') | ~r2_hidden(C_5, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_3923, c_4])).
% 8.29/2.77  tff(c_3941, plain, (![C_5]: (~r2_hidden(C_5, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_3874, c_3937])).
% 8.29/2.77  tff(c_6838, plain, (![A_479, B_480]: (r2_hidden('#skF_3'(A_479, B_480, '#skF_12'), A_479) | k2_zfmisc_1(A_479, B_480)='#skF_12')), inference(resolution, [status(thm)], [c_5692, c_3941])).
% 8.29/2.77  tff(c_6955, plain, (![B_480]: (k2_zfmisc_1('#skF_12', B_480)='#skF_12')), inference(resolution, [status(thm)], [c_6838, c_3941])).
% 8.29/2.77  tff(c_3870, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3867, c_1003])).
% 8.29/2.77  tff(c_6992, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6955, c_3870])).
% 8.29/2.77  tff(c_6993, plain, (k2_zfmisc_1('#skF_14', '#skF_15')=k1_xboole_0), inference(splitRight, [status(thm)], [c_64])).
% 8.29/2.77  tff(c_7005, plain, (k2_zfmisc_1('#skF_14', '#skF_15')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_6995, c_6993])).
% 8.29/2.77  tff(c_1002, plain, (k2_zfmisc_1('#skF_14', '#skF_15')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_66])).
% 8.29/2.77  tff(c_7030, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7005, c_6995, c_1002])).
% 8.29/2.77  tff(c_7031, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_1001])).
% 8.29/2.77  tff(c_7043, plain, (k2_zfmisc_1('#skF_14', '#skF_15')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_7031, c_1002])).
% 8.29/2.77  tff(c_7049, plain, (k2_zfmisc_1('#skF_14', '#skF_15')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_7031, c_6993])).
% 8.29/2.77  tff(c_7050, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7043, c_7049])).
% 8.29/2.77  tff(c_7052, plain, (k1_xboole_0='#skF_15'), inference(splitRight, [status(thm)], [c_58])).
% 8.29/2.77  tff(c_7051, plain, (k1_xboole_0='#skF_12' | k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_58])).
% 8.29/2.77  tff(c_7067, plain, ('#skF_15'='#skF_12' | '#skF_15'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_7052, c_7052, c_7051])).
% 8.29/2.77  tff(c_7068, plain, ('#skF_15'='#skF_13'), inference(splitLeft, [status(thm)], [c_7067])).
% 8.29/2.77  tff(c_7055, plain, (![A_9]: (r1_xboole_0(A_9, '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_7052, c_10])).
% 8.29/2.77  tff(c_7070, plain, (![A_9]: (r1_xboole_0(A_9, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_7068, c_7055])).
% 8.29/2.77  tff(c_7054, plain, (![A_6]: (k4_xboole_0(A_6, '#skF_15')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_7052, c_6])).
% 8.29/2.77  tff(c_7086, plain, (![A_6]: (k4_xboole_0(A_6, '#skF_13')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_7068, c_7054])).
% 8.29/2.77  tff(c_7100, plain, (![A_490, B_491]: (k4_xboole_0(A_490, k4_xboole_0(A_490, B_491))=k3_xboole_0(A_490, B_491))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.29/2.77  tff(c_7118, plain, (![A_492]: (k4_xboole_0(A_492, A_492)=k3_xboole_0(A_492, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_7086, c_7100])).
% 8.29/2.77  tff(c_7128, plain, (k3_xboole_0('#skF_13', '#skF_13')='#skF_13'), inference(superposition, [status(thm), theory('equality')], [c_7118, c_7086])).
% 8.29/2.77  tff(c_7143, plain, (![A_493, B_494, C_495]: (~r1_xboole_0(A_493, B_494) | ~r2_hidden(C_495, k3_xboole_0(A_493, B_494)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.29/2.77  tff(c_7146, plain, (![C_495]: (~r1_xboole_0('#skF_13', '#skF_13') | ~r2_hidden(C_495, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_7128, c_7143])).
% 8.29/2.77  tff(c_7148, plain, (![C_495]: (~r2_hidden(C_495, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_7070, c_7146])).
% 8.29/2.77  tff(c_10101, plain, (![A_675, C_676]: (r2_hidden('#skF_5'(A_675, '#skF_13', C_676), C_676) | k2_zfmisc_1(A_675, '#skF_13')=C_676)), inference(resolution, [status(thm)], [c_8716, c_7148])).
% 8.29/2.77  tff(c_10218, plain, (![A_675]: (k2_zfmisc_1(A_675, '#skF_13')='#skF_13')), inference(resolution, [status(thm)], [c_10101, c_7148])).
% 8.29/2.77  tff(c_7072, plain, (k1_xboole_0='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_7068, c_7052])).
% 8.29/2.77  tff(c_56, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!=k1_xboole_0 | k1_xboole_0!='#skF_15'), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.29/2.77  tff(c_7097, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_7072, c_7068, c_7072, c_56])).
% 8.29/2.77  tff(c_10244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10218, c_7097])).
% 8.29/2.77  tff(c_10245, plain, ('#skF_15'='#skF_12'), inference(splitRight, [status(thm)], [c_7067])).
% 8.29/2.77  tff(c_10248, plain, (![A_9]: (r1_xboole_0(A_9, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_10245, c_7055])).
% 8.29/2.77  tff(c_10265, plain, (![A_6]: (k4_xboole_0(A_6, '#skF_12')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_10245, c_7054])).
% 8.29/2.77  tff(c_10277, plain, (![A_679, B_680]: (k4_xboole_0(A_679, k4_xboole_0(A_679, B_680))=k3_xboole_0(A_679, B_680))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.29/2.77  tff(c_10295, plain, (![A_681]: (k4_xboole_0(A_681, A_681)=k3_xboole_0(A_681, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_10265, c_10277])).
% 8.29/2.77  tff(c_10305, plain, (k3_xboole_0('#skF_12', '#skF_12')='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_10295, c_10265])).
% 8.29/2.77  tff(c_10322, plain, (![A_682, B_683, C_684]: (~r1_xboole_0(A_682, B_683) | ~r2_hidden(C_684, k3_xboole_0(A_682, B_683)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.29/2.77  tff(c_10325, plain, (![C_684]: (~r1_xboole_0('#skF_12', '#skF_12') | ~r2_hidden(C_684, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_10305, c_10322])).
% 8.29/2.77  tff(c_10327, plain, (![C_684]: (~r2_hidden(C_684, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_10248, c_10325])).
% 8.29/2.77  tff(c_12896, plain, (![A_843, B_844]: (r2_hidden('#skF_3'(A_843, B_844, '#skF_12'), A_843) | k2_zfmisc_1(A_843, B_844)='#skF_12')), inference(resolution, [status(thm)], [c_11808, c_10327])).
% 8.29/2.77  tff(c_13008, plain, (![B_844]: (k2_zfmisc_1('#skF_12', B_844)='#skF_12')), inference(resolution, [status(thm)], [c_12896, c_10327])).
% 8.29/2.77  tff(c_10250, plain, (k1_xboole_0='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_10245, c_7052])).
% 8.29/2.77  tff(c_10276, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_10250, c_10245, c_10250, c_56])).
% 8.29/2.77  tff(c_13045, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13008, c_10276])).
% 8.29/2.77  tff(c_13047, plain, (k1_xboole_0='#skF_14'), inference(splitRight, [status(thm)], [c_60])).
% 8.29/2.77  tff(c_62, plain, (k1_xboole_0='#skF_13' | k1_xboole_0='#skF_12' | k1_xboole_0!='#skF_14'), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.29/2.77  tff(c_13073, plain, ('#skF_14'='#skF_13' | '#skF_14'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_13047, c_13047, c_13047, c_62])).
% 8.29/2.77  tff(c_13074, plain, ('#skF_14'='#skF_12'), inference(splitLeft, [status(thm)], [c_13073])).
% 8.29/2.77  tff(c_13049, plain, (![A_9]: (r1_xboole_0(A_9, '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_13047, c_10])).
% 8.29/2.77  tff(c_13079, plain, (![A_9]: (r1_xboole_0(A_9, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_13074, c_13049])).
% 8.29/2.77  tff(c_13048, plain, (![A_6]: (k4_xboole_0(A_6, '#skF_14')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_13047, c_6])).
% 8.29/2.77  tff(c_13075, plain, (![A_6]: (k4_xboole_0(A_6, '#skF_12')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_13074, c_13048])).
% 8.29/2.77  tff(c_13107, plain, (![A_855, B_856]: (k4_xboole_0(A_855, k4_xboole_0(A_855, B_856))=k3_xboole_0(A_855, B_856))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.29/2.77  tff(c_13125, plain, (![A_857]: (k4_xboole_0(A_857, A_857)=k3_xboole_0(A_857, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_13075, c_13107])).
% 8.29/2.77  tff(c_13135, plain, (k3_xboole_0('#skF_12', '#skF_12')='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_13125, c_13075])).
% 8.29/2.77  tff(c_13148, plain, (![C_5]: (~r1_xboole_0('#skF_12', '#skF_12') | ~r2_hidden(C_5, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_13135, c_4])).
% 8.29/2.77  tff(c_13152, plain, (![C_5]: (~r2_hidden(C_5, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_13079, c_13148])).
% 8.29/2.77  tff(c_15930, plain, (![A_1025, C_1026]: (r2_hidden('#skF_5'(A_1025, '#skF_12', C_1026), C_1026) | k2_zfmisc_1(A_1025, '#skF_12')=C_1026)), inference(resolution, [status(thm)], [c_14792, c_13152])).
% 8.29/2.77  tff(c_16042, plain, (![A_1025]: (k2_zfmisc_1(A_1025, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_15930, c_13152])).
% 8.29/2.77  tff(c_13807, plain, (![A_912, B_913, D_914]: (r2_hidden('#skF_6'(A_912, B_913, k2_zfmisc_1(A_912, B_913), D_914), A_912) | ~r2_hidden(D_914, k2_zfmisc_1(A_912, B_913)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.29/2.77  tff(c_13844, plain, (![D_914, B_913]: (~r2_hidden(D_914, k2_zfmisc_1('#skF_12', B_913)))), inference(resolution, [status(thm)], [c_13807, c_13152])).
% 8.29/2.77  tff(c_16035, plain, (![A_1025, B_913]: (k2_zfmisc_1(A_1025, '#skF_12')=k2_zfmisc_1('#skF_12', B_913))), inference(resolution, [status(thm)], [c_15930, c_13844])).
% 8.29/2.77  tff(c_16185, plain, (![B_913]: (k2_zfmisc_1('#skF_12', B_913)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_16042, c_16035])).
% 8.29/2.77  tff(c_13046, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 8.29/2.77  tff(c_13062, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_13047, c_13046])).
% 8.29/2.77  tff(c_13076, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_13074, c_13062])).
% 8.29/2.77  tff(c_16213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16185, c_13076])).
% 8.29/2.77  tff(c_16214, plain, ('#skF_14'='#skF_13'), inference(splitRight, [status(thm)], [c_13073])).
% 8.29/2.77  tff(c_16220, plain, (![A_9]: (r1_xboole_0(A_9, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_16214, c_13049])).
% 8.29/2.77  tff(c_16216, plain, (![A_6]: (k4_xboole_0(A_6, '#skF_13')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_16214, c_13048])).
% 8.29/2.77  tff(c_16251, plain, (![A_1033, B_1034]: (k4_xboole_0(A_1033, k4_xboole_0(A_1033, B_1034))=k3_xboole_0(A_1033, B_1034))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.29/2.77  tff(c_16269, plain, (![A_1035]: (k4_xboole_0(A_1035, A_1035)=k3_xboole_0(A_1035, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_16216, c_16251])).
% 8.29/2.77  tff(c_16279, plain, (k3_xboole_0('#skF_13', '#skF_13')='#skF_13'), inference(superposition, [status(thm), theory('equality')], [c_16269, c_16216])).
% 8.29/2.77  tff(c_16292, plain, (![C_5]: (~r1_xboole_0('#skF_13', '#skF_13') | ~r2_hidden(C_5, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_16279, c_4])).
% 8.29/2.77  tff(c_16296, plain, (![C_5]: (~r2_hidden(C_5, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_16220, c_16292])).
% 8.29/2.77  tff(c_19074, plain, (![A_1203, C_1204]: (r2_hidden('#skF_5'(A_1203, '#skF_13', C_1204), C_1204) | k2_zfmisc_1(A_1203, '#skF_13')=C_1204)), inference(resolution, [status(thm)], [c_17936, c_16296])).
% 8.29/2.77  tff(c_19186, plain, (![A_1203]: (k2_zfmisc_1(A_1203, '#skF_13')='#skF_13')), inference(resolution, [status(thm)], [c_19074, c_16296])).
% 8.29/2.77  tff(c_16217, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_16214, c_13062])).
% 8.29/2.77  tff(c_19212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19186, c_16217])).
% 8.29/2.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.29/2.77  
% 8.29/2.77  Inference rules
% 8.29/2.77  ----------------------
% 8.29/2.77  #Ref     : 0
% 8.29/2.77  #Sup     : 4177
% 8.29/2.77  #Fact    : 0
% 8.29/2.77  #Define  : 0
% 8.29/2.77  #Split   : 10
% 8.29/2.77  #Chain   : 0
% 8.29/2.77  #Close   : 0
% 8.29/2.77  
% 8.29/2.77  Ordering : KBO
% 8.29/2.77  
% 8.29/2.77  Simplification rules
% 8.29/2.77  ----------------------
% 8.29/2.77  #Subsume      : 875
% 8.29/2.77  #Demod        : 1304
% 8.29/2.77  #Tautology    : 1615
% 8.29/2.77  #SimpNegUnit  : 185
% 8.29/2.77  #BackRed      : 173
% 8.29/2.77  
% 8.29/2.77  #Partial instantiations: 0
% 8.29/2.77  #Strategies tried      : 1
% 8.29/2.77  
% 8.29/2.77  Timing (in seconds)
% 8.29/2.77  ----------------------
% 8.29/2.78  Preprocessing        : 0.32
% 8.29/2.78  Parsing              : 0.16
% 8.29/2.78  CNF conversion       : 0.03
% 8.29/2.78  Main loop            : 1.67
% 8.29/2.78  Inferencing          : 0.64
% 8.29/2.78  Reduction            : 0.50
% 8.29/2.78  Demodulation         : 0.32
% 8.29/2.78  BG Simplification    : 0.07
% 8.29/2.78  Subsumption          : 0.30
% 8.29/2.78  Abstraction          : 0.10
% 8.29/2.78  MUC search           : 0.00
% 8.29/2.78  Cooper               : 0.00
% 8.29/2.78  Total                : 2.04
% 8.29/2.78  Index Insertion      : 0.00
% 8.29/2.78  Index Deletion       : 0.00
% 8.29/2.78  Index Matching       : 0.00
% 8.29/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
