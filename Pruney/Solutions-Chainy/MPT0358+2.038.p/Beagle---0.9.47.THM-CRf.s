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
% DateTime   : Thu Dec  3 09:56:05 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 185 expanded)
%              Number of leaves         :   31 (  74 expanded)
%              Depth                    :   11
%              Number of atoms          :  139 ( 343 expanded)
%              Number of equality atoms :   43 (  97 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_86,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_75,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [A_23] : ~ v1_xboole_0(k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    ! [C_15,A_11] :
      ( r2_hidden(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_183,plain,(
    ! [B_55,A_56] :
      ( m1_subset_1(B_55,A_56)
      | ~ r2_hidden(B_55,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_186,plain,(
    ! [C_15,A_11] :
      ( m1_subset_1(C_15,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(resolution,[status(thm)],[c_22,c_183])).

tff(c_189,plain,(
    ! [C_15,A_11] :
      ( m1_subset_1(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_186])).

tff(c_40,plain,(
    ! [A_18] : k1_subset_1(A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_58,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_59,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_58])).

tff(c_77,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_112,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(A_38,B_39) = '#skF_4'
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_10])).

tff(c_116,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_112])).

tff(c_208,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = k3_subset_1(A_61,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_338,plain,(
    ! [A_74,C_75] :
      ( k4_xboole_0(A_74,C_75) = k3_subset_1(A_74,C_75)
      | ~ r1_tarski(C_75,A_74) ) ),
    inference(resolution,[status(thm)],[c_189,c_208])).

tff(c_350,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k3_subset_1(B_2,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_338])).

tff(c_371,plain,(
    ! [B_78] : k3_subset_1(B_78,B_78) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_350])).

tff(c_259,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1(k3_subset_1(A_65,B_66),k1_zfmisc_1(A_65))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_196,plain,(
    ! [B_59,A_60] :
      ( r2_hidden(B_59,A_60)
      | ~ m1_subset_1(B_59,A_60)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    ! [C_15,A_11] :
      ( r1_tarski(C_15,A_11)
      | ~ r2_hidden(C_15,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_203,plain,(
    ! [B_59,A_11] :
      ( r1_tarski(B_59,A_11)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_196,c_20])).

tff(c_207,plain,(
    ! [B_59,A_11] :
      ( r1_tarski(B_59,A_11)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_11)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_203])).

tff(c_269,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(k3_subset_1(A_65,B_66),A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(resolution,[status(thm)],[c_259,c_207])).

tff(c_396,plain,(
    ! [B_79] :
      ( r1_tarski('#skF_4',B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(B_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_269])).

tff(c_400,plain,(
    ! [A_11] :
      ( r1_tarski('#skF_4',A_11)
      | ~ r1_tarski(A_11,A_11) ) ),
    inference(resolution,[status(thm)],[c_189,c_396])).

tff(c_407,plain,(
    ! [A_11] : r1_tarski('#skF_4',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_400])).

tff(c_52,plain,
    ( k1_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_60,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52])).

tff(c_93,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_60])).

tff(c_438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_93])).

tff(c_440,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_439,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_449,plain,(
    ! [A_86,B_87] :
      ( k4_xboole_0(A_86,B_87) = k1_xboole_0
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_456,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_439,c_449])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_687,plain,(
    ! [A_122,B_123] :
      ( k3_subset_1(A_122,k3_subset_1(A_122,B_123)) = B_123
      | ~ m1_subset_1(B_123,k1_zfmisc_1(A_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_700,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_687])).

tff(c_641,plain,(
    ! [A_117,B_118] :
      ( m1_subset_1(k3_subset_1(A_117,B_118),k1_zfmisc_1(A_117))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_508,plain,(
    ! [B_102,A_103] :
      ( r2_hidden(B_102,A_103)
      | ~ m1_subset_1(B_102,A_103)
      | v1_xboole_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_515,plain,(
    ! [B_102,A_11] :
      ( r1_tarski(B_102,A_11)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_508,c_20])).

tff(c_519,plain,(
    ! [B_102,A_11] :
      ( r1_tarski(B_102,A_11)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_11)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_515])).

tff(c_1115,plain,(
    ! [A_151,B_152] :
      ( r1_tarski(k3_subset_1(A_151,B_152),A_151)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(A_151)) ) ),
    inference(resolution,[status(thm)],[c_641,c_519])).

tff(c_1369,plain,(
    ! [A_164,B_165] :
      ( k4_xboole_0(k3_subset_1(A_164,B_165),A_164) = k1_xboole_0
      | ~ m1_subset_1(B_165,k1_zfmisc_1(A_164)) ) ),
    inference(resolution,[status(thm)],[c_1115,c_10])).

tff(c_1390,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_1369])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_484,plain,(
    ! [B_95,A_96] :
      ( m1_subset_1(B_95,A_96)
      | ~ r2_hidden(B_95,A_96)
      | v1_xboole_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_487,plain,(
    ! [C_15,A_11] :
      ( m1_subset_1(C_15,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(resolution,[status(thm)],[c_22,c_484])).

tff(c_490,plain,(
    ! [C_15,A_11] :
      ( m1_subset_1(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_487])).

tff(c_650,plain,(
    ! [A_119,B_120] :
      ( k4_xboole_0(A_119,B_120) = k3_subset_1(A_119,B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_709,plain,(
    ! [A_124,C_125] :
      ( k4_xboole_0(A_124,C_125) = k3_subset_1(A_124,C_125)
      | ~ r1_tarski(C_125,A_124) ) ),
    inference(resolution,[status(thm)],[c_490,c_650])).

tff(c_724,plain,(
    ! [B_4,A_3] :
      ( k4_xboole_0(B_4,A_3) = k3_subset_1(B_4,A_3)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_709])).

tff(c_1393,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1390,c_724])).

tff(c_1408,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_700,c_1393])).

tff(c_496,plain,(
    ! [A_99,C_100,B_101] :
      ( r1_xboole_0(A_99,k4_xboole_0(C_100,B_101))
      | ~ r1_tarski(A_99,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [A_7] :
      ( ~ r1_xboole_0(A_7,A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_603,plain,(
    ! [C_113,B_114] :
      ( k4_xboole_0(C_113,B_114) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(C_113,B_114),B_114) ) ),
    inference(resolution,[status(thm)],[c_496,c_16])).

tff(c_618,plain,(
    ! [C_113,B_4] :
      ( k4_xboole_0(C_113,B_4) = k1_xboole_0
      | k4_xboole_0(k4_xboole_0(C_113,B_4),B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_603])).

tff(c_1422,plain,
    ( k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k1_xboole_0
    | k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1408,c_618])).

tff(c_1435,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_1408,c_1422])).

tff(c_1437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_440,c_1435])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.50  
% 3.14/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.50  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.14/1.50  
% 3.14/1.50  %Foreground sorts:
% 3.14/1.50  
% 3.14/1.50  
% 3.14/1.50  %Background operators:
% 3.14/1.50  
% 3.14/1.50  
% 3.14/1.50  %Foreground operators:
% 3.14/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.14/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.14/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.50  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.14/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.14/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.14/1.50  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.14/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.14/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.14/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.50  
% 3.14/1.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.14/1.52  tff(f_86, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.14/1.52  tff(f_60, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.14/1.52  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.14/1.52  tff(f_75, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 3.14/1.52  tff(f_97, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 3.14/1.52  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.14/1.52  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.14/1.52  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.14/1.52  tff(f_90, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.14/1.52  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.14/1.52  tff(f_49, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.14/1.52  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.14/1.52  tff(c_46, plain, (![A_23]: (~v1_xboole_0(k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.14/1.52  tff(c_22, plain, (![C_15, A_11]: (r2_hidden(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.14/1.52  tff(c_183, plain, (![B_55, A_56]: (m1_subset_1(B_55, A_56) | ~r2_hidden(B_55, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.14/1.52  tff(c_186, plain, (![C_15, A_11]: (m1_subset_1(C_15, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(resolution, [status(thm)], [c_22, c_183])).
% 3.14/1.52  tff(c_189, plain, (![C_15, A_11]: (m1_subset_1(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(negUnitSimplification, [status(thm)], [c_46, c_186])).
% 3.14/1.52  tff(c_40, plain, (![A_18]: (k1_subset_1(A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.14/1.52  tff(c_58, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.14/1.52  tff(c_59, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_58])).
% 3.14/1.52  tff(c_77, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_59])).
% 3.14/1.52  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.14/1.52  tff(c_112, plain, (![A_38, B_39]: (k4_xboole_0(A_38, B_39)='#skF_4' | ~r1_tarski(A_38, B_39))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_10])).
% 3.14/1.52  tff(c_116, plain, (![B_2]: (k4_xboole_0(B_2, B_2)='#skF_4')), inference(resolution, [status(thm)], [c_6, c_112])).
% 3.14/1.52  tff(c_208, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=k3_subset_1(A_61, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.14/1.52  tff(c_338, plain, (![A_74, C_75]: (k4_xboole_0(A_74, C_75)=k3_subset_1(A_74, C_75) | ~r1_tarski(C_75, A_74))), inference(resolution, [status(thm)], [c_189, c_208])).
% 3.14/1.52  tff(c_350, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k3_subset_1(B_2, B_2))), inference(resolution, [status(thm)], [c_6, c_338])).
% 3.14/1.52  tff(c_371, plain, (![B_78]: (k3_subset_1(B_78, B_78)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_350])).
% 3.14/1.52  tff(c_259, plain, (![A_65, B_66]: (m1_subset_1(k3_subset_1(A_65, B_66), k1_zfmisc_1(A_65)) | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.14/1.52  tff(c_196, plain, (![B_59, A_60]: (r2_hidden(B_59, A_60) | ~m1_subset_1(B_59, A_60) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.14/1.52  tff(c_20, plain, (![C_15, A_11]: (r1_tarski(C_15, A_11) | ~r2_hidden(C_15, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.14/1.52  tff(c_203, plain, (![B_59, A_11]: (r1_tarski(B_59, A_11) | ~m1_subset_1(B_59, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_196, c_20])).
% 3.14/1.52  tff(c_207, plain, (![B_59, A_11]: (r1_tarski(B_59, A_11) | ~m1_subset_1(B_59, k1_zfmisc_1(A_11)))), inference(negUnitSimplification, [status(thm)], [c_46, c_203])).
% 3.14/1.52  tff(c_269, plain, (![A_65, B_66]: (r1_tarski(k3_subset_1(A_65, B_66), A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(resolution, [status(thm)], [c_259, c_207])).
% 3.14/1.52  tff(c_396, plain, (![B_79]: (r1_tarski('#skF_4', B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(B_79)))), inference(superposition, [status(thm), theory('equality')], [c_371, c_269])).
% 3.14/1.52  tff(c_400, plain, (![A_11]: (r1_tarski('#skF_4', A_11) | ~r1_tarski(A_11, A_11))), inference(resolution, [status(thm)], [c_189, c_396])).
% 3.14/1.52  tff(c_407, plain, (![A_11]: (r1_tarski('#skF_4', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_400])).
% 3.14/1.52  tff(c_52, plain, (k1_subset_1('#skF_3')!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.14/1.52  tff(c_60, plain, (k1_xboole_0!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52])).
% 3.14/1.52  tff(c_93, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_60])).
% 3.14/1.52  tff(c_438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_407, c_93])).
% 3.14/1.52  tff(c_440, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_59])).
% 3.14/1.52  tff(c_439, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_59])).
% 3.14/1.52  tff(c_449, plain, (![A_86, B_87]: (k4_xboole_0(A_86, B_87)=k1_xboole_0 | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.14/1.52  tff(c_456, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_439, c_449])).
% 3.14/1.52  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.14/1.52  tff(c_687, plain, (![A_122, B_123]: (k3_subset_1(A_122, k3_subset_1(A_122, B_123))=B_123 | ~m1_subset_1(B_123, k1_zfmisc_1(A_122)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.14/1.52  tff(c_700, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_50, c_687])).
% 3.14/1.52  tff(c_641, plain, (![A_117, B_118]: (m1_subset_1(k3_subset_1(A_117, B_118), k1_zfmisc_1(A_117)) | ~m1_subset_1(B_118, k1_zfmisc_1(A_117)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.14/1.52  tff(c_508, plain, (![B_102, A_103]: (r2_hidden(B_102, A_103) | ~m1_subset_1(B_102, A_103) | v1_xboole_0(A_103))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.14/1.52  tff(c_515, plain, (![B_102, A_11]: (r1_tarski(B_102, A_11) | ~m1_subset_1(B_102, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_508, c_20])).
% 3.14/1.52  tff(c_519, plain, (![B_102, A_11]: (r1_tarski(B_102, A_11) | ~m1_subset_1(B_102, k1_zfmisc_1(A_11)))), inference(negUnitSimplification, [status(thm)], [c_46, c_515])).
% 3.14/1.52  tff(c_1115, plain, (![A_151, B_152]: (r1_tarski(k3_subset_1(A_151, B_152), A_151) | ~m1_subset_1(B_152, k1_zfmisc_1(A_151)))), inference(resolution, [status(thm)], [c_641, c_519])).
% 3.14/1.52  tff(c_1369, plain, (![A_164, B_165]: (k4_xboole_0(k3_subset_1(A_164, B_165), A_164)=k1_xboole_0 | ~m1_subset_1(B_165, k1_zfmisc_1(A_164)))), inference(resolution, [status(thm)], [c_1115, c_10])).
% 3.14/1.52  tff(c_1390, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_1369])).
% 3.14/1.52  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.14/1.52  tff(c_484, plain, (![B_95, A_96]: (m1_subset_1(B_95, A_96) | ~r2_hidden(B_95, A_96) | v1_xboole_0(A_96))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.14/1.52  tff(c_487, plain, (![C_15, A_11]: (m1_subset_1(C_15, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(resolution, [status(thm)], [c_22, c_484])).
% 3.14/1.52  tff(c_490, plain, (![C_15, A_11]: (m1_subset_1(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(negUnitSimplification, [status(thm)], [c_46, c_487])).
% 3.14/1.52  tff(c_650, plain, (![A_119, B_120]: (k4_xboole_0(A_119, B_120)=k3_subset_1(A_119, B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(A_119)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.14/1.52  tff(c_709, plain, (![A_124, C_125]: (k4_xboole_0(A_124, C_125)=k3_subset_1(A_124, C_125) | ~r1_tarski(C_125, A_124))), inference(resolution, [status(thm)], [c_490, c_650])).
% 3.14/1.52  tff(c_724, plain, (![B_4, A_3]: (k4_xboole_0(B_4, A_3)=k3_subset_1(B_4, A_3) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_709])).
% 3.14/1.52  tff(c_1393, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1390, c_724])).
% 3.14/1.52  tff(c_1408, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_700, c_1393])).
% 3.14/1.52  tff(c_496, plain, (![A_99, C_100, B_101]: (r1_xboole_0(A_99, k4_xboole_0(C_100, B_101)) | ~r1_tarski(A_99, B_101))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.14/1.52  tff(c_16, plain, (![A_7]: (~r1_xboole_0(A_7, A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.14/1.52  tff(c_603, plain, (![C_113, B_114]: (k4_xboole_0(C_113, B_114)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(C_113, B_114), B_114))), inference(resolution, [status(thm)], [c_496, c_16])).
% 3.14/1.52  tff(c_618, plain, (![C_113, B_4]: (k4_xboole_0(C_113, B_4)=k1_xboole_0 | k4_xboole_0(k4_xboole_0(C_113, B_4), B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_603])).
% 3.14/1.52  tff(c_1422, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k1_xboole_0 | k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1408, c_618])).
% 3.14/1.52  tff(c_1435, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_456, c_1408, c_1422])).
% 3.14/1.52  tff(c_1437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_440, c_1435])).
% 3.14/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.52  
% 3.14/1.52  Inference rules
% 3.14/1.52  ----------------------
% 3.14/1.52  #Ref     : 0
% 3.14/1.52  #Sup     : 305
% 3.14/1.52  #Fact    : 0
% 3.14/1.52  #Define  : 0
% 3.14/1.52  #Split   : 5
% 3.14/1.52  #Chain   : 0
% 3.14/1.52  #Close   : 0
% 3.14/1.52  
% 3.14/1.52  Ordering : KBO
% 3.14/1.52  
% 3.14/1.52  Simplification rules
% 3.14/1.52  ----------------------
% 3.14/1.52  #Subsume      : 46
% 3.14/1.52  #Demod        : 141
% 3.14/1.52  #Tautology    : 162
% 3.14/1.52  #SimpNegUnit  : 12
% 3.14/1.52  #BackRed      : 9
% 3.14/1.52  
% 3.14/1.52  #Partial instantiations: 0
% 3.14/1.52  #Strategies tried      : 1
% 3.14/1.52  
% 3.14/1.52  Timing (in seconds)
% 3.14/1.52  ----------------------
% 3.14/1.52  Preprocessing        : 0.32
% 3.14/1.52  Parsing              : 0.16
% 3.14/1.52  CNF conversion       : 0.02
% 3.14/1.52  Main loop            : 0.43
% 3.14/1.52  Inferencing          : 0.16
% 3.14/1.52  Reduction            : 0.13
% 3.14/1.52  Demodulation         : 0.09
% 3.14/1.52  BG Simplification    : 0.02
% 3.14/1.52  Subsumption          : 0.09
% 3.14/1.52  Abstraction          : 0.02
% 3.14/1.52  MUC search           : 0.00
% 3.14/1.52  Cooper               : 0.00
% 3.14/1.52  Total                : 0.79
% 3.14/1.52  Index Insertion      : 0.00
% 3.14/1.52  Index Deletion       : 0.00
% 3.14/1.52  Index Matching       : 0.00
% 3.14/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
