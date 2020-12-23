%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:06 EST 2020

% Result     : Theorem 8.14s
% Output     : CNFRefutation 8.43s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 270 expanded)
%              Number of leaves         :   39 ( 102 expanded)
%              Depth                    :   12
%              Number of atoms          :  174 ( 553 expanded)
%              Number of equality atoms :   69 ( 354 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_72,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_89,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_82,plain,
    ( k1_xboole_0 != '#skF_10'
    | k1_tarski('#skF_8') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_101,plain,(
    k1_tarski('#skF_8') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_88,plain,(
    k2_xboole_0('#skF_9','#skF_10') = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_52,plain,(
    ! [A_34,B_35] : r1_tarski(A_34,k2_xboole_0(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_116,plain,(
    r1_tarski('#skF_9',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_52])).

tff(c_755,plain,(
    ! [B_100,A_101] :
      ( B_100 = A_101
      | ~ r1_tarski(B_100,A_101)
      | ~ r1_tarski(A_101,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_763,plain,
    ( k1_tarski('#skF_8') = '#skF_9'
    | ~ r1_tarski(k1_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_116,c_755])).

tff(c_773,plain,(
    ~ r1_tarski(k1_tarski('#skF_8'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_763])).

tff(c_84,plain,
    ( k1_tarski('#skF_8') != '#skF_10'
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_112,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_32,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_5'(A_18),A_18)
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_56,plain,(
    ! [C_40] : r2_hidden(C_40,k1_tarski(C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,(
    ! [A_26] : k4_xboole_0(A_26,k1_xboole_0) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_992,plain,(
    ! [D_111,B_112,A_113] :
      ( ~ r2_hidden(D_111,B_112)
      | ~ r2_hidden(D_111,k4_xboole_0(A_113,B_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1056,plain,(
    ! [D_116,A_117] :
      ( ~ r2_hidden(D_116,k1_xboole_0)
      | ~ r2_hidden(D_116,A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_992])).

tff(c_1070,plain,(
    ! [A_117] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0),A_117)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_1056])).

tff(c_1073,plain,(
    ! [A_120] : ~ r2_hidden('#skF_1'(k1_xboole_0),A_120) ),
    inference(splitLeft,[status(thm)],[c_1070])).

tff(c_1083,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_56,c_1073])).

tff(c_1084,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1070])).

tff(c_221,plain,(
    ! [A_75,B_76] : k4_xboole_0(A_75,k2_xboole_0(A_75,B_76)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_234,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_221])).

tff(c_4843,plain,(
    ! [D_3621,A_3622,B_3623] :
      ( r2_hidden(D_3621,k4_xboole_0(A_3622,B_3623))
      | r2_hidden(D_3621,B_3623)
      | ~ r2_hidden(D_3621,A_3622) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_7246,plain,(
    ! [D_4336] :
      ( r2_hidden(D_4336,k1_xboole_0)
      | r2_hidden(D_4336,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_4336,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_4843])).

tff(c_54,plain,(
    ! [C_40,A_36] :
      ( C_40 = A_36
      | ~ r2_hidden(C_40,k1_tarski(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_7312,plain,(
    ! [D_4371] :
      ( D_4371 = '#skF_8'
      | r2_hidden(D_4371,k1_xboole_0)
      | ~ r2_hidden(D_4371,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_7246,c_54])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_7329,plain,(
    ! [D_4371] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | D_4371 = '#skF_8'
      | ~ r2_hidden(D_4371,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_7312,c_4])).

tff(c_7340,plain,(
    ! [D_4406] :
      ( D_4406 = '#skF_8'
      | ~ r2_hidden(D_4406,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1084,c_7329])).

tff(c_7348,plain,
    ( '#skF_5'('#skF_9') = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_32,c_7340])).

tff(c_7356,plain,(
    '#skF_5'('#skF_9') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_7348])).

tff(c_7361,plain,
    ( r2_hidden('#skF_8','#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_7356,c_32])).

tff(c_7364,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_7361])).

tff(c_976,plain,(
    ! [A_109,B_110] :
      ( r2_hidden('#skF_2'(A_109,B_110),A_109)
      | r1_tarski(A_109,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10316,plain,(
    ! [A_6787,B_6788] :
      ( '#skF_2'(k1_tarski(A_6787),B_6788) = A_6787
      | r1_tarski(k1_tarski(A_6787),B_6788) ) ),
    inference(resolution,[status(thm)],[c_976,c_54])).

tff(c_10420,plain,(
    '#skF_2'(k1_tarski('#skF_8'),'#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_10316,c_773])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_2'(A_7,B_8),B_8)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10430,plain,
    ( ~ r2_hidden('#skF_8','#skF_9')
    | r1_tarski(k1_tarski('#skF_8'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_10420,c_10])).

tff(c_10481,plain,(
    r1_tarski(k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7364,c_10430])).

tff(c_10483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_773,c_10481])).

tff(c_10484,plain,(
    k1_tarski('#skF_8') != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_10485,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_10486,plain,(
    ! [A_26] : k4_xboole_0(A_26,'#skF_9') = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10485,c_44])).

tff(c_10879,plain,(
    ! [A_6897,B_6898] : k4_xboole_0(k2_xboole_0(A_6897,B_6898),B_6898) = k4_xboole_0(A_6897,B_6898) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10889,plain,(
    ! [A_6897] : k4_xboole_0(A_6897,'#skF_9') = k2_xboole_0(A_6897,'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_10879,c_10486])).

tff(c_10927,plain,(
    ! [A_6899] : k2_xboole_0(A_6899,'#skF_9') = A_6899 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10486,c_10889])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10949,plain,(
    ! [A_6899] : k2_xboole_0('#skF_9',A_6899) = A_6899 ),
    inference(superposition,[status(thm),theory(equality)],[c_10927,c_2])).

tff(c_10993,plain,(
    k1_tarski('#skF_8') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10949,c_88])).

tff(c_10995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10484,c_10993])).

tff(c_10996,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_10997,plain,(
    k1_tarski('#skF_8') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_86,plain,
    ( k1_tarski('#skF_8') != '#skF_10'
    | k1_tarski('#skF_8') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_11083,plain,(
    '#skF_10' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10997,c_10997,c_86])).

tff(c_11017,plain,(
    k2_xboole_0('#skF_9','#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10997,c_88])).

tff(c_11043,plain,(
    ! [B_6908,A_6909] : k2_xboole_0(B_6908,A_6909) = k2_xboole_0(A_6909,B_6908) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_11084,plain,(
    ! [A_6910,B_6911] : r1_tarski(A_6910,k2_xboole_0(B_6911,A_6910)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11043,c_52])).

tff(c_11093,plain,(
    r1_tarski('#skF_10','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_11017,c_11084])).

tff(c_11437,plain,(
    ! [B_6934,A_6935] :
      ( B_6934 = A_6935
      | ~ r1_tarski(B_6934,A_6935)
      | ~ r1_tarski(A_6935,B_6934) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_11439,plain,
    ( '#skF_10' = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_11093,c_11437])).

tff(c_11448,plain,(
    ~ r1_tarski('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_11083,c_11439])).

tff(c_12164,plain,(
    ! [A_6980,B_6981] :
      ( r2_hidden('#skF_2'(A_6980,B_6981),A_6980)
      | r1_tarski(A_6980,B_6981) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_11103,plain,(
    ! [C_6914,A_6915] :
      ( C_6914 = A_6915
      | ~ r2_hidden(C_6914,k1_tarski(A_6915)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_11114,plain,(
    ! [C_6914] :
      ( C_6914 = '#skF_8'
      | ~ r2_hidden(C_6914,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10997,c_11103])).

tff(c_12356,plain,(
    ! [B_7000] :
      ( '#skF_2'('#skF_9',B_7000) = '#skF_8'
      | r1_tarski('#skF_9',B_7000) ) ),
    inference(resolution,[status(thm)],[c_12164,c_11114])).

tff(c_12384,plain,(
    '#skF_2'('#skF_9','#skF_10') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_12356,c_11448])).

tff(c_12390,plain,
    ( ~ r2_hidden('#skF_8','#skF_10')
    | r1_tarski('#skF_9','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_12384,c_10])).

tff(c_12396,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_11448,c_12390])).

tff(c_11058,plain,(
    ! [A_6909,B_6908] : r1_tarski(A_6909,k2_xboole_0(B_6908,A_6909)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11043,c_52])).

tff(c_66,plain,(
    ! [A_41] : k2_tarski(A_41,A_41) = k1_tarski(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_11455,plain,(
    ! [B_6936,C_6937,A_6938] :
      ( r2_hidden(B_6936,C_6937)
      | ~ r1_tarski(k2_tarski(A_6938,B_6936),C_6937) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_11486,plain,(
    ! [A_6943,C_6944] :
      ( r2_hidden(A_6943,C_6944)
      | ~ r1_tarski(k1_tarski(A_6943),C_6944) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_11455])).

tff(c_11502,plain,(
    ! [A_6943,B_6908] : r2_hidden(A_6943,k2_xboole_0(B_6908,k1_tarski(A_6943))) ),
    inference(resolution,[status(thm)],[c_11058,c_11486])).

tff(c_11506,plain,(
    ! [D_6945,B_6946,A_6947] :
      ( ~ r2_hidden(D_6945,B_6946)
      | ~ r2_hidden(D_6945,k4_xboole_0(A_6947,B_6946)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_11532,plain,(
    ! [D_6948,A_6949] :
      ( ~ r2_hidden(D_6948,k1_xboole_0)
      | ~ r2_hidden(D_6948,A_6949) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_11506])).

tff(c_11541,plain,(
    ! [A_6949] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0),A_6949)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_11532])).

tff(c_12041,plain,(
    ! [A_6974] : ~ r2_hidden('#skF_1'(k1_xboole_0),A_6974) ),
    inference(splitLeft,[status(thm)],[c_11541])).

tff(c_12056,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_11502,c_12041])).

tff(c_12057,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_11541])).

tff(c_11170,plain,(
    ! [A_6918,B_6919] : k4_xboole_0(A_6918,k2_xboole_0(A_6918,B_6919)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_11199,plain,(
    ! [B_6920,A_6921] : k4_xboole_0(B_6920,k2_xboole_0(A_6921,B_6920)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_11170])).

tff(c_11218,plain,(
    k4_xboole_0('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11017,c_11199])).

tff(c_13488,plain,(
    ! [D_7049,A_7050,B_7051] :
      ( r2_hidden(D_7049,k4_xboole_0(A_7050,B_7051))
      | r2_hidden(D_7049,B_7051)
      | ~ r2_hidden(D_7049,A_7050) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_13587,plain,(
    ! [D_7054] :
      ( r2_hidden(D_7054,k1_xboole_0)
      | r2_hidden(D_7054,'#skF_9')
      | ~ r2_hidden(D_7054,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11218,c_13488])).

tff(c_13603,plain,(
    ! [D_7054] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | r2_hidden(D_7054,'#skF_9')
      | ~ r2_hidden(D_7054,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_13587,c_4])).

tff(c_13615,plain,(
    ! [D_7055] :
      ( r2_hidden(D_7055,'#skF_9')
      | ~ r2_hidden(D_7055,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12057,c_13603])).

tff(c_13627,plain,
    ( r2_hidden('#skF_5'('#skF_10'),'#skF_9')
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_32,c_13615])).

tff(c_13637,plain,(
    r2_hidden('#skF_5'('#skF_10'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_10996,c_13627])).

tff(c_13648,plain,(
    '#skF_5'('#skF_10') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_13637,c_11114])).

tff(c_13655,plain,
    ( r2_hidden('#skF_8','#skF_10')
    | k1_xboole_0 = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_13648,c_32])).

tff(c_13659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10996,c_12396,c_13655])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:43:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.14/2.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.43/2.83  
% 8.43/2.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.43/2.83  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_7
% 8.43/2.83  
% 8.43/2.83  %Foreground sorts:
% 8.43/2.83  
% 8.43/2.83  
% 8.43/2.83  %Background operators:
% 8.43/2.83  
% 8.43/2.83  
% 8.43/2.83  %Foreground operators:
% 8.43/2.83  tff('#skF_5', type, '#skF_5': $i > $i).
% 8.43/2.83  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.43/2.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.43/2.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.43/2.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.43/2.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.43/2.83  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.43/2.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.43/2.83  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.43/2.83  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.43/2.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.43/2.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.43/2.83  tff('#skF_10', type, '#skF_10': $i).
% 8.43/2.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.43/2.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.43/2.83  tff('#skF_9', type, '#skF_9': $i).
% 8.43/2.83  tff('#skF_8', type, '#skF_8': $i).
% 8.43/2.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.43/2.83  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.43/2.83  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.43/2.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.43/2.83  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.43/2.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.43/2.83  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 8.43/2.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.43/2.83  
% 8.43/2.85  tff(f_122, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 8.43/2.85  tff(f_80, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.43/2.85  tff(f_64, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.43/2.85  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.43/2.85  tff(f_87, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 8.43/2.85  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.43/2.85  tff(f_72, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.43/2.85  tff(f_50, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 8.43/2.85  tff(f_78, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 8.43/2.85  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.43/2.85  tff(f_74, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 8.43/2.85  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.43/2.85  tff(f_89, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 8.43/2.85  tff(f_103, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 8.43/2.85  tff(c_82, plain, (k1_xboole_0!='#skF_10' | k1_tarski('#skF_8')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.43/2.85  tff(c_101, plain, (k1_tarski('#skF_8')!='#skF_9'), inference(splitLeft, [status(thm)], [c_82])).
% 8.43/2.85  tff(c_88, plain, (k2_xboole_0('#skF_9', '#skF_10')=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.43/2.85  tff(c_52, plain, (![A_34, B_35]: (r1_tarski(A_34, k2_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.43/2.85  tff(c_116, plain, (r1_tarski('#skF_9', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_52])).
% 8.43/2.85  tff(c_755, plain, (![B_100, A_101]: (B_100=A_101 | ~r1_tarski(B_100, A_101) | ~r1_tarski(A_101, B_100))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.43/2.85  tff(c_763, plain, (k1_tarski('#skF_8')='#skF_9' | ~r1_tarski(k1_tarski('#skF_8'), '#skF_9')), inference(resolution, [status(thm)], [c_116, c_755])).
% 8.43/2.85  tff(c_773, plain, (~r1_tarski(k1_tarski('#skF_8'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_101, c_763])).
% 8.43/2.85  tff(c_84, plain, (k1_tarski('#skF_8')!='#skF_10' | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.43/2.85  tff(c_112, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_84])).
% 8.43/2.85  tff(c_32, plain, (![A_18]: (r2_hidden('#skF_5'(A_18), A_18) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.43/2.85  tff(c_56, plain, (![C_40]: (r2_hidden(C_40, k1_tarski(C_40)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.43/2.85  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.43/2.85  tff(c_44, plain, (![A_26]: (k4_xboole_0(A_26, k1_xboole_0)=A_26)), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.43/2.85  tff(c_992, plain, (![D_111, B_112, A_113]: (~r2_hidden(D_111, B_112) | ~r2_hidden(D_111, k4_xboole_0(A_113, B_112)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.43/2.85  tff(c_1056, plain, (![D_116, A_117]: (~r2_hidden(D_116, k1_xboole_0) | ~r2_hidden(D_116, A_117))), inference(superposition, [status(thm), theory('equality')], [c_44, c_992])).
% 8.43/2.85  tff(c_1070, plain, (![A_117]: (~r2_hidden('#skF_1'(k1_xboole_0), A_117) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_1056])).
% 8.43/2.85  tff(c_1073, plain, (![A_120]: (~r2_hidden('#skF_1'(k1_xboole_0), A_120))), inference(splitLeft, [status(thm)], [c_1070])).
% 8.43/2.85  tff(c_1083, plain, $false, inference(resolution, [status(thm)], [c_56, c_1073])).
% 8.43/2.85  tff(c_1084, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_1070])).
% 8.43/2.85  tff(c_221, plain, (![A_75, B_76]: (k4_xboole_0(A_75, k2_xboole_0(A_75, B_76))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.43/2.85  tff(c_234, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_8'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_88, c_221])).
% 8.43/2.85  tff(c_4843, plain, (![D_3621, A_3622, B_3623]: (r2_hidden(D_3621, k4_xboole_0(A_3622, B_3623)) | r2_hidden(D_3621, B_3623) | ~r2_hidden(D_3621, A_3622))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.43/2.85  tff(c_7246, plain, (![D_4336]: (r2_hidden(D_4336, k1_xboole_0) | r2_hidden(D_4336, k1_tarski('#skF_8')) | ~r2_hidden(D_4336, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_234, c_4843])).
% 8.43/2.85  tff(c_54, plain, (![C_40, A_36]: (C_40=A_36 | ~r2_hidden(C_40, k1_tarski(A_36)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.43/2.85  tff(c_7312, plain, (![D_4371]: (D_4371='#skF_8' | r2_hidden(D_4371, k1_xboole_0) | ~r2_hidden(D_4371, '#skF_9'))), inference(resolution, [status(thm)], [c_7246, c_54])).
% 8.43/2.85  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.43/2.85  tff(c_7329, plain, (![D_4371]: (~v1_xboole_0(k1_xboole_0) | D_4371='#skF_8' | ~r2_hidden(D_4371, '#skF_9'))), inference(resolution, [status(thm)], [c_7312, c_4])).
% 8.43/2.85  tff(c_7340, plain, (![D_4406]: (D_4406='#skF_8' | ~r2_hidden(D_4406, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1084, c_7329])).
% 8.43/2.85  tff(c_7348, plain, ('#skF_5'('#skF_9')='#skF_8' | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_32, c_7340])).
% 8.43/2.85  tff(c_7356, plain, ('#skF_5'('#skF_9')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_112, c_7348])).
% 8.43/2.85  tff(c_7361, plain, (r2_hidden('#skF_8', '#skF_9') | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_7356, c_32])).
% 8.43/2.85  tff(c_7364, plain, (r2_hidden('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_112, c_7361])).
% 8.43/2.85  tff(c_976, plain, (![A_109, B_110]: (r2_hidden('#skF_2'(A_109, B_110), A_109) | r1_tarski(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.43/2.85  tff(c_10316, plain, (![A_6787, B_6788]: ('#skF_2'(k1_tarski(A_6787), B_6788)=A_6787 | r1_tarski(k1_tarski(A_6787), B_6788))), inference(resolution, [status(thm)], [c_976, c_54])).
% 8.43/2.85  tff(c_10420, plain, ('#skF_2'(k1_tarski('#skF_8'), '#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_10316, c_773])).
% 8.43/2.85  tff(c_10, plain, (![A_7, B_8]: (~r2_hidden('#skF_2'(A_7, B_8), B_8) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.43/2.85  tff(c_10430, plain, (~r2_hidden('#skF_8', '#skF_9') | r1_tarski(k1_tarski('#skF_8'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_10420, c_10])).
% 8.43/2.85  tff(c_10481, plain, (r1_tarski(k1_tarski('#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_7364, c_10430])).
% 8.43/2.85  tff(c_10483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_773, c_10481])).
% 8.43/2.85  tff(c_10484, plain, (k1_tarski('#skF_8')!='#skF_10'), inference(splitRight, [status(thm)], [c_84])).
% 8.43/2.85  tff(c_10485, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_84])).
% 8.43/2.85  tff(c_10486, plain, (![A_26]: (k4_xboole_0(A_26, '#skF_9')=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_10485, c_44])).
% 8.43/2.85  tff(c_10879, plain, (![A_6897, B_6898]: (k4_xboole_0(k2_xboole_0(A_6897, B_6898), B_6898)=k4_xboole_0(A_6897, B_6898))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.43/2.85  tff(c_10889, plain, (![A_6897]: (k4_xboole_0(A_6897, '#skF_9')=k2_xboole_0(A_6897, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_10879, c_10486])).
% 8.43/2.85  tff(c_10927, plain, (![A_6899]: (k2_xboole_0(A_6899, '#skF_9')=A_6899)), inference(demodulation, [status(thm), theory('equality')], [c_10486, c_10889])).
% 8.43/2.85  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.43/2.85  tff(c_10949, plain, (![A_6899]: (k2_xboole_0('#skF_9', A_6899)=A_6899)), inference(superposition, [status(thm), theory('equality')], [c_10927, c_2])).
% 8.43/2.85  tff(c_10993, plain, (k1_tarski('#skF_8')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_10949, c_88])).
% 8.43/2.85  tff(c_10995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10484, c_10993])).
% 8.43/2.85  tff(c_10996, plain, (k1_xboole_0!='#skF_10'), inference(splitRight, [status(thm)], [c_82])).
% 8.43/2.85  tff(c_10997, plain, (k1_tarski('#skF_8')='#skF_9'), inference(splitRight, [status(thm)], [c_82])).
% 8.43/2.85  tff(c_86, plain, (k1_tarski('#skF_8')!='#skF_10' | k1_tarski('#skF_8')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.43/2.85  tff(c_11083, plain, ('#skF_10'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_10997, c_10997, c_86])).
% 8.43/2.85  tff(c_11017, plain, (k2_xboole_0('#skF_9', '#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_10997, c_88])).
% 8.43/2.85  tff(c_11043, plain, (![B_6908, A_6909]: (k2_xboole_0(B_6908, A_6909)=k2_xboole_0(A_6909, B_6908))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.43/2.85  tff(c_11084, plain, (![A_6910, B_6911]: (r1_tarski(A_6910, k2_xboole_0(B_6911, A_6910)))), inference(superposition, [status(thm), theory('equality')], [c_11043, c_52])).
% 8.43/2.85  tff(c_11093, plain, (r1_tarski('#skF_10', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_11017, c_11084])).
% 8.43/2.85  tff(c_11437, plain, (![B_6934, A_6935]: (B_6934=A_6935 | ~r1_tarski(B_6934, A_6935) | ~r1_tarski(A_6935, B_6934))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.43/2.85  tff(c_11439, plain, ('#skF_10'='#skF_9' | ~r1_tarski('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_11093, c_11437])).
% 8.43/2.85  tff(c_11448, plain, (~r1_tarski('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_11083, c_11439])).
% 8.43/2.85  tff(c_12164, plain, (![A_6980, B_6981]: (r2_hidden('#skF_2'(A_6980, B_6981), A_6980) | r1_tarski(A_6980, B_6981))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.43/2.85  tff(c_11103, plain, (![C_6914, A_6915]: (C_6914=A_6915 | ~r2_hidden(C_6914, k1_tarski(A_6915)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.43/2.85  tff(c_11114, plain, (![C_6914]: (C_6914='#skF_8' | ~r2_hidden(C_6914, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_10997, c_11103])).
% 8.43/2.85  tff(c_12356, plain, (![B_7000]: ('#skF_2'('#skF_9', B_7000)='#skF_8' | r1_tarski('#skF_9', B_7000))), inference(resolution, [status(thm)], [c_12164, c_11114])).
% 8.43/2.85  tff(c_12384, plain, ('#skF_2'('#skF_9', '#skF_10')='#skF_8'), inference(resolution, [status(thm)], [c_12356, c_11448])).
% 8.43/2.85  tff(c_12390, plain, (~r2_hidden('#skF_8', '#skF_10') | r1_tarski('#skF_9', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_12384, c_10])).
% 8.43/2.85  tff(c_12396, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_11448, c_12390])).
% 8.43/2.85  tff(c_11058, plain, (![A_6909, B_6908]: (r1_tarski(A_6909, k2_xboole_0(B_6908, A_6909)))), inference(superposition, [status(thm), theory('equality')], [c_11043, c_52])).
% 8.43/2.85  tff(c_66, plain, (![A_41]: (k2_tarski(A_41, A_41)=k1_tarski(A_41))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.43/2.85  tff(c_11455, plain, (![B_6936, C_6937, A_6938]: (r2_hidden(B_6936, C_6937) | ~r1_tarski(k2_tarski(A_6938, B_6936), C_6937))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.43/2.85  tff(c_11486, plain, (![A_6943, C_6944]: (r2_hidden(A_6943, C_6944) | ~r1_tarski(k1_tarski(A_6943), C_6944))), inference(superposition, [status(thm), theory('equality')], [c_66, c_11455])).
% 8.43/2.85  tff(c_11502, plain, (![A_6943, B_6908]: (r2_hidden(A_6943, k2_xboole_0(B_6908, k1_tarski(A_6943))))), inference(resolution, [status(thm)], [c_11058, c_11486])).
% 8.43/2.85  tff(c_11506, plain, (![D_6945, B_6946, A_6947]: (~r2_hidden(D_6945, B_6946) | ~r2_hidden(D_6945, k4_xboole_0(A_6947, B_6946)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.43/2.85  tff(c_11532, plain, (![D_6948, A_6949]: (~r2_hidden(D_6948, k1_xboole_0) | ~r2_hidden(D_6948, A_6949))), inference(superposition, [status(thm), theory('equality')], [c_44, c_11506])).
% 8.43/2.85  tff(c_11541, plain, (![A_6949]: (~r2_hidden('#skF_1'(k1_xboole_0), A_6949) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_11532])).
% 8.43/2.85  tff(c_12041, plain, (![A_6974]: (~r2_hidden('#skF_1'(k1_xboole_0), A_6974))), inference(splitLeft, [status(thm)], [c_11541])).
% 8.43/2.85  tff(c_12056, plain, $false, inference(resolution, [status(thm)], [c_11502, c_12041])).
% 8.43/2.85  tff(c_12057, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_11541])).
% 8.43/2.85  tff(c_11170, plain, (![A_6918, B_6919]: (k4_xboole_0(A_6918, k2_xboole_0(A_6918, B_6919))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.43/2.85  tff(c_11199, plain, (![B_6920, A_6921]: (k4_xboole_0(B_6920, k2_xboole_0(A_6921, B_6920))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_11170])).
% 8.43/2.85  tff(c_11218, plain, (k4_xboole_0('#skF_10', '#skF_9')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11017, c_11199])).
% 8.43/2.85  tff(c_13488, plain, (![D_7049, A_7050, B_7051]: (r2_hidden(D_7049, k4_xboole_0(A_7050, B_7051)) | r2_hidden(D_7049, B_7051) | ~r2_hidden(D_7049, A_7050))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.43/2.85  tff(c_13587, plain, (![D_7054]: (r2_hidden(D_7054, k1_xboole_0) | r2_hidden(D_7054, '#skF_9') | ~r2_hidden(D_7054, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_11218, c_13488])).
% 8.43/2.85  tff(c_13603, plain, (![D_7054]: (~v1_xboole_0(k1_xboole_0) | r2_hidden(D_7054, '#skF_9') | ~r2_hidden(D_7054, '#skF_10'))), inference(resolution, [status(thm)], [c_13587, c_4])).
% 8.43/2.85  tff(c_13615, plain, (![D_7055]: (r2_hidden(D_7055, '#skF_9') | ~r2_hidden(D_7055, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_12057, c_13603])).
% 8.43/2.85  tff(c_13627, plain, (r2_hidden('#skF_5'('#skF_10'), '#skF_9') | k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_32, c_13615])).
% 8.43/2.85  tff(c_13637, plain, (r2_hidden('#skF_5'('#skF_10'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_10996, c_13627])).
% 8.43/2.85  tff(c_13648, plain, ('#skF_5'('#skF_10')='#skF_8'), inference(resolution, [status(thm)], [c_13637, c_11114])).
% 8.43/2.85  tff(c_13655, plain, (r2_hidden('#skF_8', '#skF_10') | k1_xboole_0='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_13648, c_32])).
% 8.43/2.85  tff(c_13659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10996, c_12396, c_13655])).
% 8.43/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.43/2.85  
% 8.43/2.85  Inference rules
% 8.43/2.85  ----------------------
% 8.43/2.85  #Ref     : 0
% 8.43/2.85  #Sup     : 2917
% 8.43/2.85  #Fact    : 0
% 8.43/2.85  #Define  : 0
% 8.43/2.85  #Split   : 15
% 8.43/2.85  #Chain   : 0
% 8.43/2.85  #Close   : 0
% 8.43/2.85  
% 8.43/2.85  Ordering : KBO
% 8.43/2.85  
% 8.43/2.85  Simplification rules
% 8.43/2.85  ----------------------
% 8.43/2.85  #Subsume      : 505
% 8.43/2.85  #Demod        : 2031
% 8.43/2.85  #Tautology    : 1585
% 8.43/2.85  #SimpNegUnit  : 80
% 8.43/2.85  #BackRed      : 52
% 8.43/2.85  
% 8.43/2.85  #Partial instantiations: 3629
% 8.43/2.85  #Strategies tried      : 1
% 8.43/2.85  
% 8.43/2.85  Timing (in seconds)
% 8.43/2.85  ----------------------
% 8.43/2.85  Preprocessing        : 0.38
% 8.43/2.86  Parsing              : 0.19
% 8.43/2.86  CNF conversion       : 0.03
% 8.43/2.86  Main loop            : 1.68
% 8.43/2.86  Inferencing          : 0.57
% 8.43/2.86  Reduction            : 0.67
% 8.43/2.86  Demodulation         : 0.53
% 8.43/2.86  BG Simplification    : 0.05
% 8.43/2.86  Subsumption          : 0.26
% 8.43/2.86  Abstraction          : 0.06
% 8.43/2.86  MUC search           : 0.00
% 8.43/2.86  Cooper               : 0.00
% 8.43/2.86  Total                : 2.10
% 8.43/2.86  Index Insertion      : 0.00
% 8.43/2.86  Index Deletion       : 0.00
% 8.43/2.86  Index Matching       : 0.00
% 8.43/2.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
