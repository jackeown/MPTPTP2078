%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:10 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 236 expanded)
%              Number of leaves         :   29 (  89 expanded)
%              Depth                    :   12
%              Number of atoms          :  103 ( 285 expanded)
%              Number of equality atoms :   71 ( 183 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_67,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(c_16,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_289,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_297,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_289])).

tff(c_390,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k4_xboole_0(A_68,B_69)) = k3_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_479,plain,(
    ! [B_72] : k3_xboole_0(k1_xboole_0,B_72) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_297])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_109,plain,(
    ! [A_46,B_47] : k2_xboole_0(A_46,k3_xboole_0(A_46,B_47)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_121,plain,(
    ! [B_4,A_3] : k2_xboole_0(B_4,k3_xboole_0(A_3,B_4)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_109])).

tff(c_543,plain,(
    ! [B_73] : k2_xboole_0(B_73,k1_xboole_0) = B_73 ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_121])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_555,plain,(
    ! [B_73] : k2_xboole_0(k1_xboole_0,B_73) = B_73 ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_2])).

tff(c_22,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_678,plain,(
    ! [B_79] : k2_xboole_0(k1_xboole_0,B_79) = B_79 ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_2])).

tff(c_720,plain,(
    ! [B_19] : k4_xboole_0(B_19,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_678])).

tff(c_767,plain,(
    ! [B_80] : k4_xboole_0(B_80,k1_xboole_0) = B_80 ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_720])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_296,plain,(
    ! [A_14,B_15] : k4_xboole_0(k4_xboole_0(A_14,B_15),A_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_289])).

tff(c_782,plain,(
    ! [B_80] : k4_xboole_0(B_80,B_80) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_767,c_296])).

tff(c_30,plain,(
    ! [A_27] : k2_subset_1(A_27) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_34,plain,(
    ! [A_30] : m1_subset_1(k2_subset_1(A_30),k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_52,plain,(
    ! [A_30] : m1_subset_1(A_30,k1_zfmisc_1(A_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34])).

tff(c_876,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(A_85,B_86) = k3_subset_1(A_85,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_879,plain,(
    ! [A_30] : k4_xboole_0(A_30,A_30) = k3_subset_1(A_30,A_30) ),
    inference(resolution,[status(thm)],[c_52,c_876])).

tff(c_881,plain,(
    ! [A_30] : k3_subset_1(A_30,A_30) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_879])).

tff(c_358,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(A_65,B_66)
      | k4_xboole_0(A_65,B_66) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_50,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | k2_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_53,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_50])).

tff(c_157,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_44,plain,
    ( k2_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_51,plain,
    ( '#skF_2' != '#skF_1'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_44])).

tff(c_242,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_157,c_157,c_51])).

tff(c_376,plain,(
    k4_xboole_0(k3_subset_1('#skF_1','#skF_1'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_358,c_242])).

tff(c_883,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_881,c_376])).

tff(c_887,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_883])).

tff(c_889,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_1136,plain,(
    ! [A_105,B_106] : k4_xboole_0(A_105,k4_xboole_0(A_105,B_106)) = k3_xboole_0(A_105,B_106) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_969,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(A_92,B_93) = k1_xboole_0
      | ~ r1_tarski(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_981,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_969])).

tff(c_1229,plain,(
    ! [B_109] : k3_xboole_0(k1_xboole_0,B_109) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1136,c_981])).

tff(c_1373,plain,(
    ! [B_111] : k2_xboole_0(B_111,k1_xboole_0) = B_111 ),
    inference(superposition,[status(thm),theory(equality)],[c_1229,c_121])).

tff(c_1399,plain,(
    ! [A_1] : k2_xboole_0(k1_xboole_0,A_1) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1373])).

tff(c_1454,plain,(
    ! [A_114] : k2_xboole_0(k1_xboole_0,A_114) = A_114 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1373])).

tff(c_1496,plain,(
    ! [B_19] : k4_xboole_0(B_19,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1454])).

tff(c_1556,plain,(
    ! [B_115] : k4_xboole_0(B_115,k1_xboole_0) = B_115 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1399,c_1496])).

tff(c_980,plain,(
    ! [A_14,B_15] : k4_xboole_0(k4_xboole_0(A_14,B_15),A_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_969])).

tff(c_1571,plain,(
    ! [B_115] : k4_xboole_0(B_115,B_115) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1556,c_980])).

tff(c_1758,plain,(
    ! [A_125,B_126] :
      ( k4_xboole_0(A_125,B_126) = k3_subset_1(A_125,B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1761,plain,(
    ! [A_30] : k4_xboole_0(A_30,A_30) = k3_subset_1(A_30,A_30) ),
    inference(resolution,[status(thm)],[c_52,c_1758])).

tff(c_1766,plain,(
    ! [A_30] : k3_subset_1(A_30,A_30) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1571,c_1761])).

tff(c_1981,plain,(
    ! [A_132,B_133] :
      ( k3_subset_1(A_132,k3_subset_1(A_132,B_133)) = B_133
      | ~ m1_subset_1(B_133,k1_zfmisc_1(A_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1983,plain,(
    ! [A_30] : k3_subset_1(A_30,k3_subset_1(A_30,A_30)) = A_30 ),
    inference(resolution,[status(thm)],[c_52,c_1981])).

tff(c_1987,plain,(
    ! [A_30] : k3_subset_1(A_30,k1_xboole_0) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1766,c_1983])).

tff(c_1241,plain,(
    ! [B_109] : k2_xboole_0(B_109,k1_xboole_0) = B_109 ),
    inference(superposition,[status(thm),theory(equality)],[c_1229,c_121])).

tff(c_888,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_979,plain,(
    k4_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_888,c_969])).

tff(c_1414,plain,(
    ! [A_112,B_113] : k2_xboole_0(A_112,k4_xboole_0(B_113,A_112)) = k2_xboole_0(A_112,B_113) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1438,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_979,c_1414])).

tff(c_1450,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1241,c_1438])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1767,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_1758])).

tff(c_1857,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1767,c_22])).

tff(c_1872,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1450,c_2,c_1857])).

tff(c_12,plain,(
    ! [A_9,B_10] : k3_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1683,plain,(
    ! [A_121,B_122] : r1_tarski(k3_xboole_0(A_121,B_122),A_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_1136,c_18])).

tff(c_1720,plain,(
    ! [B_123,A_124] : r1_tarski(k3_xboole_0(B_123,A_124),A_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1683])).

tff(c_1742,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1720])).

tff(c_1878,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1872,c_1742])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1896,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1878,c_10])).

tff(c_1920,plain,(
    k3_subset_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1896,c_1767])).

tff(c_1988,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_42,c_1981])).

tff(c_2019,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1987,c_1920,c_1988])).

tff(c_2020,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_889,c_2019])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.72  
% 3.21/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.72  %$ r1_tarski > m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.21/1.72  
% 3.21/1.72  %Foreground sorts:
% 3.21/1.72  
% 3.21/1.72  
% 3.21/1.72  %Background operators:
% 3.21/1.72  
% 3.21/1.72  
% 3.21/1.72  %Foreground operators:
% 3.21/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.21/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.21/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.72  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.21/1.72  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.21/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.72  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.21/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.21/1.72  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.21/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.72  
% 3.21/1.74  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.21/1.74  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.21/1.74  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.21/1.74  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.21/1.74  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.21/1.74  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.21/1.74  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.21/1.74  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.21/1.74  tff(f_61, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.21/1.74  tff(f_67, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.21/1.74  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.21/1.74  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 3.21/1.74  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.21/1.74  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.21/1.74  tff(c_16, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.21/1.74  tff(c_289, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.74  tff(c_297, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_289])).
% 3.21/1.74  tff(c_390, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k4_xboole_0(A_68, B_69))=k3_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.21/1.74  tff(c_479, plain, (![B_72]: (k3_xboole_0(k1_xboole_0, B_72)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_390, c_297])).
% 3.21/1.74  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.21/1.74  tff(c_109, plain, (![A_46, B_47]: (k2_xboole_0(A_46, k3_xboole_0(A_46, B_47))=A_46)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.21/1.74  tff(c_121, plain, (![B_4, A_3]: (k2_xboole_0(B_4, k3_xboole_0(A_3, B_4))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_109])).
% 3.21/1.74  tff(c_543, plain, (![B_73]: (k2_xboole_0(B_73, k1_xboole_0)=B_73)), inference(superposition, [status(thm), theory('equality')], [c_479, c_121])).
% 3.21/1.74  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.21/1.74  tff(c_555, plain, (![B_73]: (k2_xboole_0(k1_xboole_0, B_73)=B_73)), inference(superposition, [status(thm), theory('equality')], [c_543, c_2])).
% 3.21/1.74  tff(c_22, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.21/1.74  tff(c_678, plain, (![B_79]: (k2_xboole_0(k1_xboole_0, B_79)=B_79)), inference(superposition, [status(thm), theory('equality')], [c_543, c_2])).
% 3.21/1.74  tff(c_720, plain, (![B_19]: (k4_xboole_0(B_19, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_19))), inference(superposition, [status(thm), theory('equality')], [c_22, c_678])).
% 3.21/1.74  tff(c_767, plain, (![B_80]: (k4_xboole_0(B_80, k1_xboole_0)=B_80)), inference(demodulation, [status(thm), theory('equality')], [c_555, c_720])).
% 3.21/1.74  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.21/1.74  tff(c_296, plain, (![A_14, B_15]: (k4_xboole_0(k4_xboole_0(A_14, B_15), A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_289])).
% 3.21/1.74  tff(c_782, plain, (![B_80]: (k4_xboole_0(B_80, B_80)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_767, c_296])).
% 3.21/1.74  tff(c_30, plain, (![A_27]: (k2_subset_1(A_27)=A_27)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.21/1.74  tff(c_34, plain, (![A_30]: (m1_subset_1(k2_subset_1(A_30), k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.21/1.74  tff(c_52, plain, (![A_30]: (m1_subset_1(A_30, k1_zfmisc_1(A_30)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34])).
% 3.21/1.74  tff(c_876, plain, (![A_85, B_86]: (k4_xboole_0(A_85, B_86)=k3_subset_1(A_85, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.21/1.74  tff(c_879, plain, (![A_30]: (k4_xboole_0(A_30, A_30)=k3_subset_1(A_30, A_30))), inference(resolution, [status(thm)], [c_52, c_876])).
% 3.21/1.74  tff(c_881, plain, (![A_30]: (k3_subset_1(A_30, A_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_782, c_879])).
% 3.21/1.74  tff(c_358, plain, (![A_65, B_66]: (r1_tarski(A_65, B_66) | k4_xboole_0(A_65, B_66)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.74  tff(c_50, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | k2_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.21/1.74  tff(c_53, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_50])).
% 3.21/1.74  tff(c_157, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_53])).
% 3.21/1.74  tff(c_44, plain, (k2_subset_1('#skF_1')!='#skF_2' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.21/1.74  tff(c_51, plain, ('#skF_2'!='#skF_1' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_44])).
% 3.21/1.74  tff(c_242, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_157, c_157, c_51])).
% 3.21/1.74  tff(c_376, plain, (k4_xboole_0(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_358, c_242])).
% 3.21/1.74  tff(c_883, plain, (k4_xboole_0(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_881, c_376])).
% 3.21/1.74  tff(c_887, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_297, c_883])).
% 3.21/1.74  tff(c_889, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_53])).
% 3.21/1.74  tff(c_1136, plain, (![A_105, B_106]: (k4_xboole_0(A_105, k4_xboole_0(A_105, B_106))=k3_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.21/1.74  tff(c_969, plain, (![A_92, B_93]: (k4_xboole_0(A_92, B_93)=k1_xboole_0 | ~r1_tarski(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.74  tff(c_981, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_969])).
% 3.21/1.74  tff(c_1229, plain, (![B_109]: (k3_xboole_0(k1_xboole_0, B_109)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1136, c_981])).
% 3.21/1.74  tff(c_1373, plain, (![B_111]: (k2_xboole_0(B_111, k1_xboole_0)=B_111)), inference(superposition, [status(thm), theory('equality')], [c_1229, c_121])).
% 3.21/1.74  tff(c_1399, plain, (![A_1]: (k2_xboole_0(k1_xboole_0, A_1)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1373])).
% 3.21/1.74  tff(c_1454, plain, (![A_114]: (k2_xboole_0(k1_xboole_0, A_114)=A_114)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1373])).
% 3.21/1.74  tff(c_1496, plain, (![B_19]: (k4_xboole_0(B_19, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_19))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1454])).
% 3.21/1.74  tff(c_1556, plain, (![B_115]: (k4_xboole_0(B_115, k1_xboole_0)=B_115)), inference(demodulation, [status(thm), theory('equality')], [c_1399, c_1496])).
% 3.21/1.74  tff(c_980, plain, (![A_14, B_15]: (k4_xboole_0(k4_xboole_0(A_14, B_15), A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_969])).
% 3.21/1.74  tff(c_1571, plain, (![B_115]: (k4_xboole_0(B_115, B_115)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1556, c_980])).
% 3.21/1.74  tff(c_1758, plain, (![A_125, B_126]: (k4_xboole_0(A_125, B_126)=k3_subset_1(A_125, B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.21/1.74  tff(c_1761, plain, (![A_30]: (k4_xboole_0(A_30, A_30)=k3_subset_1(A_30, A_30))), inference(resolution, [status(thm)], [c_52, c_1758])).
% 3.21/1.74  tff(c_1766, plain, (![A_30]: (k3_subset_1(A_30, A_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1571, c_1761])).
% 3.21/1.74  tff(c_1981, plain, (![A_132, B_133]: (k3_subset_1(A_132, k3_subset_1(A_132, B_133))=B_133 | ~m1_subset_1(B_133, k1_zfmisc_1(A_132)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.21/1.74  tff(c_1983, plain, (![A_30]: (k3_subset_1(A_30, k3_subset_1(A_30, A_30))=A_30)), inference(resolution, [status(thm)], [c_52, c_1981])).
% 3.21/1.74  tff(c_1987, plain, (![A_30]: (k3_subset_1(A_30, k1_xboole_0)=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_1766, c_1983])).
% 3.21/1.74  tff(c_1241, plain, (![B_109]: (k2_xboole_0(B_109, k1_xboole_0)=B_109)), inference(superposition, [status(thm), theory('equality')], [c_1229, c_121])).
% 3.21/1.74  tff(c_888, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_53])).
% 3.21/1.74  tff(c_979, plain, (k4_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_888, c_969])).
% 3.21/1.74  tff(c_1414, plain, (![A_112, B_113]: (k2_xboole_0(A_112, k4_xboole_0(B_113, A_112))=k2_xboole_0(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.21/1.74  tff(c_1438, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_979, c_1414])).
% 3.21/1.74  tff(c_1450, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1241, c_1438])).
% 3.21/1.74  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.21/1.74  tff(c_1767, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_1758])).
% 3.21/1.74  tff(c_1857, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1767, c_22])).
% 3.21/1.74  tff(c_1872, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1450, c_2, c_1857])).
% 3.21/1.74  tff(c_12, plain, (![A_9, B_10]: (k3_xboole_0(A_9, k2_xboole_0(A_9, B_10))=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.21/1.74  tff(c_1683, plain, (![A_121, B_122]: (r1_tarski(k3_xboole_0(A_121, B_122), A_121))), inference(superposition, [status(thm), theory('equality')], [c_1136, c_18])).
% 3.21/1.74  tff(c_1720, plain, (![B_123, A_124]: (r1_tarski(k3_xboole_0(B_123, A_124), A_124))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1683])).
% 3.21/1.74  tff(c_1742, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1720])).
% 3.21/1.74  tff(c_1878, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1872, c_1742])).
% 3.21/1.74  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.74  tff(c_1896, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1878, c_10])).
% 3.21/1.74  tff(c_1920, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1896, c_1767])).
% 3.21/1.74  tff(c_1988, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_42, c_1981])).
% 3.21/1.74  tff(c_2019, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1987, c_1920, c_1988])).
% 3.21/1.74  tff(c_2020, plain, $false, inference(negUnitSimplification, [status(thm)], [c_889, c_2019])).
% 3.21/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.74  
% 3.21/1.74  Inference rules
% 3.21/1.74  ----------------------
% 3.21/1.74  #Ref     : 0
% 3.21/1.74  #Sup     : 471
% 3.21/1.74  #Fact    : 0
% 3.21/1.74  #Define  : 0
% 3.21/1.74  #Split   : 2
% 3.21/1.74  #Chain   : 0
% 3.21/1.74  #Close   : 0
% 3.21/1.74  
% 3.21/1.74  Ordering : KBO
% 3.21/1.74  
% 3.21/1.74  Simplification rules
% 3.21/1.74  ----------------------
% 3.21/1.74  #Subsume      : 6
% 3.21/1.74  #Demod        : 248
% 3.21/1.74  #Tautology    : 365
% 3.21/1.74  #SimpNegUnit  : 3
% 3.21/1.74  #BackRed      : 9
% 3.21/1.74  
% 3.21/1.74  #Partial instantiations: 0
% 3.21/1.74  #Strategies tried      : 1
% 3.21/1.74  
% 3.21/1.74  Timing (in seconds)
% 3.21/1.74  ----------------------
% 3.21/1.74  Preprocessing        : 0.43
% 3.21/1.74  Parsing              : 0.24
% 3.21/1.74  CNF conversion       : 0.02
% 3.21/1.74  Main loop            : 0.45
% 3.21/1.74  Inferencing          : 0.16
% 3.21/1.74  Reduction            : 0.17
% 3.21/1.74  Demodulation         : 0.13
% 3.21/1.74  BG Simplification    : 0.02
% 3.21/1.74  Subsumption          : 0.06
% 3.21/1.74  Abstraction          : 0.03
% 3.21/1.74  MUC search           : 0.00
% 3.21/1.74  Cooper               : 0.00
% 3.21/1.74  Total                : 0.92
% 3.21/1.74  Index Insertion      : 0.00
% 3.21/1.74  Index Deletion       : 0.00
% 3.21/1.74  Index Matching       : 0.00
% 3.21/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
