%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:39 EST 2020

% Result     : Theorem 5.16s
% Output     : CNFRefutation 5.16s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 269 expanded)
%              Number of leaves         :   27 (  97 expanded)
%              Depth                    :   21
%              Number of atoms          :  137 ( 420 expanded)
%              Number of equality atoms :   80 ( 192 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_52,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_42,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_104,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_36,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_187,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_36])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_xboole_0(k4_xboole_0(A_11,B_12),B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_113,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = A_33
      | ~ r1_xboole_0(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_129,plain,(
    ! [A_11,B_12] : k4_xboole_0(k4_xboole_0(A_11,B_12),B_12) = k4_xboole_0(A_11,B_12) ),
    inference(resolution,[status(thm)],[c_14,c_113])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_543,plain,(
    ! [B_65,A_66] :
      ( k3_xboole_0(k1_relat_1(B_65),A_66) = k1_relat_1(k7_relat_1(B_65,A_66))
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1822,plain,(
    ! [B_91,B_92] :
      ( k3_xboole_0(B_91,k1_relat_1(B_92)) = k1_relat_1(k7_relat_1(B_92,B_91))
      | ~ v1_relat_1(B_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_543])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    r1_xboole_0('#skF_1',k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_104,c_4])).

tff(c_126,plain,(
    k4_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_107,c_113])).

tff(c_352,plain,(
    ! [A_56,B_57] : k4_xboole_0(A_56,k4_xboole_0(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_402,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_352])).

tff(c_1841,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = k4_xboole_0('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1822,c_402])).

tff(c_1902,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = k4_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1841])).

tff(c_211,plain,(
    ! [B_44,A_45] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_44,A_45)),A_45)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_215,plain,(
    ! [B_44,A_45] :
      ( k4_xboole_0(k1_relat_1(k7_relat_1(B_44,A_45)),A_45) = k1_xboole_0
      | ~ v1_relat_1(B_44) ) ),
    inference(resolution,[status(thm)],[c_211,c_8])).

tff(c_1916,plain,
    ( k4_xboole_0(k4_xboole_0('#skF_1','#skF_1'),'#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1902,c_215])).

tff(c_1926,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_129,c_1916])).

tff(c_1930,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1926,c_1902])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k7_relat_1(A_15,B_16))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_95,plain,(
    ! [A_32] :
      ( k1_relat_1(A_32) != k1_xboole_0
      | k1_xboole_0 = A_32
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2543,plain,(
    ! [A_100,B_101] :
      ( k1_relat_1(k7_relat_1(A_100,B_101)) != k1_xboole_0
      | k7_relat_1(A_100,B_101) = k1_xboole_0
      | ~ v1_relat_1(A_100) ) ),
    inference(resolution,[status(thm)],[c_20,c_95])).

tff(c_2549,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1930,c_2543])).

tff(c_2553,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2549])).

tff(c_2555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_2553])).

tff(c_2556,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2844,plain,(
    ! [B_126,A_127] :
      ( k3_xboole_0(k1_relat_1(B_126),A_127) = k1_relat_1(k7_relat_1(B_126,A_127))
      | ~ v1_relat_1(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2866,plain,(
    ! [A_127,B_126] :
      ( k3_xboole_0(A_127,k1_relat_1(B_126)) = k1_relat_1(k7_relat_1(B_126,A_127))
      | ~ v1_relat_1(B_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2844,c_2])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2656,plain,(
    ! [A_115,B_116] : k4_xboole_0(A_115,k4_xboole_0(A_115,B_116)) = k3_xboole_0(A_115,B_116) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2659,plain,(
    ! [A_115,B_116] : k4_xboole_0(A_115,k3_xboole_0(A_115,B_116)) = k3_xboole_0(A_115,k4_xboole_0(A_115,B_116)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2656,c_12])).

tff(c_4048,plain,(
    ! [A_115,B_116] : k3_xboole_0(A_115,k4_xboole_0(A_115,B_116)) = k4_xboole_0(A_115,B_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2659])).

tff(c_2561,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2556,c_20])).

tff(c_2565,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2561])).

tff(c_2884,plain,(
    ! [A_127] :
      ( k1_relat_1(k7_relat_1(k1_xboole_0,A_127)) = k3_xboole_0(k1_xboole_0,A_127)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2844])).

tff(c_2974,plain,(
    ! [A_128] : k1_relat_1(k7_relat_1(k1_xboole_0,A_128)) = k3_xboole_0(k1_xboole_0,A_128) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2565,c_2884])).

tff(c_30,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_19,A_18)),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2983,plain,(
    ! [A_128] :
      ( r1_tarski(k3_xboole_0(k1_xboole_0,A_128),A_128)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2974,c_30])).

tff(c_2991,plain,(
    ! [A_129] : r1_tarski(k3_xboole_0(k1_xboole_0,A_129),A_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2565,c_2983])).

tff(c_3007,plain,(
    ! [A_129] : k4_xboole_0(k3_xboole_0(k1_xboole_0,A_129),A_129) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2991,c_8])).

tff(c_2595,plain,(
    ! [A_105,B_106] :
      ( k4_xboole_0(A_105,B_106) = A_105
      | ~ r1_xboole_0(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3325,plain,(
    ! [A_137,B_138] : k4_xboole_0(k4_xboole_0(A_137,B_138),B_138) = k4_xboole_0(A_137,B_138) ),
    inference(resolution,[status(thm)],[c_14,c_2595])).

tff(c_3369,plain,(
    ! [A_129] : k4_xboole_0(k3_xboole_0(k1_xboole_0,A_129),A_129) = k4_xboole_0(k1_xboole_0,A_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_3007,c_3325])).

tff(c_3405,plain,(
    ! [A_139] : k4_xboole_0(k1_xboole_0,A_139) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3007,c_3369])).

tff(c_3485,plain,(
    ! [B_140] : k3_xboole_0(k1_xboole_0,B_140) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3405,c_12])).

tff(c_3535,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3485])).

tff(c_3219,plain,(
    ! [A_133] : k4_xboole_0(k3_xboole_0(k1_xboole_0,A_133),A_133) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2991,c_8])).

tff(c_85,plain,(
    ! [B_26,A_27] :
      ( r1_xboole_0(B_26,A_27)
      | ~ r1_xboole_0(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [B_12,A_11] : r1_xboole_0(B_12,k4_xboole_0(A_11,B_12)) ),
    inference(resolution,[status(thm)],[c_14,c_85])).

tff(c_2602,plain,(
    ! [B_12,A_11] : k4_xboole_0(B_12,k4_xboole_0(A_11,B_12)) = B_12 ),
    inference(resolution,[status(thm)],[c_88,c_2595])).

tff(c_3286,plain,(
    ! [A_136] : k4_xboole_0(A_136,k1_xboole_0) = A_136 ),
    inference(superposition,[status(thm),theory(equality)],[c_3219,c_2602])).

tff(c_3302,plain,(
    ! [A_136] : k4_xboole_0(A_136,A_136) = k3_xboole_0(A_136,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3286,c_12])).

tff(c_3739,plain,(
    ! [A_136] : k4_xboole_0(A_136,A_136) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3535,c_3302])).

tff(c_4049,plain,(
    ! [A_155,B_156] : k3_xboole_0(A_155,k4_xboole_0(A_155,B_156)) = k4_xboole_0(A_155,B_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2659])).

tff(c_2700,plain,(
    ! [A_118,B_119] : k4_xboole_0(A_118,k3_xboole_0(A_118,B_119)) = k4_xboole_0(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2724,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2700])).

tff(c_4065,plain,(
    ! [A_155,B_156] : k4_xboole_0(k4_xboole_0(A_155,B_156),k4_xboole_0(A_155,B_156)) = k4_xboole_0(k4_xboole_0(A_155,B_156),A_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_4049,c_2724])).

tff(c_4126,plain,(
    ! [A_155,B_156] : k4_xboole_0(k4_xboole_0(A_155,B_156),A_155) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3739,c_4065])).

tff(c_2632,plain,(
    ! [A_111,B_112] :
      ( r1_xboole_0(A_111,B_112)
      | k4_xboole_0(A_111,B_112) != A_111 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2644,plain,(
    ! [B_113,A_114] :
      ( r1_xboole_0(B_113,A_114)
      | k4_xboole_0(A_114,B_113) != A_114 ) ),
    inference(resolution,[status(thm)],[c_2632,c_4])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4894,plain,(
    ! [B_172,A_173] :
      ( k4_xboole_0(B_172,A_173) = B_172
      | k4_xboole_0(A_173,B_172) != A_173 ) ),
    inference(resolution,[status(thm)],[c_2644,c_16])).

tff(c_4900,plain,(
    ! [A_155,B_156] :
      ( k4_xboole_0(A_155,k4_xboole_0(A_155,B_156)) = A_155
      | k4_xboole_0(A_155,B_156) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4126,c_4894])).

tff(c_5471,plain,(
    ! [A_182,B_183] :
      ( k3_xboole_0(A_182,B_183) = A_182
      | k4_xboole_0(A_182,B_183) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4900])).

tff(c_5507,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = A_9
      | k3_xboole_0(A_9,B_10) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_5471])).

tff(c_5864,plain,(
    ! [A_188,B_189] :
      ( k4_xboole_0(A_188,B_189) = A_188
      | k3_xboole_0(A_188,B_189) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4048,c_5507])).

tff(c_2557,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2654,plain,(
    k4_xboole_0('#skF_1',k1_relat_1('#skF_2')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_2644,c_2557])).

tff(c_6050,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5864,c_2654])).

tff(c_6079,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2866,c_6050])).

tff(c_6082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_24,c_2556,c_6079])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:17:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.16/1.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.16/2.00  
% 5.16/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.16/2.00  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.16/2.00  
% 5.16/2.00  %Foreground sorts:
% 5.16/2.00  
% 5.16/2.00  
% 5.16/2.00  %Background operators:
% 5.16/2.00  
% 5.16/2.00  
% 5.16/2.00  %Foreground operators:
% 5.16/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.16/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.16/2.00  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.16/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.16/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.16/2.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.16/2.00  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.16/2.00  tff('#skF_2', type, '#skF_2': $i).
% 5.16/2.00  tff('#skF_1', type, '#skF_1': $i).
% 5.16/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.16/2.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.16/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.16/2.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.16/2.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.16/2.00  
% 5.16/2.02  tff(f_75, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 5.16/2.02  tff(f_52, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.16/2.02  tff(f_41, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.16/2.02  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.16/2.02  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.16/2.02  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 5.16/2.02  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.16/2.02  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.16/2.02  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 5.16/2.02  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.16/2.02  tff(f_49, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 5.16/2.02  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.16/2.02  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.16/2.02  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.16/2.02  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.16/2.02  tff(c_42, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.16/2.02  tff(c_104, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 5.16/2.02  tff(c_36, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.16/2.02  tff(c_187, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_104, c_36])).
% 5.16/2.02  tff(c_14, plain, (![A_11, B_12]: (r1_xboole_0(k4_xboole_0(A_11, B_12), B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.16/2.02  tff(c_113, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=A_33 | ~r1_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.16/2.02  tff(c_129, plain, (![A_11, B_12]: (k4_xboole_0(k4_xboole_0(A_11, B_12), B_12)=k4_xboole_0(A_11, B_12))), inference(resolution, [status(thm)], [c_14, c_113])).
% 5.16/2.02  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.16/2.02  tff(c_543, plain, (![B_65, A_66]: (k3_xboole_0(k1_relat_1(B_65), A_66)=k1_relat_1(k7_relat_1(B_65, A_66)) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.16/2.02  tff(c_1822, plain, (![B_91, B_92]: (k3_xboole_0(B_91, k1_relat_1(B_92))=k1_relat_1(k7_relat_1(B_92, B_91)) | ~v1_relat_1(B_92))), inference(superposition, [status(thm), theory('equality')], [c_2, c_543])).
% 5.16/2.02  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.16/2.02  tff(c_107, plain, (r1_xboole_0('#skF_1', k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_104, c_4])).
% 5.16/2.02  tff(c_126, plain, (k4_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_107, c_113])).
% 5.16/2.02  tff(c_352, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k4_xboole_0(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.16/2.02  tff(c_402, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_126, c_352])).
% 5.16/2.02  tff(c_1841, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k4_xboole_0('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1822, c_402])).
% 5.16/2.02  tff(c_1902, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k4_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1841])).
% 5.16/2.02  tff(c_211, plain, (![B_44, A_45]: (r1_tarski(k1_relat_1(k7_relat_1(B_44, A_45)), A_45) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.16/2.02  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.16/2.02  tff(c_215, plain, (![B_44, A_45]: (k4_xboole_0(k1_relat_1(k7_relat_1(B_44, A_45)), A_45)=k1_xboole_0 | ~v1_relat_1(B_44))), inference(resolution, [status(thm)], [c_211, c_8])).
% 5.16/2.02  tff(c_1916, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_1'), '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1902, c_215])).
% 5.16/2.02  tff(c_1926, plain, (k4_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_129, c_1916])).
% 5.16/2.02  tff(c_1930, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1926, c_1902])).
% 5.16/2.02  tff(c_20, plain, (![A_15, B_16]: (v1_relat_1(k7_relat_1(A_15, B_16)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.16/2.02  tff(c_95, plain, (![A_32]: (k1_relat_1(A_32)!=k1_xboole_0 | k1_xboole_0=A_32 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.16/2.02  tff(c_2543, plain, (![A_100, B_101]: (k1_relat_1(k7_relat_1(A_100, B_101))!=k1_xboole_0 | k7_relat_1(A_100, B_101)=k1_xboole_0 | ~v1_relat_1(A_100))), inference(resolution, [status(thm)], [c_20, c_95])).
% 5.16/2.02  tff(c_2549, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1930, c_2543])).
% 5.16/2.02  tff(c_2553, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2549])).
% 5.16/2.02  tff(c_2555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_187, c_2553])).
% 5.16/2.02  tff(c_2556, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 5.16/2.02  tff(c_2844, plain, (![B_126, A_127]: (k3_xboole_0(k1_relat_1(B_126), A_127)=k1_relat_1(k7_relat_1(B_126, A_127)) | ~v1_relat_1(B_126))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.16/2.02  tff(c_2866, plain, (![A_127, B_126]: (k3_xboole_0(A_127, k1_relat_1(B_126))=k1_relat_1(k7_relat_1(B_126, A_127)) | ~v1_relat_1(B_126))), inference(superposition, [status(thm), theory('equality')], [c_2844, c_2])).
% 5.16/2.02  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.16/2.02  tff(c_2656, plain, (![A_115, B_116]: (k4_xboole_0(A_115, k4_xboole_0(A_115, B_116))=k3_xboole_0(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.16/2.02  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.16/2.02  tff(c_2659, plain, (![A_115, B_116]: (k4_xboole_0(A_115, k3_xboole_0(A_115, B_116))=k3_xboole_0(A_115, k4_xboole_0(A_115, B_116)))), inference(superposition, [status(thm), theory('equality')], [c_2656, c_12])).
% 5.16/2.02  tff(c_4048, plain, (![A_115, B_116]: (k3_xboole_0(A_115, k4_xboole_0(A_115, B_116))=k4_xboole_0(A_115, B_116))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2659])).
% 5.16/2.02  tff(c_2561, plain, (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2556, c_20])).
% 5.16/2.02  tff(c_2565, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2561])).
% 5.16/2.02  tff(c_2884, plain, (![A_127]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_127))=k3_xboole_0(k1_xboole_0, A_127) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2844])).
% 5.16/2.02  tff(c_2974, plain, (![A_128]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_128))=k3_xboole_0(k1_xboole_0, A_128))), inference(demodulation, [status(thm), theory('equality')], [c_2565, c_2884])).
% 5.16/2.02  tff(c_30, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(k7_relat_1(B_19, A_18)), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.16/2.02  tff(c_2983, plain, (![A_128]: (r1_tarski(k3_xboole_0(k1_xboole_0, A_128), A_128) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2974, c_30])).
% 5.16/2.02  tff(c_2991, plain, (![A_129]: (r1_tarski(k3_xboole_0(k1_xboole_0, A_129), A_129))), inference(demodulation, [status(thm), theory('equality')], [c_2565, c_2983])).
% 5.16/2.02  tff(c_3007, plain, (![A_129]: (k4_xboole_0(k3_xboole_0(k1_xboole_0, A_129), A_129)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2991, c_8])).
% 5.16/2.02  tff(c_2595, plain, (![A_105, B_106]: (k4_xboole_0(A_105, B_106)=A_105 | ~r1_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.16/2.02  tff(c_3325, plain, (![A_137, B_138]: (k4_xboole_0(k4_xboole_0(A_137, B_138), B_138)=k4_xboole_0(A_137, B_138))), inference(resolution, [status(thm)], [c_14, c_2595])).
% 5.16/2.02  tff(c_3369, plain, (![A_129]: (k4_xboole_0(k3_xboole_0(k1_xboole_0, A_129), A_129)=k4_xboole_0(k1_xboole_0, A_129))), inference(superposition, [status(thm), theory('equality')], [c_3007, c_3325])).
% 5.16/2.02  tff(c_3405, plain, (![A_139]: (k4_xboole_0(k1_xboole_0, A_139)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3007, c_3369])).
% 5.16/2.02  tff(c_3485, plain, (![B_140]: (k3_xboole_0(k1_xboole_0, B_140)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3405, c_12])).
% 5.16/2.02  tff(c_3535, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_3485])).
% 5.16/2.02  tff(c_3219, plain, (![A_133]: (k4_xboole_0(k3_xboole_0(k1_xboole_0, A_133), A_133)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2991, c_8])).
% 5.16/2.02  tff(c_85, plain, (![B_26, A_27]: (r1_xboole_0(B_26, A_27) | ~r1_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.16/2.02  tff(c_88, plain, (![B_12, A_11]: (r1_xboole_0(B_12, k4_xboole_0(A_11, B_12)))), inference(resolution, [status(thm)], [c_14, c_85])).
% 5.16/2.02  tff(c_2602, plain, (![B_12, A_11]: (k4_xboole_0(B_12, k4_xboole_0(A_11, B_12))=B_12)), inference(resolution, [status(thm)], [c_88, c_2595])).
% 5.16/2.02  tff(c_3286, plain, (![A_136]: (k4_xboole_0(A_136, k1_xboole_0)=A_136)), inference(superposition, [status(thm), theory('equality')], [c_3219, c_2602])).
% 5.16/2.02  tff(c_3302, plain, (![A_136]: (k4_xboole_0(A_136, A_136)=k3_xboole_0(A_136, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3286, c_12])).
% 5.16/2.02  tff(c_3739, plain, (![A_136]: (k4_xboole_0(A_136, A_136)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3535, c_3302])).
% 5.16/2.02  tff(c_4049, plain, (![A_155, B_156]: (k3_xboole_0(A_155, k4_xboole_0(A_155, B_156))=k4_xboole_0(A_155, B_156))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2659])).
% 5.16/2.02  tff(c_2700, plain, (![A_118, B_119]: (k4_xboole_0(A_118, k3_xboole_0(A_118, B_119))=k4_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.16/2.02  tff(c_2724, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2700])).
% 5.16/2.02  tff(c_4065, plain, (![A_155, B_156]: (k4_xboole_0(k4_xboole_0(A_155, B_156), k4_xboole_0(A_155, B_156))=k4_xboole_0(k4_xboole_0(A_155, B_156), A_155))), inference(superposition, [status(thm), theory('equality')], [c_4049, c_2724])).
% 5.16/2.02  tff(c_4126, plain, (![A_155, B_156]: (k4_xboole_0(k4_xboole_0(A_155, B_156), A_155)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3739, c_4065])).
% 5.16/2.02  tff(c_2632, plain, (![A_111, B_112]: (r1_xboole_0(A_111, B_112) | k4_xboole_0(A_111, B_112)!=A_111)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.16/2.02  tff(c_2644, plain, (![B_113, A_114]: (r1_xboole_0(B_113, A_114) | k4_xboole_0(A_114, B_113)!=A_114)), inference(resolution, [status(thm)], [c_2632, c_4])).
% 5.16/2.02  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.16/2.02  tff(c_4894, plain, (![B_172, A_173]: (k4_xboole_0(B_172, A_173)=B_172 | k4_xboole_0(A_173, B_172)!=A_173)), inference(resolution, [status(thm)], [c_2644, c_16])).
% 5.16/2.02  tff(c_4900, plain, (![A_155, B_156]: (k4_xboole_0(A_155, k4_xboole_0(A_155, B_156))=A_155 | k4_xboole_0(A_155, B_156)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4126, c_4894])).
% 5.16/2.02  tff(c_5471, plain, (![A_182, B_183]: (k3_xboole_0(A_182, B_183)=A_182 | k4_xboole_0(A_182, B_183)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4900])).
% 5.16/2.02  tff(c_5507, plain, (![A_9, B_10]: (k3_xboole_0(A_9, k4_xboole_0(A_9, B_10))=A_9 | k3_xboole_0(A_9, B_10)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_5471])).
% 5.16/2.02  tff(c_5864, plain, (![A_188, B_189]: (k4_xboole_0(A_188, B_189)=A_188 | k3_xboole_0(A_188, B_189)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4048, c_5507])).
% 5.16/2.02  tff(c_2557, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 5.16/2.02  tff(c_2654, plain, (k4_xboole_0('#skF_1', k1_relat_1('#skF_2'))!='#skF_1'), inference(resolution, [status(thm)], [c_2644, c_2557])).
% 5.16/2.02  tff(c_6050, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5864, c_2654])).
% 5.16/2.02  tff(c_6079, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2866, c_6050])).
% 5.16/2.02  tff(c_6082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_24, c_2556, c_6079])).
% 5.16/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.16/2.02  
% 5.16/2.02  Inference rules
% 5.16/2.02  ----------------------
% 5.16/2.02  #Ref     : 0
% 5.16/2.02  #Sup     : 1486
% 5.16/2.02  #Fact    : 0
% 5.16/2.02  #Define  : 0
% 5.16/2.02  #Split   : 9
% 5.16/2.02  #Chain   : 0
% 5.16/2.02  #Close   : 0
% 5.16/2.02  
% 5.16/2.02  Ordering : KBO
% 5.16/2.02  
% 5.16/2.02  Simplification rules
% 5.16/2.02  ----------------------
% 5.16/2.02  #Subsume      : 62
% 5.16/2.02  #Demod        : 1472
% 5.16/2.02  #Tautology    : 1064
% 5.16/2.02  #SimpNegUnit  : 4
% 5.16/2.02  #BackRed      : 27
% 5.16/2.02  
% 5.16/2.02  #Partial instantiations: 0
% 5.16/2.02  #Strategies tried      : 1
% 5.16/2.02  
% 5.16/2.02  Timing (in seconds)
% 5.16/2.02  ----------------------
% 5.16/2.02  Preprocessing        : 0.30
% 5.16/2.02  Parsing              : 0.16
% 5.16/2.02  CNF conversion       : 0.02
% 5.16/2.02  Main loop            : 0.88
% 5.16/2.02  Inferencing          : 0.27
% 5.16/2.02  Reduction            : 0.37
% 5.16/2.02  Demodulation         : 0.30
% 5.16/2.02  BG Simplification    : 0.03
% 5.16/2.02  Subsumption          : 0.14
% 5.16/2.02  Abstraction          : 0.04
% 5.16/2.02  MUC search           : 0.00
% 5.16/2.02  Cooper               : 0.00
% 5.16/2.02  Total                : 1.22
% 5.16/2.02  Index Insertion      : 0.00
% 5.16/2.02  Index Deletion       : 0.00
% 5.16/2.02  Index Matching       : 0.00
% 5.16/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
