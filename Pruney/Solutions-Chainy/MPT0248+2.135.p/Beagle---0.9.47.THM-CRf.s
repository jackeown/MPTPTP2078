%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:23 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 216 expanded)
%              Number of leaves         :   32 (  84 expanded)
%              Depth                    :   15
%              Number of atoms          :   91 ( 321 expanded)
%              Number of equality atoms :   73 ( 302 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(c_44,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_96,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_42,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_95,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_81,plain,(
    ! [A_52,B_53] : r1_tarski(A_52,k2_xboole_0(A_52,B_53)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_84,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_81])).

tff(c_354,plain,(
    ! [B_76,A_77] :
      ( k1_tarski(B_76) = A_77
      | k1_xboole_0 = A_77
      | ~ r1_tarski(A_77,k1_tarski(B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_360,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_84,c_354])).

tff(c_374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_95,c_360])).

tff(c_375,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_376,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_379,plain,(
    ! [A_5] : r1_tarski('#skF_2',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_6])).

tff(c_413,plain,(
    ! [A_82,B_83] :
      ( k2_xboole_0(A_82,B_83) = B_83
      | ~ r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_427,plain,(
    ! [A_5] : k2_xboole_0('#skF_2',A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_379,c_413])).

tff(c_439,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_48])).

tff(c_441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_375,c_439])).

tff(c_442,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_443,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_46,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_470,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_443,c_46])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_672,plain,(
    ! [B_102,A_103] :
      ( k1_tarski(B_102) = A_103
      | k1_xboole_0 = A_103
      | ~ r1_tarski(A_103,k1_tarski(B_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_678,plain,(
    ! [A_103] :
      ( k1_tarski('#skF_1') = A_103
      | k1_xboole_0 = A_103
      | ~ r1_tarski(A_103,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_672])).

tff(c_693,plain,(
    ! [A_104] :
      ( A_104 = '#skF_2'
      | k1_xboole_0 = A_104
      | ~ r1_tarski(A_104,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_678])).

tff(c_709,plain,(
    ! [B_7] :
      ( k4_xboole_0('#skF_2',B_7) = '#skF_2'
      | k4_xboole_0('#skF_2',B_7) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_693])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] : k5_xboole_0(k5_xboole_0(A_11,B_12),C_13) = k5_xboole_0(A_11,k5_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_445,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_48])).

tff(c_1050,plain,(
    ! [A_119,B_120] : k5_xboole_0(k5_xboole_0(A_119,B_120),k2_xboole_0(A_119,B_120)) = k3_xboole_0(A_119,B_120) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1120,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_3'),'#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_1050])).

tff(c_1246,plain,(
    k5_xboole_0('#skF_2',k5_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1120])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_952,plain,(
    ! [A_114,B_115,C_116] : k5_xboole_0(k5_xboole_0(A_114,B_115),C_116) = k5_xboole_0(A_114,k5_xboole_0(B_115,C_116)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1413,plain,(
    ! [A_127,C_128] : k5_xboole_0(A_127,k5_xboole_0(A_127,C_128)) = k5_xboole_0(k1_xboole_0,C_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_952])).

tff(c_1511,plain,(
    ! [A_14] : k5_xboole_0(k1_xboole_0,A_14) = k5_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1413])).

tff(c_1535,plain,(
    ! [A_14] : k5_xboole_0(k1_xboole_0,A_14) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1511])).

tff(c_993,plain,(
    ! [A_14,C_116] : k5_xboole_0(A_14,k5_xboole_0(A_14,C_116)) = k5_xboole_0(k1_xboole_0,C_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_952])).

tff(c_1672,plain,(
    ! [A_137,C_138] : k5_xboole_0(A_137,k5_xboole_0(A_137,C_138)) = C_138 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1535,c_993])).

tff(c_1722,plain,(
    k5_xboole_0('#skF_2',k3_xboole_0('#skF_2','#skF_3')) = k5_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1246,c_1672])).

tff(c_1768,plain,(
    k5_xboole_0('#skF_3','#skF_2') = k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1722])).

tff(c_1545,plain,(
    ! [A_14,C_116] : k5_xboole_0(A_14,k5_xboole_0(A_14,C_116)) = C_116 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1535,c_993])).

tff(c_1884,plain,(
    k5_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1768,c_1545])).

tff(c_1936,plain,
    ( k5_xboole_0('#skF_3',k1_xboole_0) = '#skF_2'
    | k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_709,c_1884])).

tff(c_1940,plain,
    ( '#skF_2' = '#skF_3'
    | k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1936])).

tff(c_1941,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_470,c_1940])).

tff(c_1942,plain,(
    k5_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1941,c_1884])).

tff(c_970,plain,(
    ! [A_114,B_115] : k5_xboole_0(A_114,k5_xboole_0(B_115,k5_xboole_0(A_114,B_115))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_952,c_16])).

tff(c_1734,plain,(
    ! [B_115,A_114] : k5_xboole_0(B_115,k5_xboole_0(A_114,B_115)) = k5_xboole_0(A_114,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_970,c_1672])).

tff(c_1769,plain,(
    ! [B_115,A_114] : k5_xboole_0(B_115,k5_xboole_0(A_114,B_115)) = A_114 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1734])).

tff(c_1969,plain,(
    k5_xboole_0('#skF_2','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1942,c_1769])).

tff(c_2007,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1969,c_16])).

tff(c_2015,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_442,c_2007])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.75/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.68  
% 3.75/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.68  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.75/1.68  
% 3.75/1.68  %Foreground sorts:
% 3.75/1.68  
% 3.75/1.68  
% 3.75/1.68  %Background operators:
% 3.75/1.68  
% 3.75/1.68  
% 3.75/1.68  %Foreground operators:
% 3.75/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.75/1.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.75/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.75/1.68  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.75/1.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.75/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.75/1.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.75/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.75/1.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.75/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.75/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.75/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.75/1.68  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.75/1.68  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.75/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.68  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.75/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.75/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.75/1.68  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.75/1.68  
% 3.97/1.70  tff(f_86, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.97/1.70  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.97/1.70  tff(f_65, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.97/1.70  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.97/1.70  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.97/1.70  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.97/1.70  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.97/1.70  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.97/1.70  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.97/1.70  tff(f_45, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.97/1.70  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.97/1.70  tff(c_44, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.97/1.70  tff(c_96, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_44])).
% 3.97/1.70  tff(c_42, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.97/1.70  tff(c_95, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_42])).
% 3.97/1.70  tff(c_48, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.97/1.70  tff(c_81, plain, (![A_52, B_53]: (r1_tarski(A_52, k2_xboole_0(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.97/1.70  tff(c_84, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_81])).
% 3.97/1.70  tff(c_354, plain, (![B_76, A_77]: (k1_tarski(B_76)=A_77 | k1_xboole_0=A_77 | ~r1_tarski(A_77, k1_tarski(B_76)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.97/1.70  tff(c_360, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_84, c_354])).
% 3.97/1.70  tff(c_374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_95, c_360])).
% 3.97/1.70  tff(c_375, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 3.97/1.70  tff(c_376, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_44])).
% 3.97/1.70  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.97/1.70  tff(c_379, plain, (![A_5]: (r1_tarski('#skF_2', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_376, c_6])).
% 3.97/1.70  tff(c_413, plain, (![A_82, B_83]: (k2_xboole_0(A_82, B_83)=B_83 | ~r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.97/1.70  tff(c_427, plain, (![A_5]: (k2_xboole_0('#skF_2', A_5)=A_5)), inference(resolution, [status(thm)], [c_379, c_413])).
% 3.97/1.70  tff(c_439, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_427, c_48])).
% 3.97/1.70  tff(c_441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_375, c_439])).
% 3.97/1.70  tff(c_442, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_42])).
% 3.97/1.70  tff(c_443, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_42])).
% 3.97/1.70  tff(c_46, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.97/1.70  tff(c_470, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_443, c_443, c_46])).
% 3.97/1.70  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.97/1.70  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.97/1.70  tff(c_672, plain, (![B_102, A_103]: (k1_tarski(B_102)=A_103 | k1_xboole_0=A_103 | ~r1_tarski(A_103, k1_tarski(B_102)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.97/1.70  tff(c_678, plain, (![A_103]: (k1_tarski('#skF_1')=A_103 | k1_xboole_0=A_103 | ~r1_tarski(A_103, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_443, c_672])).
% 3.97/1.70  tff(c_693, plain, (![A_104]: (A_104='#skF_2' | k1_xboole_0=A_104 | ~r1_tarski(A_104, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_443, c_678])).
% 3.97/1.70  tff(c_709, plain, (![B_7]: (k4_xboole_0('#skF_2', B_7)='#skF_2' | k4_xboole_0('#skF_2', B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_693])).
% 3.97/1.70  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.97/1.70  tff(c_14, plain, (![A_11, B_12, C_13]: (k5_xboole_0(k5_xboole_0(A_11, B_12), C_13)=k5_xboole_0(A_11, k5_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.97/1.70  tff(c_445, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_443, c_48])).
% 3.97/1.70  tff(c_1050, plain, (![A_119, B_120]: (k5_xboole_0(k5_xboole_0(A_119, B_120), k2_xboole_0(A_119, B_120))=k3_xboole_0(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.97/1.70  tff(c_1120, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_3'), '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_445, c_1050])).
% 3.97/1.70  tff(c_1246, plain, (k5_xboole_0('#skF_2', k5_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_1120])).
% 3.97/1.70  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.97/1.70  tff(c_952, plain, (![A_114, B_115, C_116]: (k5_xboole_0(k5_xboole_0(A_114, B_115), C_116)=k5_xboole_0(A_114, k5_xboole_0(B_115, C_116)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.97/1.70  tff(c_1413, plain, (![A_127, C_128]: (k5_xboole_0(A_127, k5_xboole_0(A_127, C_128))=k5_xboole_0(k1_xboole_0, C_128))), inference(superposition, [status(thm), theory('equality')], [c_16, c_952])).
% 3.97/1.70  tff(c_1511, plain, (![A_14]: (k5_xboole_0(k1_xboole_0, A_14)=k5_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1413])).
% 3.97/1.70  tff(c_1535, plain, (![A_14]: (k5_xboole_0(k1_xboole_0, A_14)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1511])).
% 3.97/1.70  tff(c_993, plain, (![A_14, C_116]: (k5_xboole_0(A_14, k5_xboole_0(A_14, C_116))=k5_xboole_0(k1_xboole_0, C_116))), inference(superposition, [status(thm), theory('equality')], [c_16, c_952])).
% 3.97/1.70  tff(c_1672, plain, (![A_137, C_138]: (k5_xboole_0(A_137, k5_xboole_0(A_137, C_138))=C_138)), inference(demodulation, [status(thm), theory('equality')], [c_1535, c_993])).
% 3.97/1.70  tff(c_1722, plain, (k5_xboole_0('#skF_2', k3_xboole_0('#skF_2', '#skF_3'))=k5_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1246, c_1672])).
% 3.97/1.70  tff(c_1768, plain, (k5_xboole_0('#skF_3', '#skF_2')=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1722])).
% 3.97/1.70  tff(c_1545, plain, (![A_14, C_116]: (k5_xboole_0(A_14, k5_xboole_0(A_14, C_116))=C_116)), inference(demodulation, [status(thm), theory('equality')], [c_1535, c_993])).
% 3.97/1.70  tff(c_1884, plain, (k5_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1768, c_1545])).
% 3.97/1.70  tff(c_1936, plain, (k5_xboole_0('#skF_3', k1_xboole_0)='#skF_2' | k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_709, c_1884])).
% 3.97/1.70  tff(c_1940, plain, ('#skF_2'='#skF_3' | k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1936])).
% 3.97/1.70  tff(c_1941, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_470, c_1940])).
% 3.97/1.70  tff(c_1942, plain, (k5_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1941, c_1884])).
% 3.97/1.70  tff(c_970, plain, (![A_114, B_115]: (k5_xboole_0(A_114, k5_xboole_0(B_115, k5_xboole_0(A_114, B_115)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_952, c_16])).
% 3.97/1.70  tff(c_1734, plain, (![B_115, A_114]: (k5_xboole_0(B_115, k5_xboole_0(A_114, B_115))=k5_xboole_0(A_114, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_970, c_1672])).
% 3.97/1.70  tff(c_1769, plain, (![B_115, A_114]: (k5_xboole_0(B_115, k5_xboole_0(A_114, B_115))=A_114)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1734])).
% 3.97/1.70  tff(c_1969, plain, (k5_xboole_0('#skF_2', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1942, c_1769])).
% 3.97/1.70  tff(c_2007, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1969, c_16])).
% 3.97/1.70  tff(c_2015, plain, $false, inference(negUnitSimplification, [status(thm)], [c_442, c_2007])).
% 3.97/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.70  
% 3.97/1.70  Inference rules
% 3.97/1.70  ----------------------
% 3.97/1.70  #Ref     : 0
% 3.97/1.70  #Sup     : 501
% 3.97/1.70  #Fact    : 1
% 3.97/1.70  #Define  : 0
% 3.97/1.70  #Split   : 3
% 3.97/1.70  #Chain   : 0
% 3.97/1.70  #Close   : 0
% 3.97/1.70  
% 3.97/1.70  Ordering : KBO
% 3.97/1.70  
% 3.97/1.70  Simplification rules
% 3.97/1.70  ----------------------
% 3.97/1.70  #Subsume      : 7
% 3.97/1.70  #Demod        : 315
% 3.97/1.70  #Tautology    : 333
% 3.97/1.70  #SimpNegUnit  : 10
% 3.97/1.70  #BackRed      : 18
% 3.97/1.70  
% 3.97/1.70  #Partial instantiations: 0
% 3.97/1.70  #Strategies tried      : 1
% 3.97/1.70  
% 3.97/1.70  Timing (in seconds)
% 3.97/1.70  ----------------------
% 3.97/1.70  Preprocessing        : 0.34
% 3.97/1.70  Parsing              : 0.18
% 3.97/1.70  CNF conversion       : 0.02
% 3.97/1.70  Main loop            : 0.58
% 3.97/1.70  Inferencing          : 0.21
% 3.97/1.70  Reduction            : 0.22
% 3.97/1.70  Demodulation         : 0.17
% 3.97/1.70  BG Simplification    : 0.03
% 3.97/1.70  Subsumption          : 0.07
% 3.97/1.70  Abstraction          : 0.03
% 3.97/1.70  MUC search           : 0.00
% 3.97/1.70  Cooper               : 0.00
% 3.97/1.70  Total                : 0.96
% 3.97/1.70  Index Insertion      : 0.00
% 3.97/1.70  Index Deletion       : 0.00
% 3.97/1.70  Index Matching       : 0.00
% 3.97/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
