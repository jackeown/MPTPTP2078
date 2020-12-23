%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:57 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 176 expanded)
%              Number of leaves         :   43 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 240 expanded)
%              Number of equality atoms :   50 ( 113 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_1 > #skF_3 > #skF_8 > #skF_7 > #skF_9 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_56,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_75,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    ! [A_43] :
      ( r2_hidden('#skF_2'(A_43),A_43)
      | v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_77,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(k1_tarski(A_88),B_89)
      | ~ r2_hidden(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_83,plain,(
    ! [A_90] :
      ( k1_tarski(A_90) = k1_xboole_0
      | ~ r2_hidden(A_90,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_77,c_6])).

tff(c_94,plain,
    ( k1_tarski('#skF_2'(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_40,c_83])).

tff(c_124,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_54,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_9'(A_80,B_81),k2_relat_1(B_81))
      | ~ r2_hidden(A_80,k1_relat_1(B_81))
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_299,plain,(
    ! [A_133,C_134] :
      ( r2_hidden(k4_tarski('#skF_8'(A_133,k2_relat_1(A_133),C_134),C_134),A_133)
      | ~ r2_hidden(C_134,k2_relat_1(A_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_141,plain,(
    ! [A_102,B_103] : k3_xboole_0(k1_tarski(A_102),k2_tarski(A_102,B_103)) = k1_tarski(A_102) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_150,plain,(
    ! [A_7] : k3_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_tarski(A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_141])).

tff(c_168,plain,(
    ! [A_105,B_106] : k5_xboole_0(A_105,k3_xboole_0(A_105,B_106)) = k4_xboole_0(A_105,B_106) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_177,plain,(
    ! [A_7] : k5_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k4_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_168])).

tff(c_186,plain,(
    ! [A_7] : k4_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_177])).

tff(c_30,plain,(
    ! [B_40] : k4_xboole_0(k1_tarski(B_40),k1_tarski(B_40)) != k1_tarski(B_40) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_198,plain,(
    ! [B_40] : k1_tarski(B_40) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_30])).

tff(c_82,plain,(
    ! [A_88] :
      ( k1_tarski(A_88) = k1_xboole_0
      | ~ r2_hidden(A_88,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_77,c_6])).

tff(c_206,plain,(
    ! [A_88] : ~ r2_hidden(A_88,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_82])).

tff(c_309,plain,(
    ! [C_135] : ~ r2_hidden(C_135,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_299,c_206])).

tff(c_317,plain,(
    ! [A_80] :
      ( ~ r2_hidden(A_80,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_54,c_309])).

tff(c_362,plain,(
    ! [A_138] : ~ r2_hidden(A_138,k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_317])).

tff(c_370,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_362])).

tff(c_379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_370])).

tff(c_380,plain,(
    k1_tarski('#skF_2'(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_397,plain,(
    ! [B_141] : k4_xboole_0(k1_tarski(B_141),k1_tarski(B_141)) != k1_tarski(B_141) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_400,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_2'(k1_xboole_0))) != k1_tarski('#skF_2'(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_397])).

tff(c_404,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_380,c_400])).

tff(c_429,plain,(
    ! [A_148,B_149] : k3_xboole_0(k1_tarski(A_148),k2_tarski(A_148,B_149)) = k1_tarski(A_148) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_445,plain,(
    ! [A_150] : k3_xboole_0(k1_tarski(A_150),k1_tarski(A_150)) = k1_tarski(A_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_429])).

tff(c_457,plain,(
    k3_xboole_0(k1_xboole_0,k1_tarski('#skF_2'(k1_xboole_0))) = k1_tarski('#skF_2'(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_445])).

tff(c_466,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_380,c_457])).

tff(c_487,plain,(
    ! [A_152,B_153] : k5_xboole_0(A_152,k3_xboole_0(A_152,B_153)) = k4_xboole_0(A_152,B_153) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_496,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_487])).

tff(c_508,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_496])).

tff(c_510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_404,c_508])).

tff(c_511,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_729,plain,(
    ! [A_195,C_196] :
      ( r2_hidden(k4_tarski('#skF_8'(A_195,k2_relat_1(A_195),C_196),C_196),A_195)
      | ~ r2_hidden(C_196,k2_relat_1(A_195)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_582,plain,(
    ! [A_169,B_170] : k3_xboole_0(k1_tarski(A_169),k2_tarski(A_169,B_170)) = k1_tarski(A_169) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_591,plain,(
    ! [A_7] : k3_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_tarski(A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_582])).

tff(c_619,plain,(
    ! [A_173,B_174] : k5_xboole_0(A_173,k3_xboole_0(A_173,B_174)) = k4_xboole_0(A_173,B_174) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_628,plain,(
    ! [A_7] : k5_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k4_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_619])).

tff(c_637,plain,(
    ! [A_7] : k4_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_628])).

tff(c_639,plain,(
    ! [B_40] : k1_tarski(B_40) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_30])).

tff(c_518,plain,(
    ! [A_155,B_156] :
      ( r1_tarski(k1_tarski(A_155),B_156)
      | ~ r2_hidden(A_155,B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_523,plain,(
    ! [A_155] :
      ( k1_tarski(A_155) = k1_xboole_0
      | ~ r2_hidden(A_155,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_518,c_6])).

tff(c_666,plain,(
    ! [A_155] : ~ r2_hidden(A_155,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_639,c_523])).

tff(c_752,plain,(
    ! [C_199] : ~ r2_hidden(C_199,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_729,c_666])).

tff(c_764,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_752])).

tff(c_776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_511,c_764])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.39  
% 2.84/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.39  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_1 > #skF_3 > #skF_8 > #skF_7 > #skF_9 > #skF_5 > #skF_4
% 2.84/1.39  
% 2.84/1.39  %Foreground sorts:
% 2.84/1.39  
% 2.84/1.39  
% 2.84/1.39  %Background operators:
% 2.84/1.39  
% 2.84/1.39  
% 2.84/1.39  %Foreground operators:
% 2.84/1.39  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.84/1.39  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.84/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.84/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.84/1.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.84/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.84/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.84/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.84/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.84/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.84/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.84/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.84/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.84/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.84/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.84/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.84/1.40  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 2.84/1.40  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.84/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.40  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 2.84/1.40  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.84/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.84/1.40  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.84/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.84/1.40  
% 2.84/1.41  tff(f_99, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.84/1.41  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.84/1.41  tff(f_78, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.84/1.41  tff(f_59, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.84/1.41  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.84/1.41  tff(f_95, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_relat_1)).
% 2.84/1.41  tff(f_86, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.84/1.41  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.84/1.41  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.84/1.41  tff(f_61, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.84/1.41  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.84/1.41  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.84/1.41  tff(c_56, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.84/1.41  tff(c_75, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 2.84/1.41  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.84/1.41  tff(c_40, plain, (![A_43]: (r2_hidden('#skF_2'(A_43), A_43) | v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.84/1.41  tff(c_77, plain, (![A_88, B_89]: (r1_tarski(k1_tarski(A_88), B_89) | ~r2_hidden(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.84/1.41  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.84/1.41  tff(c_83, plain, (![A_90]: (k1_tarski(A_90)=k1_xboole_0 | ~r2_hidden(A_90, k1_xboole_0))), inference(resolution, [status(thm)], [c_77, c_6])).
% 2.84/1.41  tff(c_94, plain, (k1_tarski('#skF_2'(k1_xboole_0))=k1_xboole_0 | v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_83])).
% 2.84/1.41  tff(c_124, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_94])).
% 2.84/1.41  tff(c_54, plain, (![A_80, B_81]: (r2_hidden('#skF_9'(A_80, B_81), k2_relat_1(B_81)) | ~r2_hidden(A_80, k1_relat_1(B_81)) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.84/1.41  tff(c_299, plain, (![A_133, C_134]: (r2_hidden(k4_tarski('#skF_8'(A_133, k2_relat_1(A_133), C_134), C_134), A_133) | ~r2_hidden(C_134, k2_relat_1(A_133)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.84/1.41  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.84/1.41  tff(c_10, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.84/1.41  tff(c_141, plain, (![A_102, B_103]: (k3_xboole_0(k1_tarski(A_102), k2_tarski(A_102, B_103))=k1_tarski(A_102))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.84/1.41  tff(c_150, plain, (![A_7]: (k3_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_tarski(A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_141])).
% 2.84/1.41  tff(c_168, plain, (![A_105, B_106]: (k5_xboole_0(A_105, k3_xboole_0(A_105, B_106))=k4_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.41  tff(c_177, plain, (![A_7]: (k5_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k4_xboole_0(k1_tarski(A_7), k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_150, c_168])).
% 2.84/1.41  tff(c_186, plain, (![A_7]: (k4_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_177])).
% 2.84/1.41  tff(c_30, plain, (![B_40]: (k4_xboole_0(k1_tarski(B_40), k1_tarski(B_40))!=k1_tarski(B_40))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.84/1.41  tff(c_198, plain, (![B_40]: (k1_tarski(B_40)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_186, c_30])).
% 2.84/1.41  tff(c_82, plain, (![A_88]: (k1_tarski(A_88)=k1_xboole_0 | ~r2_hidden(A_88, k1_xboole_0))), inference(resolution, [status(thm)], [c_77, c_6])).
% 2.84/1.41  tff(c_206, plain, (![A_88]: (~r2_hidden(A_88, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_198, c_82])).
% 2.84/1.41  tff(c_309, plain, (![C_135]: (~r2_hidden(C_135, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_299, c_206])).
% 2.84/1.41  tff(c_317, plain, (![A_80]: (~r2_hidden(A_80, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_54, c_309])).
% 2.84/1.41  tff(c_362, plain, (![A_138]: (~r2_hidden(A_138, k1_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_317])).
% 2.84/1.41  tff(c_370, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_362])).
% 2.84/1.41  tff(c_379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_370])).
% 2.84/1.41  tff(c_380, plain, (k1_tarski('#skF_2'(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_94])).
% 2.84/1.41  tff(c_397, plain, (![B_141]: (k4_xboole_0(k1_tarski(B_141), k1_tarski(B_141))!=k1_tarski(B_141))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.84/1.41  tff(c_400, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_2'(k1_xboole_0)))!=k1_tarski('#skF_2'(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_380, c_397])).
% 2.84/1.41  tff(c_404, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_380, c_380, c_400])).
% 2.84/1.41  tff(c_429, plain, (![A_148, B_149]: (k3_xboole_0(k1_tarski(A_148), k2_tarski(A_148, B_149))=k1_tarski(A_148))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.84/1.41  tff(c_445, plain, (![A_150]: (k3_xboole_0(k1_tarski(A_150), k1_tarski(A_150))=k1_tarski(A_150))), inference(superposition, [status(thm), theory('equality')], [c_10, c_429])).
% 2.84/1.41  tff(c_457, plain, (k3_xboole_0(k1_xboole_0, k1_tarski('#skF_2'(k1_xboole_0)))=k1_tarski('#skF_2'(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_380, c_445])).
% 2.84/1.41  tff(c_466, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_380, c_380, c_457])).
% 2.84/1.41  tff(c_487, plain, (![A_152, B_153]: (k5_xboole_0(A_152, k3_xboole_0(A_152, B_153))=k4_xboole_0(A_152, B_153))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.41  tff(c_496, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_466, c_487])).
% 2.84/1.41  tff(c_508, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_496])).
% 2.84/1.41  tff(c_510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_404, c_508])).
% 2.84/1.41  tff(c_511, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 2.84/1.41  tff(c_729, plain, (![A_195, C_196]: (r2_hidden(k4_tarski('#skF_8'(A_195, k2_relat_1(A_195), C_196), C_196), A_195) | ~r2_hidden(C_196, k2_relat_1(A_195)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.84/1.41  tff(c_582, plain, (![A_169, B_170]: (k3_xboole_0(k1_tarski(A_169), k2_tarski(A_169, B_170))=k1_tarski(A_169))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.84/1.41  tff(c_591, plain, (![A_7]: (k3_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_tarski(A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_582])).
% 2.84/1.41  tff(c_619, plain, (![A_173, B_174]: (k5_xboole_0(A_173, k3_xboole_0(A_173, B_174))=k4_xboole_0(A_173, B_174))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.41  tff(c_628, plain, (![A_7]: (k5_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k4_xboole_0(k1_tarski(A_7), k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_591, c_619])).
% 2.84/1.41  tff(c_637, plain, (![A_7]: (k4_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_628])).
% 2.84/1.41  tff(c_639, plain, (![B_40]: (k1_tarski(B_40)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_637, c_30])).
% 2.84/1.41  tff(c_518, plain, (![A_155, B_156]: (r1_tarski(k1_tarski(A_155), B_156) | ~r2_hidden(A_155, B_156))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.84/1.41  tff(c_523, plain, (![A_155]: (k1_tarski(A_155)=k1_xboole_0 | ~r2_hidden(A_155, k1_xboole_0))), inference(resolution, [status(thm)], [c_518, c_6])).
% 2.84/1.41  tff(c_666, plain, (![A_155]: (~r2_hidden(A_155, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_639, c_523])).
% 2.84/1.41  tff(c_752, plain, (![C_199]: (~r2_hidden(C_199, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_729, c_666])).
% 2.84/1.41  tff(c_764, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_752])).
% 2.84/1.41  tff(c_776, plain, $false, inference(negUnitSimplification, [status(thm)], [c_511, c_764])).
% 2.84/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.41  
% 2.84/1.41  Inference rules
% 2.84/1.41  ----------------------
% 2.84/1.41  #Ref     : 0
% 2.84/1.41  #Sup     : 159
% 2.84/1.41  #Fact    : 0
% 2.84/1.41  #Define  : 0
% 2.84/1.41  #Split   : 3
% 2.84/1.41  #Chain   : 0
% 2.84/1.41  #Close   : 0
% 2.84/1.41  
% 2.84/1.41  Ordering : KBO
% 2.84/1.41  
% 2.84/1.41  Simplification rules
% 2.84/1.41  ----------------------
% 2.84/1.41  #Subsume      : 4
% 2.84/1.41  #Demod        : 41
% 2.84/1.41  #Tautology    : 112
% 2.84/1.41  #SimpNegUnit  : 10
% 2.84/1.41  #BackRed      : 5
% 2.84/1.41  
% 2.84/1.41  #Partial instantiations: 0
% 2.84/1.41  #Strategies tried      : 1
% 2.84/1.41  
% 2.84/1.41  Timing (in seconds)
% 2.84/1.41  ----------------------
% 2.84/1.42  Preprocessing        : 0.33
% 2.84/1.42  Parsing              : 0.17
% 2.84/1.42  CNF conversion       : 0.02
% 2.84/1.42  Main loop            : 0.32
% 2.84/1.42  Inferencing          : 0.14
% 2.84/1.42  Reduction            : 0.10
% 2.84/1.42  Demodulation         : 0.07
% 2.84/1.42  BG Simplification    : 0.02
% 2.84/1.42  Subsumption          : 0.04
% 2.84/1.42  Abstraction          : 0.02
% 2.84/1.42  MUC search           : 0.00
% 2.84/1.42  Cooper               : 0.00
% 2.84/1.42  Total                : 0.70
% 2.84/1.42  Index Insertion      : 0.00
% 2.84/1.42  Index Deletion       : 0.00
% 2.84/1.42  Index Matching       : 0.00
% 2.84/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
