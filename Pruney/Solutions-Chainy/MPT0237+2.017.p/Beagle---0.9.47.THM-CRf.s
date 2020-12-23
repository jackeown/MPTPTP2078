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
% DateTime   : Thu Dec  3 09:49:47 EST 2020

% Result     : Theorem 6.08s
% Output     : CNFRefutation 6.08s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 184 expanded)
%              Number of leaves         :   40 (  78 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 226 expanded)
%              Number of equality atoms :   45 ( 144 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_60,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_38,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_523,plain,(
    ! [A_103,B_104] :
      ( k4_xboole_0(A_103,B_104) = A_103
      | ~ r1_xboole_0(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_535,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(resolution,[status(thm)],[c_16,c_523])).

tff(c_14,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_175,plain,(
    ! [A_78,B_79] :
      ( k3_xboole_0(A_78,B_79) = A_78
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_196,plain,(
    ! [A_80] : k3_xboole_0(k1_xboole_0,A_80) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_175])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_204,plain,(
    ! [A_80] : k3_xboole_0(A_80,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_2])).

tff(c_605,plain,(
    ! [A_107,B_108] : k5_xboole_0(A_107,k3_xboole_0(A_107,B_108)) = k4_xboole_0(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_623,plain,(
    ! [A_80] : k5_xboole_0(A_80,k1_xboole_0) = k4_xboole_0(A_80,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_605])).

tff(c_638,plain,(
    ! [A_80] : k5_xboole_0(A_80,k1_xboole_0) = A_80 ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_623])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_270,plain,(
    ! [A_84,B_85] : k3_xboole_0(A_84,k2_xboole_0(A_84,B_85)) = A_84 ),
    inference(resolution,[status(thm)],[c_18,c_175])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_283,plain,(
    ! [A_84] : r1_tarski(A_84,A_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_10])).

tff(c_379,plain,(
    ! [A_93,B_94] :
      ( k4_xboole_0(A_93,B_94) = k1_xboole_0
      | ~ r1_tarski(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_402,plain,(
    ! [A_84] : k4_xboole_0(A_84,A_84) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_283,c_379])).

tff(c_669,plain,(
    ! [A_111,B_112] : k5_xboole_0(A_111,k4_xboole_0(B_112,A_111)) = k2_xboole_0(A_111,B_112) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_693,plain,(
    ! [A_84] : k5_xboole_0(A_84,k1_xboole_0) = k2_xboole_0(A_84,A_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_669])).

tff(c_703,plain,(
    ! [A_84] : k2_xboole_0(A_84,A_84) = A_84 ),
    inference(demodulation,[status(thm),theory(equality)],[c_638,c_693])).

tff(c_52,plain,(
    ! [A_52,B_53] :
      ( r1_xboole_0(k1_tarski(A_52),B_53)
      | r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2571,plain,(
    ! [A_186,B_187] :
      ( k4_xboole_0(k1_tarski(A_186),B_187) = k1_tarski(A_186)
      | r2_hidden(A_186,B_187) ) ),
    inference(resolution,[status(thm)],[c_52,c_523])).

tff(c_24,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3366,plain,(
    ! [B_204,A_205] :
      ( k5_xboole_0(B_204,k1_tarski(A_205)) = k2_xboole_0(B_204,k1_tarski(A_205))
      | r2_hidden(A_205,B_204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2571,c_24])).

tff(c_56,plain,(
    ! [A_56,B_57] :
      ( k5_xboole_0(k1_tarski(A_56),k1_tarski(B_57)) = k2_tarski(A_56,B_57)
      | B_57 = A_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6758,plain,(
    ! [A_248,A_249] :
      ( k2_xboole_0(k1_tarski(A_248),k1_tarski(A_249)) = k2_tarski(A_248,A_249)
      | A_249 = A_248
      | r2_hidden(A_249,k1_tarski(A_248)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3366,c_56])).

tff(c_54,plain,(
    ! [A_54,B_55] : k3_tarski(k2_tarski(A_54,B_55)) = k2_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_58,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_59,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58])).

tff(c_6808,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6758,c_59])).

tff(c_6812,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6808])).

tff(c_26,plain,(
    ! [C_23,A_19] :
      ( C_23 = A_19
      | ~ r2_hidden(C_23,k1_tarski(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6816,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6812,c_26])).

tff(c_6818,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) != k2_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6816,c_6816,c_59])).

tff(c_6822,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_703,c_38,c_6818])).

tff(c_6823,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6808])).

tff(c_6825,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) != k2_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6823,c_6823,c_59])).

tff(c_6828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_703,c_6825])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:37:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.08/2.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.08/2.34  
% 6.08/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.08/2.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 6.08/2.34  
% 6.08/2.34  %Foreground sorts:
% 6.08/2.34  
% 6.08/2.34  
% 6.08/2.34  %Background operators:
% 6.08/2.34  
% 6.08/2.34  
% 6.08/2.34  %Foreground operators:
% 6.08/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.08/2.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.08/2.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.08/2.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.08/2.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.08/2.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.08/2.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.08/2.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.08/2.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.08/2.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.08/2.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.08/2.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.08/2.34  tff('#skF_3', type, '#skF_3': $i).
% 6.08/2.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.08/2.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.08/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.08/2.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.08/2.34  tff('#skF_4', type, '#skF_4': $i).
% 6.08/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.08/2.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.08/2.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.08/2.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.08/2.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.08/2.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.08/2.34  
% 6.08/2.36  tff(f_60, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.08/2.36  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 6.08/2.36  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.08/2.36  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.08/2.36  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.08/2.36  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.08/2.36  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.08/2.36  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.08/2.36  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.08/2.36  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.08/2.36  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.08/2.36  tff(f_77, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 6.08/2.36  tff(f_84, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 6.08/2.36  tff(f_79, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.08/2.36  tff(f_87, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 6.08/2.36  tff(f_58, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 6.08/2.36  tff(c_38, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.08/2.36  tff(c_16, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.08/2.36  tff(c_523, plain, (![A_103, B_104]: (k4_xboole_0(A_103, B_104)=A_103 | ~r1_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.08/2.36  tff(c_535, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(resolution, [status(thm)], [c_16, c_523])).
% 6.08/2.36  tff(c_14, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.08/2.36  tff(c_175, plain, (![A_78, B_79]: (k3_xboole_0(A_78, B_79)=A_78 | ~r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.08/2.36  tff(c_196, plain, (![A_80]: (k3_xboole_0(k1_xboole_0, A_80)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_175])).
% 6.08/2.36  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.08/2.36  tff(c_204, plain, (![A_80]: (k3_xboole_0(A_80, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_196, c_2])).
% 6.08/2.36  tff(c_605, plain, (![A_107, B_108]: (k5_xboole_0(A_107, k3_xboole_0(A_107, B_108))=k4_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.08/2.36  tff(c_623, plain, (![A_80]: (k5_xboole_0(A_80, k1_xboole_0)=k4_xboole_0(A_80, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_204, c_605])).
% 6.08/2.36  tff(c_638, plain, (![A_80]: (k5_xboole_0(A_80, k1_xboole_0)=A_80)), inference(demodulation, [status(thm), theory('equality')], [c_535, c_623])).
% 6.08/2.36  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.08/2.36  tff(c_270, plain, (![A_84, B_85]: (k3_xboole_0(A_84, k2_xboole_0(A_84, B_85))=A_84)), inference(resolution, [status(thm)], [c_18, c_175])).
% 6.08/2.36  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.08/2.36  tff(c_283, plain, (![A_84]: (r1_tarski(A_84, A_84))), inference(superposition, [status(thm), theory('equality')], [c_270, c_10])).
% 6.08/2.36  tff(c_379, plain, (![A_93, B_94]: (k4_xboole_0(A_93, B_94)=k1_xboole_0 | ~r1_tarski(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.08/2.36  tff(c_402, plain, (![A_84]: (k4_xboole_0(A_84, A_84)=k1_xboole_0)), inference(resolution, [status(thm)], [c_283, c_379])).
% 6.08/2.36  tff(c_669, plain, (![A_111, B_112]: (k5_xboole_0(A_111, k4_xboole_0(B_112, A_111))=k2_xboole_0(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.08/2.36  tff(c_693, plain, (![A_84]: (k5_xboole_0(A_84, k1_xboole_0)=k2_xboole_0(A_84, A_84))), inference(superposition, [status(thm), theory('equality')], [c_402, c_669])).
% 6.08/2.36  tff(c_703, plain, (![A_84]: (k2_xboole_0(A_84, A_84)=A_84)), inference(demodulation, [status(thm), theory('equality')], [c_638, c_693])).
% 6.08/2.36  tff(c_52, plain, (![A_52, B_53]: (r1_xboole_0(k1_tarski(A_52), B_53) | r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.08/2.36  tff(c_2571, plain, (![A_186, B_187]: (k4_xboole_0(k1_tarski(A_186), B_187)=k1_tarski(A_186) | r2_hidden(A_186, B_187))), inference(resolution, [status(thm)], [c_52, c_523])).
% 6.08/2.36  tff(c_24, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.08/2.36  tff(c_3366, plain, (![B_204, A_205]: (k5_xboole_0(B_204, k1_tarski(A_205))=k2_xboole_0(B_204, k1_tarski(A_205)) | r2_hidden(A_205, B_204))), inference(superposition, [status(thm), theory('equality')], [c_2571, c_24])).
% 6.08/2.36  tff(c_56, plain, (![A_56, B_57]: (k5_xboole_0(k1_tarski(A_56), k1_tarski(B_57))=k2_tarski(A_56, B_57) | B_57=A_56)), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.08/2.36  tff(c_6758, plain, (![A_248, A_249]: (k2_xboole_0(k1_tarski(A_248), k1_tarski(A_249))=k2_tarski(A_248, A_249) | A_249=A_248 | r2_hidden(A_249, k1_tarski(A_248)))), inference(superposition, [status(thm), theory('equality')], [c_3366, c_56])).
% 6.08/2.36  tff(c_54, plain, (![A_54, B_55]: (k3_tarski(k2_tarski(A_54, B_55))=k2_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.08/2.36  tff(c_58, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4')))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.08/2.36  tff(c_59, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58])).
% 6.08/2.36  tff(c_6808, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6758, c_59])).
% 6.08/2.36  tff(c_6812, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_6808])).
% 6.08/2.36  tff(c_26, plain, (![C_23, A_19]: (C_23=A_19 | ~r2_hidden(C_23, k1_tarski(A_19)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.08/2.36  tff(c_6816, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_6812, c_26])).
% 6.08/2.36  tff(c_6818, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))!=k2_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6816, c_6816, c_59])).
% 6.08/2.36  tff(c_6822, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_703, c_38, c_6818])).
% 6.08/2.36  tff(c_6823, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_6808])).
% 6.08/2.36  tff(c_6825, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))!=k2_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6823, c_6823, c_59])).
% 6.08/2.36  tff(c_6828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_703, c_6825])).
% 6.08/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.08/2.36  
% 6.08/2.36  Inference rules
% 6.08/2.36  ----------------------
% 6.08/2.36  #Ref     : 0
% 6.08/2.36  #Sup     : 1636
% 6.08/2.36  #Fact    : 0
% 6.08/2.36  #Define  : 0
% 6.08/2.36  #Split   : 2
% 6.08/2.36  #Chain   : 0
% 6.08/2.36  #Close   : 0
% 6.08/2.36  
% 6.08/2.36  Ordering : KBO
% 6.08/2.36  
% 6.08/2.36  Simplification rules
% 6.08/2.36  ----------------------
% 6.08/2.36  #Subsume      : 181
% 6.08/2.36  #Demod        : 2538
% 6.08/2.36  #Tautology    : 1272
% 6.08/2.36  #SimpNegUnit  : 0
% 6.08/2.36  #BackRed      : 7
% 6.08/2.36  
% 6.08/2.36  #Partial instantiations: 0
% 6.08/2.36  #Strategies tried      : 1
% 6.08/2.36  
% 6.08/2.36  Timing (in seconds)
% 6.08/2.36  ----------------------
% 6.08/2.36  Preprocessing        : 0.35
% 6.08/2.36  Parsing              : 0.18
% 6.08/2.36  CNF conversion       : 0.02
% 6.08/2.36  Main loop            : 1.23
% 6.08/2.36  Inferencing          : 0.32
% 6.08/2.36  Reduction            : 0.66
% 6.08/2.36  Demodulation         : 0.57
% 6.08/2.36  BG Simplification    : 0.04
% 6.08/2.36  Subsumption          : 0.16
% 6.08/2.36  Abstraction          : 0.06
% 6.08/2.36  MUC search           : 0.00
% 6.08/2.36  Cooper               : 0.00
% 6.08/2.36  Total                : 1.61
% 6.08/2.36  Index Insertion      : 0.00
% 6.08/2.36  Index Deletion       : 0.00
% 6.08/2.36  Index Matching       : 0.00
% 6.08/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
