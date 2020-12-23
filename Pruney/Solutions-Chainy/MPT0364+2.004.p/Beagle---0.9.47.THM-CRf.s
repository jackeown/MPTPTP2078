%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:39 EST 2020

% Result     : Theorem 11.21s
% Output     : CNFRefutation 11.21s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 409 expanded)
%              Number of leaves         :   47 ( 156 expanded)
%              Depth                    :   18
%              Number of atoms          :  181 ( 468 expanded)
%              Number of equality atoms :   90 ( 299 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_112,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

tff(c_88,plain,
    ( r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5'))
    | r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_165,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_82,plain,
    ( ~ r1_tarski('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_278,plain,(
    ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_82])).

tff(c_30,plain,(
    ! [A_30] : k5_xboole_0(A_30,k1_xboole_0) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_261,plain,(
    ! [A_98,B_99] : k3_xboole_0(A_98,k2_xboole_0(A_98,B_99)) = A_98 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_113,plain,(
    ! [B_89,A_90] : k3_xboole_0(B_89,A_90) = k3_xboole_0(A_90,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_17,B_18] : r1_tarski(k3_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_128,plain,(
    ! [B_89,A_90] : r1_tarski(k3_xboole_0(B_89,A_90),A_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_18])).

tff(c_267,plain,(
    ! [A_98,B_99] : r1_tarski(A_98,k2_xboole_0(A_98,B_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_128])).

tff(c_22,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k2_xboole_0(A_21,B_22)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_19,B_20] : k3_xboole_0(A_19,k2_xboole_0(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_328,plain,(
    ! [A_118,B_119] : k5_xboole_0(A_118,k3_xboole_0(A_118,B_119)) = k4_xboole_0(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_341,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k2_xboole_0(A_19,B_20)) = k5_xboole_0(A_19,A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_328])).

tff(c_357,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_341])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_354,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_328])).

tff(c_385,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_354])).

tff(c_423,plain,(
    ! [A_123,C_124,B_125] :
      ( r1_xboole_0(A_123,k4_xboole_0(C_124,B_125))
      | ~ r1_tarski(A_123,B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_437,plain,(
    ! [A_126,A_127] :
      ( r1_xboole_0(A_126,k1_xboole_0)
      | ~ r1_tarski(A_126,A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_423])).

tff(c_454,plain,(
    ! [A_128] : r1_xboole_0(A_128,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_267,c_437])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_461,plain,(
    ! [A_129] : k3_xboole_0(A_129,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_454,c_6])).

tff(c_12,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_466,plain,(
    ! [A_129] : k5_xboole_0(A_129,k1_xboole_0) = k4_xboole_0(A_129,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_12])).

tff(c_498,plain,(
    ! [A_129] : k4_xboole_0(A_129,k1_xboole_0) = A_129 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_466])).

tff(c_7676,plain,(
    ! [A_340,C_341,B_342] :
      ( k3_xboole_0(A_340,k4_xboole_0(C_341,B_342)) = k1_xboole_0
      | ~ r1_tarski(A_340,B_342) ) ),
    inference(resolution,[status(thm)],[c_423,c_6])).

tff(c_1387,plain,(
    ! [A_176,B_177,C_178] : k4_xboole_0(k3_xboole_0(A_176,B_177),C_178) = k3_xboole_0(A_176,k4_xboole_0(B_177,C_178)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1490,plain,(
    ! [A_7,C_178] : k3_xboole_0(A_7,k4_xboole_0(A_7,C_178)) = k4_xboole_0(A_7,C_178) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1387])).

tff(c_7983,plain,(
    ! [C_343,B_344] :
      ( k4_xboole_0(C_343,B_344) = k1_xboole_0
      | ~ r1_tarski(C_343,B_344) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7676,c_1490])).

tff(c_8105,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_165,c_7983])).

tff(c_26,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8435,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8105,c_26])).

tff(c_8469,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_8435])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_78,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1760,plain,(
    ! [A_185,B_186] :
      ( k4_xboole_0(A_185,B_186) = k3_subset_1(A_185,B_186)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(A_185)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1776,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_1760])).

tff(c_448,plain,(
    ! [A_98] : r1_xboole_0(A_98,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_267,c_437])).

tff(c_721,plain,(
    ! [A_144,B_145] : k4_xboole_0(A_144,k3_xboole_0(A_144,B_145)) = k4_xboole_0(A_144,B_145) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_727,plain,(
    ! [A_144,B_145] : k4_xboole_0(A_144,k4_xboole_0(A_144,B_145)) = k3_xboole_0(A_144,k3_xboole_0(A_144,B_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_721,c_26])).

tff(c_862,plain,(
    ! [A_155,B_156] : k3_xboole_0(A_155,k3_xboole_0(A_155,B_156)) = k3_xboole_0(A_155,B_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_727])).

tff(c_348,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_328])).

tff(c_871,plain,(
    ! [A_155,B_156] : k5_xboole_0(k3_xboole_0(A_155,B_156),k3_xboole_0(A_155,B_156)) = k4_xboole_0(k3_xboole_0(A_155,B_156),A_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_862,c_348])).

tff(c_918,plain,(
    ! [A_155,B_156] : k4_xboole_0(k3_xboole_0(A_155,B_156),A_155) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_871])).

tff(c_1287,plain,(
    ! [B_170,A_171,C_172] :
      ( r1_xboole_0(B_170,k4_xboole_0(A_171,C_172))
      | ~ r1_xboole_0(A_171,k4_xboole_0(B_170,C_172)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1293,plain,(
    ! [A_155,B_156,A_171] :
      ( r1_xboole_0(k3_xboole_0(A_155,B_156),k4_xboole_0(A_171,A_155))
      | ~ r1_xboole_0(A_171,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_918,c_1287])).

tff(c_3371,plain,(
    ! [A_221,B_222,A_223] : r1_xboole_0(k3_xboole_0(A_221,B_222),k4_xboole_0(A_223,A_221)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_1293])).

tff(c_3657,plain,(
    ! [B_232] : r1_xboole_0(k3_xboole_0('#skF_5',B_232),k3_subset_1('#skF_3','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1776,c_3371])).

tff(c_3688,plain,(
    ! [B_2] : r1_xboole_0(k3_xboole_0(B_2,'#skF_5'),k3_subset_1('#skF_3','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3657])).

tff(c_8706,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8469,c_3688])).

tff(c_8782,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_8706])).

tff(c_8784,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_8957,plain,(
    ! [A_370,B_371] : k4_xboole_0(A_370,k4_xboole_0(A_370,B_371)) = k3_xboole_0(A_370,B_371) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8972,plain,(
    ! [A_21,B_22] : k3_xboole_0(A_21,k2_xboole_0(A_21,B_22)) = k4_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_8957])).

tff(c_8975,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_8972])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_76,plain,(
    ! [A_81] : ~ v1_xboole_0(k1_zfmisc_1(A_81)) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_9585,plain,(
    ! [B_401,A_402] :
      ( r2_hidden(B_401,A_402)
      | ~ m1_subset_1(B_401,A_402)
      | v1_xboole_0(A_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_52,plain,(
    ! [C_74,A_70] :
      ( r1_tarski(C_74,A_70)
      | ~ r2_hidden(C_74,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_9592,plain,(
    ! [B_401,A_70] :
      ( r1_tarski(B_401,A_70)
      | ~ m1_subset_1(B_401,k1_zfmisc_1(A_70))
      | v1_xboole_0(k1_zfmisc_1(A_70)) ) ),
    inference(resolution,[status(thm)],[c_9585,c_52])).

tff(c_9597,plain,(
    ! [B_403,A_404] :
      ( r1_tarski(B_403,A_404)
      | ~ m1_subset_1(B_403,k1_zfmisc_1(A_404)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_9592])).

tff(c_9614,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_9597])).

tff(c_9011,plain,(
    ! [A_374,C_375,B_376] :
      ( r1_xboole_0(A_374,k4_xboole_0(C_375,B_376))
      | ~ r1_tarski(A_374,B_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18402,plain,(
    ! [A_606,C_607,B_608] :
      ( k3_xboole_0(A_606,k4_xboole_0(C_607,B_608)) = k1_xboole_0
      | ~ r1_tarski(A_606,B_608) ) ),
    inference(resolution,[status(thm)],[c_9011,c_6])).

tff(c_11226,plain,(
    ! [A_449,B_450,C_451] : k4_xboole_0(k3_xboole_0(A_449,B_450),C_451) = k3_xboole_0(A_449,k4_xboole_0(B_450,C_451)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_11354,plain,(
    ! [A_7,C_451] : k3_xboole_0(A_7,k4_xboole_0(A_7,C_451)) = k4_xboole_0(A_7,C_451) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_11226])).

tff(c_18779,plain,(
    ! [C_609,B_610] :
      ( k4_xboole_0(C_609,B_610) = k1_xboole_0
      | ~ r1_tarski(C_609,B_610) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18402,c_11354])).

tff(c_18897,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9614,c_18779])).

tff(c_18981,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18897,c_26])).

tff(c_19010,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8975,c_18981])).

tff(c_10506,plain,(
    ! [A_431,B_432] :
      ( k4_xboole_0(A_431,B_432) = k3_subset_1(A_431,B_432)
      | ~ m1_subset_1(B_432,k1_zfmisc_1(A_431)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10523,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_10506])).

tff(c_10540,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10523,c_26])).

tff(c_10543,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10540])).

tff(c_19153,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19010,c_10543])).

tff(c_8783,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_10522,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_10506])).

tff(c_10937,plain,(
    ! [B_439,A_440,C_441] :
      ( r1_xboole_0(B_439,k4_xboole_0(A_440,C_441))
      | ~ r1_xboole_0(A_440,k4_xboole_0(B_439,C_441)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_13320,plain,(
    ! [A_484] :
      ( r1_xboole_0('#skF_3',k4_xboole_0(A_484,'#skF_5'))
      | ~ r1_xboole_0(A_484,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10522,c_10937])).

tff(c_13354,plain,(
    r1_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_8783,c_13320])).

tff(c_13368,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13354,c_6])).

tff(c_13434,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k5_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_13368,c_12])).

tff(c_13463,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_13434])).

tff(c_8976,plain,(
    ! [A_372] : k4_xboole_0(A_372,k1_xboole_0) = A_372 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_8972])).

tff(c_8982,plain,(
    ! [A_372] : k4_xboole_0(A_372,A_372) = k3_xboole_0(A_372,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8976,c_26])).

tff(c_9122,plain,(
    ! [A_383,B_384] : k4_xboole_0(A_383,k3_xboole_0(A_383,B_384)) = k4_xboole_0(A_383,B_384) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_9155,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k2_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_9122])).

tff(c_9173,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8982,c_22,c_9155])).

tff(c_9176,plain,(
    ! [A_372] : k4_xboole_0(A_372,A_372) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9173,c_8982])).

tff(c_9139,plain,(
    ! [A_383,B_384] : k4_xboole_0(A_383,k4_xboole_0(A_383,B_384)) = k3_xboole_0(A_383,k3_xboole_0(A_383,B_384)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9122,c_26])).

tff(c_9833,plain,(
    ! [A_414,B_415] : k3_xboole_0(A_414,k3_xboole_0(A_414,B_415)) = k3_xboole_0(A_414,B_415) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_9139])).

tff(c_9158,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_9122])).

tff(c_9842,plain,(
    ! [A_414,B_415] : k4_xboole_0(k3_xboole_0(A_414,B_415),k3_xboole_0(A_414,B_415)) = k4_xboole_0(k3_xboole_0(A_414,B_415),A_414) ),
    inference(superposition,[status(thm),theory(equality)],[c_9833,c_9158])).

tff(c_9902,plain,(
    ! [A_414,B_415] : k4_xboole_0(k3_xboole_0(A_414,B_415),A_414) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9176,c_9842])).

tff(c_11417,plain,(
    ! [A_453,B_454] : k3_xboole_0(A_453,k4_xboole_0(B_454,A_453)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_9902,c_11226])).

tff(c_11467,plain,(
    ! [A_453,B_454] : k4_xboole_0(A_453,k4_xboole_0(B_454,A_453)) = k5_xboole_0(A_453,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11417,c_12])).

tff(c_11552,plain,(
    ! [A_453,B_454] : k4_xboole_0(A_453,k4_xboole_0(B_454,A_453)) = A_453 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_11467])).

tff(c_108,plain,(
    ! [A_86,B_87] : r1_tarski(k3_xboole_0(A_86,B_87),A_86) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_111,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_108])).

tff(c_9232,plain,(
    ! [A_387] : k4_xboole_0(A_387,A_387) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9173,c_8982])).

tff(c_36,plain,(
    ! [A_37,C_39,B_38] :
      ( r1_xboole_0(A_37,k4_xboole_0(C_39,B_38))
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_9406,plain,(
    ! [A_392,A_393] :
      ( r1_xboole_0(A_392,k1_xboole_0)
      | ~ r1_tarski(A_392,A_393) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9232,c_36])).

tff(c_9420,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_111,c_9406])).

tff(c_9463,plain,(
    ! [A_396,B_397] : k5_xboole_0(A_396,k3_xboole_0(A_396,B_397)) = k4_xboole_0(A_396,B_397) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_9492,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_9463])).

tff(c_12979,plain,(
    ! [A_479,B_480,C_481] : k5_xboole_0(k3_xboole_0(A_479,B_480),k3_xboole_0(C_481,B_480)) = k3_xboole_0(k5_xboole_0(A_479,C_481),B_480) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_13147,plain,(
    ! [A_7,C_481] : k5_xboole_0(A_7,k3_xboole_0(C_481,A_7)) = k3_xboole_0(k5_xboole_0(A_7,C_481),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_12979])).

tff(c_16641,plain,(
    ! [A_581,C_582] : k3_xboole_0(A_581,k5_xboole_0(A_581,C_582)) = k4_xboole_0(A_581,C_582) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9492,c_2,c_13147])).

tff(c_16962,plain,(
    ! [A_585,C_586] : k4_xboole_0(k4_xboole_0(A_585,C_586),A_585) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16641,c_9902])).

tff(c_34,plain,(
    ! [B_35,A_34,C_36] :
      ( r1_xboole_0(B_35,k4_xboole_0(A_34,C_36))
      | ~ r1_xboole_0(A_34,k4_xboole_0(B_35,C_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_17026,plain,(
    ! [A_585,C_586,A_34] :
      ( r1_xboole_0(k4_xboole_0(A_585,C_586),k4_xboole_0(A_34,A_585))
      | ~ r1_xboole_0(A_34,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16962,c_34])).

tff(c_27958,plain,(
    ! [A_675,C_676,A_677] : r1_xboole_0(k4_xboole_0(A_675,C_676),k4_xboole_0(A_677,A_675)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9420,c_17026])).

tff(c_28441,plain,(
    ! [B_681,A_682,C_683] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_681,A_682),C_683),A_682) ),
    inference(superposition,[status(thm),theory(equality)],[c_11552,c_27958])).

tff(c_32540,plain,(
    ! [C_734] : r1_xboole_0(k4_xboole_0('#skF_3',C_734),k4_xboole_0('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13463,c_28441])).

tff(c_32551,plain,(
    r1_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_19153,c_32540])).

tff(c_32613,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32551,c_6])).

tff(c_24,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = k4_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_32770,plain,(
    k4_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) = k4_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32613,c_24])).

tff(c_32831,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8975,c_26,c_32770])).

tff(c_33157,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_32831,c_128])).

tff(c_33198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8784,c_33157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.21/4.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.21/4.91  
% 11.21/4.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.21/4.91  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 11.21/4.91  
% 11.21/4.91  %Foreground sorts:
% 11.21/4.91  
% 11.21/4.91  
% 11.21/4.91  %Background operators:
% 11.21/4.91  
% 11.21/4.91  
% 11.21/4.91  %Foreground operators:
% 11.21/4.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.21/4.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.21/4.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.21/4.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.21/4.91  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.21/4.91  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.21/4.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.21/4.91  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.21/4.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.21/4.91  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.21/4.91  tff('#skF_5', type, '#skF_5': $i).
% 11.21/4.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.21/4.91  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.21/4.91  tff('#skF_3', type, '#skF_3': $i).
% 11.21/4.91  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.21/4.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.21/4.91  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.21/4.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.21/4.91  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.21/4.91  tff('#skF_4', type, '#skF_4': $i).
% 11.21/4.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.21/4.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.21/4.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.21/4.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.21/4.91  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.21/4.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.21/4.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.21/4.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.21/4.91  
% 11.21/4.93  tff(f_122, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_subset_1)).
% 11.21/4.93  tff(f_55, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 11.21/4.93  tff(f_45, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 11.21/4.93  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.21/4.93  tff(f_43, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 11.21/4.93  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 11.21/4.93  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.21/4.93  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 11.21/4.93  tff(f_69, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 11.21/4.93  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 11.21/4.93  tff(f_53, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 11.21/4.93  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.21/4.93  tff(f_109, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 11.21/4.93  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 11.21/4.93  tff(f_65, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 11.21/4.93  tff(f_112, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 11.21/4.93  tff(f_105, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 11.21/4.93  tff(f_90, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 11.21/4.93  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 11.21/4.93  tff(c_88, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5')) | r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 11.21/4.93  tff(c_165, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_88])).
% 11.21/4.93  tff(c_82, plain, (~r1_tarski('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 11.21/4.93  tff(c_278, plain, (~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_82])).
% 11.21/4.93  tff(c_30, plain, (![A_30]: (k5_xboole_0(A_30, k1_xboole_0)=A_30)), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.21/4.93  tff(c_261, plain, (![A_98, B_99]: (k3_xboole_0(A_98, k2_xboole_0(A_98, B_99))=A_98)), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.21/4.93  tff(c_113, plain, (![B_89, A_90]: (k3_xboole_0(B_89, A_90)=k3_xboole_0(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.21/4.93  tff(c_18, plain, (![A_17, B_18]: (r1_tarski(k3_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.21/4.93  tff(c_128, plain, (![B_89, A_90]: (r1_tarski(k3_xboole_0(B_89, A_90), A_90))), inference(superposition, [status(thm), theory('equality')], [c_113, c_18])).
% 11.21/4.93  tff(c_267, plain, (![A_98, B_99]: (r1_tarski(A_98, k2_xboole_0(A_98, B_99)))), inference(superposition, [status(thm), theory('equality')], [c_261, c_128])).
% 11.21/4.93  tff(c_22, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k2_xboole_0(A_21, B_22))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.21/4.93  tff(c_20, plain, (![A_19, B_20]: (k3_xboole_0(A_19, k2_xboole_0(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.21/4.93  tff(c_328, plain, (![A_118, B_119]: (k5_xboole_0(A_118, k3_xboole_0(A_118, B_119))=k4_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.21/4.93  tff(c_341, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k2_xboole_0(A_19, B_20))=k5_xboole_0(A_19, A_19))), inference(superposition, [status(thm), theory('equality')], [c_20, c_328])).
% 11.21/4.93  tff(c_357, plain, (![A_19]: (k5_xboole_0(A_19, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_341])).
% 11.21/4.93  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.21/4.93  tff(c_354, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_328])).
% 11.21/4.93  tff(c_385, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_357, c_354])).
% 11.21/4.93  tff(c_423, plain, (![A_123, C_124, B_125]: (r1_xboole_0(A_123, k4_xboole_0(C_124, B_125)) | ~r1_tarski(A_123, B_125))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.21/4.93  tff(c_437, plain, (![A_126, A_127]: (r1_xboole_0(A_126, k1_xboole_0) | ~r1_tarski(A_126, A_127))), inference(superposition, [status(thm), theory('equality')], [c_385, c_423])).
% 11.21/4.93  tff(c_454, plain, (![A_128]: (r1_xboole_0(A_128, k1_xboole_0))), inference(resolution, [status(thm)], [c_267, c_437])).
% 11.21/4.93  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.21/4.93  tff(c_461, plain, (![A_129]: (k3_xboole_0(A_129, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_454, c_6])).
% 11.21/4.93  tff(c_12, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.21/4.93  tff(c_466, plain, (![A_129]: (k5_xboole_0(A_129, k1_xboole_0)=k4_xboole_0(A_129, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_461, c_12])).
% 11.21/4.93  tff(c_498, plain, (![A_129]: (k4_xboole_0(A_129, k1_xboole_0)=A_129)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_466])).
% 11.21/4.93  tff(c_7676, plain, (![A_340, C_341, B_342]: (k3_xboole_0(A_340, k4_xboole_0(C_341, B_342))=k1_xboole_0 | ~r1_tarski(A_340, B_342))), inference(resolution, [status(thm)], [c_423, c_6])).
% 11.21/4.93  tff(c_1387, plain, (![A_176, B_177, C_178]: (k4_xboole_0(k3_xboole_0(A_176, B_177), C_178)=k3_xboole_0(A_176, k4_xboole_0(B_177, C_178)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.21/4.93  tff(c_1490, plain, (![A_7, C_178]: (k3_xboole_0(A_7, k4_xboole_0(A_7, C_178))=k4_xboole_0(A_7, C_178))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1387])).
% 11.21/4.93  tff(c_7983, plain, (![C_343, B_344]: (k4_xboole_0(C_343, B_344)=k1_xboole_0 | ~r1_tarski(C_343, B_344))), inference(superposition, [status(thm), theory('equality')], [c_7676, c_1490])).
% 11.21/4.93  tff(c_8105, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_165, c_7983])).
% 11.21/4.93  tff(c_26, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.21/4.93  tff(c_8435, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8105, c_26])).
% 11.21/4.93  tff(c_8469, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_498, c_8435])).
% 11.21/4.93  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.21/4.93  tff(c_78, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 11.21/4.93  tff(c_1760, plain, (![A_185, B_186]: (k4_xboole_0(A_185, B_186)=k3_subset_1(A_185, B_186) | ~m1_subset_1(B_186, k1_zfmisc_1(A_185)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.21/4.93  tff(c_1776, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_78, c_1760])).
% 11.21/4.93  tff(c_448, plain, (![A_98]: (r1_xboole_0(A_98, k1_xboole_0))), inference(resolution, [status(thm)], [c_267, c_437])).
% 11.21/4.93  tff(c_721, plain, (![A_144, B_145]: (k4_xboole_0(A_144, k3_xboole_0(A_144, B_145))=k4_xboole_0(A_144, B_145))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.21/4.93  tff(c_727, plain, (![A_144, B_145]: (k4_xboole_0(A_144, k4_xboole_0(A_144, B_145))=k3_xboole_0(A_144, k3_xboole_0(A_144, B_145)))), inference(superposition, [status(thm), theory('equality')], [c_721, c_26])).
% 11.21/4.93  tff(c_862, plain, (![A_155, B_156]: (k3_xboole_0(A_155, k3_xboole_0(A_155, B_156))=k3_xboole_0(A_155, B_156))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_727])).
% 11.21/4.93  tff(c_348, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_328])).
% 11.21/4.93  tff(c_871, plain, (![A_155, B_156]: (k5_xboole_0(k3_xboole_0(A_155, B_156), k3_xboole_0(A_155, B_156))=k4_xboole_0(k3_xboole_0(A_155, B_156), A_155))), inference(superposition, [status(thm), theory('equality')], [c_862, c_348])).
% 11.21/4.93  tff(c_918, plain, (![A_155, B_156]: (k4_xboole_0(k3_xboole_0(A_155, B_156), A_155)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_357, c_871])).
% 11.21/4.93  tff(c_1287, plain, (![B_170, A_171, C_172]: (r1_xboole_0(B_170, k4_xboole_0(A_171, C_172)) | ~r1_xboole_0(A_171, k4_xboole_0(B_170, C_172)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.21/4.93  tff(c_1293, plain, (![A_155, B_156, A_171]: (r1_xboole_0(k3_xboole_0(A_155, B_156), k4_xboole_0(A_171, A_155)) | ~r1_xboole_0(A_171, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_918, c_1287])).
% 11.21/4.93  tff(c_3371, plain, (![A_221, B_222, A_223]: (r1_xboole_0(k3_xboole_0(A_221, B_222), k4_xboole_0(A_223, A_221)))), inference(demodulation, [status(thm), theory('equality')], [c_448, c_1293])).
% 11.21/4.93  tff(c_3657, plain, (![B_232]: (r1_xboole_0(k3_xboole_0('#skF_5', B_232), k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1776, c_3371])).
% 11.21/4.93  tff(c_3688, plain, (![B_2]: (r1_xboole_0(k3_xboole_0(B_2, '#skF_5'), k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3657])).
% 11.21/4.93  tff(c_8706, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8469, c_3688])).
% 11.21/4.93  tff(c_8782, plain, $false, inference(negUnitSimplification, [status(thm)], [c_278, c_8706])).
% 11.21/4.93  tff(c_8784, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_88])).
% 11.21/4.93  tff(c_8957, plain, (![A_370, B_371]: (k4_xboole_0(A_370, k4_xboole_0(A_370, B_371))=k3_xboole_0(A_370, B_371))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.21/4.93  tff(c_8972, plain, (![A_21, B_22]: (k3_xboole_0(A_21, k2_xboole_0(A_21, B_22))=k4_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_8957])).
% 11.21/4.93  tff(c_8975, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_8972])).
% 11.21/4.93  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 11.21/4.93  tff(c_76, plain, (![A_81]: (~v1_xboole_0(k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.21/4.93  tff(c_9585, plain, (![B_401, A_402]: (r2_hidden(B_401, A_402) | ~m1_subset_1(B_401, A_402) | v1_xboole_0(A_402))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.21/4.93  tff(c_52, plain, (![C_74, A_70]: (r1_tarski(C_74, A_70) | ~r2_hidden(C_74, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.93  tff(c_9592, plain, (![B_401, A_70]: (r1_tarski(B_401, A_70) | ~m1_subset_1(B_401, k1_zfmisc_1(A_70)) | v1_xboole_0(k1_zfmisc_1(A_70)))), inference(resolution, [status(thm)], [c_9585, c_52])).
% 11.21/4.93  tff(c_9597, plain, (![B_403, A_404]: (r1_tarski(B_403, A_404) | ~m1_subset_1(B_403, k1_zfmisc_1(A_404)))), inference(negUnitSimplification, [status(thm)], [c_76, c_9592])).
% 11.21/4.93  tff(c_9614, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_80, c_9597])).
% 11.21/4.93  tff(c_9011, plain, (![A_374, C_375, B_376]: (r1_xboole_0(A_374, k4_xboole_0(C_375, B_376)) | ~r1_tarski(A_374, B_376))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.21/4.93  tff(c_18402, plain, (![A_606, C_607, B_608]: (k3_xboole_0(A_606, k4_xboole_0(C_607, B_608))=k1_xboole_0 | ~r1_tarski(A_606, B_608))), inference(resolution, [status(thm)], [c_9011, c_6])).
% 11.21/4.93  tff(c_11226, plain, (![A_449, B_450, C_451]: (k4_xboole_0(k3_xboole_0(A_449, B_450), C_451)=k3_xboole_0(A_449, k4_xboole_0(B_450, C_451)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.21/4.93  tff(c_11354, plain, (![A_7, C_451]: (k3_xboole_0(A_7, k4_xboole_0(A_7, C_451))=k4_xboole_0(A_7, C_451))), inference(superposition, [status(thm), theory('equality')], [c_10, c_11226])).
% 11.21/4.93  tff(c_18779, plain, (![C_609, B_610]: (k4_xboole_0(C_609, B_610)=k1_xboole_0 | ~r1_tarski(C_609, B_610))), inference(superposition, [status(thm), theory('equality')], [c_18402, c_11354])).
% 11.21/4.93  tff(c_18897, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_9614, c_18779])).
% 11.21/4.93  tff(c_18981, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18897, c_26])).
% 11.21/4.93  tff(c_19010, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8975, c_18981])).
% 11.21/4.93  tff(c_10506, plain, (![A_431, B_432]: (k4_xboole_0(A_431, B_432)=k3_subset_1(A_431, B_432) | ~m1_subset_1(B_432, k1_zfmisc_1(A_431)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.21/4.93  tff(c_10523, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_10506])).
% 11.21/4.93  tff(c_10540, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10523, c_26])).
% 11.21/4.93  tff(c_10543, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10540])).
% 11.21/4.93  tff(c_19153, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19010, c_10543])).
% 11.21/4.93  tff(c_8783, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_88])).
% 11.21/4.93  tff(c_10522, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_78, c_10506])).
% 11.21/4.93  tff(c_10937, plain, (![B_439, A_440, C_441]: (r1_xboole_0(B_439, k4_xboole_0(A_440, C_441)) | ~r1_xboole_0(A_440, k4_xboole_0(B_439, C_441)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.21/4.93  tff(c_13320, plain, (![A_484]: (r1_xboole_0('#skF_3', k4_xboole_0(A_484, '#skF_5')) | ~r1_xboole_0(A_484, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_10522, c_10937])).
% 11.21/4.93  tff(c_13354, plain, (r1_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_8783, c_13320])).
% 11.21/4.93  tff(c_13368, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_13354, c_6])).
% 11.21/4.93  tff(c_13434, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k5_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13368, c_12])).
% 11.21/4.93  tff(c_13463, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_13434])).
% 11.21/4.93  tff(c_8976, plain, (![A_372]: (k4_xboole_0(A_372, k1_xboole_0)=A_372)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_8972])).
% 11.21/4.93  tff(c_8982, plain, (![A_372]: (k4_xboole_0(A_372, A_372)=k3_xboole_0(A_372, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8976, c_26])).
% 11.21/4.93  tff(c_9122, plain, (![A_383, B_384]: (k4_xboole_0(A_383, k3_xboole_0(A_383, B_384))=k4_xboole_0(A_383, B_384))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.21/4.93  tff(c_9155, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k2_xboole_0(A_19, B_20))=k4_xboole_0(A_19, A_19))), inference(superposition, [status(thm), theory('equality')], [c_20, c_9122])).
% 11.21/4.93  tff(c_9173, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8982, c_22, c_9155])).
% 11.21/4.93  tff(c_9176, plain, (![A_372]: (k4_xboole_0(A_372, A_372)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_9173, c_8982])).
% 11.21/4.93  tff(c_9139, plain, (![A_383, B_384]: (k4_xboole_0(A_383, k4_xboole_0(A_383, B_384))=k3_xboole_0(A_383, k3_xboole_0(A_383, B_384)))), inference(superposition, [status(thm), theory('equality')], [c_9122, c_26])).
% 11.21/4.93  tff(c_9833, plain, (![A_414, B_415]: (k3_xboole_0(A_414, k3_xboole_0(A_414, B_415))=k3_xboole_0(A_414, B_415))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_9139])).
% 11.21/4.93  tff(c_9158, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_9122])).
% 11.21/4.93  tff(c_9842, plain, (![A_414, B_415]: (k4_xboole_0(k3_xboole_0(A_414, B_415), k3_xboole_0(A_414, B_415))=k4_xboole_0(k3_xboole_0(A_414, B_415), A_414))), inference(superposition, [status(thm), theory('equality')], [c_9833, c_9158])).
% 11.21/4.93  tff(c_9902, plain, (![A_414, B_415]: (k4_xboole_0(k3_xboole_0(A_414, B_415), A_414)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_9176, c_9842])).
% 11.21/4.93  tff(c_11417, plain, (![A_453, B_454]: (k3_xboole_0(A_453, k4_xboole_0(B_454, A_453))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9902, c_11226])).
% 11.21/4.93  tff(c_11467, plain, (![A_453, B_454]: (k4_xboole_0(A_453, k4_xboole_0(B_454, A_453))=k5_xboole_0(A_453, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_11417, c_12])).
% 11.21/4.93  tff(c_11552, plain, (![A_453, B_454]: (k4_xboole_0(A_453, k4_xboole_0(B_454, A_453))=A_453)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_11467])).
% 11.21/4.93  tff(c_108, plain, (![A_86, B_87]: (r1_tarski(k3_xboole_0(A_86, B_87), A_86))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.21/4.93  tff(c_111, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_108])).
% 11.21/4.93  tff(c_9232, plain, (![A_387]: (k4_xboole_0(A_387, A_387)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_9173, c_8982])).
% 11.21/4.93  tff(c_36, plain, (![A_37, C_39, B_38]: (r1_xboole_0(A_37, k4_xboole_0(C_39, B_38)) | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.21/4.93  tff(c_9406, plain, (![A_392, A_393]: (r1_xboole_0(A_392, k1_xboole_0) | ~r1_tarski(A_392, A_393))), inference(superposition, [status(thm), theory('equality')], [c_9232, c_36])).
% 11.21/4.93  tff(c_9420, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_111, c_9406])).
% 11.21/4.93  tff(c_9463, plain, (![A_396, B_397]: (k5_xboole_0(A_396, k3_xboole_0(A_396, B_397))=k4_xboole_0(A_396, B_397))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.21/4.93  tff(c_9492, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_9463])).
% 11.21/4.93  tff(c_12979, plain, (![A_479, B_480, C_481]: (k5_xboole_0(k3_xboole_0(A_479, B_480), k3_xboole_0(C_481, B_480))=k3_xboole_0(k5_xboole_0(A_479, C_481), B_480))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.21/4.93  tff(c_13147, plain, (![A_7, C_481]: (k5_xboole_0(A_7, k3_xboole_0(C_481, A_7))=k3_xboole_0(k5_xboole_0(A_7, C_481), A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_12979])).
% 11.21/4.93  tff(c_16641, plain, (![A_581, C_582]: (k3_xboole_0(A_581, k5_xboole_0(A_581, C_582))=k4_xboole_0(A_581, C_582))), inference(demodulation, [status(thm), theory('equality')], [c_9492, c_2, c_13147])).
% 11.21/4.93  tff(c_16962, plain, (![A_585, C_586]: (k4_xboole_0(k4_xboole_0(A_585, C_586), A_585)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16641, c_9902])).
% 11.21/4.93  tff(c_34, plain, (![B_35, A_34, C_36]: (r1_xboole_0(B_35, k4_xboole_0(A_34, C_36)) | ~r1_xboole_0(A_34, k4_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.21/4.93  tff(c_17026, plain, (![A_585, C_586, A_34]: (r1_xboole_0(k4_xboole_0(A_585, C_586), k4_xboole_0(A_34, A_585)) | ~r1_xboole_0(A_34, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16962, c_34])).
% 11.21/4.93  tff(c_27958, plain, (![A_675, C_676, A_677]: (r1_xboole_0(k4_xboole_0(A_675, C_676), k4_xboole_0(A_677, A_675)))), inference(demodulation, [status(thm), theory('equality')], [c_9420, c_17026])).
% 11.21/4.93  tff(c_28441, plain, (![B_681, A_682, C_683]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_681, A_682), C_683), A_682))), inference(superposition, [status(thm), theory('equality')], [c_11552, c_27958])).
% 11.21/4.93  tff(c_32540, plain, (![C_734]: (r1_xboole_0(k4_xboole_0('#skF_3', C_734), k4_xboole_0('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_13463, c_28441])).
% 11.21/4.93  tff(c_32551, plain, (r1_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_19153, c_32540])).
% 11.21/4.93  tff(c_32613, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_32551, c_6])).
% 11.21/4.93  tff(c_24, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k3_xboole_0(A_23, B_24))=k4_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.21/4.93  tff(c_32770, plain, (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))=k4_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32613, c_24])).
% 11.21/4.93  tff(c_32831, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8975, c_26, c_32770])).
% 11.21/4.93  tff(c_33157, plain, (r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_32831, c_128])).
% 11.21/4.93  tff(c_33198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8784, c_33157])).
% 11.21/4.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.21/4.93  
% 11.21/4.93  Inference rules
% 11.21/4.93  ----------------------
% 11.21/4.93  #Ref     : 0
% 11.21/4.93  #Sup     : 8452
% 11.21/4.93  #Fact    : 0
% 11.21/4.93  #Define  : 0
% 11.21/4.93  #Split   : 3
% 11.21/4.93  #Chain   : 0
% 11.21/4.93  #Close   : 0
% 11.21/4.93  
% 11.21/4.93  Ordering : KBO
% 11.21/4.93  
% 11.21/4.93  Simplification rules
% 11.21/4.93  ----------------------
% 11.21/4.93  #Subsume      : 134
% 11.21/4.93  #Demod        : 7818
% 11.21/4.93  #Tautology    : 5468
% 11.21/4.93  #SimpNegUnit  : 6
% 11.21/4.93  #BackRed      : 22
% 11.21/4.93  
% 11.21/4.93  #Partial instantiations: 0
% 11.21/4.93  #Strategies tried      : 1
% 11.21/4.93  
% 11.21/4.93  Timing (in seconds)
% 11.21/4.93  ----------------------
% 11.21/4.94  Preprocessing        : 0.38
% 11.21/4.94  Parsing              : 0.21
% 11.21/4.94  CNF conversion       : 0.02
% 11.21/4.94  Main loop            : 3.70
% 11.21/4.94  Inferencing          : 0.70
% 11.21/4.94  Reduction            : 2.04
% 11.21/4.94  Demodulation         : 1.76
% 11.21/4.94  BG Simplification    : 0.08
% 11.21/4.94  Subsumption          : 0.69
% 11.21/4.94  Abstraction          : 0.10
% 11.21/4.94  MUC search           : 0.00
% 11.21/4.94  Cooper               : 0.00
% 11.21/4.94  Total                : 4.13
% 11.21/4.94  Index Insertion      : 0.00
% 11.21/4.94  Index Deletion       : 0.00
% 11.21/4.94  Index Matching       : 0.00
% 11.21/4.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
