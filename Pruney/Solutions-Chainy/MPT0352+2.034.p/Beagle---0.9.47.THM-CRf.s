%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:51 EST 2020

% Result     : Theorem 33.56s
% Output     : CNFRefutation 33.56s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 140 expanded)
%              Number of leaves         :   36 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :  135 ( 233 expanded)
%              Number of equality atoms :   25 (  36 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_101,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_81,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_52,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_88,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_20,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_84,plain,(
    ! [A_45,B_46] : r1_tarski(k4_xboole_0(A_45,B_46),A_45) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_87,plain,(
    ! [A_20] : r1_tarski(A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_84])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_46,plain,(
    ! [A_36] : ~ v1_xboole_0(k1_zfmisc_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_409,plain,(
    ! [B_83,A_84] :
      ( r2_hidden(B_83,A_84)
      | ~ m1_subset_1(B_83,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,(
    ! [A_31] : k3_tarski(k1_zfmisc_1(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_254,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,k3_tarski(B_65))
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_257,plain,(
    ! [A_64,A_31] :
      ( r1_tarski(A_64,A_31)
      | ~ r2_hidden(A_64,k1_zfmisc_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_254])).

tff(c_413,plain,(
    ! [B_83,A_31] :
      ( r1_tarski(B_83,A_31)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_31))
      | v1_xboole_0(k1_zfmisc_1(A_31)) ) ),
    inference(resolution,[status(thm)],[c_409,c_257])).

tff(c_1299,plain,(
    ! [B_135,A_136] :
      ( r1_tarski(B_135,A_136)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(A_136)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_413])).

tff(c_1311,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1299])).

tff(c_12,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,C_11)
      | ~ r1_tarski(B_10,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1319,plain,(
    ! [A_137] :
      ( r1_tarski(A_137,'#skF_1')
      | ~ r1_tarski(A_137,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1311,c_12])).

tff(c_1361,plain,(
    ! [B_19] : r1_tarski(k4_xboole_0('#skF_3',B_19),'#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_1319])).

tff(c_26,plain,(
    ! [A_25,B_26] : r1_xboole_0(k4_xboole_0(A_25,B_26),B_26) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_560,plain,(
    ! [B_94,A_95] :
      ( ~ r1_xboole_0(B_94,A_95)
      | ~ r1_tarski(B_94,A_95)
      | v1_xboole_0(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3961,plain,(
    ! [A_205,B_206] :
      ( ~ r1_tarski(k4_xboole_0(A_205,B_206),B_206)
      | v1_xboole_0(k4_xboole_0(A_205,B_206)) ) ),
    inference(resolution,[status(thm)],[c_26,c_560])).

tff(c_4045,plain,(
    v1_xboole_0(k4_xboole_0('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1361,c_3961])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4068,plain,(
    k4_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4045,c_4])).

tff(c_22,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4303,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4068,c_22])).

tff(c_4346,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20,c_4303])).

tff(c_1429,plain,(
    ! [A_141,B_142] :
      ( k4_xboole_0(A_141,B_142) = k3_subset_1(A_141,B_142)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(A_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1441,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1429])).

tff(c_1484,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1441,c_22])).

tff(c_11465,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4346,c_1484])).

tff(c_58,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_236,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_58])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1442,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1429])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_xboole_0(A_6,C_8)
      | ~ r1_tarski(A_6,k4_xboole_0(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14703,plain,(
    ! [A_352] :
      ( r1_xboole_0(A_352,'#skF_2')
      | ~ r1_tarski(A_352,k3_subset_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1442,c_8])).

tff(c_14813,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_236,c_14703])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_xboole_0(B_5,A_4)
      | ~ r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14828,plain,(
    r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_14813,c_6])).

tff(c_28,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = A_27
      | ~ r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14838,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14828,c_28])).

tff(c_1312,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1299])).

tff(c_14,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_tarski(k4_xboole_0(A_12,C_14),k4_xboole_0(B_13,C_14))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1603,plain,(
    ! [A_143,C_144,B_145] :
      ( r1_tarski(k4_xboole_0(A_143,C_144),k4_xboole_0(B_145,C_144))
      | ~ r1_tarski(A_143,B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10703,plain,(
    ! [A_279,B_280,C_281,A_282] :
      ( r1_tarski(A_279,k4_xboole_0(B_280,C_281))
      | ~ r1_tarski(A_279,k4_xboole_0(A_282,C_281))
      | ~ r1_tarski(A_282,B_280) ) ),
    inference(resolution,[status(thm)],[c_1603,c_12])).

tff(c_116303,plain,(
    ! [A_1095,C_1096,B_1097,B_1098] :
      ( r1_tarski(k4_xboole_0(A_1095,C_1096),k4_xboole_0(B_1097,C_1096))
      | ~ r1_tarski(B_1098,B_1097)
      | ~ r1_tarski(A_1095,B_1098) ) ),
    inference(resolution,[status(thm)],[c_14,c_10703])).

tff(c_126937,plain,(
    ! [A_1146,C_1147] :
      ( r1_tarski(k4_xboole_0(A_1146,C_1147),k4_xboole_0('#skF_1',C_1147))
      | ~ r1_tarski(A_1146,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1312,c_116303])).

tff(c_127158,plain,
    ( r1_tarski('#skF_2',k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14838,c_126937])).

tff(c_127338,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_11465,c_127158])).

tff(c_127340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_127338])).

tff(c_127341,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_127342,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_128464,plain,(
    ! [A_1231,B_1232] :
      ( k4_xboole_0(A_1231,B_1232) = k3_subset_1(A_1231,B_1232)
      | ~ m1_subset_1(B_1232,k1_zfmisc_1(A_1231)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_128477,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_128464])).

tff(c_128476,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_128464])).

tff(c_16,plain,(
    ! [C_17,B_16,A_15] :
      ( r1_tarski(k4_xboole_0(C_17,B_16),k4_xboole_0(C_17,A_15))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_153813,plain,(
    ! [A_1632] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),k4_xboole_0('#skF_1',A_1632))
      | ~ r1_tarski(A_1632,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128476,c_16])).

tff(c_153857,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_128477,c_153813])).

tff(c_153891,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127342,c_153857])).

tff(c_153893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127341,c_153891])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 11:40:45 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 33.56/23.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 33.56/23.47  
% 33.56/23.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 33.56/23.48  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 33.56/23.48  
% 33.56/23.48  %Foreground sorts:
% 33.56/23.48  
% 33.56/23.48  
% 33.56/23.48  %Background operators:
% 33.56/23.48  
% 33.56/23.48  
% 33.56/23.48  %Foreground operators:
% 33.56/23.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 33.56/23.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 33.56/23.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 33.56/23.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 33.56/23.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 33.56/23.48  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 33.56/23.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 33.56/23.48  tff('#skF_2', type, '#skF_2': $i).
% 33.56/23.48  tff('#skF_3', type, '#skF_3': $i).
% 33.56/23.48  tff('#skF_1', type, '#skF_1': $i).
% 33.56/23.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 33.56/23.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 33.56/23.48  tff(k3_tarski, type, k3_tarski: $i > $i).
% 33.56/23.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 33.56/23.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 33.56/23.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 33.56/23.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 33.56/23.48  
% 33.56/23.49  tff(f_111, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 33.56/23.49  tff(f_59, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 33.56/23.49  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 33.56/23.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 33.56/23.49  tff(f_101, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 33.56/23.49  tff(f_94, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 33.56/23.49  tff(f_81, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 33.56/23.49  tff(f_79, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 33.56/23.49  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 33.56/23.49  tff(f_71, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 33.56/23.49  tff(f_69, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 33.56/23.49  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 33.56/23.49  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 33.56/23.49  tff(f_98, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 33.56/23.49  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 33.56/23.49  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 33.56/23.49  tff(f_75, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 33.56/23.49  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_xboole_1)).
% 33.56/23.49  tff(f_55, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 33.56/23.49  tff(c_52, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 33.56/23.49  tff(c_88, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 33.56/23.49  tff(c_20, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_59])).
% 33.56/23.49  tff(c_84, plain, (![A_45, B_46]: (r1_tarski(k4_xboole_0(A_45, B_46), A_45))), inference(cnfTransformation, [status(thm)], [f_57])).
% 33.56/23.49  tff(c_87, plain, (![A_20]: (r1_tarski(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_20, c_84])).
% 33.56/23.49  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 33.56/23.49  tff(c_18, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 33.56/23.49  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 33.56/23.49  tff(c_46, plain, (![A_36]: (~v1_xboole_0(k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 33.56/23.49  tff(c_409, plain, (![B_83, A_84]: (r2_hidden(B_83, A_84) | ~m1_subset_1(B_83, A_84) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_94])).
% 33.56/23.49  tff(c_34, plain, (![A_31]: (k3_tarski(k1_zfmisc_1(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_81])).
% 33.56/23.49  tff(c_254, plain, (![A_64, B_65]: (r1_tarski(A_64, k3_tarski(B_65)) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_79])).
% 33.56/23.49  tff(c_257, plain, (![A_64, A_31]: (r1_tarski(A_64, A_31) | ~r2_hidden(A_64, k1_zfmisc_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_254])).
% 33.56/23.49  tff(c_413, plain, (![B_83, A_31]: (r1_tarski(B_83, A_31) | ~m1_subset_1(B_83, k1_zfmisc_1(A_31)) | v1_xboole_0(k1_zfmisc_1(A_31)))), inference(resolution, [status(thm)], [c_409, c_257])).
% 33.56/23.49  tff(c_1299, plain, (![B_135, A_136]: (r1_tarski(B_135, A_136) | ~m1_subset_1(B_135, k1_zfmisc_1(A_136)))), inference(negUnitSimplification, [status(thm)], [c_46, c_413])).
% 33.56/23.49  tff(c_1311, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_1299])).
% 33.56/23.49  tff(c_12, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, C_11) | ~r1_tarski(B_10, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 33.56/23.49  tff(c_1319, plain, (![A_137]: (r1_tarski(A_137, '#skF_1') | ~r1_tarski(A_137, '#skF_3'))), inference(resolution, [status(thm)], [c_1311, c_12])).
% 33.56/23.49  tff(c_1361, plain, (![B_19]: (r1_tarski(k4_xboole_0('#skF_3', B_19), '#skF_1'))), inference(resolution, [status(thm)], [c_18, c_1319])).
% 33.56/23.49  tff(c_26, plain, (![A_25, B_26]: (r1_xboole_0(k4_xboole_0(A_25, B_26), B_26))), inference(cnfTransformation, [status(thm)], [f_71])).
% 33.56/23.49  tff(c_560, plain, (![B_94, A_95]: (~r1_xboole_0(B_94, A_95) | ~r1_tarski(B_94, A_95) | v1_xboole_0(B_94))), inference(cnfTransformation, [status(thm)], [f_69])).
% 33.56/23.49  tff(c_3961, plain, (![A_205, B_206]: (~r1_tarski(k4_xboole_0(A_205, B_206), B_206) | v1_xboole_0(k4_xboole_0(A_205, B_206)))), inference(resolution, [status(thm)], [c_26, c_560])).
% 33.56/23.49  tff(c_4045, plain, (v1_xboole_0(k4_xboole_0('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_1361, c_3961])).
% 33.56/23.49  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 33.56/23.49  tff(c_4068, plain, (k4_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_4045, c_4])).
% 33.56/23.49  tff(c_22, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 33.56/23.49  tff(c_4303, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4068, c_22])).
% 33.56/23.49  tff(c_4346, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20, c_4303])).
% 33.56/23.49  tff(c_1429, plain, (![A_141, B_142]: (k4_xboole_0(A_141, B_142)=k3_subset_1(A_141, B_142) | ~m1_subset_1(B_142, k1_zfmisc_1(A_141)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 33.56/23.49  tff(c_1441, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_1429])).
% 33.56/23.49  tff(c_1484, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1441, c_22])).
% 33.56/23.49  tff(c_11465, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4346, c_1484])).
% 33.56/23.49  tff(c_58, plain, (r1_tarski('#skF_2', '#skF_3') | r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 33.56/23.49  tff(c_236, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_88, c_58])).
% 33.56/23.49  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 33.56/23.49  tff(c_1442, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_1429])).
% 33.56/23.49  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_xboole_0(A_6, C_8) | ~r1_tarski(A_6, k4_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 33.56/23.49  tff(c_14703, plain, (![A_352]: (r1_xboole_0(A_352, '#skF_2') | ~r1_tarski(A_352, k3_subset_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1442, c_8])).
% 33.56/23.49  tff(c_14813, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_236, c_14703])).
% 33.56/23.49  tff(c_6, plain, (![B_5, A_4]: (r1_xboole_0(B_5, A_4) | ~r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 33.56/23.49  tff(c_14828, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_14813, c_6])).
% 33.56/23.49  tff(c_28, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=A_27 | ~r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_75])).
% 33.56/23.49  tff(c_14838, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))='#skF_2'), inference(resolution, [status(thm)], [c_14828, c_28])).
% 33.56/23.49  tff(c_1312, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_1299])).
% 33.56/23.49  tff(c_14, plain, (![A_12, C_14, B_13]: (r1_tarski(k4_xboole_0(A_12, C_14), k4_xboole_0(B_13, C_14)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 33.56/23.49  tff(c_1603, plain, (![A_143, C_144, B_145]: (r1_tarski(k4_xboole_0(A_143, C_144), k4_xboole_0(B_145, C_144)) | ~r1_tarski(A_143, B_145))), inference(cnfTransformation, [status(thm)], [f_51])).
% 33.56/23.49  tff(c_10703, plain, (![A_279, B_280, C_281, A_282]: (r1_tarski(A_279, k4_xboole_0(B_280, C_281)) | ~r1_tarski(A_279, k4_xboole_0(A_282, C_281)) | ~r1_tarski(A_282, B_280))), inference(resolution, [status(thm)], [c_1603, c_12])).
% 33.56/23.49  tff(c_116303, plain, (![A_1095, C_1096, B_1097, B_1098]: (r1_tarski(k4_xboole_0(A_1095, C_1096), k4_xboole_0(B_1097, C_1096)) | ~r1_tarski(B_1098, B_1097) | ~r1_tarski(A_1095, B_1098))), inference(resolution, [status(thm)], [c_14, c_10703])).
% 33.56/23.49  tff(c_126937, plain, (![A_1146, C_1147]: (r1_tarski(k4_xboole_0(A_1146, C_1147), k4_xboole_0('#skF_1', C_1147)) | ~r1_tarski(A_1146, '#skF_2'))), inference(resolution, [status(thm)], [c_1312, c_116303])).
% 33.56/23.49  tff(c_127158, plain, (r1_tarski('#skF_2', k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14838, c_126937])).
% 33.56/23.49  tff(c_127338, plain, (r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_11465, c_127158])).
% 33.56/23.49  tff(c_127340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_127338])).
% 33.56/23.49  tff(c_127341, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_52])).
% 33.56/23.49  tff(c_127342, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 33.56/23.49  tff(c_128464, plain, (![A_1231, B_1232]: (k4_xboole_0(A_1231, B_1232)=k3_subset_1(A_1231, B_1232) | ~m1_subset_1(B_1232, k1_zfmisc_1(A_1231)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 33.56/23.49  tff(c_128477, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_128464])).
% 33.56/23.49  tff(c_128476, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_128464])).
% 33.56/23.49  tff(c_16, plain, (![C_17, B_16, A_15]: (r1_tarski(k4_xboole_0(C_17, B_16), k4_xboole_0(C_17, A_15)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 33.56/23.49  tff(c_153813, plain, (![A_1632]: (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k4_xboole_0('#skF_1', A_1632)) | ~r1_tarski(A_1632, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_128476, c_16])).
% 33.56/23.49  tff(c_153857, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_128477, c_153813])).
% 33.56/23.49  tff(c_153891, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_127342, c_153857])).
% 33.56/23.49  tff(c_153893, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127341, c_153891])).
% 33.56/23.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 33.56/23.49  
% 33.56/23.49  Inference rules
% 33.56/23.49  ----------------------
% 33.56/23.49  #Ref     : 0
% 33.56/23.49  #Sup     : 39629
% 33.56/23.49  #Fact    : 0
% 33.56/23.49  #Define  : 0
% 33.56/23.49  #Split   : 33
% 33.56/23.49  #Chain   : 0
% 33.56/23.49  #Close   : 0
% 33.56/23.49  
% 33.56/23.49  Ordering : KBO
% 33.56/23.49  
% 33.56/23.49  Simplification rules
% 33.56/23.49  ----------------------
% 33.56/23.49  #Subsume      : 8170
% 33.56/23.49  #Demod        : 35815
% 33.56/23.49  #Tautology    : 22560
% 33.56/23.49  #SimpNegUnit  : 325
% 33.56/23.49  #BackRed      : 49
% 33.56/23.49  
% 33.56/23.49  #Partial instantiations: 0
% 33.56/23.49  #Strategies tried      : 1
% 33.56/23.49  
% 33.56/23.49  Timing (in seconds)
% 33.56/23.49  ----------------------
% 33.56/23.50  Preprocessing        : 0.33
% 33.56/23.50  Parsing              : 0.17
% 33.56/23.50  CNF conversion       : 0.02
% 33.56/23.50  Main loop            : 22.38
% 33.56/23.50  Inferencing          : 2.32
% 33.56/23.50  Reduction            : 12.82
% 33.56/23.50  Demodulation         : 10.62
% 33.56/23.50  BG Simplification    : 0.20
% 33.56/23.50  Subsumption          : 6.18
% 33.56/23.50  Abstraction          : 0.33
% 33.56/23.50  MUC search           : 0.00
% 33.56/23.50  Cooper               : 0.00
% 33.56/23.50  Total                : 22.75
% 33.56/23.50  Index Insertion      : 0.00
% 33.56/23.50  Index Deletion       : 0.00
% 33.56/23.50  Index Matching       : 0.00
% 33.56/23.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
