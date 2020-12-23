%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:48 EST 2020

% Result     : Theorem 12.01s
% Output     : CNFRefutation 12.19s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 128 expanded)
%              Number of leaves         :   34 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  124 ( 199 expanded)
%              Number of equality atoms :   36 (  47 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_88,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_56,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_151,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_20,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_50,plain,(
    ! [A_34] : ~ v1_xboole_0(k1_zfmisc_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_313,plain,(
    ! [B_62,A_63] :
      ( r2_hidden(B_62,A_63)
      | ~ m1_subset_1(B_62,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    ! [C_29,A_25] :
      ( r1_tarski(C_29,A_25)
      | ~ r2_hidden(C_29,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_317,plain,(
    ! [B_62,A_25] :
      ( r1_tarski(B_62,A_25)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_25))
      | v1_xboole_0(k1_zfmisc_1(A_25)) ) ),
    inference(resolution,[status(thm)],[c_313,c_28])).

tff(c_362,plain,(
    ! [B_65,A_66] :
      ( r1_tarski(B_65,A_66)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_317])).

tff(c_375,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_362])).

tff(c_16,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_142,plain,(
    ! [A_44,B_45] :
      ( k2_xboole_0(A_44,B_45) = B_45
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_161,plain,(
    ! [A_47] : k2_xboole_0(k1_xboole_0,A_47) = A_47 ),
    inference(resolution,[status(thm)],[c_16,c_142])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_171,plain,(
    ! [A_47] : k2_xboole_0(A_47,k1_xboole_0) = A_47 ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_2])).

tff(c_1014,plain,(
    ! [A_97,B_98,C_99] :
      ( r1_tarski(k4_xboole_0(A_97,B_98),C_99)
      | ~ r1_tarski(A_97,k2_xboole_0(B_98,C_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_269,plain,(
    ! [B_57,A_58] :
      ( B_57 = A_58
      | ~ r1_tarski(B_57,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_281,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_269])).

tff(c_1021,plain,(
    ! [A_97,B_98] :
      ( k4_xboole_0(A_97,B_98) = k1_xboole_0
      | ~ r1_tarski(A_97,k2_xboole_0(B_98,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1014,c_281])).

tff(c_2105,plain,(
    ! [A_133,B_134] :
      ( k4_xboole_0(A_133,B_134) = k1_xboole_0
      | ~ r1_tarski(A_133,B_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_1021])).

tff(c_2205,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_375,c_2105])).

tff(c_26,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2327,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2205,c_26])).

tff(c_2339,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2327])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1236,plain,(
    ! [A_106,B_107] :
      ( k4_xboole_0(A_106,B_107) = k3_subset_1(A_106,B_107)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1249,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1236])).

tff(c_1309,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1249,c_26])).

tff(c_1312,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1309])).

tff(c_14501,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2339,c_1312])).

tff(c_62,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_250,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_62])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1248,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_1236])).

tff(c_24,plain,(
    ! [A_20,B_21,C_22] :
      ( r1_tarski(A_20,k2_xboole_0(B_21,C_22))
      | ~ r1_tarski(k4_xboole_0(A_20,B_21),C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5330,plain,(
    ! [C_178] :
      ( r1_tarski('#skF_3',k2_xboole_0('#skF_5',C_178))
      | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),C_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1248,c_24])).

tff(c_5381,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_250,c_5330])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k2_xboole_0(A_10,B_11) = B_11
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4944,plain,(
    ! [A_172,B_173,C_174] :
      ( k2_xboole_0(k4_xboole_0(A_172,B_173),C_174) = C_174
      | ~ r1_tarski(A_172,k2_xboole_0(B_173,C_174)) ) ),
    inference(resolution,[status(thm)],[c_1014,c_14])).

tff(c_27148,plain,(
    ! [A_457,A_458,B_459] :
      ( k2_xboole_0(k4_xboole_0(A_457,A_458),B_459) = B_459
      | ~ r1_tarski(A_457,k2_xboole_0(B_459,A_458)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4944])).

tff(c_27445,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_5381,c_27148])).

tff(c_27693,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14501,c_27445])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_410,plain,(
    ! [A_67,C_68,B_69] :
      ( r1_tarski(A_67,C_68)
      | ~ r1_tarski(k2_xboole_0(A_67,B_69),C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_440,plain,(
    ! [A_67,B_69] : r1_tarski(A_67,k2_xboole_0(A_67,B_69)) ),
    inference(resolution,[status(thm)],[c_10,c_410])).

tff(c_27837,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_27693,c_440])).

tff(c_27862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_27837])).

tff(c_27864,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_28575,plain,(
    ! [A_503,B_504] :
      ( k4_xboole_0(A_503,B_504) = k3_subset_1(A_503,B_504)
      | ~ m1_subset_1(B_504,k1_zfmisc_1(A_503)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_28588,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_28575])).

tff(c_18,plain,(
    ! [C_15,B_14,A_13] :
      ( r1_tarski(k4_xboole_0(C_15,B_14),k4_xboole_0(C_15,A_13))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28750,plain,(
    ! [A_511,B_512,C_513] :
      ( r1_tarski(A_511,k2_xboole_0(B_512,C_513))
      | ~ r1_tarski(k4_xboole_0(A_511,B_512),C_513) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_31941,plain,(
    ! [C_577,B_578,A_579] :
      ( r1_tarski(C_577,k2_xboole_0(B_578,k4_xboole_0(C_577,A_579)))
      | ~ r1_tarski(A_579,B_578) ) ),
    inference(resolution,[status(thm)],[c_18,c_28750])).

tff(c_34184,plain,(
    ! [B_611] :
      ( r1_tarski('#skF_3',k2_xboole_0(B_611,k3_subset_1('#skF_3','#skF_4')))
      | ~ r1_tarski('#skF_4',B_611) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28588,c_31941])).

tff(c_28587,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_28575])).

tff(c_29074,plain,(
    ! [A_520,B_521,C_522] :
      ( r1_tarski(k4_xboole_0(A_520,B_521),C_522)
      | ~ r1_tarski(A_520,k2_xboole_0(B_521,C_522)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32423,plain,(
    ! [C_585] :
      ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),C_585)
      | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_5',C_585)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28587,c_29074])).

tff(c_27863,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_32448,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_32423,c_27863])).

tff(c_34187,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_34184,c_32448])).

tff(c_34236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27864,c_34187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n006.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 12:14:52 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.01/5.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.01/5.25  
% 12.01/5.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.01/5.25  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 12.01/5.25  
% 12.01/5.25  %Foreground sorts:
% 12.01/5.25  
% 12.01/5.25  
% 12.01/5.25  %Background operators:
% 12.01/5.25  
% 12.01/5.25  
% 12.01/5.25  %Foreground operators:
% 12.01/5.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.01/5.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.01/5.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.01/5.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.01/5.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.01/5.25  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 12.01/5.25  tff('#skF_5', type, '#skF_5': $i).
% 12.01/5.25  tff('#skF_3', type, '#skF_3': $i).
% 12.01/5.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.01/5.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.01/5.25  tff('#skF_4', type, '#skF_4': $i).
% 12.01/5.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.01/5.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.01/5.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.01/5.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.01/5.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.01/5.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.01/5.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.01/5.25  
% 12.19/5.27  tff(f_98, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 12.19/5.27  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 12.19/5.27  tff(f_88, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 12.19/5.27  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 12.19/5.27  tff(f_68, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 12.19/5.27  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 12.19/5.27  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 12.19/5.27  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.19/5.27  tff(f_55, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 12.19/5.27  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.19/5.27  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.19/5.27  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.19/5.27  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 12.19/5.27  tff(f_59, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 12.19/5.27  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 12.19/5.27  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 12.19/5.27  tff(c_56, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.19/5.27  tff(c_151, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_56])).
% 12.19/5.27  tff(c_20, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.19/5.27  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.19/5.27  tff(c_50, plain, (![A_34]: (~v1_xboole_0(k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.19/5.27  tff(c_313, plain, (![B_62, A_63]: (r2_hidden(B_62, A_63) | ~m1_subset_1(B_62, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.19/5.27  tff(c_28, plain, (![C_29, A_25]: (r1_tarski(C_29, A_25) | ~r2_hidden(C_29, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.19/5.27  tff(c_317, plain, (![B_62, A_25]: (r1_tarski(B_62, A_25) | ~m1_subset_1(B_62, k1_zfmisc_1(A_25)) | v1_xboole_0(k1_zfmisc_1(A_25)))), inference(resolution, [status(thm)], [c_313, c_28])).
% 12.19/5.27  tff(c_362, plain, (![B_65, A_66]: (r1_tarski(B_65, A_66) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)))), inference(negUnitSimplification, [status(thm)], [c_50, c_317])).
% 12.19/5.27  tff(c_375, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_362])).
% 12.19/5.27  tff(c_16, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.19/5.27  tff(c_142, plain, (![A_44, B_45]: (k2_xboole_0(A_44, B_45)=B_45 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.19/5.27  tff(c_161, plain, (![A_47]: (k2_xboole_0(k1_xboole_0, A_47)=A_47)), inference(resolution, [status(thm)], [c_16, c_142])).
% 12.19/5.27  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.19/5.27  tff(c_171, plain, (![A_47]: (k2_xboole_0(A_47, k1_xboole_0)=A_47)), inference(superposition, [status(thm), theory('equality')], [c_161, c_2])).
% 12.19/5.27  tff(c_1014, plain, (![A_97, B_98, C_99]: (r1_tarski(k4_xboole_0(A_97, B_98), C_99) | ~r1_tarski(A_97, k2_xboole_0(B_98, C_99)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.19/5.27  tff(c_269, plain, (![B_57, A_58]: (B_57=A_58 | ~r1_tarski(B_57, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.19/5.27  tff(c_281, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_269])).
% 12.19/5.27  tff(c_1021, plain, (![A_97, B_98]: (k4_xboole_0(A_97, B_98)=k1_xboole_0 | ~r1_tarski(A_97, k2_xboole_0(B_98, k1_xboole_0)))), inference(resolution, [status(thm)], [c_1014, c_281])).
% 12.19/5.27  tff(c_2105, plain, (![A_133, B_134]: (k4_xboole_0(A_133, B_134)=k1_xboole_0 | ~r1_tarski(A_133, B_134))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_1021])).
% 12.19/5.27  tff(c_2205, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_375, c_2105])).
% 12.19/5.27  tff(c_26, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.19/5.27  tff(c_2327, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2205, c_26])).
% 12.19/5.27  tff(c_2339, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2327])).
% 12.19/5.27  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.19/5.27  tff(c_1236, plain, (![A_106, B_107]: (k4_xboole_0(A_106, B_107)=k3_subset_1(A_106, B_107) | ~m1_subset_1(B_107, k1_zfmisc_1(A_106)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.19/5.27  tff(c_1249, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_1236])).
% 12.19/5.27  tff(c_1309, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1249, c_26])).
% 12.19/5.27  tff(c_1312, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1309])).
% 12.19/5.27  tff(c_14501, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2339, c_1312])).
% 12.19/5.27  tff(c_62, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.19/5.27  tff(c_250, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_151, c_62])).
% 12.19/5.27  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.19/5.27  tff(c_1248, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_1236])).
% 12.19/5.27  tff(c_24, plain, (![A_20, B_21, C_22]: (r1_tarski(A_20, k2_xboole_0(B_21, C_22)) | ~r1_tarski(k4_xboole_0(A_20, B_21), C_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.19/5.27  tff(c_5330, plain, (![C_178]: (r1_tarski('#skF_3', k2_xboole_0('#skF_5', C_178)) | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), C_178))), inference(superposition, [status(thm), theory('equality')], [c_1248, c_24])).
% 12.19/5.27  tff(c_5381, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_250, c_5330])).
% 12.19/5.27  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, B_11)=B_11 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.19/5.27  tff(c_4944, plain, (![A_172, B_173, C_174]: (k2_xboole_0(k4_xboole_0(A_172, B_173), C_174)=C_174 | ~r1_tarski(A_172, k2_xboole_0(B_173, C_174)))), inference(resolution, [status(thm)], [c_1014, c_14])).
% 12.19/5.27  tff(c_27148, plain, (![A_457, A_458, B_459]: (k2_xboole_0(k4_xboole_0(A_457, A_458), B_459)=B_459 | ~r1_tarski(A_457, k2_xboole_0(B_459, A_458)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4944])).
% 12.19/5.27  tff(c_27445, plain, (k2_xboole_0(k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4')), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_5381, c_27148])).
% 12.19/5.27  tff(c_27693, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_14501, c_27445])).
% 12.19/5.27  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.19/5.27  tff(c_410, plain, (![A_67, C_68, B_69]: (r1_tarski(A_67, C_68) | ~r1_tarski(k2_xboole_0(A_67, B_69), C_68))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.19/5.27  tff(c_440, plain, (![A_67, B_69]: (r1_tarski(A_67, k2_xboole_0(A_67, B_69)))), inference(resolution, [status(thm)], [c_10, c_410])).
% 12.19/5.27  tff(c_27837, plain, (r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_27693, c_440])).
% 12.19/5.27  tff(c_27862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_27837])).
% 12.19/5.27  tff(c_27864, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_56])).
% 12.19/5.27  tff(c_28575, plain, (![A_503, B_504]: (k4_xboole_0(A_503, B_504)=k3_subset_1(A_503, B_504) | ~m1_subset_1(B_504, k1_zfmisc_1(A_503)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.19/5.27  tff(c_28588, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_28575])).
% 12.19/5.27  tff(c_18, plain, (![C_15, B_14, A_13]: (r1_tarski(k4_xboole_0(C_15, B_14), k4_xboole_0(C_15, A_13)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.19/5.27  tff(c_28750, plain, (![A_511, B_512, C_513]: (r1_tarski(A_511, k2_xboole_0(B_512, C_513)) | ~r1_tarski(k4_xboole_0(A_511, B_512), C_513))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.19/5.27  tff(c_31941, plain, (![C_577, B_578, A_579]: (r1_tarski(C_577, k2_xboole_0(B_578, k4_xboole_0(C_577, A_579))) | ~r1_tarski(A_579, B_578))), inference(resolution, [status(thm)], [c_18, c_28750])).
% 12.19/5.27  tff(c_34184, plain, (![B_611]: (r1_tarski('#skF_3', k2_xboole_0(B_611, k3_subset_1('#skF_3', '#skF_4'))) | ~r1_tarski('#skF_4', B_611))), inference(superposition, [status(thm), theory('equality')], [c_28588, c_31941])).
% 12.19/5.27  tff(c_28587, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_28575])).
% 12.19/5.27  tff(c_29074, plain, (![A_520, B_521, C_522]: (r1_tarski(k4_xboole_0(A_520, B_521), C_522) | ~r1_tarski(A_520, k2_xboole_0(B_521, C_522)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.19/5.27  tff(c_32423, plain, (![C_585]: (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), C_585) | ~r1_tarski('#skF_3', k2_xboole_0('#skF_5', C_585)))), inference(superposition, [status(thm), theory('equality')], [c_28587, c_29074])).
% 12.19/5.27  tff(c_27863, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_56])).
% 12.19/5.27  tff(c_32448, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_32423, c_27863])).
% 12.19/5.27  tff(c_34187, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_34184, c_32448])).
% 12.19/5.27  tff(c_34236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27864, c_34187])).
% 12.19/5.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.19/5.27  
% 12.19/5.27  Inference rules
% 12.19/5.27  ----------------------
% 12.19/5.27  #Ref     : 0
% 12.19/5.27  #Sup     : 8532
% 12.19/5.27  #Fact    : 0
% 12.19/5.27  #Define  : 0
% 12.19/5.27  #Split   : 13
% 12.19/5.27  #Chain   : 0
% 12.19/5.27  #Close   : 0
% 12.19/5.27  
% 12.19/5.27  Ordering : KBO
% 12.19/5.27  
% 12.19/5.27  Simplification rules
% 12.19/5.27  ----------------------
% 12.19/5.27  #Subsume      : 554
% 12.19/5.27  #Demod        : 6714
% 12.19/5.27  #Tautology    : 5184
% 12.19/5.27  #SimpNegUnit  : 81
% 12.19/5.27  #BackRed      : 5
% 12.19/5.27  
% 12.19/5.27  #Partial instantiations: 0
% 12.19/5.27  #Strategies tried      : 1
% 12.20/5.27  
% 12.20/5.27  Timing (in seconds)
% 12.20/5.27  ----------------------
% 12.20/5.27  Preprocessing        : 0.33
% 12.20/5.27  Parsing              : 0.17
% 12.20/5.27  CNF conversion       : 0.02
% 12.20/5.27  Main loop            : 4.21
% 12.20/5.27  Inferencing          : 0.76
% 12.20/5.27  Reduction            : 2.20
% 12.20/5.27  Demodulation         : 1.85
% 12.20/5.27  BG Simplification    : 0.08
% 12.20/5.27  Subsumption          : 0.91
% 12.20/5.27  Abstraction          : 0.11
% 12.20/5.27  MUC search           : 0.00
% 12.20/5.27  Cooper               : 0.00
% 12.20/5.27  Total                : 4.57
% 12.20/5.27  Index Insertion      : 0.00
% 12.20/5.27  Index Deletion       : 0.00
% 12.20/5.27  Index Matching       : 0.00
% 12.20/5.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
