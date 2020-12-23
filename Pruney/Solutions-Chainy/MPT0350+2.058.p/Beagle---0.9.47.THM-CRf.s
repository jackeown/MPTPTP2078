%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:33 EST 2020

% Result     : Theorem 14.21s
% Output     : CNFRefutation 14.33s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 179 expanded)
%              Number of leaves         :   43 (  77 expanded)
%              Depth                    :   14
%              Number of atoms          :  101 ( 210 expanded)
%              Number of equality atoms :   59 ( 126 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_88,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_50,plain,(
    ! [A_37] : k2_subset_1(A_37) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_60,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_63,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_60])).

tff(c_16,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_750,plain,(
    ! [A_99,B_100] :
      ( k4_xboole_0(A_99,B_100) = k3_subset_1(A_99,B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_763,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_750])).

tff(c_56,plain,(
    ! [A_42] : ~ v1_xboole_0(k1_zfmisc_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_356,plain,(
    ! [B_77,A_78] :
      ( r2_hidden(B_77,A_78)
      | ~ m1_subset_1(B_77,A_78)
      | v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    ! [C_32,A_28] :
      ( r1_tarski(C_32,A_28)
      | ~ r2_hidden(C_32,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_360,plain,(
    ! [B_77,A_28] :
      ( r1_tarski(B_77,A_28)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_28))
      | v1_xboole_0(k1_zfmisc_1(A_28)) ) ),
    inference(resolution,[status(thm)],[c_356,c_28])).

tff(c_493,plain,(
    ! [B_88,A_89] :
      ( r1_tarski(B_88,A_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_89)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_360])).

tff(c_502,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_493])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_506,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_502,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_279,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k4_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_532,plain,(
    ! [A_92,B_93] : k5_xboole_0(A_92,k3_xboole_0(B_93,A_92)) = k4_xboole_0(A_92,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_279])).

tff(c_549,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_532])).

tff(c_765,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_763,c_549])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_110,plain,(
    ! [B_53,A_54] : k5_xboole_0(B_53,A_54) = k5_xboole_0(A_54,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_126,plain,(
    ! [A_54] : k5_xboole_0(k1_xboole_0,A_54) = A_54 ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_16])).

tff(c_20,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1057,plain,(
    ! [A_109,B_110,C_111] : k5_xboole_0(k5_xboole_0(A_109,B_110),C_111) = k5_xboole_0(A_109,k5_xboole_0(B_110,C_111)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1151,plain,(
    ! [A_20,C_111] : k5_xboole_0(A_20,k5_xboole_0(A_20,C_111)) = k5_xboole_0(k1_xboole_0,C_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1057])).

tff(c_1167,plain,(
    ! [A_112,C_113] : k5_xboole_0(A_112,k5_xboole_0(A_112,C_113)) = C_113 ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_1151])).

tff(c_1247,plain,(
    ! [A_114,B_115] : k5_xboole_0(A_114,k5_xboole_0(B_115,A_114)) = B_115 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1167])).

tff(c_1300,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_765,c_1247])).

tff(c_14,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_769,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_14])).

tff(c_776,plain,(
    k3_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_3') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_769,c_12])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_806,plain,(
    k5_xboole_0(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3','#skF_4')) = k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_776,c_8])).

tff(c_822,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_806])).

tff(c_1225,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1167])).

tff(c_1343,plain,(
    ! [B_116,A_117] : k5_xboole_0(k5_xboole_0(B_116,A_117),B_116) = A_117 ),
    inference(superposition,[status(thm),theory(equality)],[c_1247,c_1225])).

tff(c_1399,plain,(
    k5_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_765,c_1343])).

tff(c_292,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_279])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1588,plain,(
    ! [A_120,B_121,C_122] : k5_xboole_0(k3_xboole_0(A_120,B_121),k3_xboole_0(C_122,B_121)) = k3_xboole_0(k5_xboole_0(A_120,C_122),B_121) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1693,plain,(
    ! [A_5,C_122] : k5_xboole_0(A_5,k3_xboole_0(C_122,A_5)) = k3_xboole_0(k5_xboole_0(A_5,C_122),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1588])).

tff(c_2101,plain,(
    ! [A_134,C_135] : k3_xboole_0(A_134,k5_xboole_0(A_134,C_135)) = k4_xboole_0(A_134,C_135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_2,c_1693])).

tff(c_2141,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_3') = k3_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1399,c_2101])).

tff(c_2203,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_822,c_2,c_2141])).

tff(c_22,plain,(
    ! [A_21,B_22] : k5_xboole_0(k5_xboole_0(A_21,B_22),k3_xboole_0(A_21,B_22)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2279,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')),k1_xboole_0) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2203,c_22])).

tff(c_2290,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1300,c_2279])).

tff(c_54,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(k3_subset_1(A_40,B_41),k1_zfmisc_1(A_40))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2810,plain,(
    ! [A_147,B_148,C_149] :
      ( k4_subset_1(A_147,B_148,C_149) = k2_xboole_0(B_148,C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(A_147))
      | ~ m1_subset_1(B_148,k1_zfmisc_1(A_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_37883,plain,(
    ! [A_418,B_419,B_420] :
      ( k4_subset_1(A_418,B_419,k3_subset_1(A_418,B_420)) = k2_xboole_0(B_419,k3_subset_1(A_418,B_420))
      | ~ m1_subset_1(B_419,k1_zfmisc_1(A_418))
      | ~ m1_subset_1(B_420,k1_zfmisc_1(A_418)) ) ),
    inference(resolution,[status(thm)],[c_54,c_2810])).

tff(c_37912,plain,(
    ! [B_421] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_421)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_421))
      | ~ m1_subset_1(B_421,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_62,c_37883])).

tff(c_37935,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_37912])).

tff(c_37947,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2290,c_37935])).

tff(c_37949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_37947])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.21/7.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.21/7.91  
% 14.21/7.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.33/7.92  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 14.33/7.92  
% 14.33/7.92  %Foreground sorts:
% 14.33/7.92  
% 14.33/7.92  
% 14.33/7.92  %Background operators:
% 14.33/7.92  
% 14.33/7.92  
% 14.33/7.92  %Foreground operators:
% 14.33/7.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.33/7.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.33/7.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.33/7.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.33/7.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.33/7.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.33/7.92  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.33/7.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.33/7.92  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 14.33/7.92  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 14.33/7.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.33/7.92  tff('#skF_3', type, '#skF_3': $i).
% 14.33/7.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.33/7.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.33/7.92  tff(k3_tarski, type, k3_tarski: $i > $i).
% 14.33/7.92  tff('#skF_4', type, '#skF_4': $i).
% 14.33/7.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.33/7.92  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 14.33/7.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.33/7.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.33/7.92  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.33/7.92  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 14.33/7.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.33/7.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.33/7.92  
% 14.33/7.93  tff(f_77, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 14.33/7.93  tff(f_99, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 14.33/7.93  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 14.33/7.93  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 14.33/7.93  tff(f_88, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 14.33/7.93  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 14.33/7.93  tff(f_60, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 14.33/7.93  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 14.33/7.93  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.33/7.93  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 14.33/7.93  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 14.33/7.93  tff(f_47, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 14.33/7.93  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 14.33/7.93  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 14.33/7.93  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 14.33/7.93  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 14.33/7.93  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 14.33/7.93  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 14.33/7.93  tff(f_94, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 14.33/7.93  tff(c_50, plain, (![A_37]: (k2_subset_1(A_37)=A_37)), inference(cnfTransformation, [status(thm)], [f_77])).
% 14.33/7.93  tff(c_60, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.33/7.93  tff(c_63, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_60])).
% 14.33/7.93  tff(c_16, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.33/7.93  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.33/7.93  tff(c_750, plain, (![A_99, B_100]: (k4_xboole_0(A_99, B_100)=k3_subset_1(A_99, B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.33/7.93  tff(c_763, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_750])).
% 14.33/7.93  tff(c_56, plain, (![A_42]: (~v1_xboole_0(k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.33/7.93  tff(c_356, plain, (![B_77, A_78]: (r2_hidden(B_77, A_78) | ~m1_subset_1(B_77, A_78) | v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.33/7.93  tff(c_28, plain, (![C_32, A_28]: (r1_tarski(C_32, A_28) | ~r2_hidden(C_32, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 14.33/7.93  tff(c_360, plain, (![B_77, A_28]: (r1_tarski(B_77, A_28) | ~m1_subset_1(B_77, k1_zfmisc_1(A_28)) | v1_xboole_0(k1_zfmisc_1(A_28)))), inference(resolution, [status(thm)], [c_356, c_28])).
% 14.33/7.93  tff(c_493, plain, (![B_88, A_89]: (r1_tarski(B_88, A_89) | ~m1_subset_1(B_88, k1_zfmisc_1(A_89)))), inference(negUnitSimplification, [status(thm)], [c_56, c_360])).
% 14.33/7.93  tff(c_502, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_493])).
% 14.33/7.93  tff(c_12, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.33/7.93  tff(c_506, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_502, c_12])).
% 14.33/7.93  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.33/7.93  tff(c_279, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k4_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.33/7.93  tff(c_532, plain, (![A_92, B_93]: (k5_xboole_0(A_92, k3_xboole_0(B_93, A_92))=k4_xboole_0(A_92, B_93))), inference(superposition, [status(thm), theory('equality')], [c_2, c_279])).
% 14.33/7.93  tff(c_549, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_506, c_532])).
% 14.33/7.93  tff(c_765, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_763, c_549])).
% 14.33/7.93  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.33/7.93  tff(c_110, plain, (![B_53, A_54]: (k5_xboole_0(B_53, A_54)=k5_xboole_0(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.33/7.93  tff(c_126, plain, (![A_54]: (k5_xboole_0(k1_xboole_0, A_54)=A_54)), inference(superposition, [status(thm), theory('equality')], [c_110, c_16])).
% 14.33/7.93  tff(c_20, plain, (![A_20]: (k5_xboole_0(A_20, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.33/7.93  tff(c_1057, plain, (![A_109, B_110, C_111]: (k5_xboole_0(k5_xboole_0(A_109, B_110), C_111)=k5_xboole_0(A_109, k5_xboole_0(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.33/7.93  tff(c_1151, plain, (![A_20, C_111]: (k5_xboole_0(A_20, k5_xboole_0(A_20, C_111))=k5_xboole_0(k1_xboole_0, C_111))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1057])).
% 14.33/7.93  tff(c_1167, plain, (![A_112, C_113]: (k5_xboole_0(A_112, k5_xboole_0(A_112, C_113))=C_113)), inference(demodulation, [status(thm), theory('equality')], [c_126, c_1151])).
% 14.33/7.93  tff(c_1247, plain, (![A_114, B_115]: (k5_xboole_0(A_114, k5_xboole_0(B_115, A_114))=B_115)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1167])).
% 14.33/7.93  tff(c_1300, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_765, c_1247])).
% 14.33/7.93  tff(c_14, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.33/7.93  tff(c_769, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_763, c_14])).
% 14.33/7.93  tff(c_776, plain, (k3_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_769, c_12])).
% 14.33/7.93  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.33/7.93  tff(c_806, plain, (k5_xboole_0(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', '#skF_4'))=k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_776, c_8])).
% 14.33/7.93  tff(c_822, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_806])).
% 14.33/7.93  tff(c_1225, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1167])).
% 14.33/7.93  tff(c_1343, plain, (![B_116, A_117]: (k5_xboole_0(k5_xboole_0(B_116, A_117), B_116)=A_117)), inference(superposition, [status(thm), theory('equality')], [c_1247, c_1225])).
% 14.33/7.93  tff(c_1399, plain, (k5_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_765, c_1343])).
% 14.33/7.93  tff(c_292, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_279])).
% 14.33/7.93  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.33/7.93  tff(c_1588, plain, (![A_120, B_121, C_122]: (k5_xboole_0(k3_xboole_0(A_120, B_121), k3_xboole_0(C_122, B_121))=k3_xboole_0(k5_xboole_0(A_120, C_122), B_121))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.33/7.93  tff(c_1693, plain, (![A_5, C_122]: (k5_xboole_0(A_5, k3_xboole_0(C_122, A_5))=k3_xboole_0(k5_xboole_0(A_5, C_122), A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1588])).
% 14.33/7.93  tff(c_2101, plain, (![A_134, C_135]: (k3_xboole_0(A_134, k5_xboole_0(A_134, C_135))=k4_xboole_0(A_134, C_135))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_2, c_1693])).
% 14.33/7.93  tff(c_2141, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')=k3_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1399, c_2101])).
% 14.33/7.93  tff(c_2203, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_822, c_2, c_2141])).
% 14.33/7.93  tff(c_22, plain, (![A_21, B_22]: (k5_xboole_0(k5_xboole_0(A_21, B_22), k3_xboole_0(A_21, B_22))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.33/7.93  tff(c_2279, plain, (k5_xboole_0(k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4')), k1_xboole_0)=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2203, c_22])).
% 14.33/7.93  tff(c_2290, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1300, c_2279])).
% 14.33/7.93  tff(c_54, plain, (![A_40, B_41]: (m1_subset_1(k3_subset_1(A_40, B_41), k1_zfmisc_1(A_40)) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.33/7.93  tff(c_2810, plain, (![A_147, B_148, C_149]: (k4_subset_1(A_147, B_148, C_149)=k2_xboole_0(B_148, C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(A_147)) | ~m1_subset_1(B_148, k1_zfmisc_1(A_147)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 14.33/7.93  tff(c_37883, plain, (![A_418, B_419, B_420]: (k4_subset_1(A_418, B_419, k3_subset_1(A_418, B_420))=k2_xboole_0(B_419, k3_subset_1(A_418, B_420)) | ~m1_subset_1(B_419, k1_zfmisc_1(A_418)) | ~m1_subset_1(B_420, k1_zfmisc_1(A_418)))), inference(resolution, [status(thm)], [c_54, c_2810])).
% 14.33/7.93  tff(c_37912, plain, (![B_421]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_421))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_421)) | ~m1_subset_1(B_421, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_62, c_37883])).
% 14.33/7.93  tff(c_37935, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_37912])).
% 14.33/7.93  tff(c_37947, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2290, c_37935])).
% 14.33/7.93  tff(c_37949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_37947])).
% 14.33/7.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.33/7.93  
% 14.33/7.93  Inference rules
% 14.33/7.93  ----------------------
% 14.33/7.93  #Ref     : 0
% 14.33/7.93  #Sup     : 9626
% 14.33/7.93  #Fact    : 0
% 14.33/7.93  #Define  : 0
% 14.33/7.93  #Split   : 0
% 14.33/7.93  #Chain   : 0
% 14.33/7.93  #Close   : 0
% 14.33/7.93  
% 14.33/7.93  Ordering : KBO
% 14.33/7.93  
% 14.33/7.93  Simplification rules
% 14.33/7.93  ----------------------
% 14.33/7.93  #Subsume      : 200
% 14.33/7.93  #Demod        : 14073
% 14.33/7.93  #Tautology    : 5080
% 14.33/7.93  #SimpNegUnit  : 22
% 14.33/7.93  #BackRed      : 11
% 14.33/7.93  
% 14.33/7.93  #Partial instantiations: 0
% 14.33/7.93  #Strategies tried      : 1
% 14.33/7.93  
% 14.33/7.93  Timing (in seconds)
% 14.33/7.93  ----------------------
% 14.33/7.94  Preprocessing        : 0.34
% 14.33/7.94  Parsing              : 0.18
% 14.33/7.94  CNF conversion       : 0.02
% 14.33/7.94  Main loop            : 6.82
% 14.33/7.94  Inferencing          : 0.89
% 14.33/7.94  Reduction            : 4.57
% 14.33/7.94  Demodulation         : 4.25
% 14.33/7.94  BG Simplification    : 0.13
% 14.33/7.94  Subsumption          : 0.97
% 14.33/7.94  Abstraction          : 0.23
% 14.33/7.94  MUC search           : 0.00
% 14.33/7.94  Cooper               : 0.00
% 14.33/7.94  Total                : 7.20
% 14.33/7.94  Index Insertion      : 0.00
% 14.33/7.94  Index Deletion       : 0.00
% 14.33/7.94  Index Matching       : 0.00
% 14.33/7.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
