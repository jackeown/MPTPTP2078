%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:49 EST 2020

% Result     : Theorem 21.28s
% Output     : CNFRefutation 21.28s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 371 expanded)
%              Number of leaves         :   34 ( 136 expanded)
%              Depth                    :   17
%              Number of atoms          :  183 ( 569 expanded)
%              Number of equality atoms :   66 ( 176 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_92,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_207,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,B_64)
      | k4_xboole_0(A_63,B_64) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_116,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_215,plain,(
    k4_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_207,c_116])).

tff(c_18,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_117,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k1_xboole_0
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_122,plain,(
    ! [A_53,B_54] : k4_xboole_0(k4_xboole_0(A_53,B_54),A_53) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_117])).

tff(c_130,plain,(
    ! [A_53,B_54] : r1_tarski(k1_xboole_0,k4_xboole_0(A_53,B_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_18])).

tff(c_350,plain,(
    ! [A_76,C_77,B_78] :
      ( r1_xboole_0(A_76,C_77)
      | ~ r1_tarski(A_76,k4_xboole_0(B_78,C_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_374,plain,(
    ! [B_79] : r1_xboole_0(k1_xboole_0,B_79) ),
    inference(resolution,[status(thm)],[c_130,c_350])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_440,plain,(
    ! [B_84] : r1_xboole_0(B_84,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_374,c_4])).

tff(c_26,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = A_25
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_450,plain,(
    ! [B_85] : k4_xboole_0(B_85,k1_xboole_0) = B_85 ),
    inference(resolution,[status(thm)],[c_440,c_26])).

tff(c_121,plain,(
    ! [A_16,B_17] : k4_xboole_0(k4_xboole_0(A_16,B_17),A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_117])).

tff(c_472,plain,(
    ! [B_85] : k4_xboole_0(B_85,B_85) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_121])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1830,plain,(
    ! [A_140,B_141] :
      ( k4_xboole_0(A_140,B_141) = k3_subset_1(A_140,B_141)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(A_140)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1847,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_1830])).

tff(c_507,plain,(
    ! [B_87] : r1_tarski(B_87,B_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_18])).

tff(c_10,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_xboole_0(A_7,C_9)
      | ~ r1_tarski(A_7,k4_xboole_0(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_575,plain,(
    ! [B_89,C_90] : r1_xboole_0(k4_xboole_0(B_89,C_90),C_90) ),
    inference(resolution,[status(thm)],[c_507,c_10])).

tff(c_603,plain,(
    ! [C_91,B_92] : r1_xboole_0(C_91,k4_xboole_0(B_92,C_91)) ),
    inference(resolution,[status(thm)],[c_575,c_4])).

tff(c_624,plain,(
    ! [C_91,B_92] : k4_xboole_0(C_91,k4_xboole_0(B_92,C_91)) = C_91 ),
    inference(resolution,[status(thm)],[c_603,c_26])).

tff(c_1927,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1847,c_624])).

tff(c_529,plain,(
    ! [B_88] : k4_xboole_0(B_88,B_88) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_121])).

tff(c_22,plain,(
    ! [A_20,B_21] : k2_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_544,plain,(
    ! [B_88] : k2_xboole_0(B_88,k1_xboole_0) = k2_xboole_0(B_88,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_22])).

tff(c_64,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_196,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_64])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_200,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_196,c_8])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1846,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_1830])).

tff(c_24,plain,(
    ! [A_22,B_23,C_24] : k4_xboole_0(k4_xboole_0(A_22,B_23),C_24) = k4_xboole_0(A_22,k2_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12714,plain,(
    ! [C_350] : k4_xboole_0(k3_subset_1('#skF_3','#skF_5'),C_350) = k4_xboole_0('#skF_3',k2_xboole_0('#skF_5',C_350)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1846,c_24])).

tff(c_13029,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_12714])).

tff(c_52,plain,(
    ! [A_36] : ~ v1_xboole_0(k1_zfmisc_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_740,plain,(
    ! [B_104,A_105] :
      ( r2_hidden(B_104,A_105)
      | ~ m1_subset_1(B_104,A_105)
      | v1_xboole_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_30,plain,(
    ! [C_31,A_27] :
      ( r1_tarski(C_31,A_27)
      | ~ r2_hidden(C_31,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_747,plain,(
    ! [B_104,A_27] :
      ( r1_tarski(B_104,A_27)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_27))
      | v1_xboole_0(k1_zfmisc_1(A_27)) ) ),
    inference(resolution,[status(thm)],[c_740,c_30])).

tff(c_1439,plain,(
    ! [B_132,A_133] :
      ( r1_tarski(B_132,A_133)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_133)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_747])).

tff(c_1456,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1439])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1039,plain,(
    ! [A_116,C_117,B_118] :
      ( r1_tarski(A_116,C_117)
      | ~ r1_tarski(B_118,C_117)
      | ~ r1_tarski(A_116,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5766,plain,(
    ! [A_225,B_226,A_227] :
      ( r1_tarski(A_225,B_226)
      | ~ r1_tarski(A_225,A_227)
      | k4_xboole_0(A_227,B_226) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_1039])).

tff(c_5820,plain,(
    ! [B_228] :
      ( r1_tarski('#skF_4',B_228)
      | k4_xboole_0('#skF_3',B_228) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1456,c_5766])).

tff(c_20881,plain,(
    ! [B_465] :
      ( k4_xboole_0('#skF_4',B_465) = k1_xboole_0
      | k4_xboole_0('#skF_3',B_465) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_5820,c_8])).

tff(c_20950,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13029,c_20881])).

tff(c_1467,plain,(
    ! [A_134,B_135,C_136] : k4_xboole_0(k4_xboole_0(A_134,B_135),C_136) = k4_xboole_0(A_134,k2_xboole_0(B_135,C_136)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8065,plain,(
    ! [C_274,A_275,B_276] : k2_xboole_0(C_274,k4_xboole_0(A_275,k2_xboole_0(B_276,C_274))) = k2_xboole_0(C_274,k4_xboole_0(A_275,B_276)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1467,c_22])).

tff(c_58065,plain,(
    ! [A_737,A_738,B_739] : k2_xboole_0(A_737,k4_xboole_0(A_738,k2_xboole_0(A_737,B_739))) = k2_xboole_0(A_737,k4_xboole_0(A_738,B_739)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8065])).

tff(c_58675,plain,(
    k2_xboole_0('#skF_5',k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4'))) = k2_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20950,c_58065])).

tff(c_58901,plain,(
    k2_xboole_0('#skF_5','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1927,c_544,c_58675])).

tff(c_655,plain,(
    ! [B_99] : k2_xboole_0(B_99,k1_xboole_0) = k2_xboole_0(B_99,B_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_22])).

tff(c_677,plain,(
    ! [A_1] : k2_xboole_0(k1_xboole_0,A_1) = k2_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_655])).

tff(c_373,plain,(
    ! [B_78,C_77,B_17] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_78,C_77),B_17),C_77) ),
    inference(resolution,[status(thm)],[c_18,c_350])).

tff(c_3255,plain,(
    ! [B_163,C_164,B_165] : r1_xboole_0(k4_xboole_0(B_163,k2_xboole_0(C_164,B_165)),C_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_373])).

tff(c_3719,plain,(
    ! [C_177,B_178,B_179] : r1_xboole_0(C_177,k4_xboole_0(B_178,k2_xboole_0(C_177,B_179))) ),
    inference(resolution,[status(thm)],[c_3255,c_4])).

tff(c_10939,plain,(
    ! [C_315,B_316,B_317] : k4_xboole_0(C_315,k4_xboole_0(B_316,k2_xboole_0(C_315,B_317))) = C_315 ),
    inference(resolution,[status(thm)],[c_3719,c_26])).

tff(c_11232,plain,(
    ! [A_1,B_316,B_2] : k4_xboole_0(A_1,k4_xboole_0(B_316,k2_xboole_0(B_2,A_1))) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10939])).

tff(c_1999,plain,(
    ! [C_142,B_143,A_144] :
      ( r1_tarski(k4_xboole_0(C_142,B_143),k4_xboole_0(C_142,A_144))
      | ~ r1_tarski(A_144,B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( k1_xboole_0 = A_18
      | ~ r1_tarski(A_18,k4_xboole_0(B_19,A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4913,plain,(
    ! [C_206,B_207] :
      ( k4_xboole_0(C_206,B_207) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(C_206,B_207),B_207) ) ),
    inference(resolution,[status(thm)],[c_1999,c_20])).

tff(c_5020,plain,(
    ! [C_206,B_6] :
      ( k4_xboole_0(C_206,B_6) = k1_xboole_0
      | k4_xboole_0(k4_xboole_0(C_206,B_6),B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_4913])).

tff(c_35468,plain,(
    ! [C_582,B_583] :
      ( k4_xboole_0(C_582,B_583) = k1_xboole_0
      | k4_xboole_0(C_582,k2_xboole_0(B_583,B_583)) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_5020])).

tff(c_35666,plain,(
    ! [B_584] : k4_xboole_0(k2_xboole_0(B_584,B_584),B_584) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_472,c_35468])).

tff(c_383,plain,(
    ! [A_80,B_81,C_82] :
      ( r1_tarski(A_80,B_81)
      | ~ r1_tarski(A_80,k4_xboole_0(B_81,C_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_404,plain,(
    ! [A_5,B_81,C_82] :
      ( r1_tarski(A_5,B_81)
      | k4_xboole_0(A_5,k4_xboole_0(B_81,C_82)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_383])).

tff(c_35948,plain,(
    ! [B_81,C_82] : r1_tarski(k2_xboole_0(k4_xboole_0(B_81,C_82),k4_xboole_0(B_81,C_82)),B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_35666,c_404])).

tff(c_43057,plain,(
    ! [B_604,C_605] : r1_tarski(k2_xboole_0(k1_xboole_0,k4_xboole_0(B_604,C_605)),B_604) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_544,c_35948])).

tff(c_43499,plain,(
    ! [A_606] : r1_tarski(k2_xboole_0(k1_xboole_0,A_606),A_606) ),
    inference(superposition,[status(thm),theory(equality)],[c_11232,c_43057])).

tff(c_43623,plain,(
    ! [A_1] : r1_tarski(k2_xboole_0(A_1,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_677,c_43499])).

tff(c_59018,plain,(
    r1_tarski(k2_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_58901,c_43623])).

tff(c_16,plain,(
    ! [C_15,B_14,A_13] :
      ( r1_tarski(k4_xboole_0(C_15,B_14),k4_xboole_0(C_15,A_13))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] :
      ( r1_tarski(A_7,B_8)
      | ~ r1_tarski(A_7,k4_xboole_0(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7483,plain,(
    ! [A_255,A_256,B_257,C_258] :
      ( r1_tarski(A_255,k4_xboole_0(A_256,B_257))
      | ~ r1_tarski(A_255,k4_xboole_0(A_256,k2_xboole_0(B_257,C_258))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1467,c_12])).

tff(c_63522,plain,(
    ! [C_763,B_764,B_765,C_766] :
      ( r1_tarski(k4_xboole_0(C_763,B_764),k4_xboole_0(C_763,B_765))
      | ~ r1_tarski(k2_xboole_0(B_765,C_766),B_764) ) ),
    inference(resolution,[status(thm)],[c_16,c_7483])).

tff(c_64455,plain,(
    ! [C_771] : r1_tarski(k4_xboole_0(C_771,'#skF_5'),k4_xboole_0(C_771,'#skF_4')) ),
    inference(resolution,[status(thm)],[c_59018,c_63522])).

tff(c_64606,plain,(
    r1_tarski(k4_xboole_0('#skF_4','#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_472,c_64455])).

tff(c_446,plain,(
    ! [B_84] : k4_xboole_0(B_84,k1_xboole_0) = B_84 ),
    inference(resolution,[status(thm)],[c_440,c_26])).

tff(c_684,plain,(
    ! [A_100,B_101] :
      ( r1_tarski(A_100,B_101)
      | ~ r1_tarski(A_100,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_12])).

tff(c_693,plain,(
    ! [A_5,B_101] :
      ( r1_tarski(A_5,B_101)
      | k4_xboole_0(A_5,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_684])).

tff(c_707,plain,(
    ! [A_102,B_103] :
      ( r1_tarski(A_102,B_103)
      | k1_xboole_0 != A_102 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_693])).

tff(c_754,plain,(
    ! [A_106,C_107] :
      ( r1_xboole_0(A_106,C_107)
      | k1_xboole_0 != A_106 ) ),
    inference(resolution,[status(thm)],[c_707,c_10])).

tff(c_760,plain,(
    ! [A_106,C_107] :
      ( k4_xboole_0(A_106,C_107) = A_106
      | k1_xboole_0 != A_106 ) ),
    inference(resolution,[status(thm)],[c_754,c_26])).

tff(c_5277,plain,(
    ! [C_212,A_213,B_214] :
      ( k1_xboole_0 = C_212
      | ~ r1_tarski(C_212,k4_xboole_0(A_213,k2_xboole_0(B_214,C_212))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1467,c_20])).

tff(c_5319,plain,(
    ! [C_212,A_106] :
      ( k1_xboole_0 = C_212
      | ~ r1_tarski(C_212,A_106)
      | k1_xboole_0 != A_106 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_760,c_5277])).

tff(c_64747,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64606,c_5319])).

tff(c_64781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_215,c_64747])).

tff(c_64782,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_64783,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_65901,plain,(
    ! [A_851,B_852] :
      ( k4_xboole_0(A_851,B_852) = k3_subset_1(A_851,B_852)
      | ~ m1_subset_1(B_852,k1_zfmisc_1(A_851)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_65917,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_65901])).

tff(c_65918,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_65901])).

tff(c_66036,plain,(
    ! [C_853,B_854,A_855] :
      ( r1_tarski(k4_xboole_0(C_853,B_854),k4_xboole_0(C_853,A_855))
      | ~ r1_tarski(A_855,B_854) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_78498,plain,(
    ! [B_1067] :
      ( r1_tarski(k4_xboole_0('#skF_3',B_1067),k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_4',B_1067) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65918,c_66036])).

tff(c_78556,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_65917,c_78498])).

tff(c_78588,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64783,c_78556])).

tff(c_78590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64782,c_78588])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:37:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.28/11.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.28/11.74  
% 21.28/11.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.28/11.74  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 21.28/11.74  
% 21.28/11.74  %Foreground sorts:
% 21.28/11.74  
% 21.28/11.74  
% 21.28/11.74  %Background operators:
% 21.28/11.74  
% 21.28/11.74  
% 21.28/11.74  %Foreground operators:
% 21.28/11.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.28/11.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 21.28/11.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 21.28/11.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 21.28/11.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.28/11.74  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 21.28/11.74  tff('#skF_5', type, '#skF_5': $i).
% 21.28/11.74  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 21.28/11.74  tff('#skF_3', type, '#skF_3': $i).
% 21.28/11.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.28/11.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.28/11.74  tff('#skF_4', type, '#skF_4': $i).
% 21.28/11.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.28/11.74  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 21.28/11.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 21.28/11.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 21.28/11.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 21.28/11.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.28/11.74  
% 21.28/11.76  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 21.28/11.76  tff(f_102, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 21.28/11.76  tff(f_53, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 21.28/11.76  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 21.28/11.76  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 21.28/11.76  tff(f_65, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 21.28/11.76  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 21.28/11.76  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 21.28/11.76  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 21.28/11.76  tff(f_61, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 21.28/11.76  tff(f_92, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 21.28/11.76  tff(f_85, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 21.28/11.76  tff(f_72, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 21.28/11.76  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 21.28/11.76  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 21.28/11.76  tff(f_57, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 21.28/11.76  tff(c_207, plain, (![A_63, B_64]: (r1_tarski(A_63, B_64) | k4_xboole_0(A_63, B_64)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 21.28/11.76  tff(c_58, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 21.28/11.76  tff(c_116, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_58])).
% 21.28/11.76  tff(c_215, plain, (k4_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_207, c_116])).
% 21.28/11.76  tff(c_18, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 21.28/11.76  tff(c_117, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=k1_xboole_0 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_35])).
% 21.28/11.76  tff(c_122, plain, (![A_53, B_54]: (k4_xboole_0(k4_xboole_0(A_53, B_54), A_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_117])).
% 21.28/11.76  tff(c_130, plain, (![A_53, B_54]: (r1_tarski(k1_xboole_0, k4_xboole_0(A_53, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_18])).
% 21.28/11.76  tff(c_350, plain, (![A_76, C_77, B_78]: (r1_xboole_0(A_76, C_77) | ~r1_tarski(A_76, k4_xboole_0(B_78, C_77)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 21.28/11.76  tff(c_374, plain, (![B_79]: (r1_xboole_0(k1_xboole_0, B_79))), inference(resolution, [status(thm)], [c_130, c_350])).
% 21.28/11.76  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 21.28/11.76  tff(c_440, plain, (![B_84]: (r1_xboole_0(B_84, k1_xboole_0))), inference(resolution, [status(thm)], [c_374, c_4])).
% 21.28/11.76  tff(c_26, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=A_25 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_65])).
% 21.28/11.76  tff(c_450, plain, (![B_85]: (k4_xboole_0(B_85, k1_xboole_0)=B_85)), inference(resolution, [status(thm)], [c_440, c_26])).
% 21.28/11.76  tff(c_121, plain, (![A_16, B_17]: (k4_xboole_0(k4_xboole_0(A_16, B_17), A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_117])).
% 21.28/11.76  tff(c_472, plain, (![B_85]: (k4_xboole_0(B_85, B_85)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_450, c_121])).
% 21.28/11.76  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 21.28/11.76  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 21.28/11.76  tff(c_1830, plain, (![A_140, B_141]: (k4_xboole_0(A_140, B_141)=k3_subset_1(A_140, B_141) | ~m1_subset_1(B_141, k1_zfmisc_1(A_140)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 21.28/11.76  tff(c_1847, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_1830])).
% 21.28/11.76  tff(c_507, plain, (![B_87]: (r1_tarski(B_87, B_87))), inference(superposition, [status(thm), theory('equality')], [c_450, c_18])).
% 21.28/11.76  tff(c_10, plain, (![A_7, C_9, B_8]: (r1_xboole_0(A_7, C_9) | ~r1_tarski(A_7, k4_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 21.28/11.76  tff(c_575, plain, (![B_89, C_90]: (r1_xboole_0(k4_xboole_0(B_89, C_90), C_90))), inference(resolution, [status(thm)], [c_507, c_10])).
% 21.28/11.76  tff(c_603, plain, (![C_91, B_92]: (r1_xboole_0(C_91, k4_xboole_0(B_92, C_91)))), inference(resolution, [status(thm)], [c_575, c_4])).
% 21.28/11.76  tff(c_624, plain, (![C_91, B_92]: (k4_xboole_0(C_91, k4_xboole_0(B_92, C_91))=C_91)), inference(resolution, [status(thm)], [c_603, c_26])).
% 21.28/11.76  tff(c_1927, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1847, c_624])).
% 21.28/11.76  tff(c_529, plain, (![B_88]: (k4_xboole_0(B_88, B_88)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_450, c_121])).
% 21.28/11.76  tff(c_22, plain, (![A_20, B_21]: (k2_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 21.28/11.76  tff(c_544, plain, (![B_88]: (k2_xboole_0(B_88, k1_xboole_0)=k2_xboole_0(B_88, B_88))), inference(superposition, [status(thm), theory('equality')], [c_529, c_22])).
% 21.28/11.76  tff(c_64, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 21.28/11.76  tff(c_196, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_116, c_64])).
% 21.28/11.76  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 21.28/11.76  tff(c_200, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_196, c_8])).
% 21.28/11.76  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 21.28/11.76  tff(c_1846, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_1830])).
% 21.28/11.76  tff(c_24, plain, (![A_22, B_23, C_24]: (k4_xboole_0(k4_xboole_0(A_22, B_23), C_24)=k4_xboole_0(A_22, k2_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 21.28/11.76  tff(c_12714, plain, (![C_350]: (k4_xboole_0(k3_subset_1('#skF_3', '#skF_5'), C_350)=k4_xboole_0('#skF_3', k2_xboole_0('#skF_5', C_350)))), inference(superposition, [status(thm), theory('equality')], [c_1846, c_24])).
% 21.28/11.76  tff(c_13029, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4')))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_200, c_12714])).
% 21.28/11.76  tff(c_52, plain, (![A_36]: (~v1_xboole_0(k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 21.28/11.76  tff(c_740, plain, (![B_104, A_105]: (r2_hidden(B_104, A_105) | ~m1_subset_1(B_104, A_105) | v1_xboole_0(A_105))), inference(cnfTransformation, [status(thm)], [f_85])).
% 21.28/11.76  tff(c_30, plain, (![C_31, A_27]: (r1_tarski(C_31, A_27) | ~r2_hidden(C_31, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 21.28/11.76  tff(c_747, plain, (![B_104, A_27]: (r1_tarski(B_104, A_27) | ~m1_subset_1(B_104, k1_zfmisc_1(A_27)) | v1_xboole_0(k1_zfmisc_1(A_27)))), inference(resolution, [status(thm)], [c_740, c_30])).
% 21.28/11.76  tff(c_1439, plain, (![B_132, A_133]: (r1_tarski(B_132, A_133) | ~m1_subset_1(B_132, k1_zfmisc_1(A_133)))), inference(negUnitSimplification, [status(thm)], [c_52, c_747])).
% 21.28/11.76  tff(c_1456, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_1439])).
% 21.28/11.76  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 21.28/11.76  tff(c_1039, plain, (![A_116, C_117, B_118]: (r1_tarski(A_116, C_117) | ~r1_tarski(B_118, C_117) | ~r1_tarski(A_116, B_118))), inference(cnfTransformation, [status(thm)], [f_47])).
% 21.28/11.76  tff(c_5766, plain, (![A_225, B_226, A_227]: (r1_tarski(A_225, B_226) | ~r1_tarski(A_225, A_227) | k4_xboole_0(A_227, B_226)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_1039])).
% 21.28/11.76  tff(c_5820, plain, (![B_228]: (r1_tarski('#skF_4', B_228) | k4_xboole_0('#skF_3', B_228)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1456, c_5766])).
% 21.28/11.76  tff(c_20881, plain, (![B_465]: (k4_xboole_0('#skF_4', B_465)=k1_xboole_0 | k4_xboole_0('#skF_3', B_465)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_5820, c_8])).
% 21.28/11.76  tff(c_20950, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4')))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_13029, c_20881])).
% 21.28/11.76  tff(c_1467, plain, (![A_134, B_135, C_136]: (k4_xboole_0(k4_xboole_0(A_134, B_135), C_136)=k4_xboole_0(A_134, k2_xboole_0(B_135, C_136)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 21.28/11.76  tff(c_8065, plain, (![C_274, A_275, B_276]: (k2_xboole_0(C_274, k4_xboole_0(A_275, k2_xboole_0(B_276, C_274)))=k2_xboole_0(C_274, k4_xboole_0(A_275, B_276)))), inference(superposition, [status(thm), theory('equality')], [c_1467, c_22])).
% 21.28/11.76  tff(c_58065, plain, (![A_737, A_738, B_739]: (k2_xboole_0(A_737, k4_xboole_0(A_738, k2_xboole_0(A_737, B_739)))=k2_xboole_0(A_737, k4_xboole_0(A_738, B_739)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_8065])).
% 21.28/11.76  tff(c_58675, plain, (k2_xboole_0('#skF_5', k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4')))=k2_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20950, c_58065])).
% 21.28/11.76  tff(c_58901, plain, (k2_xboole_0('#skF_5', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1927, c_544, c_58675])).
% 21.28/11.76  tff(c_655, plain, (![B_99]: (k2_xboole_0(B_99, k1_xboole_0)=k2_xboole_0(B_99, B_99))), inference(superposition, [status(thm), theory('equality')], [c_529, c_22])).
% 21.28/11.76  tff(c_677, plain, (![A_1]: (k2_xboole_0(k1_xboole_0, A_1)=k2_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_655])).
% 21.28/11.76  tff(c_373, plain, (![B_78, C_77, B_17]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_78, C_77), B_17), C_77))), inference(resolution, [status(thm)], [c_18, c_350])).
% 21.28/11.76  tff(c_3255, plain, (![B_163, C_164, B_165]: (r1_xboole_0(k4_xboole_0(B_163, k2_xboole_0(C_164, B_165)), C_164))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_373])).
% 21.28/11.76  tff(c_3719, plain, (![C_177, B_178, B_179]: (r1_xboole_0(C_177, k4_xboole_0(B_178, k2_xboole_0(C_177, B_179))))), inference(resolution, [status(thm)], [c_3255, c_4])).
% 21.28/11.76  tff(c_10939, plain, (![C_315, B_316, B_317]: (k4_xboole_0(C_315, k4_xboole_0(B_316, k2_xboole_0(C_315, B_317)))=C_315)), inference(resolution, [status(thm)], [c_3719, c_26])).
% 21.28/11.76  tff(c_11232, plain, (![A_1, B_316, B_2]: (k4_xboole_0(A_1, k4_xboole_0(B_316, k2_xboole_0(B_2, A_1)))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_10939])).
% 21.28/11.76  tff(c_1999, plain, (![C_142, B_143, A_144]: (r1_tarski(k4_xboole_0(C_142, B_143), k4_xboole_0(C_142, A_144)) | ~r1_tarski(A_144, B_143))), inference(cnfTransformation, [status(thm)], [f_51])).
% 21.28/11.76  tff(c_20, plain, (![A_18, B_19]: (k1_xboole_0=A_18 | ~r1_tarski(A_18, k4_xboole_0(B_19, A_18)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 21.28/11.76  tff(c_4913, plain, (![C_206, B_207]: (k4_xboole_0(C_206, B_207)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(C_206, B_207), B_207))), inference(resolution, [status(thm)], [c_1999, c_20])).
% 21.28/11.76  tff(c_5020, plain, (![C_206, B_6]: (k4_xboole_0(C_206, B_6)=k1_xboole_0 | k4_xboole_0(k4_xboole_0(C_206, B_6), B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_4913])).
% 21.28/11.76  tff(c_35468, plain, (![C_582, B_583]: (k4_xboole_0(C_582, B_583)=k1_xboole_0 | k4_xboole_0(C_582, k2_xboole_0(B_583, B_583))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_5020])).
% 21.28/11.76  tff(c_35666, plain, (![B_584]: (k4_xboole_0(k2_xboole_0(B_584, B_584), B_584)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_472, c_35468])).
% 21.28/11.76  tff(c_383, plain, (![A_80, B_81, C_82]: (r1_tarski(A_80, B_81) | ~r1_tarski(A_80, k4_xboole_0(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 21.28/11.76  tff(c_404, plain, (![A_5, B_81, C_82]: (r1_tarski(A_5, B_81) | k4_xboole_0(A_5, k4_xboole_0(B_81, C_82))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_383])).
% 21.28/11.76  tff(c_35948, plain, (![B_81, C_82]: (r1_tarski(k2_xboole_0(k4_xboole_0(B_81, C_82), k4_xboole_0(B_81, C_82)), B_81))), inference(superposition, [status(thm), theory('equality')], [c_35666, c_404])).
% 21.28/11.76  tff(c_43057, plain, (![B_604, C_605]: (r1_tarski(k2_xboole_0(k1_xboole_0, k4_xboole_0(B_604, C_605)), B_604))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_544, c_35948])).
% 21.28/11.76  tff(c_43499, plain, (![A_606]: (r1_tarski(k2_xboole_0(k1_xboole_0, A_606), A_606))), inference(superposition, [status(thm), theory('equality')], [c_11232, c_43057])).
% 21.28/11.76  tff(c_43623, plain, (![A_1]: (r1_tarski(k2_xboole_0(A_1, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_677, c_43499])).
% 21.28/11.76  tff(c_59018, plain, (r1_tarski(k2_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_58901, c_43623])).
% 21.28/11.76  tff(c_16, plain, (![C_15, B_14, A_13]: (r1_tarski(k4_xboole_0(C_15, B_14), k4_xboole_0(C_15, A_13)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 21.28/11.76  tff(c_12, plain, (![A_7, B_8, C_9]: (r1_tarski(A_7, B_8) | ~r1_tarski(A_7, k4_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 21.28/11.76  tff(c_7483, plain, (![A_255, A_256, B_257, C_258]: (r1_tarski(A_255, k4_xboole_0(A_256, B_257)) | ~r1_tarski(A_255, k4_xboole_0(A_256, k2_xboole_0(B_257, C_258))))), inference(superposition, [status(thm), theory('equality')], [c_1467, c_12])).
% 21.28/11.76  tff(c_63522, plain, (![C_763, B_764, B_765, C_766]: (r1_tarski(k4_xboole_0(C_763, B_764), k4_xboole_0(C_763, B_765)) | ~r1_tarski(k2_xboole_0(B_765, C_766), B_764))), inference(resolution, [status(thm)], [c_16, c_7483])).
% 21.28/11.76  tff(c_64455, plain, (![C_771]: (r1_tarski(k4_xboole_0(C_771, '#skF_5'), k4_xboole_0(C_771, '#skF_4')))), inference(resolution, [status(thm)], [c_59018, c_63522])).
% 21.28/11.76  tff(c_64606, plain, (r1_tarski(k4_xboole_0('#skF_4', '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_472, c_64455])).
% 21.28/11.76  tff(c_446, plain, (![B_84]: (k4_xboole_0(B_84, k1_xboole_0)=B_84)), inference(resolution, [status(thm)], [c_440, c_26])).
% 21.28/11.76  tff(c_684, plain, (![A_100, B_101]: (r1_tarski(A_100, B_101) | ~r1_tarski(A_100, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_529, c_12])).
% 21.28/11.76  tff(c_693, plain, (![A_5, B_101]: (r1_tarski(A_5, B_101) | k4_xboole_0(A_5, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_684])).
% 21.28/11.76  tff(c_707, plain, (![A_102, B_103]: (r1_tarski(A_102, B_103) | k1_xboole_0!=A_102)), inference(demodulation, [status(thm), theory('equality')], [c_446, c_693])).
% 21.28/11.76  tff(c_754, plain, (![A_106, C_107]: (r1_xboole_0(A_106, C_107) | k1_xboole_0!=A_106)), inference(resolution, [status(thm)], [c_707, c_10])).
% 21.28/11.76  tff(c_760, plain, (![A_106, C_107]: (k4_xboole_0(A_106, C_107)=A_106 | k1_xboole_0!=A_106)), inference(resolution, [status(thm)], [c_754, c_26])).
% 21.28/11.76  tff(c_5277, plain, (![C_212, A_213, B_214]: (k1_xboole_0=C_212 | ~r1_tarski(C_212, k4_xboole_0(A_213, k2_xboole_0(B_214, C_212))))), inference(superposition, [status(thm), theory('equality')], [c_1467, c_20])).
% 21.28/11.76  tff(c_5319, plain, (![C_212, A_106]: (k1_xboole_0=C_212 | ~r1_tarski(C_212, A_106) | k1_xboole_0!=A_106)), inference(superposition, [status(thm), theory('equality')], [c_760, c_5277])).
% 21.28/11.76  tff(c_64747, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_64606, c_5319])).
% 21.28/11.76  tff(c_64781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_215, c_64747])).
% 21.28/11.76  tff(c_64782, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_58])).
% 21.28/11.76  tff(c_64783, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_58])).
% 21.28/11.76  tff(c_65901, plain, (![A_851, B_852]: (k4_xboole_0(A_851, B_852)=k3_subset_1(A_851, B_852) | ~m1_subset_1(B_852, k1_zfmisc_1(A_851)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 21.28/11.76  tff(c_65917, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_65901])).
% 21.28/11.76  tff(c_65918, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_65901])).
% 21.28/11.76  tff(c_66036, plain, (![C_853, B_854, A_855]: (r1_tarski(k4_xboole_0(C_853, B_854), k4_xboole_0(C_853, A_855)) | ~r1_tarski(A_855, B_854))), inference(cnfTransformation, [status(thm)], [f_51])).
% 21.28/11.76  tff(c_78498, plain, (![B_1067]: (r1_tarski(k4_xboole_0('#skF_3', B_1067), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', B_1067))), inference(superposition, [status(thm), theory('equality')], [c_65918, c_66036])).
% 21.28/11.76  tff(c_78556, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_65917, c_78498])).
% 21.28/11.76  tff(c_78588, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64783, c_78556])).
% 21.28/11.76  tff(c_78590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64782, c_78588])).
% 21.28/11.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.28/11.76  
% 21.28/11.76  Inference rules
% 21.28/11.76  ----------------------
% 21.28/11.76  #Ref     : 0
% 21.28/11.76  #Sup     : 19648
% 21.28/11.76  #Fact    : 0
% 21.28/11.76  #Define  : 0
% 21.28/11.76  #Split   : 7
% 21.28/11.76  #Chain   : 0
% 21.28/11.76  #Close   : 0
% 21.28/11.76  
% 21.28/11.76  Ordering : KBO
% 21.28/11.76  
% 21.28/11.76  Simplification rules
% 21.28/11.76  ----------------------
% 21.28/11.76  #Subsume      : 6310
% 21.28/11.76  #Demod        : 13426
% 21.28/11.76  #Tautology    : 7948
% 21.28/11.76  #SimpNegUnit  : 713
% 21.28/11.77  #BackRed      : 41
% 21.28/11.77  
% 21.28/11.77  #Partial instantiations: 0
% 21.28/11.77  #Strategies tried      : 1
% 21.28/11.77  
% 21.28/11.77  Timing (in seconds)
% 21.28/11.77  ----------------------
% 21.28/11.77  Preprocessing        : 0.34
% 21.28/11.77  Parsing              : 0.18
% 21.28/11.77  CNF conversion       : 0.02
% 21.28/11.77  Main loop            : 10.64
% 21.28/11.77  Inferencing          : 1.49
% 21.28/11.77  Reduction            : 5.75
% 21.28/11.77  Demodulation         : 4.51
% 21.28/11.77  BG Simplification    : 0.14
% 21.28/11.77  Subsumption          : 2.71
% 21.28/11.77  Abstraction          : 0.21
% 21.28/11.77  MUC search           : 0.00
% 21.28/11.77  Cooper               : 0.00
% 21.28/11.77  Total                : 11.03
% 21.28/11.77  Index Insertion      : 0.00
% 21.28/11.77  Index Deletion       : 0.00
% 21.28/11.77  Index Matching       : 0.00
% 21.28/11.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
