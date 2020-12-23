%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:09 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.30s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 229 expanded)
%              Number of leaves         :   39 (  91 expanded)
%              Depth                    :   13
%              Number of atoms          :  124 ( 295 expanded)
%              Number of equality atoms :   69 ( 147 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_49,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_77,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_105,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_61,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_79,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(c_22,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_374,plain,(
    ! [A_83,B_84] :
      ( k4_xboole_0(A_83,B_84) = k1_xboole_0
      | ~ r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_387,plain,(
    ! [A_15] : k4_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_374])).

tff(c_18,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_183,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k2_xboole_0(A_63,B_64)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_193,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_183])).

tff(c_42,plain,(
    ! [A_34] : k2_subset_1(A_34) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_46,plain,(
    ! [A_37] : m1_subset_1(k2_subset_1(A_37),k1_zfmisc_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_73,plain,(
    ! [A_37] : m1_subset_1(A_37,k1_zfmisc_1(A_37)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46])).

tff(c_1227,plain,(
    ! [A_123,B_124] :
      ( k4_xboole_0(A_123,B_124) = k3_subset_1(A_123,B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(A_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1233,plain,(
    ! [A_37] : k4_xboole_0(A_37,A_37) = k3_subset_1(A_37,A_37) ),
    inference(resolution,[status(thm)],[c_73,c_1227])).

tff(c_1239,plain,(
    ! [A_37] : k3_subset_1(A_37,A_37) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_1233])).

tff(c_302,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(A_76,B_77)
      | k4_xboole_0(A_76,B_77) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_70,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | k2_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_74,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_70])).

tff(c_116,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_64,plain,
    ( k2_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_75,plain,
    ( '#skF_2' != '#skF_1'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_64])).

tff(c_223,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_116,c_116,c_75])).

tff(c_306,plain,(
    k4_xboole_0(k3_subset_1('#skF_1','#skF_1'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_302,c_223])).

tff(c_1242,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1239,c_306])).

tff(c_1246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_1242])).

tff(c_1248,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_62,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1338,plain,(
    ! [A_135,B_136] : k2_xboole_0(A_135,k3_xboole_0(A_135,B_136)) = A_135 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1344,plain,(
    ! [A_135] : k4_xboole_0(A_135,A_135) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1338,c_24])).

tff(c_3362,plain,(
    ! [A_207,B_208] :
      ( k4_xboole_0(A_207,B_208) = k3_subset_1(A_207,B_208)
      | ~ m1_subset_1(B_208,k1_zfmisc_1(A_207)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3368,plain,(
    ! [A_37] : k4_xboole_0(A_37,A_37) = k3_subset_1(A_37,A_37) ),
    inference(resolution,[status(thm)],[c_73,c_3362])).

tff(c_3377,plain,(
    ! [A_37] : k3_subset_1(A_37,A_37) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1344,c_3368])).

tff(c_3481,plain,(
    ! [B_212,C_213,A_214] :
      ( r1_tarski(B_212,C_213)
      | ~ r1_tarski(k3_subset_1(A_214,C_213),k3_subset_1(A_214,B_212))
      | ~ m1_subset_1(C_213,k1_zfmisc_1(A_214))
      | ~ m1_subset_1(B_212,k1_zfmisc_1(A_214)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3496,plain,(
    ! [B_212,A_37] :
      ( r1_tarski(B_212,A_37)
      | ~ r1_tarski(k1_xboole_0,k3_subset_1(A_37,B_212))
      | ~ m1_subset_1(A_37,k1_zfmisc_1(A_37))
      | ~ m1_subset_1(B_212,k1_zfmisc_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3377,c_3481])).

tff(c_3532,plain,(
    ! [B_215,A_216] :
      ( r1_tarski(B_215,A_216)
      | ~ m1_subset_1(B_215,k1_zfmisc_1(A_216)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_22,c_3496])).

tff(c_3556,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_3532])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3560,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_3556,c_6])).

tff(c_3569,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1248,c_3560])).

tff(c_1488,plain,(
    ! [A_148,B_149] :
      ( k3_xboole_0(A_148,B_149) = A_148
      | ~ r1_tarski(A_148,B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1506,plain,(
    ! [A_150] : k3_xboole_0(k1_xboole_0,A_150) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_1488])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1350,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1338])).

tff(c_1511,plain,(
    ! [A_150] : k2_xboole_0(A_150,k1_xboole_0) = A_150 ),
    inference(superposition,[status(thm),theory(equality)],[c_1506,c_1350])).

tff(c_1418,plain,(
    ! [A_141,B_142] :
      ( k4_xboole_0(A_141,B_142) = k1_xboole_0
      | ~ r1_tarski(A_141,B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1431,plain,(
    ! [A_15] : k4_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_1418])).

tff(c_2037,plain,(
    ! [A_172,B_173] : k5_xboole_0(A_172,k4_xboole_0(B_173,A_172)) = k2_xboole_0(A_172,B_173) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2058,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = k2_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1431,c_2037])).

tff(c_2070,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1511,c_2058])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3571,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3556,c_14])).

tff(c_26,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3636,plain,(
    k5_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3571,c_26])).

tff(c_3644,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2070,c_3636])).

tff(c_28,plain,(
    ! [B_21,A_20] : k2_tarski(B_21,A_20) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1473,plain,(
    ! [A_146,B_147] : k3_tarski(k2_tarski(A_146,B_147)) = k2_xboole_0(A_146,B_147) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1733,plain,(
    ! [B_159,A_160] : k3_tarski(k2_tarski(B_159,A_160)) = k2_xboole_0(A_160,B_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1473])).

tff(c_34,plain,(
    ! [A_27,B_28] : k3_tarski(k2_tarski(A_27,B_28)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1739,plain,(
    ! [B_159,A_160] : k2_xboole_0(B_159,A_160) = k2_xboole_0(A_160,B_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_1733,c_34])).

tff(c_3378,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_3362])).

tff(c_3404,plain,(
    k5_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3378,c_26])).

tff(c_3410,plain,(
    k5_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1739,c_3404])).

tff(c_1247,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1502,plain,(
    k3_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_1247,c_1488])).

tff(c_1661,plain,(
    ! [A_155,B_156] : k5_xboole_0(A_155,k3_xboole_0(A_155,B_156)) = k4_xboole_0(A_155,B_156) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2259,plain,(
    ! [A_180,B_181] : k5_xboole_0(A_180,k3_xboole_0(B_181,A_180)) = k4_xboole_0(A_180,B_181) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1661])).

tff(c_2287,plain,(
    k5_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1502,c_2259])).

tff(c_3420,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3410,c_2287])).

tff(c_52,plain,(
    ! [A_42,B_43] : k6_subset_1(A_42,B_43) = k4_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_48,plain,(
    ! [A_38,B_39] : m1_subset_1(k6_subset_1(A_38,B_39),k1_zfmisc_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_71,plain,(
    ! [A_38,B_39] : m1_subset_1(k4_xboole_0(A_38,B_39),k1_zfmisc_1(A_38)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48])).

tff(c_3457,plain,(
    m1_subset_1(k2_xboole_0('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3420,c_71])).

tff(c_3691,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3644,c_3457])).

tff(c_3522,plain,(
    ! [B_212,A_37] :
      ( r1_tarski(B_212,A_37)
      | ~ m1_subset_1(B_212,k1_zfmisc_1(A_37)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_22,c_3496])).

tff(c_3778,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_3691,c_3522])).

tff(c_3787,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3569,c_3778])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.07/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.78  
% 4.07/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.30/1.78  %$ r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.30/1.78  
% 4.30/1.78  %Foreground sorts:
% 4.30/1.78  
% 4.30/1.78  
% 4.30/1.78  %Background operators:
% 4.30/1.78  
% 4.30/1.78  
% 4.30/1.78  %Foreground operators:
% 4.30/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.30/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.30/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.30/1.78  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.30/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.30/1.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.30/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.30/1.78  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.30/1.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.30/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.30/1.78  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 4.30/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.30/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.30/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.30/1.78  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.30/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.30/1.78  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 4.30/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.30/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.30/1.78  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.30/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.30/1.78  
% 4.30/1.80  tff(f_49, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.30/1.80  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.30/1.80  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 4.30/1.80  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.30/1.80  tff(f_71, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.30/1.80  tff(f_77, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.30/1.80  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.30/1.80  tff(f_105, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 4.30/1.80  tff(f_96, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 4.30/1.80  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.30/1.80  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.30/1.80  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.30/1.80  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.30/1.80  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.30/1.80  tff(f_61, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.30/1.80  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.30/1.80  tff(f_85, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 4.30/1.80  tff(f_79, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 4.30/1.80  tff(c_22, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.30/1.80  tff(c_374, plain, (![A_83, B_84]: (k4_xboole_0(A_83, B_84)=k1_xboole_0 | ~r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.30/1.80  tff(c_387, plain, (![A_15]: (k4_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_374])).
% 4.30/1.80  tff(c_18, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k3_xboole_0(A_11, B_12))=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.30/1.80  tff(c_183, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k2_xboole_0(A_63, B_64))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.30/1.80  tff(c_193, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_183])).
% 4.30/1.80  tff(c_42, plain, (![A_34]: (k2_subset_1(A_34)=A_34)), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.30/1.80  tff(c_46, plain, (![A_37]: (m1_subset_1(k2_subset_1(A_37), k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.30/1.80  tff(c_73, plain, (![A_37]: (m1_subset_1(A_37, k1_zfmisc_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46])).
% 4.30/1.80  tff(c_1227, plain, (![A_123, B_124]: (k4_xboole_0(A_123, B_124)=k3_subset_1(A_123, B_124) | ~m1_subset_1(B_124, k1_zfmisc_1(A_123)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.30/1.80  tff(c_1233, plain, (![A_37]: (k4_xboole_0(A_37, A_37)=k3_subset_1(A_37, A_37))), inference(resolution, [status(thm)], [c_73, c_1227])).
% 4.30/1.80  tff(c_1239, plain, (![A_37]: (k3_subset_1(A_37, A_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_193, c_1233])).
% 4.30/1.80  tff(c_302, plain, (![A_76, B_77]: (r1_tarski(A_76, B_77) | k4_xboole_0(A_76, B_77)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.30/1.80  tff(c_70, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | k2_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.30/1.80  tff(c_74, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_70])).
% 4.30/1.80  tff(c_116, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_74])).
% 4.30/1.80  tff(c_64, plain, (k2_subset_1('#skF_1')!='#skF_2' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.30/1.80  tff(c_75, plain, ('#skF_2'!='#skF_1' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_64])).
% 4.30/1.80  tff(c_223, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_116, c_116, c_75])).
% 4.30/1.80  tff(c_306, plain, (k4_xboole_0(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_302, c_223])).
% 4.30/1.80  tff(c_1242, plain, (k4_xboole_0(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1239, c_306])).
% 4.30/1.80  tff(c_1246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_387, c_1242])).
% 4.30/1.80  tff(c_1248, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_74])).
% 4.30/1.80  tff(c_62, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.30/1.80  tff(c_1338, plain, (![A_135, B_136]: (k2_xboole_0(A_135, k3_xboole_0(A_135, B_136))=A_135)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.30/1.80  tff(c_24, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.30/1.80  tff(c_1344, plain, (![A_135]: (k4_xboole_0(A_135, A_135)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1338, c_24])).
% 4.30/1.80  tff(c_3362, plain, (![A_207, B_208]: (k4_xboole_0(A_207, B_208)=k3_subset_1(A_207, B_208) | ~m1_subset_1(B_208, k1_zfmisc_1(A_207)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.30/1.80  tff(c_3368, plain, (![A_37]: (k4_xboole_0(A_37, A_37)=k3_subset_1(A_37, A_37))), inference(resolution, [status(thm)], [c_73, c_3362])).
% 4.30/1.80  tff(c_3377, plain, (![A_37]: (k3_subset_1(A_37, A_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1344, c_3368])).
% 4.30/1.80  tff(c_3481, plain, (![B_212, C_213, A_214]: (r1_tarski(B_212, C_213) | ~r1_tarski(k3_subset_1(A_214, C_213), k3_subset_1(A_214, B_212)) | ~m1_subset_1(C_213, k1_zfmisc_1(A_214)) | ~m1_subset_1(B_212, k1_zfmisc_1(A_214)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.30/1.80  tff(c_3496, plain, (![B_212, A_37]: (r1_tarski(B_212, A_37) | ~r1_tarski(k1_xboole_0, k3_subset_1(A_37, B_212)) | ~m1_subset_1(A_37, k1_zfmisc_1(A_37)) | ~m1_subset_1(B_212, k1_zfmisc_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_3377, c_3481])).
% 4.30/1.80  tff(c_3532, plain, (![B_215, A_216]: (r1_tarski(B_215, A_216) | ~m1_subset_1(B_215, k1_zfmisc_1(A_216)))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_22, c_3496])).
% 4.30/1.80  tff(c_3556, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_3532])).
% 4.30/1.80  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.30/1.80  tff(c_3560, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_3556, c_6])).
% 4.30/1.80  tff(c_3569, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1248, c_3560])).
% 4.30/1.80  tff(c_1488, plain, (![A_148, B_149]: (k3_xboole_0(A_148, B_149)=A_148 | ~r1_tarski(A_148, B_149))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.30/1.80  tff(c_1506, plain, (![A_150]: (k3_xboole_0(k1_xboole_0, A_150)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_1488])).
% 4.30/1.80  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.30/1.80  tff(c_1350, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1338])).
% 4.30/1.80  tff(c_1511, plain, (![A_150]: (k2_xboole_0(A_150, k1_xboole_0)=A_150)), inference(superposition, [status(thm), theory('equality')], [c_1506, c_1350])).
% 4.30/1.80  tff(c_1418, plain, (![A_141, B_142]: (k4_xboole_0(A_141, B_142)=k1_xboole_0 | ~r1_tarski(A_141, B_142))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.30/1.80  tff(c_1431, plain, (![A_15]: (k4_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_1418])).
% 4.30/1.80  tff(c_2037, plain, (![A_172, B_173]: (k5_xboole_0(A_172, k4_xboole_0(B_173, A_172))=k2_xboole_0(A_172, B_173))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.30/1.80  tff(c_2058, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=k2_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1431, c_2037])).
% 4.30/1.80  tff(c_2070, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_1511, c_2058])).
% 4.30/1.80  tff(c_14, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.30/1.80  tff(c_3571, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_3556, c_14])).
% 4.30/1.80  tff(c_26, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.30/1.80  tff(c_3636, plain, (k5_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3571, c_26])).
% 4.30/1.80  tff(c_3644, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2070, c_3636])).
% 4.30/1.80  tff(c_28, plain, (![B_21, A_20]: (k2_tarski(B_21, A_20)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.30/1.80  tff(c_1473, plain, (![A_146, B_147]: (k3_tarski(k2_tarski(A_146, B_147))=k2_xboole_0(A_146, B_147))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.30/1.80  tff(c_1733, plain, (![B_159, A_160]: (k3_tarski(k2_tarski(B_159, A_160))=k2_xboole_0(A_160, B_159))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1473])).
% 4.30/1.80  tff(c_34, plain, (![A_27, B_28]: (k3_tarski(k2_tarski(A_27, B_28))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.30/1.80  tff(c_1739, plain, (![B_159, A_160]: (k2_xboole_0(B_159, A_160)=k2_xboole_0(A_160, B_159))), inference(superposition, [status(thm), theory('equality')], [c_1733, c_34])).
% 4.30/1.80  tff(c_3378, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_3362])).
% 4.30/1.80  tff(c_3404, plain, (k5_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3378, c_26])).
% 4.30/1.80  tff(c_3410, plain, (k5_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1739, c_3404])).
% 4.30/1.80  tff(c_1247, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_74])).
% 4.30/1.80  tff(c_1502, plain, (k3_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_1247, c_1488])).
% 4.30/1.80  tff(c_1661, plain, (![A_155, B_156]: (k5_xboole_0(A_155, k3_xboole_0(A_155, B_156))=k4_xboole_0(A_155, B_156))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.30/1.80  tff(c_2259, plain, (![A_180, B_181]: (k5_xboole_0(A_180, k3_xboole_0(B_181, A_180))=k4_xboole_0(A_180, B_181))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1661])).
% 4.30/1.80  tff(c_2287, plain, (k5_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1502, c_2259])).
% 4.30/1.80  tff(c_3420, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3410, c_2287])).
% 4.30/1.80  tff(c_52, plain, (![A_42, B_43]: (k6_subset_1(A_42, B_43)=k4_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.30/1.80  tff(c_48, plain, (![A_38, B_39]: (m1_subset_1(k6_subset_1(A_38, B_39), k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.30/1.80  tff(c_71, plain, (![A_38, B_39]: (m1_subset_1(k4_xboole_0(A_38, B_39), k1_zfmisc_1(A_38)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48])).
% 4.30/1.80  tff(c_3457, plain, (m1_subset_1(k2_xboole_0('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3420, c_71])).
% 4.30/1.80  tff(c_3691, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3644, c_3457])).
% 4.30/1.80  tff(c_3522, plain, (![B_212, A_37]: (r1_tarski(B_212, A_37) | ~m1_subset_1(B_212, k1_zfmisc_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_22, c_3496])).
% 4.30/1.80  tff(c_3778, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_3691, c_3522])).
% 4.30/1.80  tff(c_3787, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3569, c_3778])).
% 4.30/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.30/1.80  
% 4.30/1.80  Inference rules
% 4.30/1.80  ----------------------
% 4.30/1.80  #Ref     : 0
% 4.30/1.80  #Sup     : 903
% 4.30/1.80  #Fact    : 0
% 4.30/1.80  #Define  : 0
% 4.30/1.80  #Split   : 3
% 4.30/1.80  #Chain   : 0
% 4.30/1.80  #Close   : 0
% 4.30/1.80  
% 4.30/1.80  Ordering : KBO
% 4.30/1.80  
% 4.30/1.80  Simplification rules
% 4.30/1.80  ----------------------
% 4.30/1.80  #Subsume      : 5
% 4.30/1.80  #Demod        : 587
% 4.30/1.80  #Tautology    : 710
% 4.30/1.80  #SimpNegUnit  : 2
% 4.30/1.80  #BackRed      : 12
% 4.30/1.80  
% 4.30/1.80  #Partial instantiations: 0
% 4.30/1.80  #Strategies tried      : 1
% 4.30/1.80  
% 4.30/1.80  Timing (in seconds)
% 4.30/1.80  ----------------------
% 4.30/1.80  Preprocessing        : 0.35
% 4.30/1.80  Parsing              : 0.18
% 4.30/1.80  CNF conversion       : 0.02
% 4.30/1.80  Main loop            : 0.68
% 4.30/1.80  Inferencing          : 0.23
% 4.30/1.80  Reduction            : 0.28
% 4.30/1.80  Demodulation         : 0.23
% 4.30/1.80  BG Simplification    : 0.03
% 4.30/1.80  Subsumption          : 0.10
% 4.30/1.80  Abstraction          : 0.03
% 4.30/1.80  MUC search           : 0.00
% 4.30/1.80  Cooper               : 0.00
% 4.30/1.80  Total                : 1.07
% 4.30/1.80  Index Insertion      : 0.00
% 4.30/1.80  Index Deletion       : 0.00
% 4.30/1.80  Index Matching       : 0.00
% 4.30/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
