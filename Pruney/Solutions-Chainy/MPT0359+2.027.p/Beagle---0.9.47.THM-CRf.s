%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:12 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 176 expanded)
%              Number of leaves         :   37 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :   97 ( 208 expanded)
%              Number of equality atoms :   68 ( 135 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_67,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_59,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_73,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_16,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_17] : k5_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_178,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_185,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_178])).

tff(c_390,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k4_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_405,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_390])).

tff(c_415,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_405])).

tff(c_34,plain,(
    ! [A_28] : k2_subset_1(A_28) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_38,plain,(
    ! [A_31] : m1_subset_1(k2_subset_1(A_31),k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_60,plain,(
    ! [A_31] : m1_subset_1(A_31,k1_zfmisc_1(A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38])).

tff(c_829,plain,(
    ! [A_90,B_91] :
      ( k4_xboole_0(A_90,B_91) = k3_subset_1(A_90,B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_835,plain,(
    ! [A_31] : k4_xboole_0(A_31,A_31) = k3_subset_1(A_31,A_31) ),
    inference(resolution,[status(thm)],[c_60,c_829])).

tff(c_839,plain,(
    ! [A_31] : k3_subset_1(A_31,A_31) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_835])).

tff(c_52,plain,
    ( k2_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_62,plain,
    ( '#skF_2' != '#skF_1'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_52])).

tff(c_101,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_58,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | k2_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_61,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_58])).

tff(c_248,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_61])).

tff(c_249,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_248,c_101])).

tff(c_840,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_249])).

tff(c_843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_840])).

tff(c_844,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_32,plain,(
    ! [A_27] : k1_subset_1(A_27) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    ! [A_34] : k3_subset_1(A_34,k1_subset_1(A_34)) = k2_subset_1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_59,plain,(
    ! [A_34] : k3_subset_1(A_34,k1_subset_1(A_34)) = A_34 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_42])).

tff(c_63,plain,(
    ! [A_34] : k3_subset_1(A_34,k1_xboole_0) = A_34 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_59])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_894,plain,(
    ! [A_96,B_97] :
      ( k3_xboole_0(A_96,B_97) = A_96
      | ~ r1_tarski(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_919,plain,(
    ! [A_99] : k3_xboole_0(k1_xboole_0,A_99) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_894])).

tff(c_965,plain,(
    ! [A_101] : k3_xboole_0(A_101,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_919])).

tff(c_12,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_977,plain,(
    ! [A_101] : k2_xboole_0(A_101,k1_xboole_0) = A_101 ),
    inference(superposition,[status(thm),theory(equality)],[c_965,c_12])).

tff(c_906,plain,(
    ! [A_11] : k3_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_894])).

tff(c_1136,plain,(
    ! [A_113,B_114] : k5_xboole_0(A_113,k3_xboole_0(A_113,B_114)) = k4_xboole_0(A_113,B_114) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1151,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_906,c_1136])).

tff(c_1179,plain,(
    ! [A_117] : k4_xboole_0(k1_xboole_0,A_117) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1151])).

tff(c_24,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1184,plain,(
    ! [A_117] : k5_xboole_0(A_117,k1_xboole_0) = k2_xboole_0(A_117,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1179,c_24])).

tff(c_1191,plain,(
    ! [A_117] : k5_xboole_0(A_117,k1_xboole_0) = A_117 ),
    inference(demodulation,[status(thm),theory(equality)],[c_977,c_1184])).

tff(c_845,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_904,plain,(
    k3_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_845,c_894])).

tff(c_879,plain,(
    ! [A_94,B_95] : k2_xboole_0(A_94,k3_xboole_0(A_94,B_95)) = A_94 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_888,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_879])).

tff(c_1085,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_904,c_888])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1584,plain,(
    ! [A_133,B_134] :
      ( k4_xboole_0(A_133,B_134) = k3_subset_1(A_133,B_134)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(A_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1596,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1584])).

tff(c_18,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1622,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1596,c_18])).

tff(c_1625,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_1622])).

tff(c_1619,plain,(
    k5_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1596,c_24])).

tff(c_1631,plain,(
    k5_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1625,c_1619])).

tff(c_1433,plain,(
    ! [A_128,B_129,C_130] : k5_xboole_0(k5_xboole_0(A_128,B_129),C_130) = k5_xboole_0(A_128,k5_xboole_0(B_129,C_130)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1459,plain,(
    ! [A_128,B_129] : k5_xboole_0(A_128,k5_xboole_0(B_129,k5_xboole_0(A_128,B_129))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1433,c_22])).

tff(c_1635,plain,(
    k5_xboole_0('#skF_2',k5_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1631,c_1459])).

tff(c_1708,plain,(
    k5_xboole_0(k3_subset_1('#skF_1','#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1635,c_1459])).

tff(c_1720,plain,(
    k5_xboole_0(k3_subset_1('#skF_1','#skF_2'),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1708,c_1459])).

tff(c_1732,plain,(
    k3_subset_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1191,c_22,c_1720])).

tff(c_1735,plain,(
    ! [A_137,B_138] :
      ( k3_subset_1(A_137,k3_subset_1(A_137,B_138)) = B_138
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1744,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_50,c_1735])).

tff(c_1770,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_1732,c_1744])).

tff(c_1771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_844,c_1770])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:18:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.49  
% 3.15/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.50  %$ r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.15/1.50  
% 3.15/1.50  %Foreground sorts:
% 3.15/1.50  
% 3.15/1.50  
% 3.15/1.50  %Background operators:
% 3.15/1.50  
% 3.15/1.50  
% 3.15/1.50  %Foreground operators:
% 3.15/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.15/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.15/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.15/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.15/1.50  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.15/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.15/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.15/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.15/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.15/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.50  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.15/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.15/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.15/1.50  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.15/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.50  
% 3.29/1.51  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.29/1.51  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.29/1.51  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.29/1.51  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.29/1.51  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.29/1.51  tff(f_61, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.29/1.51  tff(f_67, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.29/1.51  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.29/1.51  tff(f_91, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 3.29/1.51  tff(f_59, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.29/1.51  tff(f_73, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 3.29/1.51  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.29/1.51  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.29/1.51  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.29/1.51  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.29/1.51  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.29/1.51  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.29/1.51  tff(c_16, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.29/1.51  tff(c_22, plain, (![A_17]: (k5_xboole_0(A_17, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.29/1.51  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.29/1.51  tff(c_178, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=A_54 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.29/1.51  tff(c_185, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_178])).
% 3.29/1.51  tff(c_390, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k4_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.29/1.51  tff(c_405, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_185, c_390])).
% 3.29/1.51  tff(c_415, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_405])).
% 3.29/1.51  tff(c_34, plain, (![A_28]: (k2_subset_1(A_28)=A_28)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.29/1.51  tff(c_38, plain, (![A_31]: (m1_subset_1(k2_subset_1(A_31), k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.29/1.51  tff(c_60, plain, (![A_31]: (m1_subset_1(A_31, k1_zfmisc_1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38])).
% 3.29/1.51  tff(c_829, plain, (![A_90, B_91]: (k4_xboole_0(A_90, B_91)=k3_subset_1(A_90, B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.29/1.51  tff(c_835, plain, (![A_31]: (k4_xboole_0(A_31, A_31)=k3_subset_1(A_31, A_31))), inference(resolution, [status(thm)], [c_60, c_829])).
% 3.29/1.51  tff(c_839, plain, (![A_31]: (k3_subset_1(A_31, A_31)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_415, c_835])).
% 3.29/1.51  tff(c_52, plain, (k2_subset_1('#skF_1')!='#skF_2' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.29/1.51  tff(c_62, plain, ('#skF_2'!='#skF_1' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_52])).
% 3.29/1.51  tff(c_101, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_62])).
% 3.29/1.51  tff(c_58, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | k2_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.29/1.51  tff(c_61, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_58])).
% 3.29/1.51  tff(c_248, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_101, c_61])).
% 3.29/1.51  tff(c_249, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_248, c_248, c_101])).
% 3.29/1.51  tff(c_840, plain, (~r1_tarski(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_839, c_249])).
% 3.29/1.51  tff(c_843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_840])).
% 3.29/1.51  tff(c_844, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_62])).
% 3.29/1.51  tff(c_32, plain, (![A_27]: (k1_subset_1(A_27)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.29/1.51  tff(c_42, plain, (![A_34]: (k3_subset_1(A_34, k1_subset_1(A_34))=k2_subset_1(A_34))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.29/1.51  tff(c_59, plain, (![A_34]: (k3_subset_1(A_34, k1_subset_1(A_34))=A_34)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_42])).
% 3.29/1.51  tff(c_63, plain, (![A_34]: (k3_subset_1(A_34, k1_xboole_0)=A_34)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_59])).
% 3.29/1.51  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.29/1.51  tff(c_894, plain, (![A_96, B_97]: (k3_xboole_0(A_96, B_97)=A_96 | ~r1_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.29/1.51  tff(c_919, plain, (![A_99]: (k3_xboole_0(k1_xboole_0, A_99)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_894])).
% 3.29/1.51  tff(c_965, plain, (![A_101]: (k3_xboole_0(A_101, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_919])).
% 3.29/1.51  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k3_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.29/1.51  tff(c_977, plain, (![A_101]: (k2_xboole_0(A_101, k1_xboole_0)=A_101)), inference(superposition, [status(thm), theory('equality')], [c_965, c_12])).
% 3.29/1.51  tff(c_906, plain, (![A_11]: (k3_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_894])).
% 3.29/1.51  tff(c_1136, plain, (![A_113, B_114]: (k5_xboole_0(A_113, k3_xboole_0(A_113, B_114))=k4_xboole_0(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.29/1.51  tff(c_1151, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_11))), inference(superposition, [status(thm), theory('equality')], [c_906, c_1136])).
% 3.29/1.51  tff(c_1179, plain, (![A_117]: (k4_xboole_0(k1_xboole_0, A_117)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1151])).
% 3.29/1.51  tff(c_24, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.29/1.51  tff(c_1184, plain, (![A_117]: (k5_xboole_0(A_117, k1_xboole_0)=k2_xboole_0(A_117, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1179, c_24])).
% 3.29/1.51  tff(c_1191, plain, (![A_117]: (k5_xboole_0(A_117, k1_xboole_0)=A_117)), inference(demodulation, [status(thm), theory('equality')], [c_977, c_1184])).
% 3.29/1.51  tff(c_845, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_62])).
% 3.29/1.51  tff(c_904, plain, (k3_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_845, c_894])).
% 3.29/1.51  tff(c_879, plain, (![A_94, B_95]: (k2_xboole_0(A_94, k3_xboole_0(A_94, B_95))=A_94)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.29/1.51  tff(c_888, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_879])).
% 3.29/1.51  tff(c_1085, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_904, c_888])).
% 3.29/1.51  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.29/1.51  tff(c_1584, plain, (![A_133, B_134]: (k4_xboole_0(A_133, B_134)=k3_subset_1(A_133, B_134) | ~m1_subset_1(B_134, k1_zfmisc_1(A_133)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.29/1.51  tff(c_1596, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_1584])).
% 3.29/1.51  tff(c_18, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.29/1.51  tff(c_1622, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1596, c_18])).
% 3.29/1.51  tff(c_1625, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_1622])).
% 3.29/1.51  tff(c_1619, plain, (k5_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1596, c_24])).
% 3.29/1.51  tff(c_1631, plain, (k5_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1625, c_1619])).
% 3.29/1.51  tff(c_1433, plain, (![A_128, B_129, C_130]: (k5_xboole_0(k5_xboole_0(A_128, B_129), C_130)=k5_xboole_0(A_128, k5_xboole_0(B_129, C_130)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.29/1.51  tff(c_1459, plain, (![A_128, B_129]: (k5_xboole_0(A_128, k5_xboole_0(B_129, k5_xboole_0(A_128, B_129)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1433, c_22])).
% 3.29/1.51  tff(c_1635, plain, (k5_xboole_0('#skF_2', k5_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1631, c_1459])).
% 3.29/1.51  tff(c_1708, plain, (k5_xboole_0(k3_subset_1('#skF_1', '#skF_2'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1635, c_1459])).
% 3.29/1.51  tff(c_1720, plain, (k5_xboole_0(k3_subset_1('#skF_1', '#skF_2'), k5_xboole_0(k1_xboole_0, k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1708, c_1459])).
% 3.29/1.51  tff(c_1732, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1191, c_22, c_1720])).
% 3.29/1.51  tff(c_1735, plain, (![A_137, B_138]: (k3_subset_1(A_137, k3_subset_1(A_137, B_138))=B_138 | ~m1_subset_1(B_138, k1_zfmisc_1(A_137)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.29/1.51  tff(c_1744, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_50, c_1735])).
% 3.29/1.51  tff(c_1770, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_1732, c_1744])).
% 3.29/1.51  tff(c_1771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_844, c_1770])).
% 3.29/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.51  
% 3.29/1.51  Inference rules
% 3.29/1.51  ----------------------
% 3.29/1.51  #Ref     : 0
% 3.29/1.51  #Sup     : 403
% 3.29/1.51  #Fact    : 0
% 3.29/1.51  #Define  : 0
% 3.29/1.51  #Split   : 2
% 3.29/1.51  #Chain   : 0
% 3.29/1.51  #Close   : 0
% 3.29/1.51  
% 3.29/1.51  Ordering : KBO
% 3.29/1.51  
% 3.29/1.51  Simplification rules
% 3.29/1.51  ----------------------
% 3.29/1.51  #Subsume      : 0
% 3.29/1.51  #Demod        : 261
% 3.29/1.51  #Tautology    : 313
% 3.29/1.51  #SimpNegUnit  : 3
% 3.29/1.51  #BackRed      : 13
% 3.29/1.51  
% 3.29/1.51  #Partial instantiations: 0
% 3.29/1.51  #Strategies tried      : 1
% 3.29/1.51  
% 3.29/1.51  Timing (in seconds)
% 3.29/1.51  ----------------------
% 3.29/1.52  Preprocessing        : 0.33
% 3.29/1.52  Parsing              : 0.17
% 3.29/1.52  CNF conversion       : 0.02
% 3.29/1.52  Main loop            : 0.42
% 3.29/1.52  Inferencing          : 0.15
% 3.29/1.52  Reduction            : 0.16
% 3.29/1.52  Demodulation         : 0.13
% 3.29/1.52  BG Simplification    : 0.02
% 3.29/1.52  Subsumption          : 0.06
% 3.29/1.52  Abstraction          : 0.02
% 3.29/1.52  MUC search           : 0.00
% 3.29/1.52  Cooper               : 0.00
% 3.29/1.52  Total                : 0.79
% 3.29/1.52  Index Insertion      : 0.00
% 3.29/1.52  Index Deletion       : 0.00
% 3.29/1.52  Index Matching       : 0.00
% 3.29/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
