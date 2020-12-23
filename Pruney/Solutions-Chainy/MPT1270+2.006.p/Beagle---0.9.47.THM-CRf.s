%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:56 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 149 expanded)
%              Number of leaves         :   31 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 249 expanded)
%              Number of equality atoms :   42 (  61 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2256,plain,(
    ! [B_145,A_146] :
      ( r1_tarski(B_145,k2_pre_topc(A_146,B_145))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2258,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2256])).

tff(c_2261,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2258])).

tff(c_12,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_40,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_111,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_34,plain,
    ( ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_159,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_34])).

tff(c_1571,plain,(
    ! [B_114,A_115] :
      ( v2_tops_1(B_114,A_115)
      | k1_tops_1(A_115,B_114) != k1_xboole_0
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1577,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1571])).

tff(c_1581,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1577])).

tff(c_1582,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_1581])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_111,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k4_xboole_0(A_13,B_14),C_15) = k4_xboole_0(A_13,k2_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_93,plain,(
    ! [A_42,B_43] :
      ( k2_xboole_0(A_42,B_43) = B_43
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    ! [A_8,B_9] : k2_xboole_0(k4_xboole_0(A_8,B_9),A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_8,c_93])).

tff(c_277,plain,(
    ! [A_65,B_66,C_67] : k4_xboole_0(k4_xboole_0(A_65,B_66),C_67) = k4_xboole_0(A_65,k2_xboole_0(B_66,C_67)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_624,plain,(
    ! [A_82,B_83,C_84] : r1_tarski(k4_xboole_0(A_82,k2_xboole_0(B_83,C_84)),k4_xboole_0(A_82,B_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_8])).

tff(c_819,plain,(
    ! [A_92,A_93,B_94] : r1_tarski(k4_xboole_0(A_92,A_93),k4_xboole_0(A_92,k4_xboole_0(A_93,B_94))) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_624])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k4_xboole_0(B_11,A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_883,plain,(
    ! [B_95] : k4_xboole_0(B_95,B_95) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_819,c_10])).

tff(c_666,plain,(
    ! [A_82,A_8,B_9] : r1_tarski(k4_xboole_0(A_82,A_8),k4_xboole_0(A_82,k4_xboole_0(A_8,B_9))) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_624])).

tff(c_895,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(k4_xboole_0(A_8,B_9),A_8),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_883,c_666])).

tff(c_1398,plain,(
    ! [A_110,B_111] : r1_tarski(k4_xboole_0(A_110,k2_xboole_0(B_111,A_110)),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_895])).

tff(c_957,plain,(
    ! [B_95] :
      ( k1_xboole_0 = B_95
      | ~ r1_tarski(B_95,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_883,c_10])).

tff(c_1461,plain,(
    ! [A_112,B_113] : k4_xboole_0(A_112,k2_xboole_0(B_113,A_112)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1398,c_957])).

tff(c_1705,plain,(
    ! [A_118,B_119] : k4_xboole_0(A_118,k2_xboole_0(A_118,B_119)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1461])).

tff(c_1789,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_1705])).

tff(c_578,plain,(
    ! [A_75,B_76,C_77] :
      ( k7_subset_1(A_75,B_76,C_77) = k4_xboole_0(B_76,C_77)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_581,plain,(
    ! [C_77] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_77) = k4_xboole_0('#skF_2',C_77) ),
    inference(resolution,[status(thm)],[c_30,c_578])).

tff(c_1923,plain,(
    ! [A_120,B_121] :
      ( k7_subset_1(u1_struct_0(A_120),B_121,k2_tops_1(A_120,B_121)) = k1_tops_1(A_120,B_121)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1927,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1923])).

tff(c_1931,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1789,c_581,c_1927])).

tff(c_1933,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1582,c_1931])).

tff(c_1934,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2963,plain,(
    ! [A_169,B_170] :
      ( k1_tops_1(A_169,B_170) = k1_xboole_0
      | ~ v2_tops_1(B_170,A_169)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ l1_pre_topc(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2966,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2963])).

tff(c_2969,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1934,c_2966])).

tff(c_2996,plain,(
    ! [A_172,B_173] :
      ( m1_subset_1(k2_pre_topc(A_172,B_173),k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_16,B_17,C_18] :
      ( k7_subset_1(A_16,B_17,C_18) = k4_xboole_0(B_17,C_18)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5978,plain,(
    ! [A_230,B_231,C_232] :
      ( k7_subset_1(u1_struct_0(A_230),k2_pre_topc(A_230,B_231),C_232) = k4_xboole_0(k2_pre_topc(A_230,B_231),C_232)
      | ~ m1_subset_1(B_231,k1_zfmisc_1(u1_struct_0(A_230)))
      | ~ l1_pre_topc(A_230) ) ),
    inference(resolution,[status(thm)],[c_2996,c_16])).

tff(c_5982,plain,(
    ! [C_232] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_232) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_232)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_5978])).

tff(c_5990,plain,(
    ! [C_233] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_233) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_233) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_5982])).

tff(c_22,plain,(
    ! [A_24,B_26] :
      ( k7_subset_1(u1_struct_0(A_24),k2_pre_topc(A_24,B_26),k1_tops_1(A_24,B_26)) = k2_tops_1(A_24,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5997,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5990,c_22])).

tff(c_6007,plain,(
    k2_tops_1('#skF_1','#skF_2') = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_12,c_2969,c_5997])).

tff(c_1935,plain,(
    ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_6014,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6007,c_1935])).

tff(c_6020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2261,c_6014])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:53:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.88  
% 4.45/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.88  %$ v2_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.45/1.88  
% 4.45/1.88  %Foreground sorts:
% 4.45/1.88  
% 4.45/1.88  
% 4.45/1.88  %Background operators:
% 4.45/1.88  
% 4.45/1.88  
% 4.45/1.88  %Foreground operators:
% 4.45/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/1.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.45/1.88  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.45/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.45/1.88  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.45/1.88  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.45/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.45/1.88  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.45/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.45/1.88  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.45/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.45/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.45/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/1.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.45/1.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.45/1.88  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.45/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.45/1.88  
% 4.45/1.90  tff(f_97, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 4.45/1.90  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 4.45/1.90  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.45/1.90  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 4.45/1.90  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.45/1.90  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.45/1.90  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.45/1.90  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.45/1.90  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 4.45/1.90  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.45/1.90  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 4.45/1.90  tff(f_57, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.45/1.90  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 4.45/1.90  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.45/1.90  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.45/1.90  tff(c_2256, plain, (![B_145, A_146]: (r1_tarski(B_145, k2_pre_topc(A_146, B_145)) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.45/1.90  tff(c_2258, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_2256])).
% 4.45/1.90  tff(c_2261, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2258])).
% 4.45/1.90  tff(c_12, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.45/1.90  tff(c_40, plain, (v2_tops_1('#skF_2', '#skF_1') | r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.45/1.90  tff(c_111, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_40])).
% 4.45/1.90  tff(c_34, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.45/1.90  tff(c_159, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_34])).
% 4.45/1.90  tff(c_1571, plain, (![B_114, A_115]: (v2_tops_1(B_114, A_115) | k1_tops_1(A_115, B_114)!=k1_xboole_0 | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.45/1.90  tff(c_1577, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1571])).
% 4.45/1.90  tff(c_1581, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1577])).
% 4.45/1.90  tff(c_1582, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_159, c_1581])).
% 4.45/1.90  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.45/1.90  tff(c_115, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_111, c_4])).
% 4.45/1.90  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.45/1.90  tff(c_14, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k4_xboole_0(A_13, B_14), C_15)=k4_xboole_0(A_13, k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.45/1.90  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.45/1.90  tff(c_93, plain, (![A_42, B_43]: (k2_xboole_0(A_42, B_43)=B_43 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.45/1.90  tff(c_101, plain, (![A_8, B_9]: (k2_xboole_0(k4_xboole_0(A_8, B_9), A_8)=A_8)), inference(resolution, [status(thm)], [c_8, c_93])).
% 4.45/1.90  tff(c_277, plain, (![A_65, B_66, C_67]: (k4_xboole_0(k4_xboole_0(A_65, B_66), C_67)=k4_xboole_0(A_65, k2_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.45/1.90  tff(c_624, plain, (![A_82, B_83, C_84]: (r1_tarski(k4_xboole_0(A_82, k2_xboole_0(B_83, C_84)), k4_xboole_0(A_82, B_83)))), inference(superposition, [status(thm), theory('equality')], [c_277, c_8])).
% 4.45/1.90  tff(c_819, plain, (![A_92, A_93, B_94]: (r1_tarski(k4_xboole_0(A_92, A_93), k4_xboole_0(A_92, k4_xboole_0(A_93, B_94))))), inference(superposition, [status(thm), theory('equality')], [c_101, c_624])).
% 4.45/1.90  tff(c_10, plain, (![A_10, B_11]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k4_xboole_0(B_11, A_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.45/1.90  tff(c_883, plain, (![B_95]: (k4_xboole_0(B_95, B_95)=k1_xboole_0)), inference(resolution, [status(thm)], [c_819, c_10])).
% 4.45/1.90  tff(c_666, plain, (![A_82, A_8, B_9]: (r1_tarski(k4_xboole_0(A_82, A_8), k4_xboole_0(A_82, k4_xboole_0(A_8, B_9))))), inference(superposition, [status(thm), theory('equality')], [c_101, c_624])).
% 4.45/1.90  tff(c_895, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_8, B_9), A_8), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_883, c_666])).
% 4.45/1.90  tff(c_1398, plain, (![A_110, B_111]: (r1_tarski(k4_xboole_0(A_110, k2_xboole_0(B_111, A_110)), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_895])).
% 4.45/1.90  tff(c_957, plain, (![B_95]: (k1_xboole_0=B_95 | ~r1_tarski(B_95, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_883, c_10])).
% 4.45/1.90  tff(c_1461, plain, (![A_112, B_113]: (k4_xboole_0(A_112, k2_xboole_0(B_113, A_112))=k1_xboole_0)), inference(resolution, [status(thm)], [c_1398, c_957])).
% 4.45/1.90  tff(c_1705, plain, (![A_118, B_119]: (k4_xboole_0(A_118, k2_xboole_0(A_118, B_119))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1461])).
% 4.45/1.90  tff(c_1789, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_115, c_1705])).
% 4.45/1.90  tff(c_578, plain, (![A_75, B_76, C_77]: (k7_subset_1(A_75, B_76, C_77)=k4_xboole_0(B_76, C_77) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.45/1.90  tff(c_581, plain, (![C_77]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_77)=k4_xboole_0('#skF_2', C_77))), inference(resolution, [status(thm)], [c_30, c_578])).
% 4.45/1.90  tff(c_1923, plain, (![A_120, B_121]: (k7_subset_1(u1_struct_0(A_120), B_121, k2_tops_1(A_120, B_121))=k1_tops_1(A_120, B_121) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.45/1.90  tff(c_1927, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1923])).
% 4.45/1.90  tff(c_1931, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1789, c_581, c_1927])).
% 4.45/1.90  tff(c_1933, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1582, c_1931])).
% 4.45/1.90  tff(c_1934, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 4.45/1.90  tff(c_2963, plain, (![A_169, B_170]: (k1_tops_1(A_169, B_170)=k1_xboole_0 | ~v2_tops_1(B_170, A_169) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0(A_169))) | ~l1_pre_topc(A_169))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.45/1.90  tff(c_2966, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_2963])).
% 4.45/1.90  tff(c_2969, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1934, c_2966])).
% 4.45/1.90  tff(c_2996, plain, (![A_172, B_173]: (m1_subset_1(k2_pre_topc(A_172, B_173), k1_zfmisc_1(u1_struct_0(A_172))) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.45/1.90  tff(c_16, plain, (![A_16, B_17, C_18]: (k7_subset_1(A_16, B_17, C_18)=k4_xboole_0(B_17, C_18) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.45/1.90  tff(c_5978, plain, (![A_230, B_231, C_232]: (k7_subset_1(u1_struct_0(A_230), k2_pre_topc(A_230, B_231), C_232)=k4_xboole_0(k2_pre_topc(A_230, B_231), C_232) | ~m1_subset_1(B_231, k1_zfmisc_1(u1_struct_0(A_230))) | ~l1_pre_topc(A_230))), inference(resolution, [status(thm)], [c_2996, c_16])).
% 4.45/1.90  tff(c_5982, plain, (![C_232]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_232)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_232) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_5978])).
% 4.45/1.90  tff(c_5990, plain, (![C_233]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_233)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_233))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_5982])).
% 4.45/1.90  tff(c_22, plain, (![A_24, B_26]: (k7_subset_1(u1_struct_0(A_24), k2_pre_topc(A_24, B_26), k1_tops_1(A_24, B_26))=k2_tops_1(A_24, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.45/1.90  tff(c_5997, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5990, c_22])).
% 4.45/1.90  tff(c_6007, plain, (k2_tops_1('#skF_1', '#skF_2')=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_12, c_2969, c_5997])).
% 4.45/1.90  tff(c_1935, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_40])).
% 4.45/1.90  tff(c_6014, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6007, c_1935])).
% 4.45/1.90  tff(c_6020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2261, c_6014])).
% 4.45/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.90  
% 4.45/1.90  Inference rules
% 4.45/1.90  ----------------------
% 4.45/1.90  #Ref     : 0
% 4.45/1.90  #Sup     : 1474
% 4.45/1.90  #Fact    : 0
% 4.45/1.90  #Define  : 0
% 4.45/1.90  #Split   : 3
% 4.45/1.90  #Chain   : 0
% 4.45/1.90  #Close   : 0
% 4.45/1.90  
% 4.45/1.90  Ordering : KBO
% 4.45/1.90  
% 4.45/1.90  Simplification rules
% 4.45/1.90  ----------------------
% 4.45/1.90  #Subsume      : 129
% 4.45/1.90  #Demod        : 1033
% 4.45/1.90  #Tautology    : 992
% 4.45/1.90  #SimpNegUnit  : 2
% 4.45/1.90  #BackRed      : 13
% 4.45/1.90  
% 4.45/1.90  #Partial instantiations: 0
% 4.45/1.90  #Strategies tried      : 1
% 4.45/1.90  
% 4.45/1.90  Timing (in seconds)
% 4.45/1.90  ----------------------
% 4.45/1.90  Preprocessing        : 0.30
% 4.45/1.90  Parsing              : 0.16
% 4.45/1.90  CNF conversion       : 0.02
% 4.45/1.90  Main loop            : 0.80
% 4.45/1.90  Inferencing          : 0.25
% 4.45/1.90  Reduction            : 0.34
% 4.45/1.90  Demodulation         : 0.27
% 4.45/1.90  BG Simplification    : 0.03
% 4.45/1.90  Subsumption          : 0.13
% 4.45/1.90  Abstraction          : 0.04
% 4.45/1.90  MUC search           : 0.00
% 4.45/1.90  Cooper               : 0.00
% 4.45/1.90  Total                : 1.14
% 4.45/1.90  Index Insertion      : 0.00
% 4.45/1.90  Index Deletion       : 0.00
% 4.45/1.90  Index Matching       : 0.00
% 4.45/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
