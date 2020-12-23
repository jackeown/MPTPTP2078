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
% DateTime   : Thu Dec  3 10:21:56 EST 2020

% Result     : Theorem 4.69s
% Output     : CNFRefutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 124 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :  111 ( 212 expanded)
%              Number of equality atoms :   28 (  40 expanded)
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

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_44,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_94,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,
    ( ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_109,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_38])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1022,plain,(
    ! [B_102,A_103] :
      ( v2_tops_1(B_102,A_103)
      | k1_tops_1(A_103,B_102) != k1_xboole_0
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1025,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_1022])).

tff(c_1028,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1025])).

tff(c_1029,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_1028])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_363,plain,(
    ! [A_67,B_68,C_69] :
      ( r1_tarski(A_67,k2_xboole_0(B_68,C_69))
      | ~ r1_tarski(k4_xboole_0(A_67,B_68),C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1386,plain,(
    ! [A_128,C_129] :
      ( r1_tarski(A_128,k2_xboole_0(k1_xboole_0,C_129))
      | ~ r1_tarski(A_128,C_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_363])).

tff(c_1410,plain,(
    ! [A_128,B_2] :
      ( r1_tarski(A_128,k2_xboole_0(B_2,k1_xboole_0))
      | ~ r1_tarski(A_128,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1386])).

tff(c_650,plain,(
    ! [A_79,B_80,C_81] :
      ( k7_subset_1(A_79,B_80,C_81) = k4_xboole_0(B_80,C_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_653,plain,(
    ! [C_81] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_81) = k4_xboole_0('#skF_2',C_81) ),
    inference(resolution,[status(thm)],[c_34,c_650])).

tff(c_1565,plain,(
    ! [A_132,B_133] :
      ( k7_subset_1(u1_struct_0(A_132),B_133,k2_tops_1(A_132,B_133)) = k1_tops_1(A_132,B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1569,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_1565])).

tff(c_1573,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_653,c_1569])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( r1_tarski(k4_xboole_0(A_11,B_12),C_13)
      | ~ r1_tarski(A_11,k2_xboole_0(B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1834,plain,(
    ! [C_142] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_142)
      | ~ r1_tarski('#skF_2',k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),C_142)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1573,c_16])).

tff(c_1838,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_xboole_0)
    | ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1410,c_1834])).

tff(c_1869,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1838])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_397,plain,(
    ! [A_70,B_71] : r1_tarski(A_70,k2_xboole_0(B_71,A_70)) ),
    inference(resolution,[status(thm)],[c_12,c_363])).

tff(c_421,plain,(
    ! [B_72,A_73] : r1_tarski(B_72,k2_xboole_0(B_72,A_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_397])).

tff(c_169,plain,(
    ! [A_55,B_56,C_57] :
      ( r1_tarski(k4_xboole_0(A_55,B_56),C_57)
      | ~ r1_tarski(A_55,k2_xboole_0(B_56,C_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_184,plain,(
    ! [A_10,C_57] :
      ( r1_tarski(A_10,C_57)
      | ~ r1_tarski(A_10,k2_xboole_0(k1_xboole_0,C_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_169])).

tff(c_446,plain,(
    ! [A_74] : r1_tarski(k1_xboole_0,A_74) ),
    inference(resolution,[status(thm)],[c_421,c_184])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_469,plain,(
    ! [A_74] :
      ( k1_xboole_0 = A_74
      | ~ r1_tarski(A_74,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_446,c_4])).

tff(c_1885,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1869,c_469])).

tff(c_1896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1029,c_1885])).

tff(c_1898,plain,(
    ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1897,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2769,plain,(
    ! [A_208,B_209] :
      ( k1_tops_1(A_208,B_209) = k1_xboole_0
      | ~ v2_tops_1(B_209,A_208)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0(A_208)))
      | ~ l1_pre_topc(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2772,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_2769])).

tff(c_2775,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1897,c_2772])).

tff(c_2192,plain,(
    ! [A_173,B_174,C_175] :
      ( k7_subset_1(A_173,B_174,C_175) = k4_xboole_0(B_174,C_175)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(A_173)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2195,plain,(
    ! [C_175] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_175) = k4_xboole_0('#skF_2',C_175) ),
    inference(resolution,[status(thm)],[c_34,c_2192])).

tff(c_3040,plain,(
    ! [A_223,B_224] :
      ( k7_subset_1(u1_struct_0(A_223),B_224,k2_tops_1(A_223,B_224)) = k1_tops_1(A_223,B_224)
      | ~ m1_subset_1(B_224,k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ l1_pre_topc(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3044,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_3040])).

tff(c_3048,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2775,c_2195,c_3044])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2094,plain,(
    ! [A_165,B_166,C_167] :
      ( r1_tarski(A_165,k2_xboole_0(B_166,C_167))
      | ~ r1_tarski(k4_xboole_0(A_165,B_166),C_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2118,plain,(
    ! [A_165,B_166] : r1_tarski(A_165,k2_xboole_0(B_166,k4_xboole_0(A_165,B_166))) ),
    inference(resolution,[status(thm)],[c_8,c_2094])).

tff(c_3061,plain,(
    r1_tarski('#skF_2',k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3048,c_2118])).

tff(c_3085,plain,(
    r1_tarski('#skF_2',k2_xboole_0(k1_xboole_0,k2_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3061])).

tff(c_1960,plain,(
    ! [A_156,B_157,C_158] :
      ( r1_tarski(k4_xboole_0(A_156,B_157),C_158)
      | ~ r1_tarski(A_156,k2_xboole_0(B_157,C_158)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1975,plain,(
    ! [A_10,C_158] :
      ( r1_tarski(A_10,C_158)
      | ~ r1_tarski(A_10,k2_xboole_0(k1_xboole_0,C_158)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1960])).

tff(c_3097,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_3085,c_1975])).

tff(c_3107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1898,c_3097])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:39:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.69/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.87  
% 4.69/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.87  %$ v2_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.69/1.87  
% 4.69/1.87  %Foreground sorts:
% 4.69/1.87  
% 4.69/1.87  
% 4.69/1.87  %Background operators:
% 4.69/1.87  
% 4.69/1.87  
% 4.69/1.87  %Foreground operators:
% 4.69/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.69/1.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.69/1.87  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.69/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.69/1.87  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.69/1.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.69/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.69/1.87  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.69/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.69/1.87  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.69/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.69/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.69/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.69/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.69/1.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.69/1.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.69/1.87  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.69/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.69/1.87  
% 4.69/1.88  tff(f_101, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 4.69/1.88  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 4.69/1.88  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.69/1.88  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.69/1.88  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 4.69/1.88  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.69/1.88  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 4.69/1.88  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 4.69/1.88  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.69/1.88  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.69/1.88  tff(c_44, plain, (v2_tops_1('#skF_2', '#skF_1') | r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.69/1.88  tff(c_94, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_44])).
% 4.69/1.88  tff(c_38, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.69/1.88  tff(c_109, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_38])).
% 4.69/1.88  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.69/1.88  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.69/1.88  tff(c_1022, plain, (![B_102, A_103]: (v2_tops_1(B_102, A_103) | k1_tops_1(A_103, B_102)!=k1_xboole_0 | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.69/1.88  tff(c_1025, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_1022])).
% 4.69/1.88  tff(c_1028, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1025])).
% 4.69/1.88  tff(c_1029, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_109, c_1028])).
% 4.69/1.88  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.69/1.88  tff(c_14, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.69/1.88  tff(c_363, plain, (![A_67, B_68, C_69]: (r1_tarski(A_67, k2_xboole_0(B_68, C_69)) | ~r1_tarski(k4_xboole_0(A_67, B_68), C_69))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.69/1.88  tff(c_1386, plain, (![A_128, C_129]: (r1_tarski(A_128, k2_xboole_0(k1_xboole_0, C_129)) | ~r1_tarski(A_128, C_129))), inference(superposition, [status(thm), theory('equality')], [c_14, c_363])).
% 4.69/1.88  tff(c_1410, plain, (![A_128, B_2]: (r1_tarski(A_128, k2_xboole_0(B_2, k1_xboole_0)) | ~r1_tarski(A_128, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1386])).
% 4.69/1.88  tff(c_650, plain, (![A_79, B_80, C_81]: (k7_subset_1(A_79, B_80, C_81)=k4_xboole_0(B_80, C_81) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.69/1.88  tff(c_653, plain, (![C_81]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_81)=k4_xboole_0('#skF_2', C_81))), inference(resolution, [status(thm)], [c_34, c_650])).
% 4.69/1.88  tff(c_1565, plain, (![A_132, B_133]: (k7_subset_1(u1_struct_0(A_132), B_133, k2_tops_1(A_132, B_133))=k1_tops_1(A_132, B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.69/1.88  tff(c_1569, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_1565])).
% 4.69/1.88  tff(c_1573, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_653, c_1569])).
% 4.69/1.88  tff(c_16, plain, (![A_11, B_12, C_13]: (r1_tarski(k4_xboole_0(A_11, B_12), C_13) | ~r1_tarski(A_11, k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.69/1.88  tff(c_1834, plain, (![C_142]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_142) | ~r1_tarski('#skF_2', k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), C_142)))), inference(superposition, [status(thm), theory('equality')], [c_1573, c_16])).
% 4.69/1.88  tff(c_1838, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_xboole_0) | ~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1410, c_1834])).
% 4.69/1.88  tff(c_1869, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1838])).
% 4.69/1.88  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.69/1.88  tff(c_397, plain, (![A_70, B_71]: (r1_tarski(A_70, k2_xboole_0(B_71, A_70)))), inference(resolution, [status(thm)], [c_12, c_363])).
% 4.69/1.88  tff(c_421, plain, (![B_72, A_73]: (r1_tarski(B_72, k2_xboole_0(B_72, A_73)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_397])).
% 4.69/1.88  tff(c_169, plain, (![A_55, B_56, C_57]: (r1_tarski(k4_xboole_0(A_55, B_56), C_57) | ~r1_tarski(A_55, k2_xboole_0(B_56, C_57)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.69/1.88  tff(c_184, plain, (![A_10, C_57]: (r1_tarski(A_10, C_57) | ~r1_tarski(A_10, k2_xboole_0(k1_xboole_0, C_57)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_169])).
% 4.69/1.88  tff(c_446, plain, (![A_74]: (r1_tarski(k1_xboole_0, A_74))), inference(resolution, [status(thm)], [c_421, c_184])).
% 4.69/1.88  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.69/1.88  tff(c_469, plain, (![A_74]: (k1_xboole_0=A_74 | ~r1_tarski(A_74, k1_xboole_0))), inference(resolution, [status(thm)], [c_446, c_4])).
% 4.69/1.88  tff(c_1885, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1869, c_469])).
% 4.69/1.88  tff(c_1896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1029, c_1885])).
% 4.69/1.88  tff(c_1898, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_44])).
% 4.69/1.88  tff(c_1897, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 4.69/1.88  tff(c_2769, plain, (![A_208, B_209]: (k1_tops_1(A_208, B_209)=k1_xboole_0 | ~v2_tops_1(B_209, A_208) | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0(A_208))) | ~l1_pre_topc(A_208))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.69/1.88  tff(c_2772, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_2769])).
% 4.69/1.88  tff(c_2775, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1897, c_2772])).
% 4.69/1.88  tff(c_2192, plain, (![A_173, B_174, C_175]: (k7_subset_1(A_173, B_174, C_175)=k4_xboole_0(B_174, C_175) | ~m1_subset_1(B_174, k1_zfmisc_1(A_173)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.69/1.88  tff(c_2195, plain, (![C_175]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_175)=k4_xboole_0('#skF_2', C_175))), inference(resolution, [status(thm)], [c_34, c_2192])).
% 4.69/1.88  tff(c_3040, plain, (![A_223, B_224]: (k7_subset_1(u1_struct_0(A_223), B_224, k2_tops_1(A_223, B_224))=k1_tops_1(A_223, B_224) | ~m1_subset_1(B_224, k1_zfmisc_1(u1_struct_0(A_223))) | ~l1_pre_topc(A_223))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.69/1.88  tff(c_3044, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_3040])).
% 4.69/1.88  tff(c_3048, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2775, c_2195, c_3044])).
% 4.69/1.88  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.69/1.88  tff(c_2094, plain, (![A_165, B_166, C_167]: (r1_tarski(A_165, k2_xboole_0(B_166, C_167)) | ~r1_tarski(k4_xboole_0(A_165, B_166), C_167))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.69/1.88  tff(c_2118, plain, (![A_165, B_166]: (r1_tarski(A_165, k2_xboole_0(B_166, k4_xboole_0(A_165, B_166))))), inference(resolution, [status(thm)], [c_8, c_2094])).
% 4.69/1.88  tff(c_3061, plain, (r1_tarski('#skF_2', k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3048, c_2118])).
% 4.69/1.88  tff(c_3085, plain, (r1_tarski('#skF_2', k2_xboole_0(k1_xboole_0, k2_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3061])).
% 4.69/1.88  tff(c_1960, plain, (![A_156, B_157, C_158]: (r1_tarski(k4_xboole_0(A_156, B_157), C_158) | ~r1_tarski(A_156, k2_xboole_0(B_157, C_158)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.69/1.88  tff(c_1975, plain, (![A_10, C_158]: (r1_tarski(A_10, C_158) | ~r1_tarski(A_10, k2_xboole_0(k1_xboole_0, C_158)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1960])).
% 4.69/1.88  tff(c_3097, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_3085, c_1975])).
% 4.69/1.88  tff(c_3107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1898, c_3097])).
% 4.69/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.88  
% 4.69/1.88  Inference rules
% 4.69/1.88  ----------------------
% 4.69/1.88  #Ref     : 0
% 4.69/1.88  #Sup     : 705
% 4.69/1.88  #Fact    : 0
% 4.69/1.88  #Define  : 0
% 4.69/1.88  #Split   : 4
% 4.69/1.88  #Chain   : 0
% 4.69/1.88  #Close   : 0
% 4.69/1.88  
% 4.69/1.88  Ordering : KBO
% 4.69/1.88  
% 4.69/1.88  Simplification rules
% 4.69/1.88  ----------------------
% 4.69/1.88  #Subsume      : 28
% 4.69/1.88  #Demod        : 384
% 4.69/1.88  #Tautology    : 326
% 4.69/1.88  #SimpNegUnit  : 4
% 4.69/1.88  #BackRed      : 0
% 4.69/1.88  
% 4.69/1.88  #Partial instantiations: 0
% 4.69/1.88  #Strategies tried      : 1
% 4.69/1.88  
% 4.69/1.88  Timing (in seconds)
% 4.69/1.88  ----------------------
% 4.69/1.89  Preprocessing        : 0.34
% 4.69/1.89  Parsing              : 0.18
% 4.69/1.89  CNF conversion       : 0.02
% 4.69/1.89  Main loop            : 0.78
% 4.69/1.89  Inferencing          : 0.23
% 4.69/1.89  Reduction            : 0.30
% 4.69/1.89  Demodulation         : 0.24
% 4.69/1.89  BG Simplification    : 0.03
% 4.69/1.89  Subsumption          : 0.16
% 4.69/1.89  Abstraction          : 0.04
% 4.69/1.89  MUC search           : 0.00
% 4.69/1.89  Cooper               : 0.00
% 4.69/1.89  Total                : 1.16
% 4.69/1.89  Index Insertion      : 0.00
% 4.69/1.89  Index Deletion       : 0.00
% 4.69/1.89  Index Matching       : 0.00
% 4.69/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
