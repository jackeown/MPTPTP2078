%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:34 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 126 expanded)
%              Number of leaves         :   33 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :  118 ( 252 expanded)
%              Number of equality atoms :   50 (  82 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_857,plain,(
    ! [A_122,B_123,C_124] :
      ( k7_subset_1(A_122,B_123,C_124) = k4_xboole_0(B_123,C_124)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(A_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_860,plain,(
    ! [C_124] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_124) = k4_xboole_0('#skF_2',C_124) ),
    inference(resolution,[status(thm)],[c_34,c_857])).

tff(c_40,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_83,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_498,plain,(
    ! [B_76,A_77] :
      ( v4_pre_topc(B_76,A_77)
      | k2_pre_topc(A_77,B_76) != B_76
      | ~ v2_pre_topc(A_77)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_504,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_498])).

tff(c_508,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_504])).

tff(c_509,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_508])).

tff(c_511,plain,(
    ! [A_80,B_81] :
      ( k4_subset_1(u1_struct_0(A_80),B_81,k2_tops_1(A_80,B_81)) = k2_pre_topc(A_80,B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_515,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_511])).

tff(c_519,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_515])).

tff(c_334,plain,(
    ! [A_60,B_61,C_62] :
      ( k7_subset_1(A_60,B_61,C_62) = k4_xboole_0(B_61,C_62)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_338,plain,(
    ! [C_63] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_63) = k4_xboole_0('#skF_2',C_63) ),
    inference(resolution,[status(thm)],[c_34,c_334])).

tff(c_46,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_223,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_46])).

tff(c_344,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_223])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_67,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_59])).

tff(c_151,plain,(
    ! [A_46,B_47] : k5_xboole_0(A_46,k4_xboole_0(B_47,A_46)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_166,plain,(
    ! [B_4] : k5_xboole_0(B_4,k1_xboole_0) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_151])).

tff(c_169,plain,(
    ! [B_4] : k5_xboole_0(B_4,k1_xboole_0) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_166])).

tff(c_14,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_66,plain,(
    ! [A_7,B_8] : k4_xboole_0(k4_xboole_0(A_7,B_8),A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_59])).

tff(c_160,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k5_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_151])).

tff(c_247,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_160])).

tff(c_362,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_247])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k2_tops_1(A_20,B_21),k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_473,plain,(
    ! [A_72,B_73,C_74] :
      ( k4_subset_1(A_72,B_73,C_74) = k2_xboole_0(B_73,C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(A_72))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_605,plain,(
    ! [A_99,B_100,B_101] :
      ( k4_subset_1(u1_struct_0(A_99),B_100,k2_tops_1(A_99,B_101)) = k2_xboole_0(B_100,k2_tops_1(A_99,B_101))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(resolution,[status(thm)],[c_26,c_473])).

tff(c_609,plain,(
    ! [B_101] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_101)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_101))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_605])).

tff(c_614,plain,(
    ! [B_102] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_102)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_102))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_609])).

tff(c_621,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_614])).

tff(c_626,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_362,c_621])).

tff(c_628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_509,c_626])).

tff(c_629,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_861,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_629])).

tff(c_630,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_891,plain,(
    ! [A_128,B_129] :
      ( k2_pre_topc(A_128,B_129) = B_129
      | ~ v4_pre_topc(B_129,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_894,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_891])).

tff(c_897,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_630,c_894])).

tff(c_997,plain,(
    ! [A_147,B_148] :
      ( k7_subset_1(u1_struct_0(A_147),k2_pre_topc(A_147,B_148),k1_tops_1(A_147,B_148)) = k2_tops_1(A_147,B_148)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1006,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_897,c_997])).

tff(c_1010,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_860,c_1006])).

tff(c_1012,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_861,c_1010])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.65  
% 2.90/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.65  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.90/1.65  
% 2.90/1.65  %Foreground sorts:
% 2.90/1.65  
% 2.90/1.65  
% 2.90/1.65  %Background operators:
% 2.90/1.65  
% 2.90/1.65  
% 2.90/1.65  %Foreground operators:
% 2.90/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.90/1.65  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.90/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.90/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.90/1.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.90/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.65  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.90/1.65  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.90/1.65  tff('#skF_2', type, '#skF_2': $i).
% 2.90/1.65  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.90/1.65  tff('#skF_1', type, '#skF_1': $i).
% 2.90/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.65  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.90/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.90/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.90/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.90/1.65  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.90/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.65  
% 2.90/1.67  tff(f_106, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 2.90/1.67  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.90/1.67  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.90/1.67  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 2.90/1.67  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.90/1.67  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.90/1.67  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.90/1.67  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.90/1.67  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.90/1.67  tff(f_72, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.90/1.67  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.90/1.67  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 2.90/1.67  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.90/1.67  tff(c_857, plain, (![A_122, B_123, C_124]: (k7_subset_1(A_122, B_123, C_124)=k4_xboole_0(B_123, C_124) | ~m1_subset_1(B_123, k1_zfmisc_1(A_122)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.90/1.67  tff(c_860, plain, (![C_124]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_124)=k4_xboole_0('#skF_2', C_124))), inference(resolution, [status(thm)], [c_34, c_857])).
% 2.90/1.67  tff(c_40, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.90/1.67  tff(c_83, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 2.90/1.67  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.90/1.67  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.90/1.67  tff(c_498, plain, (![B_76, A_77]: (v4_pre_topc(B_76, A_77) | k2_pre_topc(A_77, B_76)!=B_76 | ~v2_pre_topc(A_77) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.90/1.67  tff(c_504, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_498])).
% 2.90/1.67  tff(c_508, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_504])).
% 2.90/1.67  tff(c_509, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_83, c_508])).
% 2.90/1.67  tff(c_511, plain, (![A_80, B_81]: (k4_subset_1(u1_struct_0(A_80), B_81, k2_tops_1(A_80, B_81))=k2_pre_topc(A_80, B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.90/1.67  tff(c_515, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_511])).
% 2.90/1.67  tff(c_519, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_515])).
% 2.90/1.67  tff(c_334, plain, (![A_60, B_61, C_62]: (k7_subset_1(A_60, B_61, C_62)=k4_xboole_0(B_61, C_62) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.90/1.67  tff(c_338, plain, (![C_63]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_63)=k4_xboole_0('#skF_2', C_63))), inference(resolution, [status(thm)], [c_34, c_334])).
% 2.90/1.67  tff(c_46, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.90/1.67  tff(c_223, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_83, c_46])).
% 2.90/1.67  tff(c_344, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_338, c_223])).
% 2.90/1.67  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.90/1.67  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.90/1.67  tff(c_59, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.90/1.67  tff(c_67, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_59])).
% 2.90/1.67  tff(c_151, plain, (![A_46, B_47]: (k5_xboole_0(A_46, k4_xboole_0(B_47, A_46))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.90/1.67  tff(c_166, plain, (![B_4]: (k5_xboole_0(B_4, k1_xboole_0)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_67, c_151])).
% 2.90/1.67  tff(c_169, plain, (![B_4]: (k5_xboole_0(B_4, k1_xboole_0)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_166])).
% 2.90/1.67  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.90/1.67  tff(c_66, plain, (![A_7, B_8]: (k4_xboole_0(k4_xboole_0(A_7, B_8), A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_59])).
% 2.90/1.67  tff(c_160, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k5_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_66, c_151])).
% 2.90/1.67  tff(c_247, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(A_7, B_8))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_169, c_160])).
% 2.90/1.67  tff(c_362, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_344, c_247])).
% 2.90/1.67  tff(c_26, plain, (![A_20, B_21]: (m1_subset_1(k2_tops_1(A_20, B_21), k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.90/1.67  tff(c_473, plain, (![A_72, B_73, C_74]: (k4_subset_1(A_72, B_73, C_74)=k2_xboole_0(B_73, C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(A_72)) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.90/1.67  tff(c_605, plain, (![A_99, B_100, B_101]: (k4_subset_1(u1_struct_0(A_99), B_100, k2_tops_1(A_99, B_101))=k2_xboole_0(B_100, k2_tops_1(A_99, B_101)) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(resolution, [status(thm)], [c_26, c_473])).
% 2.90/1.67  tff(c_609, plain, (![B_101]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_101))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_101)) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_605])).
% 2.90/1.67  tff(c_614, plain, (![B_102]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_102))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_102)) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_609])).
% 2.90/1.67  tff(c_621, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_614])).
% 2.90/1.67  tff(c_626, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_519, c_362, c_621])).
% 2.90/1.67  tff(c_628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_509, c_626])).
% 2.90/1.67  tff(c_629, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 2.90/1.67  tff(c_861, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_860, c_629])).
% 2.90/1.67  tff(c_630, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 2.90/1.67  tff(c_891, plain, (![A_128, B_129]: (k2_pre_topc(A_128, B_129)=B_129 | ~v4_pre_topc(B_129, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.90/1.67  tff(c_894, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_891])).
% 2.90/1.67  tff(c_897, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_630, c_894])).
% 2.90/1.67  tff(c_997, plain, (![A_147, B_148]: (k7_subset_1(u1_struct_0(A_147), k2_pre_topc(A_147, B_148), k1_tops_1(A_147, B_148))=k2_tops_1(A_147, B_148) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.90/1.67  tff(c_1006, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_897, c_997])).
% 2.90/1.67  tff(c_1010, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_860, c_1006])).
% 2.90/1.67  tff(c_1012, plain, $false, inference(negUnitSimplification, [status(thm)], [c_861, c_1010])).
% 2.90/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.67  
% 2.90/1.67  Inference rules
% 2.90/1.67  ----------------------
% 2.90/1.67  #Ref     : 0
% 2.90/1.67  #Sup     : 221
% 2.90/1.67  #Fact    : 0
% 2.90/1.67  #Define  : 0
% 2.90/1.67  #Split   : 4
% 2.90/1.67  #Chain   : 0
% 2.90/1.67  #Close   : 0
% 2.90/1.67  
% 2.90/1.67  Ordering : KBO
% 2.90/1.67  
% 2.90/1.67  Simplification rules
% 2.90/1.67  ----------------------
% 2.90/1.67  #Subsume      : 23
% 2.90/1.67  #Demod        : 102
% 2.90/1.67  #Tautology    : 134
% 2.90/1.67  #SimpNegUnit  : 4
% 2.90/1.67  #BackRed      : 1
% 2.90/1.67  
% 2.90/1.67  #Partial instantiations: 0
% 2.90/1.67  #Strategies tried      : 1
% 2.90/1.67  
% 2.90/1.67  Timing (in seconds)
% 2.90/1.67  ----------------------
% 2.90/1.67  Preprocessing        : 0.37
% 2.90/1.67  Parsing              : 0.19
% 2.90/1.67  CNF conversion       : 0.02
% 2.90/1.67  Main loop            : 0.38
% 2.90/1.67  Inferencing          : 0.14
% 2.90/1.67  Reduction            : 0.12
% 2.90/1.67  Demodulation         : 0.09
% 2.90/1.67  BG Simplification    : 0.02
% 2.90/1.67  Subsumption          : 0.06
% 2.90/1.67  Abstraction          : 0.02
% 2.90/1.67  MUC search           : 0.00
% 2.90/1.68  Cooper               : 0.00
% 2.90/1.68  Total                : 0.78
% 2.90/1.68  Index Insertion      : 0.00
% 2.90/1.68  Index Deletion       : 0.00
% 2.90/1.68  Index Matching       : 0.00
% 2.90/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
