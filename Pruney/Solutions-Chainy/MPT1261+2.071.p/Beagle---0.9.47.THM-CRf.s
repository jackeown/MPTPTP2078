%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:21 EST 2020

% Result     : Theorem 9.71s
% Output     : CNFRefutation 9.71s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 116 expanded)
%              Number of leaves         :   33 (  55 expanded)
%              Depth                    :    7
%              Number of atoms          :  106 ( 234 expanded)
%              Number of equality atoms :   45 (  73 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_15363,plain,(
    ! [A_318,B_319,C_320] :
      ( k7_subset_1(A_318,B_319,C_320) = k4_xboole_0(B_319,C_320)
      | ~ m1_subset_1(B_319,k1_zfmisc_1(A_318)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_15366,plain,(
    ! [C_320] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_320) = k4_xboole_0('#skF_2',C_320) ),
    inference(resolution,[status(thm)],[c_36,c_15363])).

tff(c_42,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_142,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2503,plain,(
    ! [B_145,A_146] :
      ( v4_pre_topc(B_145,A_146)
      | k2_pre_topc(A_146,B_145) != B_145
      | ~ v2_pre_topc(A_146)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2509,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_2503])).

tff(c_2513,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_2509])).

tff(c_2514,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_2513])).

tff(c_2743,plain,(
    ! [A_152,B_153] :
      ( k4_subset_1(u1_struct_0(A_152),B_153,k2_tops_1(A_152,B_153)) = k2_pre_topc(A_152,B_153)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2747,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_2743])).

tff(c_2751,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2747])).

tff(c_722,plain,(
    ! [A_85,B_86,C_87] :
      ( k7_subset_1(A_85,B_86,C_87) = k4_xboole_0(B_86,C_87)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_726,plain,(
    ! [C_88] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_88) = k4_xboole_0('#skF_2',C_88) ),
    inference(resolution,[status(thm)],[c_36,c_722])).

tff(c_48,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_301,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_48])).

tff(c_732,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_301])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_336,plain,(
    ! [A_67,B_68,C_69] : k4_xboole_0(k3_xboole_0(A_67,B_68),C_69) = k3_xboole_0(A_67,k4_xboole_0(B_68,C_69)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_357,plain,(
    ! [A_70,C_71] : k3_xboole_0(A_70,k4_xboole_0(A_70,C_71)) = k4_xboole_0(A_70,C_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_336])).

tff(c_8,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_372,plain,(
    ! [A_70,C_71] : k2_xboole_0(A_70,k4_xboole_0(A_70,C_71)) = A_70 ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_8])).

tff(c_744,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_732,c_372])).

tff(c_30,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k2_tops_1(A_33,B_34),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2279,plain,(
    ! [A_136,B_137,C_138] :
      ( k4_subset_1(A_136,B_137,C_138) = k2_xboole_0(B_137,C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(A_136))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(A_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_13890,plain,(
    ! [A_275,B_276,B_277] :
      ( k4_subset_1(u1_struct_0(A_275),B_276,k2_tops_1(A_275,B_277)) = k2_xboole_0(B_276,k2_tops_1(A_275,B_277))
      | ~ m1_subset_1(B_276,k1_zfmisc_1(u1_struct_0(A_275)))
      | ~ m1_subset_1(B_277,k1_zfmisc_1(u1_struct_0(A_275)))
      | ~ l1_pre_topc(A_275) ) ),
    inference(resolution,[status(thm)],[c_30,c_2279])).

tff(c_13894,plain,(
    ! [B_277] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_277)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_277))
      | ~ m1_subset_1(B_277,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_13890])).

tff(c_14772,plain,(
    ! [B_284] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_284)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_284))
      | ~ m1_subset_1(B_284,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_13894])).

tff(c_14779,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_14772])).

tff(c_14784,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2751,c_744,c_14779])).

tff(c_14786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2514,c_14784])).

tff(c_14787,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_15367,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15366,c_14787])).

tff(c_14788,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_15715,plain,(
    ! [A_334,B_335] :
      ( k2_pre_topc(A_334,B_335) = B_335
      | ~ v4_pre_topc(B_335,A_334)
      | ~ m1_subset_1(B_335,k1_zfmisc_1(u1_struct_0(A_334)))
      | ~ l1_pre_topc(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_15718,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_15715])).

tff(c_15721,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_14788,c_15718])).

tff(c_16915,plain,(
    ! [A_382,B_383] :
      ( k7_subset_1(u1_struct_0(A_382),k2_pre_topc(A_382,B_383),k1_tops_1(A_382,B_383)) = k2_tops_1(A_382,B_383)
      | ~ m1_subset_1(B_383,k1_zfmisc_1(u1_struct_0(A_382)))
      | ~ l1_pre_topc(A_382) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_16924,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15721,c_16915])).

tff(c_16928,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_15366,c_16924])).

tff(c_16930,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15367,c_16928])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:55:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.71/3.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.71/3.83  
% 9.71/3.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.71/3.84  %$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 9.71/3.84  
% 9.71/3.84  %Foreground sorts:
% 9.71/3.84  
% 9.71/3.84  
% 9.71/3.84  %Background operators:
% 9.71/3.84  
% 9.71/3.84  
% 9.71/3.84  %Foreground operators:
% 9.71/3.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.71/3.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.71/3.84  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 9.71/3.84  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.71/3.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.71/3.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.71/3.84  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.71/3.84  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.71/3.84  tff('#skF_2', type, '#skF_2': $i).
% 9.71/3.84  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 9.71/3.84  tff('#skF_1', type, '#skF_1': $i).
% 9.71/3.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.71/3.84  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 9.71/3.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.71/3.84  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.71/3.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.71/3.84  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.71/3.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.71/3.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.71/3.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.71/3.84  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.71/3.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.71/3.84  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.71/3.84  
% 9.71/3.85  tff(f_102, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 9.71/3.85  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 9.71/3.85  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 9.71/3.85  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 9.71/3.85  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 9.71/3.85  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 9.71/3.85  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 9.71/3.85  tff(f_76, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 9.71/3.85  tff(f_49, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 9.71/3.85  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 9.71/3.85  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.71/3.85  tff(c_15363, plain, (![A_318, B_319, C_320]: (k7_subset_1(A_318, B_319, C_320)=k4_xboole_0(B_319, C_320) | ~m1_subset_1(B_319, k1_zfmisc_1(A_318)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.71/3.85  tff(c_15366, plain, (![C_320]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_320)=k4_xboole_0('#skF_2', C_320))), inference(resolution, [status(thm)], [c_36, c_15363])).
% 9.71/3.85  tff(c_42, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.71/3.85  tff(c_142, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 9.71/3.85  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.71/3.85  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.71/3.85  tff(c_2503, plain, (![B_145, A_146]: (v4_pre_topc(B_145, A_146) | k2_pre_topc(A_146, B_145)!=B_145 | ~v2_pre_topc(A_146) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.71/3.85  tff(c_2509, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_2503])).
% 9.71/3.85  tff(c_2513, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_2509])).
% 9.71/3.85  tff(c_2514, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_142, c_2513])).
% 9.71/3.85  tff(c_2743, plain, (![A_152, B_153]: (k4_subset_1(u1_struct_0(A_152), B_153, k2_tops_1(A_152, B_153))=k2_pre_topc(A_152, B_153) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.71/3.85  tff(c_2747, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_2743])).
% 9.71/3.85  tff(c_2751, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2747])).
% 9.71/3.85  tff(c_722, plain, (![A_85, B_86, C_87]: (k7_subset_1(A_85, B_86, C_87)=k4_xboole_0(B_86, C_87) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.71/3.85  tff(c_726, plain, (![C_88]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_88)=k4_xboole_0('#skF_2', C_88))), inference(resolution, [status(thm)], [c_36, c_722])).
% 9.71/3.85  tff(c_48, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.71/3.85  tff(c_301, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_142, c_48])).
% 9.71/3.85  tff(c_732, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_726, c_301])).
% 9.71/3.85  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.71/3.85  tff(c_336, plain, (![A_67, B_68, C_69]: (k4_xboole_0(k3_xboole_0(A_67, B_68), C_69)=k3_xboole_0(A_67, k4_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.71/3.85  tff(c_357, plain, (![A_70, C_71]: (k3_xboole_0(A_70, k4_xboole_0(A_70, C_71))=k4_xboole_0(A_70, C_71))), inference(superposition, [status(thm), theory('equality')], [c_2, c_336])).
% 9.71/3.85  tff(c_8, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.71/3.85  tff(c_372, plain, (![A_70, C_71]: (k2_xboole_0(A_70, k4_xboole_0(A_70, C_71))=A_70)), inference(superposition, [status(thm), theory('equality')], [c_357, c_8])).
% 9.71/3.85  tff(c_744, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_732, c_372])).
% 9.71/3.85  tff(c_30, plain, (![A_33, B_34]: (m1_subset_1(k2_tops_1(A_33, B_34), k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.71/3.85  tff(c_2279, plain, (![A_136, B_137, C_138]: (k4_subset_1(A_136, B_137, C_138)=k2_xboole_0(B_137, C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(A_136)) | ~m1_subset_1(B_137, k1_zfmisc_1(A_136)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.71/3.85  tff(c_13890, plain, (![A_275, B_276, B_277]: (k4_subset_1(u1_struct_0(A_275), B_276, k2_tops_1(A_275, B_277))=k2_xboole_0(B_276, k2_tops_1(A_275, B_277)) | ~m1_subset_1(B_276, k1_zfmisc_1(u1_struct_0(A_275))) | ~m1_subset_1(B_277, k1_zfmisc_1(u1_struct_0(A_275))) | ~l1_pre_topc(A_275))), inference(resolution, [status(thm)], [c_30, c_2279])).
% 9.71/3.85  tff(c_13894, plain, (![B_277]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_277))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_277)) | ~m1_subset_1(B_277, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_13890])).
% 9.71/3.85  tff(c_14772, plain, (![B_284]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_284))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_284)) | ~m1_subset_1(B_284, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_13894])).
% 9.71/3.85  tff(c_14779, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_14772])).
% 9.71/3.85  tff(c_14784, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2751, c_744, c_14779])).
% 9.71/3.85  tff(c_14786, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2514, c_14784])).
% 9.71/3.85  tff(c_14787, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 9.71/3.85  tff(c_15367, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_15366, c_14787])).
% 9.71/3.85  tff(c_14788, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 9.71/3.85  tff(c_15715, plain, (![A_334, B_335]: (k2_pre_topc(A_334, B_335)=B_335 | ~v4_pre_topc(B_335, A_334) | ~m1_subset_1(B_335, k1_zfmisc_1(u1_struct_0(A_334))) | ~l1_pre_topc(A_334))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.71/3.85  tff(c_15718, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_15715])).
% 9.71/3.85  tff(c_15721, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_14788, c_15718])).
% 9.71/3.85  tff(c_16915, plain, (![A_382, B_383]: (k7_subset_1(u1_struct_0(A_382), k2_pre_topc(A_382, B_383), k1_tops_1(A_382, B_383))=k2_tops_1(A_382, B_383) | ~m1_subset_1(B_383, k1_zfmisc_1(u1_struct_0(A_382))) | ~l1_pre_topc(A_382))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.71/3.85  tff(c_16924, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15721, c_16915])).
% 9.71/3.85  tff(c_16928, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_15366, c_16924])).
% 9.71/3.85  tff(c_16930, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15367, c_16928])).
% 9.71/3.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.71/3.85  
% 9.71/3.85  Inference rules
% 9.71/3.85  ----------------------
% 9.71/3.85  #Ref     : 0
% 9.71/3.85  #Sup     : 4259
% 9.71/3.85  #Fact    : 0
% 9.71/3.85  #Define  : 0
% 9.71/3.85  #Split   : 2
% 9.71/3.85  #Chain   : 0
% 9.71/3.85  #Close   : 0
% 9.71/3.85  
% 9.71/3.85  Ordering : KBO
% 9.71/3.85  
% 9.71/3.85  Simplification rules
% 9.71/3.85  ----------------------
% 9.71/3.85  #Subsume      : 129
% 9.71/3.85  #Demod        : 4337
% 9.71/3.85  #Tautology    : 1899
% 9.71/3.85  #SimpNegUnit  : 4
% 9.71/3.85  #BackRed      : 1
% 9.71/3.85  
% 9.71/3.85  #Partial instantiations: 0
% 9.71/3.85  #Strategies tried      : 1
% 9.71/3.85  
% 9.71/3.85  Timing (in seconds)
% 9.71/3.85  ----------------------
% 9.71/3.85  Preprocessing        : 0.34
% 9.71/3.85  Parsing              : 0.18
% 9.71/3.85  CNF conversion       : 0.02
% 9.71/3.85  Main loop            : 2.74
% 9.71/3.85  Inferencing          : 0.60
% 9.71/3.85  Reduction            : 1.59
% 9.71/3.85  Demodulation         : 1.41
% 9.71/3.85  BG Simplification    : 0.09
% 9.71/3.85  Subsumption          : 0.35
% 9.71/3.85  Abstraction          : 0.14
% 9.71/3.85  MUC search           : 0.00
% 9.71/3.85  Cooper               : 0.00
% 9.71/3.85  Total                : 3.12
% 9.71/3.85  Index Insertion      : 0.00
% 9.71/3.85  Index Deletion       : 0.00
% 9.71/3.85  Index Matching       : 0.00
% 9.71/3.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
