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
% DateTime   : Thu Dec  3 10:21:17 EST 2020

% Result     : Theorem 20.39s
% Output     : CNFRefutation 20.39s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 239 expanded)
%              Number of leaves         :   45 (  99 expanded)
%              Depth                    :   10
%              Number of atoms          :  164 ( 423 expanded)
%              Number of equality atoms :   72 ( 140 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_80,axiom,(
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

tff(f_51,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_43,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_35581,plain,(
    ! [A_386,B_387] :
      ( r1_tarski(k1_tops_1(A_386,B_387),B_387)
      | ~ m1_subset_1(B_387,k1_zfmisc_1(u1_struct_0(A_386)))
      | ~ l1_pre_topc(A_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_35594,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_35581])).

tff(c_35603,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_35594])).

tff(c_30,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(A_29,k1_zfmisc_1(B_30))
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_34927,plain,(
    ! [A_356,B_357] :
      ( k4_xboole_0(A_356,B_357) = k3_subset_1(A_356,B_357)
      | ~ m1_subset_1(B_357,k1_zfmisc_1(A_356)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34937,plain,(
    ! [B_30,A_29] :
      ( k4_xboole_0(B_30,A_29) = k3_subset_1(B_30,A_29)
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_30,c_34927])).

tff(c_35610,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_35603,c_34937])).

tff(c_34950,plain,(
    ! [A_358,B_359,C_360] :
      ( k7_subset_1(A_358,B_359,C_360) = k4_xboole_0(B_359,C_360)
      | ~ m1_subset_1(B_359,k1_zfmisc_1(A_358)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34959,plain,(
    ! [C_360] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_360) = k4_xboole_0('#skF_2',C_360) ),
    inference(resolution,[status(thm)],[c_46,c_34950])).

tff(c_52,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_123,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3512,plain,(
    ! [B_147,A_148] :
      ( v4_pre_topc(B_147,A_148)
      | k2_pre_topc(A_148,B_147) != B_147
      | ~ v2_pre_topc(A_148)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3543,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_3512])).

tff(c_3560,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_3543])).

tff(c_3561,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_3560])).

tff(c_519,plain,(
    ! [A_87,B_88,C_89] :
      ( k7_subset_1(A_87,B_88,C_89) = k4_xboole_0(B_88,C_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_532,plain,(
    ! [C_90] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_90) = k4_xboole_0('#skF_2',C_90) ),
    inference(resolution,[status(thm)],[c_46,c_519])).

tff(c_58,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_224,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_58])).

tff(c_538,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_224])).

tff(c_20,plain,(
    ! [A_20,B_21] : k6_subset_1(A_20,B_21) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_15,B_16] : m1_subset_1(k6_subset_1(A_15,B_16),k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_59,plain,(
    ! [A_15,B_16] : m1_subset_1(k4_xboole_0(A_15,B_16),k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16])).

tff(c_378,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,B_82) = k3_subset_1(A_81,B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_589,plain,(
    ! [A_93,B_94] : k4_xboole_0(A_93,k4_xboole_0(A_93,B_94)) = k3_subset_1(A_93,k4_xboole_0(A_93,B_94)) ),
    inference(resolution,[status(thm)],[c_59,c_378])).

tff(c_139,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(A_60,B_61)
      | ~ m1_subset_1(A_60,k1_zfmisc_1(B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_150,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(resolution,[status(thm)],[c_59,c_139])).

tff(c_598,plain,(
    ! [A_93,B_94] : r1_tarski(k3_subset_1(A_93,k4_xboole_0(A_93,B_94)),A_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_150])).

tff(c_3096,plain,(
    ! [A_141,B_142,C_143] :
      ( k4_subset_1(A_141,B_142,C_143) = k2_xboole_0(B_142,C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(A_141))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(A_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10333,plain,(
    ! [B_213,B_214,A_215] :
      ( k4_subset_1(B_213,B_214,A_215) = k2_xboole_0(B_214,A_215)
      | ~ m1_subset_1(B_214,k1_zfmisc_1(B_213))
      | ~ r1_tarski(A_215,B_213) ) ),
    inference(resolution,[status(thm)],[c_30,c_3096])).

tff(c_33480,plain,(
    ! [A_320,B_321,A_322] :
      ( k4_subset_1(A_320,k4_xboole_0(A_320,B_321),A_322) = k2_xboole_0(k4_xboole_0(A_320,B_321),A_322)
      | ~ r1_tarski(A_322,A_320) ) ),
    inference(resolution,[status(thm)],[c_59,c_10333])).

tff(c_12,plain,(
    ! [A_12] : k2_subset_1(A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [A_25,B_26] :
      ( k4_subset_1(A_25,B_26,k3_subset_1(A_25,B_26)) = k2_subset_1(A_25)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_634,plain,(
    ! [A_97,B_98] :
      ( k4_subset_1(A_97,B_98,k3_subset_1(A_97,B_98)) = A_97
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_97)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_24])).

tff(c_648,plain,(
    ! [A_15,B_16] : k4_subset_1(A_15,k4_xboole_0(A_15,B_16),k3_subset_1(A_15,k4_xboole_0(A_15,B_16))) = A_15 ),
    inference(resolution,[status(thm)],[c_59,c_634])).

tff(c_33503,plain,(
    ! [A_320,B_321] :
      ( k2_xboole_0(k4_xboole_0(A_320,B_321),k3_subset_1(A_320,k4_xboole_0(A_320,B_321))) = A_320
      | ~ r1_tarski(k3_subset_1(A_320,k4_xboole_0(A_320,B_321)),A_320) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33480,c_648])).

tff(c_33562,plain,(
    ! [A_320,B_321] : k2_xboole_0(k4_xboole_0(A_320,B_321),k3_subset_1(A_320,k4_xboole_0(A_320,B_321))) = A_320 ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_33503])).

tff(c_8,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_124,plain,(
    ! [A_58,B_59] : k3_tarski(k2_tarski(A_58,B_59)) = k2_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_168,plain,(
    ! [B_66,A_67] : k3_tarski(k2_tarski(B_66,A_67)) = k2_xboole_0(A_67,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_124])).

tff(c_10,plain,(
    ! [A_10,B_11] : k3_tarski(k2_tarski(A_10,B_11)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_174,plain,(
    ! [B_66,A_67] : k2_xboole_0(B_66,A_67) = k2_xboole_0(A_67,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_10])).

tff(c_33584,plain,(
    ! [A_323,B_324] : k2_xboole_0(k4_xboole_0(A_323,B_324),k3_subset_1(A_323,k4_xboole_0(A_323,B_324))) = A_323 ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_33503])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_330,plain,(
    ! [A_78,B_79,C_80] : k2_xboole_0(k2_xboole_0(A_78,B_79),C_80) = k2_xboole_0(A_78,k2_xboole_0(B_79,C_80)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_369,plain,(
    ! [A_1,C_80] : k2_xboole_0(A_1,k2_xboole_0(A_1,C_80)) = k2_xboole_0(A_1,C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_330])).

tff(c_33725,plain,(
    ! [A_323,B_324] : k2_xboole_0(k4_xboole_0(A_323,B_324),k3_subset_1(A_323,k4_xboole_0(A_323,B_324))) = k2_xboole_0(k4_xboole_0(A_323,B_324),A_323) ),
    inference(superposition,[status(thm),theory(equality)],[c_33584,c_369])).

tff(c_33824,plain,(
    ! [A_325,B_326] : k2_xboole_0(A_325,k4_xboole_0(A_325,B_326)) = A_325 ),
    inference(demodulation,[status(thm),theory(equality)],[c_33562,c_174,c_33725])).

tff(c_34073,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_538,c_33824])).

tff(c_4308,plain,(
    ! [A_155,B_156] :
      ( k4_subset_1(u1_struct_0(A_155),B_156,k2_tops_1(A_155,B_156)) = k2_pre_topc(A_155,B_156)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4330,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_4308])).

tff(c_4347,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4330])).

tff(c_36,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(k2_tops_1(A_34,B_35),k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20092,plain,(
    ! [A_278,B_279,B_280] :
      ( k4_subset_1(u1_struct_0(A_278),B_279,k2_tops_1(A_278,B_280)) = k2_xboole_0(B_279,k2_tops_1(A_278,B_280))
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ m1_subset_1(B_280,k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ l1_pre_topc(A_278) ) ),
    inference(resolution,[status(thm)],[c_36,c_3096])).

tff(c_20121,plain,(
    ! [B_280] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_280)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_280))
      | ~ m1_subset_1(B_280,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_20092])).

tff(c_22872,plain,(
    ! [B_290] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_290)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_290))
      | ~ m1_subset_1(B_290,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_20121])).

tff(c_22914,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_22872])).

tff(c_22929,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4347,c_22914])).

tff(c_34562,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34073,c_22929])).

tff(c_34564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3561,c_34562])).

tff(c_34565,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_34960,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34959,c_34565])).

tff(c_35914,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35610,c_34960])).

tff(c_34566,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_37124,plain,(
    ! [A_407,B_408] :
      ( k2_pre_topc(A_407,B_408) = B_408
      | ~ v4_pre_topc(B_408,A_407)
      | ~ m1_subset_1(B_408,k1_zfmisc_1(u1_struct_0(A_407)))
      | ~ l1_pre_topc(A_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_37152,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_37124])).

tff(c_37166,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_34566,c_37152])).

tff(c_39813,plain,(
    ! [A_434,B_435] :
      ( k7_subset_1(u1_struct_0(A_434),k2_pre_topc(A_434,B_435),k1_tops_1(A_434,B_435)) = k2_tops_1(A_434,B_435)
      | ~ m1_subset_1(B_435,k1_zfmisc_1(u1_struct_0(A_434)))
      | ~ l1_pre_topc(A_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_39822,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_37166,c_39813])).

tff(c_39826,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_35610,c_34959,c_39822])).

tff(c_39828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35914,c_39826])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:31:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.39/12.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.39/12.84  
% 20.39/12.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.39/12.85  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 20.39/12.85  
% 20.39/12.85  %Foreground sorts:
% 20.39/12.85  
% 20.39/12.85  
% 20.39/12.85  %Background operators:
% 20.39/12.85  
% 20.39/12.85  
% 20.39/12.85  %Foreground operators:
% 20.39/12.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.39/12.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 20.39/12.85  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 20.39/12.85  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 20.39/12.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 20.39/12.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.39/12.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.39/12.85  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 20.39/12.85  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 20.39/12.85  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 20.39/12.85  tff('#skF_2', type, '#skF_2': $i).
% 20.39/12.85  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 20.39/12.85  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 20.39/12.85  tff('#skF_1', type, '#skF_1': $i).
% 20.39/12.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.39/12.85  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 20.39/12.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.39/12.85  tff(k3_tarski, type, k3_tarski: $i > $i).
% 20.39/12.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.39/12.85  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 20.39/12.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 20.39/12.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.39/12.85  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 20.39/12.85  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 20.39/12.85  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 20.39/12.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.39/12.85  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 20.39/12.85  
% 20.39/12.86  tff(f_127, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 20.39/12.86  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 20.39/12.86  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 20.39/12.86  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 20.39/12.86  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 20.39/12.86  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 20.39/12.86  tff(f_51, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 20.39/12.86  tff(f_43, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 20.39/12.86  tff(f_49, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 20.39/12.86  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 20.39/12.86  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 20.39/12.86  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 20.39/12.86  tff(f_35, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 20.39/12.86  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 20.39/12.86  tff(f_31, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 20.39/12.86  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 20.39/12.86  tff(f_86, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 20.39/12.86  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 20.39/12.86  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 20.39/12.86  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 20.39/12.86  tff(c_35581, plain, (![A_386, B_387]: (r1_tarski(k1_tops_1(A_386, B_387), B_387) | ~m1_subset_1(B_387, k1_zfmisc_1(u1_struct_0(A_386))) | ~l1_pre_topc(A_386))), inference(cnfTransformation, [status(thm)], [f_108])).
% 20.39/12.86  tff(c_35594, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_35581])).
% 20.39/12.86  tff(c_35603, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_35594])).
% 20.39/12.86  tff(c_30, plain, (![A_29, B_30]: (m1_subset_1(A_29, k1_zfmisc_1(B_30)) | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_65])).
% 20.39/12.86  tff(c_34927, plain, (![A_356, B_357]: (k4_xboole_0(A_356, B_357)=k3_subset_1(A_356, B_357) | ~m1_subset_1(B_357, k1_zfmisc_1(A_356)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 20.39/12.86  tff(c_34937, plain, (![B_30, A_29]: (k4_xboole_0(B_30, A_29)=k3_subset_1(B_30, A_29) | ~r1_tarski(A_29, B_30))), inference(resolution, [status(thm)], [c_30, c_34927])).
% 20.39/12.86  tff(c_35610, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_35603, c_34937])).
% 20.39/12.86  tff(c_34950, plain, (![A_358, B_359, C_360]: (k7_subset_1(A_358, B_359, C_360)=k4_xboole_0(B_359, C_360) | ~m1_subset_1(B_359, k1_zfmisc_1(A_358)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 20.39/12.86  tff(c_34959, plain, (![C_360]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_360)=k4_xboole_0('#skF_2', C_360))), inference(resolution, [status(thm)], [c_46, c_34950])).
% 20.39/12.86  tff(c_52, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 20.39/12.86  tff(c_123, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 20.39/12.86  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 20.39/12.86  tff(c_3512, plain, (![B_147, A_148]: (v4_pre_topc(B_147, A_148) | k2_pre_topc(A_148, B_147)!=B_147 | ~v2_pre_topc(A_148) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_80])).
% 20.39/12.86  tff(c_3543, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_3512])).
% 20.39/12.86  tff(c_3560, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_3543])).
% 20.39/12.86  tff(c_3561, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_123, c_3560])).
% 20.39/12.86  tff(c_519, plain, (![A_87, B_88, C_89]: (k7_subset_1(A_87, B_88, C_89)=k4_xboole_0(B_88, C_89) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 20.39/12.86  tff(c_532, plain, (![C_90]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_90)=k4_xboole_0('#skF_2', C_90))), inference(resolution, [status(thm)], [c_46, c_519])).
% 20.39/12.86  tff(c_58, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 20.39/12.86  tff(c_224, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_123, c_58])).
% 20.39/12.86  tff(c_538, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_532, c_224])).
% 20.39/12.86  tff(c_20, plain, (![A_20, B_21]: (k6_subset_1(A_20, B_21)=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 20.39/12.86  tff(c_16, plain, (![A_15, B_16]: (m1_subset_1(k6_subset_1(A_15, B_16), k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 20.39/12.86  tff(c_59, plain, (![A_15, B_16]: (m1_subset_1(k4_xboole_0(A_15, B_16), k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16])).
% 20.39/12.86  tff(c_378, plain, (![A_81, B_82]: (k4_xboole_0(A_81, B_82)=k3_subset_1(A_81, B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 20.39/12.86  tff(c_589, plain, (![A_93, B_94]: (k4_xboole_0(A_93, k4_xboole_0(A_93, B_94))=k3_subset_1(A_93, k4_xboole_0(A_93, B_94)))), inference(resolution, [status(thm)], [c_59, c_378])).
% 20.39/12.86  tff(c_139, plain, (![A_60, B_61]: (r1_tarski(A_60, B_61) | ~m1_subset_1(A_60, k1_zfmisc_1(B_61)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 20.39/12.86  tff(c_150, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(resolution, [status(thm)], [c_59, c_139])).
% 20.39/12.86  tff(c_598, plain, (![A_93, B_94]: (r1_tarski(k3_subset_1(A_93, k4_xboole_0(A_93, B_94)), A_93))), inference(superposition, [status(thm), theory('equality')], [c_589, c_150])).
% 20.39/12.86  tff(c_3096, plain, (![A_141, B_142, C_143]: (k4_subset_1(A_141, B_142, C_143)=k2_xboole_0(B_142, C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(A_141)) | ~m1_subset_1(B_142, k1_zfmisc_1(A_141)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 20.39/12.86  tff(c_10333, plain, (![B_213, B_214, A_215]: (k4_subset_1(B_213, B_214, A_215)=k2_xboole_0(B_214, A_215) | ~m1_subset_1(B_214, k1_zfmisc_1(B_213)) | ~r1_tarski(A_215, B_213))), inference(resolution, [status(thm)], [c_30, c_3096])).
% 20.39/12.86  tff(c_33480, plain, (![A_320, B_321, A_322]: (k4_subset_1(A_320, k4_xboole_0(A_320, B_321), A_322)=k2_xboole_0(k4_xboole_0(A_320, B_321), A_322) | ~r1_tarski(A_322, A_320))), inference(resolution, [status(thm)], [c_59, c_10333])).
% 20.39/12.86  tff(c_12, plain, (![A_12]: (k2_subset_1(A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.39/12.86  tff(c_24, plain, (![A_25, B_26]: (k4_subset_1(A_25, B_26, k3_subset_1(A_25, B_26))=k2_subset_1(A_25) | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 20.39/12.86  tff(c_634, plain, (![A_97, B_98]: (k4_subset_1(A_97, B_98, k3_subset_1(A_97, B_98))=A_97 | ~m1_subset_1(B_98, k1_zfmisc_1(A_97)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_24])).
% 20.39/12.86  tff(c_648, plain, (![A_15, B_16]: (k4_subset_1(A_15, k4_xboole_0(A_15, B_16), k3_subset_1(A_15, k4_xboole_0(A_15, B_16)))=A_15)), inference(resolution, [status(thm)], [c_59, c_634])).
% 20.39/12.86  tff(c_33503, plain, (![A_320, B_321]: (k2_xboole_0(k4_xboole_0(A_320, B_321), k3_subset_1(A_320, k4_xboole_0(A_320, B_321)))=A_320 | ~r1_tarski(k3_subset_1(A_320, k4_xboole_0(A_320, B_321)), A_320))), inference(superposition, [status(thm), theory('equality')], [c_33480, c_648])).
% 20.39/12.86  tff(c_33562, plain, (![A_320, B_321]: (k2_xboole_0(k4_xboole_0(A_320, B_321), k3_subset_1(A_320, k4_xboole_0(A_320, B_321)))=A_320)), inference(demodulation, [status(thm), theory('equality')], [c_598, c_33503])).
% 20.39/12.86  tff(c_8, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 20.39/12.86  tff(c_124, plain, (![A_58, B_59]: (k3_tarski(k2_tarski(A_58, B_59))=k2_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_35])).
% 20.39/12.86  tff(c_168, plain, (![B_66, A_67]: (k3_tarski(k2_tarski(B_66, A_67))=k2_xboole_0(A_67, B_66))), inference(superposition, [status(thm), theory('equality')], [c_8, c_124])).
% 20.39/12.86  tff(c_10, plain, (![A_10, B_11]: (k3_tarski(k2_tarski(A_10, B_11))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 20.39/12.86  tff(c_174, plain, (![B_66, A_67]: (k2_xboole_0(B_66, A_67)=k2_xboole_0(A_67, B_66))), inference(superposition, [status(thm), theory('equality')], [c_168, c_10])).
% 20.39/12.86  tff(c_33584, plain, (![A_323, B_324]: (k2_xboole_0(k4_xboole_0(A_323, B_324), k3_subset_1(A_323, k4_xboole_0(A_323, B_324)))=A_323)), inference(demodulation, [status(thm), theory('equality')], [c_598, c_33503])).
% 20.39/12.86  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 20.39/12.86  tff(c_330, plain, (![A_78, B_79, C_80]: (k2_xboole_0(k2_xboole_0(A_78, B_79), C_80)=k2_xboole_0(A_78, k2_xboole_0(B_79, C_80)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.39/12.86  tff(c_369, plain, (![A_1, C_80]: (k2_xboole_0(A_1, k2_xboole_0(A_1, C_80))=k2_xboole_0(A_1, C_80))), inference(superposition, [status(thm), theory('equality')], [c_2, c_330])).
% 20.39/12.86  tff(c_33725, plain, (![A_323, B_324]: (k2_xboole_0(k4_xboole_0(A_323, B_324), k3_subset_1(A_323, k4_xboole_0(A_323, B_324)))=k2_xboole_0(k4_xboole_0(A_323, B_324), A_323))), inference(superposition, [status(thm), theory('equality')], [c_33584, c_369])).
% 20.39/12.86  tff(c_33824, plain, (![A_325, B_326]: (k2_xboole_0(A_325, k4_xboole_0(A_325, B_326))=A_325)), inference(demodulation, [status(thm), theory('equality')], [c_33562, c_174, c_33725])).
% 20.39/12.86  tff(c_34073, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_538, c_33824])).
% 20.39/12.86  tff(c_4308, plain, (![A_155, B_156]: (k4_subset_1(u1_struct_0(A_155), B_156, k2_tops_1(A_155, B_156))=k2_pre_topc(A_155, B_156) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(A_155))), inference(cnfTransformation, [status(thm)], [f_115])).
% 20.39/12.86  tff(c_4330, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_4308])).
% 20.39/12.86  tff(c_4347, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4330])).
% 20.39/12.86  tff(c_36, plain, (![A_34, B_35]: (m1_subset_1(k2_tops_1(A_34, B_35), k1_zfmisc_1(u1_struct_0(A_34))) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_86])).
% 20.39/12.86  tff(c_20092, plain, (![A_278, B_279, B_280]: (k4_subset_1(u1_struct_0(A_278), B_279, k2_tops_1(A_278, B_280))=k2_xboole_0(B_279, k2_tops_1(A_278, B_280)) | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0(A_278))) | ~m1_subset_1(B_280, k1_zfmisc_1(u1_struct_0(A_278))) | ~l1_pre_topc(A_278))), inference(resolution, [status(thm)], [c_36, c_3096])).
% 20.39/12.86  tff(c_20121, plain, (![B_280]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_280))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_280)) | ~m1_subset_1(B_280, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_20092])).
% 20.39/12.86  tff(c_22872, plain, (![B_290]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_290))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_290)) | ~m1_subset_1(B_290, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_20121])).
% 20.39/12.86  tff(c_22914, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_22872])).
% 20.39/12.86  tff(c_22929, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4347, c_22914])).
% 20.39/12.86  tff(c_34562, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34073, c_22929])).
% 20.39/12.86  tff(c_34564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3561, c_34562])).
% 20.39/12.86  tff(c_34565, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 20.39/12.86  tff(c_34960, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34959, c_34565])).
% 20.39/12.86  tff(c_35914, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_35610, c_34960])).
% 20.39/12.86  tff(c_34566, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 20.39/12.86  tff(c_37124, plain, (![A_407, B_408]: (k2_pre_topc(A_407, B_408)=B_408 | ~v4_pre_topc(B_408, A_407) | ~m1_subset_1(B_408, k1_zfmisc_1(u1_struct_0(A_407))) | ~l1_pre_topc(A_407))), inference(cnfTransformation, [status(thm)], [f_80])).
% 20.39/12.86  tff(c_37152, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_37124])).
% 20.39/12.86  tff(c_37166, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_34566, c_37152])).
% 20.39/12.86  tff(c_39813, plain, (![A_434, B_435]: (k7_subset_1(u1_struct_0(A_434), k2_pre_topc(A_434, B_435), k1_tops_1(A_434, B_435))=k2_tops_1(A_434, B_435) | ~m1_subset_1(B_435, k1_zfmisc_1(u1_struct_0(A_434))) | ~l1_pre_topc(A_434))), inference(cnfTransformation, [status(thm)], [f_101])).
% 20.39/12.86  tff(c_39822, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_37166, c_39813])).
% 20.39/12.86  tff(c_39826, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_35610, c_34959, c_39822])).
% 20.39/12.86  tff(c_39828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35914, c_39826])).
% 20.39/12.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.39/12.86  
% 20.39/12.86  Inference rules
% 20.39/12.86  ----------------------
% 20.39/12.86  #Ref     : 0
% 20.39/12.86  #Sup     : 9732
% 20.39/12.86  #Fact    : 0
% 20.39/12.86  #Define  : 0
% 20.39/12.86  #Split   : 2
% 20.39/12.86  #Chain   : 0
% 20.39/12.86  #Close   : 0
% 20.39/12.86  
% 20.39/12.86  Ordering : KBO
% 20.39/12.86  
% 20.39/12.86  Simplification rules
% 20.39/12.86  ----------------------
% 20.39/12.86  #Subsume      : 1524
% 20.39/12.86  #Demod        : 17200
% 20.39/12.86  #Tautology    : 2990
% 20.39/12.86  #SimpNegUnit  : 6
% 20.39/12.86  #BackRed      : 5
% 20.39/12.86  
% 20.39/12.86  #Partial instantiations: 0
% 20.39/12.86  #Strategies tried      : 1
% 20.39/12.86  
% 20.39/12.86  Timing (in seconds)
% 20.39/12.86  ----------------------
% 20.39/12.87  Preprocessing        : 0.34
% 20.39/12.87  Parsing              : 0.19
% 20.39/12.87  CNF conversion       : 0.02
% 20.39/12.87  Main loop            : 11.75
% 20.39/12.87  Inferencing          : 1.08
% 20.39/12.87  Reduction            : 9.29
% 20.39/12.87  Demodulation         : 8.91
% 20.39/12.87  BG Simplification    : 0.17
% 20.39/12.87  Subsumption          : 0.97
% 20.39/12.87  Abstraction          : 0.36
% 20.39/12.87  MUC search           : 0.00
% 20.39/12.87  Cooper               : 0.00
% 20.39/12.87  Total                : 12.13
% 20.39/12.87  Index Insertion      : 0.00
% 20.39/12.87  Index Deletion       : 0.00
% 20.39/12.87  Index Matching       : 0.00
% 20.39/12.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
