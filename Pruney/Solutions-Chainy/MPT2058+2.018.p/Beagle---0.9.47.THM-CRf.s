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
% DateTime   : Thu Dec  3 10:31:35 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :  154 (1246 expanded)
%              Number of leaves         :   43 ( 454 expanded)
%              Depth                    :   16
%              Number of atoms          :  478 (4585 expanded)
%              Number of equality atoms :   17 ( 288 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(v6_waybel_0,type,(
    v6_waybel_0: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_waybel_7,type,(
    r1_waybel_7: ( $i * $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k2_yellow19,type,(
    k2_yellow19: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_yellow19,type,(
    k3_yellow19: ( $i * $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_207,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
              & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r3_waybel_9(A,k3_yellow19(A,k2_struct_0(A),B),C)
                <=> r1_waybel_7(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow19)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_46,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_30,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_27,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & ~ v1_xboole_0(C)
        & v2_waybel_0(C,k3_yellow_1(B))
        & v13_waybel_0(C,k3_yellow_1(B))
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B)))) )
     => ( ~ v2_struct_0(k3_yellow19(A,B,C))
        & v3_orders_2(k3_yellow19(A,B,C))
        & v4_orders_2(k3_yellow19(A,B,C))
        & v6_waybel_0(k3_yellow19(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).

tff(f_137,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & ~ v1_xboole_0(C)
        & v1_subset_1(C,u1_struct_0(k3_yellow_1(B)))
        & v2_waybel_0(C,k3_yellow_1(B))
        & v13_waybel_0(C,k3_yellow_1(B))
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B)))) )
     => ( ~ v2_struct_0(k3_yellow19(A,B,C))
        & v6_waybel_0(k3_yellow19(A,B,C),A)
        & v7_waybel_0(k3_yellow19(A,B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & ~ v1_xboole_0(C)
        & v2_waybel_0(C,k3_yellow_1(B))
        & v13_waybel_0(C,k3_yellow_1(B))
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B)))) )
     => ( ~ v2_struct_0(k3_yellow19(A,B,C))
        & v6_waybel_0(k3_yellow19(A,B,C),A)
        & l1_waybel_0(k3_yellow19(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).

tff(f_180,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_subset_1(B,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
            & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
         => B = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

tff(f_161,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r3_waybel_9(A,B,C)
              <=> r1_waybel_7(A,k2_yellow19(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow19)).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_8,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_81,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_86,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_8,c_81])).

tff(c_90,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_86])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_91,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_44])).

tff(c_68,plain,
    ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3')
    | r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_151,plain,(
    r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_96,plain,(
    ! [A_38] :
      ( ~ v1_xboole_0(u1_struct_0(A_38))
      | ~ l1_struct_0(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_99,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_96])).

tff(c_100,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_99])).

tff(c_101,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_105,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_101])).

tff(c_109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_105])).

tff(c_110,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_111,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_4,plain,(
    ! [A_2] : ~ v1_subset_1(k2_subset_1(A_2),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1(k2_subset_1(A_1),k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_118,plain,(
    ! [B_40,A_41] :
      ( v1_subset_1(B_40,A_41)
      | B_40 = A_41
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_124,plain,(
    ! [A_1] :
      ( v1_subset_1(k2_subset_1(A_1),A_1)
      | k2_subset_1(A_1) = A_1 ) ),
    inference(resolution,[status(thm)],[c_2,c_118])).

tff(c_129,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_124])).

tff(c_131,plain,(
    ! [A_1] : m1_subset_1(A_1,k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_2])).

tff(c_50,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_48,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_177,plain,(
    ! [A_58,B_59,C_60] :
      ( v4_orders_2(k3_yellow19(A_58,B_59,C_60))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_59))))
      | ~ v13_waybel_0(C_60,k3_yellow_1(B_59))
      | ~ v2_waybel_0(C_60,k3_yellow_1(B_59))
      | v1_xboole_0(C_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | v1_xboole_0(B_59)
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_182,plain,(
    ! [A_58] :
      ( v4_orders_2(k3_yellow19(A_58,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_58)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_46,c_177])).

tff(c_186,plain,(
    ! [A_58] :
      ( v4_orders_2(k3_yellow19(A_58,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_58)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_182])).

tff(c_188,plain,(
    ! [A_61] :
      ( v4_orders_2(k3_yellow19(A_61,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_struct_0(A_61)
      | v2_struct_0(A_61) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_54,c_186])).

tff(c_191,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_188])).

tff(c_193,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_131,c_191])).

tff(c_194,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_193])).

tff(c_52,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_223,plain,(
    ! [A_69,B_70,C_71] :
      ( v7_waybel_0(k3_yellow19(A_69,B_70,C_71))
      | ~ m1_subset_1(C_71,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_70))))
      | ~ v13_waybel_0(C_71,k3_yellow_1(B_70))
      | ~ v2_waybel_0(C_71,k3_yellow_1(B_70))
      | ~ v1_subset_1(C_71,u1_struct_0(k3_yellow_1(B_70)))
      | v1_xboole_0(C_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | v1_xboole_0(B_70)
      | ~ l1_struct_0(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_228,plain,(
    ! [A_69] :
      ( v7_waybel_0(k3_yellow19(A_69,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_69)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_69)
      | v2_struct_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_46,c_223])).

tff(c_232,plain,(
    ! [A_69] :
      ( v7_waybel_0(k3_yellow19(A_69,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_69)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_69)
      | v2_struct_0(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_228])).

tff(c_234,plain,(
    ! [A_72] :
      ( v7_waybel_0(k3_yellow19(A_72,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_struct_0(A_72)
      | v2_struct_0(A_72) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_54,c_232])).

tff(c_237,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_234])).

tff(c_239,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_131,c_237])).

tff(c_240,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_239])).

tff(c_195,plain,(
    ! [A_62,B_63,C_64] :
      ( l1_waybel_0(k3_yellow19(A_62,B_63,C_64),A_62)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_63))))
      | ~ v13_waybel_0(C_64,k3_yellow_1(B_63))
      | ~ v2_waybel_0(C_64,k3_yellow_1(B_63))
      | v1_xboole_0(C_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | v1_xboole_0(B_63)
      | ~ l1_struct_0(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_200,plain,(
    ! [A_62] :
      ( l1_waybel_0(k3_yellow19(A_62,k2_struct_0('#skF_1'),'#skF_2'),A_62)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_62)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_62)
      | v2_struct_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_46,c_195])).

tff(c_204,plain,(
    ! [A_62] :
      ( l1_waybel_0(k3_yellow19(A_62,k2_struct_0('#skF_1'),'#skF_2'),A_62)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_62)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_62)
      | v2_struct_0(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_200])).

tff(c_206,plain,(
    ! [A_65] :
      ( l1_waybel_0(k3_yellow19(A_65,k2_struct_0('#skF_1'),'#skF_2'),A_65)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_struct_0(A_65)
      | v2_struct_0(A_65) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_54,c_204])).

tff(c_208,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_206])).

tff(c_210,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_131,c_208])).

tff(c_211,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_210])).

tff(c_251,plain,(
    ! [A_82,B_83] :
      ( k2_yellow19(A_82,k3_yellow19(A_82,k2_struct_0(A_82),B_83)) = B_83
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_82)))))
      | ~ v13_waybel_0(B_83,k3_yellow_1(k2_struct_0(A_82)))
      | ~ v2_waybel_0(B_83,k3_yellow_1(k2_struct_0(A_82)))
      | ~ v1_subset_1(B_83,u1_struct_0(k3_yellow_1(k2_struct_0(A_82))))
      | v1_xboole_0(B_83)
      | ~ l1_struct_0(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_256,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_251])).

tff(c_260,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_52,c_50,c_48,c_256])).

tff(c_261,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_260])).

tff(c_38,plain,(
    ! [A_18,B_22,C_24] :
      ( r3_waybel_9(A_18,B_22,C_24)
      | ~ r1_waybel_7(A_18,k2_yellow19(A_18,B_22),C_24)
      | ~ m1_subset_1(C_24,u1_struct_0(A_18))
      | ~ l1_waybel_0(B_22,A_18)
      | ~ v7_waybel_0(B_22)
      | ~ v4_orders_2(B_22)
      | v2_struct_0(B_22)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_265,plain,(
    ! [C_24] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_24)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_24)
      | ~ m1_subset_1(C_24,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_38])).

tff(c_272,plain,(
    ! [C_24] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_24)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_24)
      | ~ m1_subset_1(C_24,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_194,c_240,c_211,c_90,c_265])).

tff(c_273,plain,(
    ! [C_24] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_24)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_24)
      | ~ m1_subset_1(C_24,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_272])).

tff(c_278,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_30,plain,(
    ! [A_12,B_13,C_14] :
      ( ~ v2_struct_0(k3_yellow19(A_12,B_13,C_14))
      | ~ m1_subset_1(C_14,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_13))))
      | ~ v13_waybel_0(C_14,k3_yellow_1(B_13))
      | ~ v2_waybel_0(C_14,k3_yellow_1(B_13))
      | v1_xboole_0(C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_12)))
      | v1_xboole_0(B_13)
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_280,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_278,c_30])).

tff(c_283,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_131,c_90,c_50,c_48,c_46,c_280])).

tff(c_285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_110,c_54,c_283])).

tff(c_290,plain,(
    ! [C_85] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_85)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_85)
      | ~ m1_subset_1(C_85,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_62,plain,
    ( ~ r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_130,plain,(
    ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_296,plain,
    ( ~ r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_290,c_130])).

tff(c_301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_151,c_296])).

tff(c_302,plain,(
    r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_130])).

tff(c_306,plain,(
    ~ r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_307,plain,(
    r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_308,plain,(
    ! [A_1] : m1_subset_1(A_1,k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_2])).

tff(c_336,plain,(
    ! [A_95,B_96,C_97] :
      ( v4_orders_2(k3_yellow19(A_95,B_96,C_97))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_96))))
      | ~ v13_waybel_0(C_97,k3_yellow_1(B_96))
      | ~ v2_waybel_0(C_97,k3_yellow_1(B_96))
      | v1_xboole_0(C_97)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | v1_xboole_0(B_96)
      | ~ l1_struct_0(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_341,plain,(
    ! [A_95] :
      ( v4_orders_2(k3_yellow19(A_95,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_95)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_95)
      | v2_struct_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_46,c_336])).

tff(c_345,plain,(
    ! [A_95] :
      ( v4_orders_2(k3_yellow19(A_95,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_95)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_95)
      | v2_struct_0(A_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_341])).

tff(c_347,plain,(
    ! [A_98] :
      ( v4_orders_2(k3_yellow19(A_98,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_struct_0(A_98)
      | v2_struct_0(A_98) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_54,c_345])).

tff(c_350,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_347])).

tff(c_352,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_308,c_350])).

tff(c_353,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_352])).

tff(c_407,plain,(
    ! [A_114,B_115,C_116] :
      ( v7_waybel_0(k3_yellow19(A_114,B_115,C_116))
      | ~ m1_subset_1(C_116,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_115))))
      | ~ v13_waybel_0(C_116,k3_yellow_1(B_115))
      | ~ v2_waybel_0(C_116,k3_yellow_1(B_115))
      | ~ v1_subset_1(C_116,u1_struct_0(k3_yellow_1(B_115)))
      | v1_xboole_0(C_116)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | v1_xboole_0(B_115)
      | ~ l1_struct_0(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_412,plain,(
    ! [A_114] :
      ( v7_waybel_0(k3_yellow19(A_114,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_114)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_114)
      | v2_struct_0(A_114) ) ),
    inference(resolution,[status(thm)],[c_46,c_407])).

tff(c_416,plain,(
    ! [A_114] :
      ( v7_waybel_0(k3_yellow19(A_114,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_114)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_114)
      | v2_struct_0(A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_412])).

tff(c_418,plain,(
    ! [A_117] :
      ( v7_waybel_0(k3_yellow19(A_117,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_struct_0(A_117)
      | v2_struct_0(A_117) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_54,c_416])).

tff(c_421,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_418])).

tff(c_423,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_308,c_421])).

tff(c_424,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_423])).

tff(c_390,plain,(
    ! [A_110,B_111,C_112] :
      ( l1_waybel_0(k3_yellow19(A_110,B_111,C_112),A_110)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_111))))
      | ~ v13_waybel_0(C_112,k3_yellow_1(B_111))
      | ~ v2_waybel_0(C_112,k3_yellow_1(B_111))
      | v1_xboole_0(C_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | v1_xboole_0(B_111)
      | ~ l1_struct_0(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_395,plain,(
    ! [A_110] :
      ( l1_waybel_0(k3_yellow19(A_110,k2_struct_0('#skF_1'),'#skF_2'),A_110)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_110)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_110)
      | v2_struct_0(A_110) ) ),
    inference(resolution,[status(thm)],[c_46,c_390])).

tff(c_399,plain,(
    ! [A_110] :
      ( l1_waybel_0(k3_yellow19(A_110,k2_struct_0('#skF_1'),'#skF_2'),A_110)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_110)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_110)
      | v2_struct_0(A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_395])).

tff(c_401,plain,(
    ! [A_113] :
      ( l1_waybel_0(k3_yellow19(A_113,k2_struct_0('#skF_1'),'#skF_2'),A_113)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_struct_0(A_113)
      | v2_struct_0(A_113) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_54,c_399])).

tff(c_403,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_401])).

tff(c_405,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_308,c_403])).

tff(c_406,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_405])).

tff(c_426,plain,(
    ! [A_120,B_121] :
      ( k2_yellow19(A_120,k3_yellow19(A_120,k2_struct_0(A_120),B_121)) = B_121
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_120)))))
      | ~ v13_waybel_0(B_121,k3_yellow_1(k2_struct_0(A_120)))
      | ~ v2_waybel_0(B_121,k3_yellow_1(k2_struct_0(A_120)))
      | ~ v1_subset_1(B_121,u1_struct_0(k3_yellow_1(k2_struct_0(A_120))))
      | v1_xboole_0(B_121)
      | ~ l1_struct_0(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_431,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_426])).

tff(c_435,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_52,c_50,c_48,c_431])).

tff(c_436,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_435])).

tff(c_40,plain,(
    ! [A_18,B_22,C_24] :
      ( r1_waybel_7(A_18,k2_yellow19(A_18,B_22),C_24)
      | ~ r3_waybel_9(A_18,B_22,C_24)
      | ~ m1_subset_1(C_24,u1_struct_0(A_18))
      | ~ l1_waybel_0(B_22,A_18)
      | ~ v7_waybel_0(B_22)
      | ~ v4_orders_2(B_22)
      | v2_struct_0(B_22)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_440,plain,(
    ! [C_24] :
      ( r1_waybel_7('#skF_1','#skF_2',C_24)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_24)
      | ~ m1_subset_1(C_24,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_40])).

tff(c_447,plain,(
    ! [C_24] :
      ( r1_waybel_7('#skF_1','#skF_2',C_24)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_24)
      | ~ m1_subset_1(C_24,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_353,c_424,c_406,c_90,c_440])).

tff(c_448,plain,(
    ! [C_24] :
      ( r1_waybel_7('#skF_1','#skF_2',C_24)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_24)
      | ~ m1_subset_1(C_24,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_447])).

tff(c_453,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_448])).

tff(c_455,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_453,c_30])).

tff(c_458,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_308,c_90,c_50,c_48,c_46,c_455])).

tff(c_460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_110,c_54,c_458])).

tff(c_463,plain,(
    ! [C_122] :
      ( r1_waybel_7('#skF_1','#skF_2',C_122)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_122)
      | ~ m1_subset_1(C_122,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_448])).

tff(c_466,plain,
    ( r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_307,c_463])).

tff(c_469,plain,(
    r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_466])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_469])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:25:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.44  
% 3.01/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.44  %$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1
% 3.01/1.44  
% 3.01/1.44  %Foreground sorts:
% 3.01/1.44  
% 3.01/1.44  
% 3.01/1.44  %Background operators:
% 3.01/1.44  
% 3.01/1.44  
% 3.01/1.44  %Foreground operators:
% 3.01/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.01/1.44  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.01/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.44  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.01/1.44  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 3.01/1.44  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.01/1.44  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.01/1.44  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.01/1.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.01/1.44  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.01/1.44  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 3.01/1.44  tff('#skF_2', type, '#skF_2': $i).
% 3.01/1.44  tff('#skF_3', type, '#skF_3': $i).
% 3.01/1.44  tff('#skF_1', type, '#skF_1': $i).
% 3.01/1.44  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.01/1.44  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.01/1.44  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 3.01/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.01/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.01/1.44  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.01/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.44  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.01/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.44  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.01/1.44  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.01/1.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.01/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.01/1.44  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.01/1.44  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.01/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.01/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.01/1.44  
% 3.17/1.47  tff(f_207, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, k3_yellow19(A, k2_struct_0(A), B), C) <=> r1_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_yellow19)).
% 3.17/1.47  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.17/1.47  tff(f_34, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.17/1.47  tff(f_46, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.17/1.47  tff(f_30, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 3.17/1.47  tff(f_27, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.17/1.47  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 3.17/1.47  tff(f_109, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_yellow19)).
% 3.17/1.47  tff(f_137, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow19)).
% 3.17/1.47  tff(f_81, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 3.17/1.47  tff(f_180, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 3.17/1.47  tff(f_161, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> r1_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_yellow19)).
% 3.17/1.47  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.17/1.47  tff(c_8, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.17/1.47  tff(c_81, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.17/1.47  tff(c_86, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_pre_topc(A_37))), inference(resolution, [status(thm)], [c_8, c_81])).
% 3.17/1.47  tff(c_90, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_86])).
% 3.17/1.47  tff(c_44, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.17/1.47  tff(c_91, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_44])).
% 3.17/1.47  tff(c_68, plain, (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3') | r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.17/1.47  tff(c_151, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 3.17/1.47  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.17/1.47  tff(c_96, plain, (![A_38]: (~v1_xboole_0(u1_struct_0(A_38)) | ~l1_struct_0(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.17/1.47  tff(c_99, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_90, c_96])).
% 3.17/1.47  tff(c_100, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_99])).
% 3.17/1.47  tff(c_101, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_100])).
% 3.17/1.47  tff(c_105, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_101])).
% 3.17/1.47  tff(c_109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_105])).
% 3.17/1.47  tff(c_110, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_100])).
% 3.17/1.47  tff(c_54, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.17/1.47  tff(c_111, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_100])).
% 3.17/1.47  tff(c_4, plain, (![A_2]: (~v1_subset_1(k2_subset_1(A_2), A_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.17/1.47  tff(c_2, plain, (![A_1]: (m1_subset_1(k2_subset_1(A_1), k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.17/1.47  tff(c_118, plain, (![B_40, A_41]: (v1_subset_1(B_40, A_41) | B_40=A_41 | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.17/1.47  tff(c_124, plain, (![A_1]: (v1_subset_1(k2_subset_1(A_1), A_1) | k2_subset_1(A_1)=A_1)), inference(resolution, [status(thm)], [c_2, c_118])).
% 3.17/1.47  tff(c_129, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(negUnitSimplification, [status(thm)], [c_4, c_124])).
% 3.17/1.47  tff(c_131, plain, (![A_1]: (m1_subset_1(A_1, k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_2])).
% 3.17/1.47  tff(c_50, plain, (v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.17/1.47  tff(c_48, plain, (v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.17/1.47  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.17/1.47  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.17/1.47  tff(c_177, plain, (![A_58, B_59, C_60]: (v4_orders_2(k3_yellow19(A_58, B_59, C_60)) | ~m1_subset_1(C_60, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_59)))) | ~v13_waybel_0(C_60, k3_yellow_1(B_59)) | ~v2_waybel_0(C_60, k3_yellow_1(B_59)) | v1_xboole_0(C_60) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | v1_xboole_0(B_59) | ~l1_struct_0(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.17/1.47  tff(c_182, plain, (![A_58]: (v4_orders_2(k3_yellow19(A_58, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_58))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_58) | v2_struct_0(A_58))), inference(resolution, [status(thm)], [c_46, c_177])).
% 3.17/1.47  tff(c_186, plain, (![A_58]: (v4_orders_2(k3_yellow19(A_58, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_58))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_58) | v2_struct_0(A_58))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_182])).
% 3.17/1.47  tff(c_188, plain, (![A_61]: (v4_orders_2(k3_yellow19(A_61, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_struct_0(A_61) | v2_struct_0(A_61))), inference(negUnitSimplification, [status(thm)], [c_110, c_54, c_186])).
% 3.17/1.47  tff(c_191, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_90, c_188])).
% 3.17/1.47  tff(c_193, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_131, c_191])).
% 3.17/1.47  tff(c_194, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_193])).
% 3.17/1.47  tff(c_52, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.17/1.47  tff(c_223, plain, (![A_69, B_70, C_71]: (v7_waybel_0(k3_yellow19(A_69, B_70, C_71)) | ~m1_subset_1(C_71, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_70)))) | ~v13_waybel_0(C_71, k3_yellow_1(B_70)) | ~v2_waybel_0(C_71, k3_yellow_1(B_70)) | ~v1_subset_1(C_71, u1_struct_0(k3_yellow_1(B_70))) | v1_xboole_0(C_71) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | v1_xboole_0(B_70) | ~l1_struct_0(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.17/1.47  tff(c_228, plain, (![A_69]: (v7_waybel_0(k3_yellow19(A_69, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_69))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_69) | v2_struct_0(A_69))), inference(resolution, [status(thm)], [c_46, c_223])).
% 3.17/1.47  tff(c_232, plain, (![A_69]: (v7_waybel_0(k3_yellow19(A_69, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_69))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_69) | v2_struct_0(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_228])).
% 3.17/1.47  tff(c_234, plain, (![A_72]: (v7_waybel_0(k3_yellow19(A_72, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_struct_0(A_72) | v2_struct_0(A_72))), inference(negUnitSimplification, [status(thm)], [c_110, c_54, c_232])).
% 3.17/1.47  tff(c_237, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_90, c_234])).
% 3.17/1.47  tff(c_239, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_131, c_237])).
% 3.17/1.47  tff(c_240, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_239])).
% 3.17/1.47  tff(c_195, plain, (![A_62, B_63, C_64]: (l1_waybel_0(k3_yellow19(A_62, B_63, C_64), A_62) | ~m1_subset_1(C_64, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_63)))) | ~v13_waybel_0(C_64, k3_yellow_1(B_63)) | ~v2_waybel_0(C_64, k3_yellow_1(B_63)) | v1_xboole_0(C_64) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | v1_xboole_0(B_63) | ~l1_struct_0(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.17/1.47  tff(c_200, plain, (![A_62]: (l1_waybel_0(k3_yellow19(A_62, k2_struct_0('#skF_1'), '#skF_2'), A_62) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_62))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_62) | v2_struct_0(A_62))), inference(resolution, [status(thm)], [c_46, c_195])).
% 3.17/1.47  tff(c_204, plain, (![A_62]: (l1_waybel_0(k3_yellow19(A_62, k2_struct_0('#skF_1'), '#skF_2'), A_62) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_62))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_62) | v2_struct_0(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_200])).
% 3.17/1.47  tff(c_206, plain, (![A_65]: (l1_waybel_0(k3_yellow19(A_65, k2_struct_0('#skF_1'), '#skF_2'), A_65) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_struct_0(A_65) | v2_struct_0(A_65))), inference(negUnitSimplification, [status(thm)], [c_110, c_54, c_204])).
% 3.17/1.47  tff(c_208, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_90, c_206])).
% 3.17/1.47  tff(c_210, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_131, c_208])).
% 3.17/1.47  tff(c_211, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_210])).
% 3.17/1.47  tff(c_251, plain, (![A_82, B_83]: (k2_yellow19(A_82, k3_yellow19(A_82, k2_struct_0(A_82), B_83))=B_83 | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_82))))) | ~v13_waybel_0(B_83, k3_yellow_1(k2_struct_0(A_82))) | ~v2_waybel_0(B_83, k3_yellow_1(k2_struct_0(A_82))) | ~v1_subset_1(B_83, u1_struct_0(k3_yellow_1(k2_struct_0(A_82)))) | v1_xboole_0(B_83) | ~l1_struct_0(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.17/1.47  tff(c_256, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_251])).
% 3.17/1.47  tff(c_260, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_52, c_50, c_48, c_256])).
% 3.17/1.47  tff(c_261, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_260])).
% 3.17/1.47  tff(c_38, plain, (![A_18, B_22, C_24]: (r3_waybel_9(A_18, B_22, C_24) | ~r1_waybel_7(A_18, k2_yellow19(A_18, B_22), C_24) | ~m1_subset_1(C_24, u1_struct_0(A_18)) | ~l1_waybel_0(B_22, A_18) | ~v7_waybel_0(B_22) | ~v4_orders_2(B_22) | v2_struct_0(B_22) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.17/1.47  tff(c_265, plain, (![C_24]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_24) | ~r1_waybel_7('#skF_1', '#skF_2', C_24) | ~m1_subset_1(C_24, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_261, c_38])).
% 3.17/1.47  tff(c_272, plain, (![C_24]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_24) | ~r1_waybel_7('#skF_1', '#skF_2', C_24) | ~m1_subset_1(C_24, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_194, c_240, c_211, c_90, c_265])).
% 3.17/1.47  tff(c_273, plain, (![C_24]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_24) | ~r1_waybel_7('#skF_1', '#skF_2', C_24) | ~m1_subset_1(C_24, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_272])).
% 3.17/1.47  tff(c_278, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_273])).
% 3.17/1.47  tff(c_30, plain, (![A_12, B_13, C_14]: (~v2_struct_0(k3_yellow19(A_12, B_13, C_14)) | ~m1_subset_1(C_14, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_13)))) | ~v13_waybel_0(C_14, k3_yellow_1(B_13)) | ~v2_waybel_0(C_14, k3_yellow_1(B_13)) | v1_xboole_0(C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_12))) | v1_xboole_0(B_13) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.17/1.47  tff(c_280, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_278, c_30])).
% 3.17/1.47  tff(c_283, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_131, c_90, c_50, c_48, c_46, c_280])).
% 3.17/1.47  tff(c_285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_110, c_54, c_283])).
% 3.17/1.47  tff(c_290, plain, (![C_85]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_85) | ~r1_waybel_7('#skF_1', '#skF_2', C_85) | ~m1_subset_1(C_85, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_273])).
% 3.17/1.47  tff(c_62, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.17/1.47  tff(c_130, plain, (~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_62])).
% 3.17/1.47  tff(c_296, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_290, c_130])).
% 3.17/1.47  tff(c_301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_151, c_296])).
% 3.17/1.47  tff(c_302, plain, (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_68])).
% 3.17/1.47  tff(c_305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_302, c_130])).
% 3.17/1.47  tff(c_306, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 3.17/1.47  tff(c_307, plain, (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 3.17/1.47  tff(c_308, plain, (![A_1]: (m1_subset_1(A_1, k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_2])).
% 3.17/1.47  tff(c_336, plain, (![A_95, B_96, C_97]: (v4_orders_2(k3_yellow19(A_95, B_96, C_97)) | ~m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_96)))) | ~v13_waybel_0(C_97, k3_yellow_1(B_96)) | ~v2_waybel_0(C_97, k3_yellow_1(B_96)) | v1_xboole_0(C_97) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | v1_xboole_0(B_96) | ~l1_struct_0(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.17/1.47  tff(c_341, plain, (![A_95]: (v4_orders_2(k3_yellow19(A_95, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_95))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_95) | v2_struct_0(A_95))), inference(resolution, [status(thm)], [c_46, c_336])).
% 3.17/1.47  tff(c_345, plain, (![A_95]: (v4_orders_2(k3_yellow19(A_95, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_95))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_95) | v2_struct_0(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_341])).
% 3.17/1.47  tff(c_347, plain, (![A_98]: (v4_orders_2(k3_yellow19(A_98, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_struct_0(A_98) | v2_struct_0(A_98))), inference(negUnitSimplification, [status(thm)], [c_110, c_54, c_345])).
% 3.17/1.47  tff(c_350, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_90, c_347])).
% 3.17/1.47  tff(c_352, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_308, c_350])).
% 3.17/1.47  tff(c_353, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_352])).
% 3.17/1.47  tff(c_407, plain, (![A_114, B_115, C_116]: (v7_waybel_0(k3_yellow19(A_114, B_115, C_116)) | ~m1_subset_1(C_116, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_115)))) | ~v13_waybel_0(C_116, k3_yellow_1(B_115)) | ~v2_waybel_0(C_116, k3_yellow_1(B_115)) | ~v1_subset_1(C_116, u1_struct_0(k3_yellow_1(B_115))) | v1_xboole_0(C_116) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | v1_xboole_0(B_115) | ~l1_struct_0(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.17/1.47  tff(c_412, plain, (![A_114]: (v7_waybel_0(k3_yellow19(A_114, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_114))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_114) | v2_struct_0(A_114))), inference(resolution, [status(thm)], [c_46, c_407])).
% 3.17/1.47  tff(c_416, plain, (![A_114]: (v7_waybel_0(k3_yellow19(A_114, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_114))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_114) | v2_struct_0(A_114))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_412])).
% 3.17/1.47  tff(c_418, plain, (![A_117]: (v7_waybel_0(k3_yellow19(A_117, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_struct_0(A_117) | v2_struct_0(A_117))), inference(negUnitSimplification, [status(thm)], [c_110, c_54, c_416])).
% 3.17/1.47  tff(c_421, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_90, c_418])).
% 3.17/1.47  tff(c_423, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_308, c_421])).
% 3.17/1.47  tff(c_424, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_423])).
% 3.17/1.47  tff(c_390, plain, (![A_110, B_111, C_112]: (l1_waybel_0(k3_yellow19(A_110, B_111, C_112), A_110) | ~m1_subset_1(C_112, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_111)))) | ~v13_waybel_0(C_112, k3_yellow_1(B_111)) | ~v2_waybel_0(C_112, k3_yellow_1(B_111)) | v1_xboole_0(C_112) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | v1_xboole_0(B_111) | ~l1_struct_0(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.17/1.47  tff(c_395, plain, (![A_110]: (l1_waybel_0(k3_yellow19(A_110, k2_struct_0('#skF_1'), '#skF_2'), A_110) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_110))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_110) | v2_struct_0(A_110))), inference(resolution, [status(thm)], [c_46, c_390])).
% 3.17/1.47  tff(c_399, plain, (![A_110]: (l1_waybel_0(k3_yellow19(A_110, k2_struct_0('#skF_1'), '#skF_2'), A_110) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_110))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_110) | v2_struct_0(A_110))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_395])).
% 3.17/1.47  tff(c_401, plain, (![A_113]: (l1_waybel_0(k3_yellow19(A_113, k2_struct_0('#skF_1'), '#skF_2'), A_113) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_struct_0(A_113) | v2_struct_0(A_113))), inference(negUnitSimplification, [status(thm)], [c_110, c_54, c_399])).
% 3.17/1.47  tff(c_403, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_90, c_401])).
% 3.17/1.47  tff(c_405, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_308, c_403])).
% 3.17/1.47  tff(c_406, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_405])).
% 3.17/1.47  tff(c_426, plain, (![A_120, B_121]: (k2_yellow19(A_120, k3_yellow19(A_120, k2_struct_0(A_120), B_121))=B_121 | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_120))))) | ~v13_waybel_0(B_121, k3_yellow_1(k2_struct_0(A_120))) | ~v2_waybel_0(B_121, k3_yellow_1(k2_struct_0(A_120))) | ~v1_subset_1(B_121, u1_struct_0(k3_yellow_1(k2_struct_0(A_120)))) | v1_xboole_0(B_121) | ~l1_struct_0(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.17/1.47  tff(c_431, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_426])).
% 3.17/1.47  tff(c_435, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_52, c_50, c_48, c_431])).
% 3.17/1.47  tff(c_436, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_435])).
% 3.17/1.47  tff(c_40, plain, (![A_18, B_22, C_24]: (r1_waybel_7(A_18, k2_yellow19(A_18, B_22), C_24) | ~r3_waybel_9(A_18, B_22, C_24) | ~m1_subset_1(C_24, u1_struct_0(A_18)) | ~l1_waybel_0(B_22, A_18) | ~v7_waybel_0(B_22) | ~v4_orders_2(B_22) | v2_struct_0(B_22) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.17/1.47  tff(c_440, plain, (![C_24]: (r1_waybel_7('#skF_1', '#skF_2', C_24) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_24) | ~m1_subset_1(C_24, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_436, c_40])).
% 3.17/1.47  tff(c_447, plain, (![C_24]: (r1_waybel_7('#skF_1', '#skF_2', C_24) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_24) | ~m1_subset_1(C_24, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_353, c_424, c_406, c_90, c_440])).
% 3.17/1.47  tff(c_448, plain, (![C_24]: (r1_waybel_7('#skF_1', '#skF_2', C_24) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_24) | ~m1_subset_1(C_24, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_447])).
% 3.17/1.47  tff(c_453, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_448])).
% 3.17/1.47  tff(c_455, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_453, c_30])).
% 3.17/1.47  tff(c_458, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_308, c_90, c_50, c_48, c_46, c_455])).
% 3.17/1.47  tff(c_460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_110, c_54, c_458])).
% 3.17/1.47  tff(c_463, plain, (![C_122]: (r1_waybel_7('#skF_1', '#skF_2', C_122) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_122) | ~m1_subset_1(C_122, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_448])).
% 3.17/1.47  tff(c_466, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_307, c_463])).
% 3.17/1.47  tff(c_469, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_466])).
% 3.17/1.47  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_306, c_469])).
% 3.17/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.47  
% 3.17/1.47  Inference rules
% 3.17/1.47  ----------------------
% 3.17/1.47  #Ref     : 0
% 3.17/1.47  #Sup     : 66
% 3.17/1.47  #Fact    : 0
% 3.17/1.47  #Define  : 0
% 3.17/1.47  #Split   : 6
% 3.17/1.47  #Chain   : 0
% 3.17/1.47  #Close   : 0
% 3.17/1.47  
% 3.17/1.47  Ordering : KBO
% 3.17/1.47  
% 3.17/1.47  Simplification rules
% 3.17/1.47  ----------------------
% 3.17/1.47  #Subsume      : 10
% 3.17/1.47  #Demod        : 99
% 3.17/1.47  #Tautology    : 22
% 3.17/1.47  #SimpNegUnit  : 35
% 3.17/1.47  #BackRed      : 5
% 3.17/1.47  
% 3.17/1.47  #Partial instantiations: 0
% 3.17/1.47  #Strategies tried      : 1
% 3.17/1.47  
% 3.17/1.47  Timing (in seconds)
% 3.17/1.47  ----------------------
% 3.17/1.47  Preprocessing        : 0.36
% 3.17/1.47  Parsing              : 0.19
% 3.17/1.47  CNF conversion       : 0.02
% 3.17/1.47  Main loop            : 0.32
% 3.17/1.47  Inferencing          : 0.11
% 3.17/1.47  Reduction            : 0.11
% 3.17/1.47  Demodulation         : 0.08
% 3.17/1.47  BG Simplification    : 0.02
% 3.17/1.47  Subsumption          : 0.06
% 3.17/1.47  Abstraction          : 0.02
% 3.17/1.47  MUC search           : 0.00
% 3.17/1.47  Cooper               : 0.00
% 3.17/1.47  Total                : 0.74
% 3.17/1.47  Index Insertion      : 0.00
% 3.17/1.47  Index Deletion       : 0.00
% 3.17/1.47  Index Matching       : 0.00
% 3.17/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
