%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:35 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  159 (1620 expanded)
%              Number of leaves         :   42 ( 584 expanded)
%              Depth                    :   17
%              Number of atoms          :  505 (6097 expanded)
%              Number of equality atoms :   17 ( 378 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_208,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow19)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_47,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_31,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_110,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_yellow19)).

tff(f_138,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow19)).

tff(f_82,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow19)).

tff(f_181,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

tff(f_162,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow19)).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_8,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_81,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_86,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_8,c_81])).

tff(c_90,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_86])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_91,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_44])).

tff(c_68,plain,
    ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_4')
    | r1_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_151,plain,(
    r1_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_96,plain,(
    ! [A_38] :
      ( ~ v1_xboole_0(u1_struct_0(A_38))
      | ~ l1_struct_0(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_99,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_96])).

tff(c_100,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_99])).

tff(c_101,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_105,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_101])).

tff(c_109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_105])).

tff(c_110,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_111,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_2,plain,(
    ! [A_1] : ~ v1_subset_1('#skF_1'(A_1),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1('#skF_1'(A_1),k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,(
    ! [B_40,A_41] :
      ( v1_subset_1(B_40,A_41)
      | B_40 = A_41
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_124,plain,(
    ! [A_1] :
      ( v1_subset_1('#skF_1'(A_1),A_1)
      | '#skF_1'(A_1) = A_1 ) ),
    inference(resolution,[status(thm)],[c_4,c_118])).

tff(c_129,plain,(
    ! [A_1] : '#skF_1'(A_1) = A_1 ),
    inference(negUnitSimplification,[status(thm)],[c_2,c_124])).

tff(c_131,plain,(
    ! [A_1] : m1_subset_1(A_1,k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_4])).

tff(c_50,plain,(
    v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_48,plain,(
    v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

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
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_182,plain,(
    ! [A_58] :
      ( v4_orders_2(k3_yellow19(A_58,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_58)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_46,c_177])).

tff(c_186,plain,(
    ! [A_58] :
      ( v4_orders_2(k3_yellow19(A_58,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_58)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_182])).

tff(c_188,plain,(
    ! [A_61] :
      ( v4_orders_2(k3_yellow19(A_61,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_struct_0(A_61)
      | v2_struct_0(A_61) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_54,c_186])).

tff(c_191,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_188])).

tff(c_193,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_131,c_191])).

tff(c_194,plain,(
    v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_193])).

tff(c_52,plain,(
    v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

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
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_228,plain,(
    ! [A_69] :
      ( v7_waybel_0(k3_yellow19(A_69,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_69)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_69)
      | v2_struct_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_46,c_223])).

tff(c_232,plain,(
    ! [A_69] :
      ( v7_waybel_0(k3_yellow19(A_69,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_69)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_69)
      | v2_struct_0(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_228])).

tff(c_234,plain,(
    ! [A_72] :
      ( v7_waybel_0(k3_yellow19(A_72,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_struct_0(A_72)
      | v2_struct_0(A_72) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_54,c_232])).

tff(c_237,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_234])).

tff(c_239,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_131,c_237])).

tff(c_240,plain,(
    v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_239])).

tff(c_212,plain,(
    ! [A_66,B_67,C_68] :
      ( l1_waybel_0(k3_yellow19(A_66,B_67,C_68),A_66)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_67))))
      | ~ v13_waybel_0(C_68,k3_yellow_1(B_67))
      | ~ v2_waybel_0(C_68,k3_yellow_1(B_67))
      | v1_xboole_0(C_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | v1_xboole_0(B_67)
      | ~ l1_struct_0(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_217,plain,(
    ! [A_66] :
      ( l1_waybel_0(k3_yellow19(A_66,k2_struct_0('#skF_2'),'#skF_3'),A_66)
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_66)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_66)
      | v2_struct_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_46,c_212])).

tff(c_221,plain,(
    ! [A_66] :
      ( l1_waybel_0(k3_yellow19(A_66,k2_struct_0('#skF_2'),'#skF_3'),A_66)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_66)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_66)
      | v2_struct_0(A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_217])).

tff(c_241,plain,(
    ! [A_73] :
      ( l1_waybel_0(k3_yellow19(A_73,k2_struct_0('#skF_2'),'#skF_3'),A_73)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_struct_0(A_73)
      | v2_struct_0(A_73) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_54,c_221])).

tff(c_243,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_241])).

tff(c_245,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_131,c_243])).

tff(c_246,plain,(
    l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_245])).

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
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_256,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
    | v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_251])).

tff(c_260,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_52,c_50,c_48,c_256])).

tff(c_261,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_260])).

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
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_265,plain,(
    ! [C_24] :
      ( r1_waybel_7('#skF_2','#skF_3',C_24)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_24)
      | ~ m1_subset_1(C_24,u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_40])).

tff(c_272,plain,(
    ! [C_24] :
      ( r1_waybel_7('#skF_2','#skF_3',C_24)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_24)
      | ~ m1_subset_1(C_24,k2_struct_0('#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_194,c_240,c_246,c_90,c_265])).

tff(c_273,plain,(
    ! [C_24] :
      ( r1_waybel_7('#skF_2','#skF_3',C_24)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_24)
      | ~ m1_subset_1(C_24,k2_struct_0('#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_272])).

tff(c_278,plain,(
    v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
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
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_280,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_278,c_30])).

tff(c_283,plain,
    ( v1_xboole_0('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_131,c_90,c_50,c_48,c_46,c_280])).

tff(c_285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_110,c_54,c_283])).

tff(c_287,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_273])).

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
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_268,plain,(
    ! [C_24] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_24)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_24)
      | ~ m1_subset_1(C_24,u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_38])).

tff(c_275,plain,(
    ! [C_24] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_24)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_24)
      | ~ m1_subset_1(C_24,k2_struct_0('#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_194,c_240,c_246,c_90,c_268])).

tff(c_276,plain,(
    ! [C_24] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_24)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_24)
      | ~ m1_subset_1(C_24,k2_struct_0('#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_275])).

tff(c_289,plain,(
    ! [C_84] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_84)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_84)
      | ~ m1_subset_1(C_84,k2_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_276])).

tff(c_62,plain,
    ( ~ r1_waybel_7('#skF_2','#skF_3','#skF_4')
    | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_130,plain,(
    ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_292,plain,
    ( ~ r1_waybel_7('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_289,c_130])).

tff(c_296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_151,c_292])).

tff(c_297,plain,(
    r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_130])).

tff(c_301,plain,(
    ~ r1_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_302,plain,(
    r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_303,plain,(
    ! [A_1] : m1_subset_1(A_1,k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_4])).

tff(c_331,plain,(
    ! [A_94,B_95,C_96] :
      ( v4_orders_2(k3_yellow19(A_94,B_95,C_96))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_95))))
      | ~ v13_waybel_0(C_96,k3_yellow_1(B_95))
      | ~ v2_waybel_0(C_96,k3_yellow_1(B_95))
      | v1_xboole_0(C_96)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | v1_xboole_0(B_95)
      | ~ l1_struct_0(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_336,plain,(
    ! [A_94] :
      ( v4_orders_2(k3_yellow19(A_94,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_94)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_94)
      | v2_struct_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_46,c_331])).

tff(c_340,plain,(
    ! [A_94] :
      ( v4_orders_2(k3_yellow19(A_94,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_94)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_94)
      | v2_struct_0(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_336])).

tff(c_342,plain,(
    ! [A_97] :
      ( v4_orders_2(k3_yellow19(A_97,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_struct_0(A_97)
      | v2_struct_0(A_97) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_54,c_340])).

tff(c_345,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_342])).

tff(c_347,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_303,c_345])).

tff(c_348,plain,(
    v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_347])).

tff(c_385,plain,(
    ! [A_109,B_110,C_111] :
      ( l1_waybel_0(k3_yellow19(A_109,B_110,C_111),A_109)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_110))))
      | ~ v13_waybel_0(C_111,k3_yellow_1(B_110))
      | ~ v2_waybel_0(C_111,k3_yellow_1(B_110))
      | v1_xboole_0(C_111)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | v1_xboole_0(B_110)
      | ~ l1_struct_0(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_390,plain,(
    ! [A_109] :
      ( l1_waybel_0(k3_yellow19(A_109,k2_struct_0('#skF_2'),'#skF_3'),A_109)
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_109)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_109)
      | v2_struct_0(A_109) ) ),
    inference(resolution,[status(thm)],[c_46,c_385])).

tff(c_394,plain,(
    ! [A_109] :
      ( l1_waybel_0(k3_yellow19(A_109,k2_struct_0('#skF_2'),'#skF_3'),A_109)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_109)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_109)
      | v2_struct_0(A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_390])).

tff(c_396,plain,(
    ! [A_112] :
      ( l1_waybel_0(k3_yellow19(A_112,k2_struct_0('#skF_2'),'#skF_3'),A_112)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_struct_0(A_112)
      | v2_struct_0(A_112) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_54,c_394])).

tff(c_398,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_396])).

tff(c_400,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_303,c_398])).

tff(c_401,plain,(
    l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_400])).

tff(c_403,plain,(
    ! [A_115,B_116] :
      ( k2_yellow19(A_115,k3_yellow19(A_115,k2_struct_0(A_115),B_116)) = B_116
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_115)))))
      | ~ v13_waybel_0(B_116,k3_yellow_1(k2_struct_0(A_115)))
      | ~ v2_waybel_0(B_116,k3_yellow_1(k2_struct_0(A_115)))
      | ~ v1_subset_1(B_116,u1_struct_0(k3_yellow_1(k2_struct_0(A_115))))
      | v1_xboole_0(B_116)
      | ~ l1_struct_0(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_408,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
    | v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_403])).

tff(c_412,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_52,c_50,c_48,c_408])).

tff(c_413,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_412])).

tff(c_417,plain,(
    ! [C_24] :
      ( r1_waybel_7('#skF_2','#skF_3',C_24)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_24)
      | ~ m1_subset_1(C_24,u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_40])).

tff(c_424,plain,(
    ! [C_24] :
      ( r1_waybel_7('#skF_2','#skF_3',C_24)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_24)
      | ~ m1_subset_1(C_24,k2_struct_0('#skF_2'))
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_348,c_401,c_90,c_417])).

tff(c_425,plain,(
    ! [C_24] :
      ( r1_waybel_7('#skF_2','#skF_3',C_24)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_24)
      | ~ m1_subset_1(C_24,k2_struct_0('#skF_2'))
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_424])).

tff(c_430,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_425])).

tff(c_434,plain,(
    ! [A_123,B_124,C_125] :
      ( v7_waybel_0(k3_yellow19(A_123,B_124,C_125))
      | ~ m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_124))))
      | ~ v13_waybel_0(C_125,k3_yellow_1(B_124))
      | ~ v2_waybel_0(C_125,k3_yellow_1(B_124))
      | ~ v1_subset_1(C_125,u1_struct_0(k3_yellow_1(B_124)))
      | v1_xboole_0(C_125)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | v1_xboole_0(B_124)
      | ~ l1_struct_0(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_439,plain,(
    ! [A_123] :
      ( v7_waybel_0(k3_yellow19(A_123,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_123)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_123)
      | v2_struct_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_46,c_434])).

tff(c_443,plain,(
    ! [A_123] :
      ( v7_waybel_0(k3_yellow19(A_123,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_123)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_123)
      | v2_struct_0(A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_439])).

tff(c_445,plain,(
    ! [A_126] :
      ( v7_waybel_0(k3_yellow19(A_126,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_struct_0(A_126)
      | v2_struct_0(A_126) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_54,c_443])).

tff(c_448,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_445])).

tff(c_450,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_303,c_448])).

tff(c_452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_430,c_450])).

tff(c_453,plain,(
    ! [C_24] :
      ( v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | r1_waybel_7('#skF_2','#skF_3',C_24)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_24)
      | ~ m1_subset_1(C_24,k2_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_425])).

tff(c_473,plain,(
    v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_453])).

tff(c_478,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_473,c_30])).

tff(c_481,plain,
    ( v1_xboole_0('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_303,c_90,c_50,c_48,c_46,c_478])).

tff(c_483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_110,c_54,c_481])).

tff(c_486,plain,(
    ! [C_131] :
      ( r1_waybel_7('#skF_2','#skF_3',C_131)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_131)
      | ~ m1_subset_1(C_131,k2_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_453])).

tff(c_489,plain,
    ( r1_waybel_7('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_302,c_486])).

tff(c_492,plain,(
    r1_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_489])).

tff(c_494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_301,c_492])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:21:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.46  
% 2.93/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.46  %$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.93/1.46  
% 2.93/1.46  %Foreground sorts:
% 2.93/1.46  
% 2.93/1.46  
% 2.93/1.46  %Background operators:
% 2.93/1.46  
% 2.93/1.46  
% 2.93/1.46  %Foreground operators:
% 2.93/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.93/1.46  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.93/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.46  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.93/1.46  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 2.93/1.46  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.93/1.46  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.93/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.93/1.46  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.93/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.93/1.46  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.93/1.46  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 2.93/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.93/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.93/1.46  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.93/1.46  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.93/1.46  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 2.93/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.93/1.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.93/1.46  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.93/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.46  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.93/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.93/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.46  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.93/1.46  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.93/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.93/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.93/1.46  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.93/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.93/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.93/1.46  
% 3.53/1.49  tff(f_208, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, k3_yellow19(A, k2_struct_0(A), B), C) <=> r1_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_yellow19)).
% 3.53/1.49  tff(f_39, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.53/1.49  tff(f_35, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.53/1.49  tff(f_47, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.53/1.49  tff(f_31, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 3.53/1.49  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 3.53/1.49  tff(f_110, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_yellow19)).
% 3.53/1.49  tff(f_138, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow19)).
% 3.53/1.49  tff(f_82, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 3.53/1.49  tff(f_181, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 3.53/1.49  tff(f_162, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> r1_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_yellow19)).
% 3.53/1.49  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.53/1.49  tff(c_8, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.53/1.49  tff(c_81, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.53/1.49  tff(c_86, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_pre_topc(A_37))), inference(resolution, [status(thm)], [c_8, c_81])).
% 3.53/1.49  tff(c_90, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_86])).
% 3.53/1.49  tff(c_44, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.53/1.49  tff(c_91, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_44])).
% 3.53/1.49  tff(c_68, plain, (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_4') | r1_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.53/1.49  tff(c_151, plain, (r1_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_68])).
% 3.53/1.49  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.53/1.49  tff(c_96, plain, (![A_38]: (~v1_xboole_0(u1_struct_0(A_38)) | ~l1_struct_0(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.53/1.49  tff(c_99, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_96])).
% 3.53/1.49  tff(c_100, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_99])).
% 3.53/1.49  tff(c_101, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_100])).
% 3.53/1.49  tff(c_105, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_101])).
% 3.53/1.49  tff(c_109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_105])).
% 3.53/1.49  tff(c_110, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_100])).
% 3.53/1.49  tff(c_54, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.53/1.49  tff(c_111, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_100])).
% 3.53/1.49  tff(c_2, plain, (![A_1]: (~v1_subset_1('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.49  tff(c_4, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.49  tff(c_118, plain, (![B_40, A_41]: (v1_subset_1(B_40, A_41) | B_40=A_41 | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.53/1.49  tff(c_124, plain, (![A_1]: (v1_subset_1('#skF_1'(A_1), A_1) | '#skF_1'(A_1)=A_1)), inference(resolution, [status(thm)], [c_4, c_118])).
% 3.53/1.49  tff(c_129, plain, (![A_1]: ('#skF_1'(A_1)=A_1)), inference(negUnitSimplification, [status(thm)], [c_2, c_124])).
% 3.53/1.49  tff(c_131, plain, (![A_1]: (m1_subset_1(A_1, k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_4])).
% 3.53/1.49  tff(c_50, plain, (v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.53/1.49  tff(c_48, plain, (v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.53/1.49  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.53/1.49  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.53/1.49  tff(c_177, plain, (![A_58, B_59, C_60]: (v4_orders_2(k3_yellow19(A_58, B_59, C_60)) | ~m1_subset_1(C_60, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_59)))) | ~v13_waybel_0(C_60, k3_yellow_1(B_59)) | ~v2_waybel_0(C_60, k3_yellow_1(B_59)) | v1_xboole_0(C_60) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | v1_xboole_0(B_59) | ~l1_struct_0(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.53/1.49  tff(c_182, plain, (![A_58]: (v4_orders_2(k3_yellow19(A_58, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_58))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_58) | v2_struct_0(A_58))), inference(resolution, [status(thm)], [c_46, c_177])).
% 3.53/1.49  tff(c_186, plain, (![A_58]: (v4_orders_2(k3_yellow19(A_58, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_58))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_58) | v2_struct_0(A_58))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_182])).
% 3.53/1.49  tff(c_188, plain, (![A_61]: (v4_orders_2(k3_yellow19(A_61, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_struct_0(A_61) | v2_struct_0(A_61))), inference(negUnitSimplification, [status(thm)], [c_110, c_54, c_186])).
% 3.53/1.49  tff(c_191, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_188])).
% 3.53/1.49  tff(c_193, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_131, c_191])).
% 3.53/1.49  tff(c_194, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_193])).
% 3.53/1.49  tff(c_52, plain, (v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.53/1.49  tff(c_223, plain, (![A_69, B_70, C_71]: (v7_waybel_0(k3_yellow19(A_69, B_70, C_71)) | ~m1_subset_1(C_71, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_70)))) | ~v13_waybel_0(C_71, k3_yellow_1(B_70)) | ~v2_waybel_0(C_71, k3_yellow_1(B_70)) | ~v1_subset_1(C_71, u1_struct_0(k3_yellow_1(B_70))) | v1_xboole_0(C_71) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | v1_xboole_0(B_70) | ~l1_struct_0(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.53/1.49  tff(c_228, plain, (![A_69]: (v7_waybel_0(k3_yellow19(A_69, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_69))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_69) | v2_struct_0(A_69))), inference(resolution, [status(thm)], [c_46, c_223])).
% 3.53/1.49  tff(c_232, plain, (![A_69]: (v7_waybel_0(k3_yellow19(A_69, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_69))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_69) | v2_struct_0(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_228])).
% 3.53/1.49  tff(c_234, plain, (![A_72]: (v7_waybel_0(k3_yellow19(A_72, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_struct_0(A_72) | v2_struct_0(A_72))), inference(negUnitSimplification, [status(thm)], [c_110, c_54, c_232])).
% 3.53/1.49  tff(c_237, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_234])).
% 3.53/1.49  tff(c_239, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_131, c_237])).
% 3.53/1.49  tff(c_240, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_239])).
% 3.53/1.49  tff(c_212, plain, (![A_66, B_67, C_68]: (l1_waybel_0(k3_yellow19(A_66, B_67, C_68), A_66) | ~m1_subset_1(C_68, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_67)))) | ~v13_waybel_0(C_68, k3_yellow_1(B_67)) | ~v2_waybel_0(C_68, k3_yellow_1(B_67)) | v1_xboole_0(C_68) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | v1_xboole_0(B_67) | ~l1_struct_0(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.53/1.49  tff(c_217, plain, (![A_66]: (l1_waybel_0(k3_yellow19(A_66, k2_struct_0('#skF_2'), '#skF_3'), A_66) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_66))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_66) | v2_struct_0(A_66))), inference(resolution, [status(thm)], [c_46, c_212])).
% 3.53/1.49  tff(c_221, plain, (![A_66]: (l1_waybel_0(k3_yellow19(A_66, k2_struct_0('#skF_2'), '#skF_3'), A_66) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_66))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_66) | v2_struct_0(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_217])).
% 3.53/1.49  tff(c_241, plain, (![A_73]: (l1_waybel_0(k3_yellow19(A_73, k2_struct_0('#skF_2'), '#skF_3'), A_73) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_struct_0(A_73) | v2_struct_0(A_73))), inference(negUnitSimplification, [status(thm)], [c_110, c_54, c_221])).
% 3.53/1.49  tff(c_243, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_241])).
% 3.53/1.49  tff(c_245, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_131, c_243])).
% 3.53/1.49  tff(c_246, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_245])).
% 3.53/1.49  tff(c_251, plain, (![A_82, B_83]: (k2_yellow19(A_82, k3_yellow19(A_82, k2_struct_0(A_82), B_83))=B_83 | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_82))))) | ~v13_waybel_0(B_83, k3_yellow_1(k2_struct_0(A_82))) | ~v2_waybel_0(B_83, k3_yellow_1(k2_struct_0(A_82))) | ~v1_subset_1(B_83, u1_struct_0(k3_yellow_1(k2_struct_0(A_82)))) | v1_xboole_0(B_83) | ~l1_struct_0(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.53/1.49  tff(c_256, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_251])).
% 3.53/1.49  tff(c_260, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_52, c_50, c_48, c_256])).
% 3.53/1.49  tff(c_261, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_260])).
% 3.53/1.49  tff(c_40, plain, (![A_18, B_22, C_24]: (r1_waybel_7(A_18, k2_yellow19(A_18, B_22), C_24) | ~r3_waybel_9(A_18, B_22, C_24) | ~m1_subset_1(C_24, u1_struct_0(A_18)) | ~l1_waybel_0(B_22, A_18) | ~v7_waybel_0(B_22) | ~v4_orders_2(B_22) | v2_struct_0(B_22) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.53/1.49  tff(c_265, plain, (![C_24]: (r1_waybel_7('#skF_2', '#skF_3', C_24) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_24) | ~m1_subset_1(C_24, u1_struct_0('#skF_2')) | ~l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_261, c_40])).
% 3.53/1.49  tff(c_272, plain, (![C_24]: (r1_waybel_7('#skF_2', '#skF_3', C_24) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_24) | ~m1_subset_1(C_24, k2_struct_0('#skF_2')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_194, c_240, c_246, c_90, c_265])).
% 3.53/1.49  tff(c_273, plain, (![C_24]: (r1_waybel_7('#skF_2', '#skF_3', C_24) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_24) | ~m1_subset_1(C_24, k2_struct_0('#skF_2')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_272])).
% 3.53/1.49  tff(c_278, plain, (v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_273])).
% 3.53/1.49  tff(c_30, plain, (![A_12, B_13, C_14]: (~v2_struct_0(k3_yellow19(A_12, B_13, C_14)) | ~m1_subset_1(C_14, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_13)))) | ~v13_waybel_0(C_14, k3_yellow_1(B_13)) | ~v2_waybel_0(C_14, k3_yellow_1(B_13)) | v1_xboole_0(C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_12))) | v1_xboole_0(B_13) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.53/1.49  tff(c_280, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_278, c_30])).
% 3.53/1.49  tff(c_283, plain, (v1_xboole_0('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_131, c_90, c_50, c_48, c_46, c_280])).
% 3.53/1.49  tff(c_285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_110, c_54, c_283])).
% 3.53/1.49  tff(c_287, plain, (~v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitRight, [status(thm)], [c_273])).
% 3.53/1.49  tff(c_38, plain, (![A_18, B_22, C_24]: (r3_waybel_9(A_18, B_22, C_24) | ~r1_waybel_7(A_18, k2_yellow19(A_18, B_22), C_24) | ~m1_subset_1(C_24, u1_struct_0(A_18)) | ~l1_waybel_0(B_22, A_18) | ~v7_waybel_0(B_22) | ~v4_orders_2(B_22) | v2_struct_0(B_22) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.53/1.49  tff(c_268, plain, (![C_24]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_24) | ~r1_waybel_7('#skF_2', '#skF_3', C_24) | ~m1_subset_1(C_24, u1_struct_0('#skF_2')) | ~l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_261, c_38])).
% 3.53/1.49  tff(c_275, plain, (![C_24]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_24) | ~r1_waybel_7('#skF_2', '#skF_3', C_24) | ~m1_subset_1(C_24, k2_struct_0('#skF_2')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_194, c_240, c_246, c_90, c_268])).
% 3.53/1.49  tff(c_276, plain, (![C_24]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_24) | ~r1_waybel_7('#skF_2', '#skF_3', C_24) | ~m1_subset_1(C_24, k2_struct_0('#skF_2')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_275])).
% 3.53/1.49  tff(c_289, plain, (![C_84]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_84) | ~r1_waybel_7('#skF_2', '#skF_3', C_84) | ~m1_subset_1(C_84, k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_287, c_276])).
% 3.53/1.49  tff(c_62, plain, (~r1_waybel_7('#skF_2', '#skF_3', '#skF_4') | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.53/1.49  tff(c_130, plain, (~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_62])).
% 3.53/1.49  tff(c_292, plain, (~r1_waybel_7('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_289, c_130])).
% 3.53/1.49  tff(c_296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_151, c_292])).
% 3.53/1.49  tff(c_297, plain, (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_68])).
% 3.53/1.49  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_297, c_130])).
% 3.53/1.49  tff(c_301, plain, (~r1_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_62])).
% 3.53/1.49  tff(c_302, plain, (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_62])).
% 3.53/1.49  tff(c_303, plain, (![A_1]: (m1_subset_1(A_1, k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_4])).
% 3.53/1.49  tff(c_331, plain, (![A_94, B_95, C_96]: (v4_orders_2(k3_yellow19(A_94, B_95, C_96)) | ~m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_95)))) | ~v13_waybel_0(C_96, k3_yellow_1(B_95)) | ~v2_waybel_0(C_96, k3_yellow_1(B_95)) | v1_xboole_0(C_96) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | v1_xboole_0(B_95) | ~l1_struct_0(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.53/1.49  tff(c_336, plain, (![A_94]: (v4_orders_2(k3_yellow19(A_94, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_94))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_94) | v2_struct_0(A_94))), inference(resolution, [status(thm)], [c_46, c_331])).
% 3.53/1.49  tff(c_340, plain, (![A_94]: (v4_orders_2(k3_yellow19(A_94, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_94))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_94) | v2_struct_0(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_336])).
% 3.53/1.49  tff(c_342, plain, (![A_97]: (v4_orders_2(k3_yellow19(A_97, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_struct_0(A_97) | v2_struct_0(A_97))), inference(negUnitSimplification, [status(thm)], [c_110, c_54, c_340])).
% 3.53/1.49  tff(c_345, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_342])).
% 3.53/1.49  tff(c_347, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_303, c_345])).
% 3.53/1.49  tff(c_348, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_347])).
% 3.53/1.49  tff(c_385, plain, (![A_109, B_110, C_111]: (l1_waybel_0(k3_yellow19(A_109, B_110, C_111), A_109) | ~m1_subset_1(C_111, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_110)))) | ~v13_waybel_0(C_111, k3_yellow_1(B_110)) | ~v2_waybel_0(C_111, k3_yellow_1(B_110)) | v1_xboole_0(C_111) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | v1_xboole_0(B_110) | ~l1_struct_0(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.53/1.49  tff(c_390, plain, (![A_109]: (l1_waybel_0(k3_yellow19(A_109, k2_struct_0('#skF_2'), '#skF_3'), A_109) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_109))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_109) | v2_struct_0(A_109))), inference(resolution, [status(thm)], [c_46, c_385])).
% 3.53/1.49  tff(c_394, plain, (![A_109]: (l1_waybel_0(k3_yellow19(A_109, k2_struct_0('#skF_2'), '#skF_3'), A_109) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_109))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_109) | v2_struct_0(A_109))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_390])).
% 3.53/1.49  tff(c_396, plain, (![A_112]: (l1_waybel_0(k3_yellow19(A_112, k2_struct_0('#skF_2'), '#skF_3'), A_112) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_struct_0(A_112) | v2_struct_0(A_112))), inference(negUnitSimplification, [status(thm)], [c_110, c_54, c_394])).
% 3.53/1.49  tff(c_398, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_396])).
% 3.53/1.49  tff(c_400, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_303, c_398])).
% 3.53/1.49  tff(c_401, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_400])).
% 3.53/1.49  tff(c_403, plain, (![A_115, B_116]: (k2_yellow19(A_115, k3_yellow19(A_115, k2_struct_0(A_115), B_116))=B_116 | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_115))))) | ~v13_waybel_0(B_116, k3_yellow_1(k2_struct_0(A_115))) | ~v2_waybel_0(B_116, k3_yellow_1(k2_struct_0(A_115))) | ~v1_subset_1(B_116, u1_struct_0(k3_yellow_1(k2_struct_0(A_115)))) | v1_xboole_0(B_116) | ~l1_struct_0(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.53/1.49  tff(c_408, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_403])).
% 3.53/1.49  tff(c_412, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_52, c_50, c_48, c_408])).
% 3.53/1.49  tff(c_413, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_412])).
% 3.53/1.49  tff(c_417, plain, (![C_24]: (r1_waybel_7('#skF_2', '#skF_3', C_24) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_24) | ~m1_subset_1(C_24, u1_struct_0('#skF_2')) | ~l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_413, c_40])).
% 3.53/1.49  tff(c_424, plain, (![C_24]: (r1_waybel_7('#skF_2', '#skF_3', C_24) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_24) | ~m1_subset_1(C_24, k2_struct_0('#skF_2')) | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_348, c_401, c_90, c_417])).
% 3.53/1.49  tff(c_425, plain, (![C_24]: (r1_waybel_7('#skF_2', '#skF_3', C_24) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_24) | ~m1_subset_1(C_24, k2_struct_0('#skF_2')) | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_424])).
% 3.53/1.49  tff(c_430, plain, (~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_425])).
% 3.53/1.49  tff(c_434, plain, (![A_123, B_124, C_125]: (v7_waybel_0(k3_yellow19(A_123, B_124, C_125)) | ~m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_124)))) | ~v13_waybel_0(C_125, k3_yellow_1(B_124)) | ~v2_waybel_0(C_125, k3_yellow_1(B_124)) | ~v1_subset_1(C_125, u1_struct_0(k3_yellow_1(B_124))) | v1_xboole_0(C_125) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | v1_xboole_0(B_124) | ~l1_struct_0(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.53/1.49  tff(c_439, plain, (![A_123]: (v7_waybel_0(k3_yellow19(A_123, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_123))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_123) | v2_struct_0(A_123))), inference(resolution, [status(thm)], [c_46, c_434])).
% 3.53/1.49  tff(c_443, plain, (![A_123]: (v7_waybel_0(k3_yellow19(A_123, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_123))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_123) | v2_struct_0(A_123))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_439])).
% 3.53/1.49  tff(c_445, plain, (![A_126]: (v7_waybel_0(k3_yellow19(A_126, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_struct_0(A_126) | v2_struct_0(A_126))), inference(negUnitSimplification, [status(thm)], [c_110, c_54, c_443])).
% 3.53/1.49  tff(c_448, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_445])).
% 3.53/1.49  tff(c_450, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_303, c_448])).
% 3.53/1.49  tff(c_452, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_430, c_450])).
% 3.53/1.49  tff(c_453, plain, (![C_24]: (v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | r1_waybel_7('#skF_2', '#skF_3', C_24) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_24) | ~m1_subset_1(C_24, k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_425])).
% 3.53/1.49  tff(c_473, plain, (v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_453])).
% 3.53/1.49  tff(c_478, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_473, c_30])).
% 3.53/1.49  tff(c_481, plain, (v1_xboole_0('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_303, c_90, c_50, c_48, c_46, c_478])).
% 3.53/1.49  tff(c_483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_110, c_54, c_481])).
% 3.53/1.49  tff(c_486, plain, (![C_131]: (r1_waybel_7('#skF_2', '#skF_3', C_131) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_131) | ~m1_subset_1(C_131, k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_453])).
% 3.53/1.49  tff(c_489, plain, (r1_waybel_7('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_302, c_486])).
% 3.53/1.49  tff(c_492, plain, (r1_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_489])).
% 3.53/1.49  tff(c_494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_301, c_492])).
% 3.53/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.49  
% 3.53/1.49  Inference rules
% 3.53/1.49  ----------------------
% 3.53/1.49  #Ref     : 0
% 3.53/1.49  #Sup     : 68
% 3.53/1.49  #Fact    : 0
% 3.53/1.49  #Define  : 0
% 3.53/1.49  #Split   : 8
% 3.53/1.49  #Chain   : 0
% 3.53/1.49  #Close   : 0
% 3.53/1.49  
% 3.53/1.49  Ordering : KBO
% 3.53/1.49  
% 3.53/1.49  Simplification rules
% 3.53/1.49  ----------------------
% 3.53/1.49  #Subsume      : 12
% 3.53/1.49  #Demod        : 104
% 3.53/1.49  #Tautology    : 22
% 3.53/1.49  #SimpNegUnit  : 37
% 3.53/1.49  #BackRed      : 5
% 3.53/1.49  
% 3.53/1.49  #Partial instantiations: 0
% 3.53/1.49  #Strategies tried      : 1
% 3.53/1.49  
% 3.53/1.49  Timing (in seconds)
% 3.53/1.49  ----------------------
% 3.53/1.50  Preprocessing        : 0.39
% 3.53/1.50  Parsing              : 0.20
% 3.53/1.50  CNF conversion       : 0.03
% 3.53/1.50  Main loop            : 0.36
% 3.53/1.50  Inferencing          : 0.13
% 3.53/1.50  Reduction            : 0.12
% 3.53/1.50  Demodulation         : 0.08
% 3.53/1.50  BG Simplification    : 0.02
% 3.53/1.50  Subsumption          : 0.06
% 3.53/1.50  Abstraction          : 0.02
% 3.53/1.50  MUC search           : 0.00
% 3.53/1.50  Cooper               : 0.00
% 3.53/1.50  Total                : 0.81
% 3.53/1.50  Index Insertion      : 0.00
% 3.53/1.50  Index Deletion       : 0.00
% 3.53/1.50  Index Matching       : 0.00
% 3.53/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
