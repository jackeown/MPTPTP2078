%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:35 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  155 (1276 expanded)
%              Number of leaves         :   40 ( 461 expanded)
%              Depth                    :   17
%              Number of atoms          :  501 (5145 expanded)
%              Number of equality atoms :   13 ( 237 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_199,negated_conjecture,(
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

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_45,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_129,axiom,(
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

tff(f_101,axiom,(
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

tff(f_73,axiom,(
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

tff(f_172,axiom,(
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

tff(f_153,axiom,(
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

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_6,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_73,plain,(
    ! [A_31] :
      ( u1_struct_0(A_31) = k2_struct_0(A_31)
      | ~ l1_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_82,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_78])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_83,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_38])).

tff(c_56,plain,
    ( ~ r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_108,plain,(
    ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,
    ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3')
    | r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_115,plain,(
    r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_62])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_88,plain,(
    ! [A_33] :
      ( ~ v1_xboole_0(u1_struct_0(A_33))
      | ~ l1_struct_0(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_91,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_88])).

tff(c_92,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_91])).

tff(c_93,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_96,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_93])).

tff(c_100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_96])).

tff(c_101,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_102,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_109,plain,(
    ! [A_34] :
      ( m1_subset_1(k2_struct_0(A_34),k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_112,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_109])).

tff(c_114,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_112])).

tff(c_44,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_42,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_4,plain,(
    ! [A_2] :
      ( m1_subset_1(k2_struct_0(A_2),k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_46,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_238,plain,(
    ! [A_62,B_63,C_64] :
      ( v7_waybel_0(k3_yellow19(A_62,B_63,C_64))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_63))))
      | ~ v13_waybel_0(C_64,k3_yellow_1(B_63))
      | ~ v2_waybel_0(C_64,k3_yellow_1(B_63))
      | ~ v1_subset_1(C_64,u1_struct_0(k3_yellow_1(B_63)))
      | v1_xboole_0(C_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | v1_xboole_0(B_63)
      | ~ l1_struct_0(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_243,plain,(
    ! [A_62] :
      ( v7_waybel_0(k3_yellow19(A_62,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_62)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_62)
      | v2_struct_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_40,c_238])).

tff(c_247,plain,(
    ! [A_62] :
      ( v7_waybel_0(k3_yellow19(A_62,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_62)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_62)
      | v2_struct_0(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_243])).

tff(c_265,plain,(
    ! [A_65] :
      ( v7_waybel_0(k3_yellow19(A_65,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_struct_0(A_65)
      | v2_struct_0(A_65) ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_48,c_247])).

tff(c_269,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_265])).

tff(c_275,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_269])).

tff(c_276,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_275])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_123,plain,(
    ! [A_44,B_45,C_46] :
      ( v4_orders_2(k3_yellow19(A_44,B_45,C_46))
      | ~ m1_subset_1(C_46,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_45))))
      | ~ v13_waybel_0(C_46,k3_yellow_1(B_45))
      | ~ v2_waybel_0(C_46,k3_yellow_1(B_45))
      | v1_xboole_0(C_46)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | v1_xboole_0(B_45)
      | ~ l1_struct_0(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_128,plain,(
    ! [A_44] :
      ( v4_orders_2(k3_yellow19(A_44,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_44)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_44)
      | v2_struct_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_40,c_123])).

tff(c_132,plain,(
    ! [A_44] :
      ( v4_orders_2(k3_yellow19(A_44,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_44)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_44)
      | v2_struct_0(A_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_128])).

tff(c_134,plain,(
    ! [A_47] :
      ( v4_orders_2(k3_yellow19(A_47,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_struct_0(A_47)
      | v2_struct_0(A_47) ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_48,c_132])).

tff(c_138,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_134])).

tff(c_144,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_138])).

tff(c_145,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_144])).

tff(c_176,plain,(
    ! [A_52,B_53,C_54] :
      ( l1_waybel_0(k3_yellow19(A_52,B_53,C_54),A_52)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_53))))
      | ~ v13_waybel_0(C_54,k3_yellow_1(B_53))
      | ~ v2_waybel_0(C_54,k3_yellow_1(B_53))
      | v1_xboole_0(C_54)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | v1_xboole_0(B_53)
      | ~ l1_struct_0(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_181,plain,(
    ! [A_52] :
      ( l1_waybel_0(k3_yellow19(A_52,k2_struct_0('#skF_1'),'#skF_2'),A_52)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_52)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_52)
      | v2_struct_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_40,c_176])).

tff(c_185,plain,(
    ! [A_52] :
      ( l1_waybel_0(k3_yellow19(A_52,k2_struct_0('#skF_1'),'#skF_2'),A_52)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_52)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_52)
      | v2_struct_0(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_181])).

tff(c_188,plain,(
    ! [A_55] :
      ( l1_waybel_0(k3_yellow19(A_55,k2_struct_0('#skF_1'),'#skF_2'),A_55)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_struct_0(A_55)
      | v2_struct_0(A_55) ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_48,c_185])).

tff(c_191,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_188])).

tff(c_196,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_191])).

tff(c_197,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_196])).

tff(c_227,plain,(
    ! [A_60,B_61] :
      ( k2_yellow19(A_60,k3_yellow19(A_60,k2_struct_0(A_60),B_61)) = B_61
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_60)))))
      | ~ v13_waybel_0(B_61,k3_yellow_1(k2_struct_0(A_60)))
      | ~ v2_waybel_0(B_61,k3_yellow_1(k2_struct_0(A_60)))
      | ~ v1_subset_1(B_61,u1_struct_0(k3_yellow_1(k2_struct_0(A_60))))
      | v1_xboole_0(B_61)
      | ~ l1_struct_0(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_232,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_227])).

tff(c_236,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_46,c_44,c_42,c_232])).

tff(c_237,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_236])).

tff(c_34,plain,(
    ! [A_15,B_19,C_21] :
      ( r1_waybel_7(A_15,k2_yellow19(A_15,B_19),C_21)
      | ~ r3_waybel_9(A_15,B_19,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_15))
      | ~ l1_waybel_0(B_19,A_15)
      | ~ v7_waybel_0(B_19)
      | ~ v4_orders_2(B_19)
      | v2_struct_0(B_19)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_252,plain,(
    ! [C_21] :
      ( r1_waybel_7('#skF_1','#skF_2',C_21)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_34])).

tff(c_259,plain,(
    ! [C_21] :
      ( r1_waybel_7('#skF_1','#skF_2',C_21)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_21)
      | ~ m1_subset_1(C_21,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_145,c_197,c_82,c_252])).

tff(c_260,plain,(
    ! [C_21] :
      ( r1_waybel_7('#skF_1','#skF_2',C_21)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_21)
      | ~ m1_subset_1(C_21,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_259])).

tff(c_282,plain,(
    ! [C_21] :
      ( r1_waybel_7('#skF_1','#skF_2',C_21)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_21)
      | ~ m1_subset_1(C_21,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_260])).

tff(c_283,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_282])).

tff(c_24,plain,(
    ! [A_9,B_10,C_11] :
      ( ~ v2_struct_0(k3_yellow19(A_9,B_10,C_11))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_10))))
      | ~ v13_waybel_0(C_11,k3_yellow_1(B_10))
      | ~ v2_waybel_0(C_11,k3_yellow_1(B_10))
      | v1_xboole_0(C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_9)))
      | v1_xboole_0(B_10)
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_285,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_283,c_24])).

tff(c_288,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_114,c_82,c_44,c_42,c_40,c_285])).

tff(c_290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_101,c_48,c_288])).

tff(c_292,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_282])).

tff(c_32,plain,(
    ! [A_15,B_19,C_21] :
      ( r3_waybel_9(A_15,B_19,C_21)
      | ~ r1_waybel_7(A_15,k2_yellow19(A_15,B_19),C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_15))
      | ~ l1_waybel_0(B_19,A_15)
      | ~ v7_waybel_0(B_19)
      | ~ v4_orders_2(B_19)
      | v2_struct_0(B_19)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_255,plain,(
    ! [C_21] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_21)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_32])).

tff(c_262,plain,(
    ! [C_21] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_21)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_21)
      | ~ m1_subset_1(C_21,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_145,c_197,c_82,c_255])).

tff(c_263,plain,(
    ! [C_21] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_21)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_21)
      | ~ m1_subset_1(C_21,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_262])).

tff(c_295,plain,(
    ! [C_21] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_21)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_21)
      | ~ m1_subset_1(C_21,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_263])).

tff(c_297,plain,(
    ! [C_67] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_67)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_67)
      | ~ m1_subset_1(C_67,k2_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_292,c_295])).

tff(c_303,plain,
    ( ~ r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_297,c_108])).

tff(c_308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_115,c_303])).

tff(c_309,plain,(
    ~ r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_310,plain,(
    r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_311,plain,(
    ! [A_68] :
      ( m1_subset_1(k2_struct_0(A_68),k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_314,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_311])).

tff(c_316,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_314])).

tff(c_337,plain,(
    ! [A_81,B_82,C_83] :
      ( v4_orders_2(k3_yellow19(A_81,B_82,C_83))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_82))))
      | ~ v13_waybel_0(C_83,k3_yellow_1(B_82))
      | ~ v2_waybel_0(C_83,k3_yellow_1(B_82))
      | v1_xboole_0(C_83)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | v1_xboole_0(B_82)
      | ~ l1_struct_0(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_342,plain,(
    ! [A_81] :
      ( v4_orders_2(k3_yellow19(A_81,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_81)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_81)
      | v2_struct_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_40,c_337])).

tff(c_346,plain,(
    ! [A_81] :
      ( v4_orders_2(k3_yellow19(A_81,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_81)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_81)
      | v2_struct_0(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_342])).

tff(c_364,plain,(
    ! [A_85] :
      ( v4_orders_2(k3_yellow19(A_85,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_struct_0(A_85)
      | v2_struct_0(A_85) ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_48,c_346])).

tff(c_368,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_364])).

tff(c_374,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_368])).

tff(c_375,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_374])).

tff(c_430,plain,(
    ! [A_94,B_95,C_96] :
      ( v7_waybel_0(k3_yellow19(A_94,B_95,C_96))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_95))))
      | ~ v13_waybel_0(C_96,k3_yellow_1(B_95))
      | ~ v2_waybel_0(C_96,k3_yellow_1(B_95))
      | ~ v1_subset_1(C_96,u1_struct_0(k3_yellow_1(B_95)))
      | v1_xboole_0(C_96)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | v1_xboole_0(B_95)
      | ~ l1_struct_0(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_435,plain,(
    ! [A_94] :
      ( v7_waybel_0(k3_yellow19(A_94,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_94)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_94)
      | v2_struct_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_40,c_430])).

tff(c_439,plain,(
    ! [A_94] :
      ( v7_waybel_0(k3_yellow19(A_94,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_94)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_94)
      | v2_struct_0(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_435])).

tff(c_441,plain,(
    ! [A_97] :
      ( v7_waybel_0(k3_yellow19(A_97,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_struct_0(A_97)
      | v2_struct_0(A_97) ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_48,c_439])).

tff(c_445,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_441])).

tff(c_451,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_445])).

tff(c_452,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_451])).

tff(c_380,plain,(
    ! [A_86,B_87,C_88] :
      ( l1_waybel_0(k3_yellow19(A_86,B_87,C_88),A_86)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_87))))
      | ~ v13_waybel_0(C_88,k3_yellow_1(B_87))
      | ~ v2_waybel_0(C_88,k3_yellow_1(B_87))
      | v1_xboole_0(C_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | v1_xboole_0(B_87)
      | ~ l1_struct_0(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_385,plain,(
    ! [A_86] :
      ( l1_waybel_0(k3_yellow19(A_86,k2_struct_0('#skF_1'),'#skF_2'),A_86)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_86)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_86)
      | v2_struct_0(A_86) ) ),
    inference(resolution,[status(thm)],[c_40,c_380])).

tff(c_389,plain,(
    ! [A_86] :
      ( l1_waybel_0(k3_yellow19(A_86,k2_struct_0('#skF_1'),'#skF_2'),A_86)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_86)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_86)
      | v2_struct_0(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_385])).

tff(c_391,plain,(
    ! [A_89] :
      ( l1_waybel_0(k3_yellow19(A_89,k2_struct_0('#skF_1'),'#skF_2'),A_89)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_struct_0(A_89)
      | v2_struct_0(A_89) ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_48,c_389])).

tff(c_394,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_391])).

tff(c_399,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_394])).

tff(c_400,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_399])).

tff(c_457,plain,(
    ! [A_98,B_99] :
      ( k2_yellow19(A_98,k3_yellow19(A_98,k2_struct_0(A_98),B_99)) = B_99
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_98)))))
      | ~ v13_waybel_0(B_99,k3_yellow_1(k2_struct_0(A_98)))
      | ~ v2_waybel_0(B_99,k3_yellow_1(k2_struct_0(A_98)))
      | ~ v1_subset_1(B_99,u1_struct_0(k3_yellow_1(k2_struct_0(A_98))))
      | v1_xboole_0(B_99)
      | ~ l1_struct_0(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_462,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_457])).

tff(c_466,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_46,c_44,c_42,c_462])).

tff(c_467,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_466])).

tff(c_472,plain,(
    ! [C_21] :
      ( r1_waybel_7('#skF_1','#skF_2',C_21)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_34])).

tff(c_479,plain,(
    ! [C_21] :
      ( r1_waybel_7('#skF_1','#skF_2',C_21)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_21)
      | ~ m1_subset_1(C_21,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_375,c_452,c_400,c_82,c_472])).

tff(c_480,plain,(
    ! [C_21] :
      ( r1_waybel_7('#skF_1','#skF_2',C_21)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_21)
      | ~ m1_subset_1(C_21,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_479])).

tff(c_485,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_480])).

tff(c_487,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_485,c_24])).

tff(c_490,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_316,c_82,c_44,c_42,c_40,c_487])).

tff(c_492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_101,c_48,c_490])).

tff(c_501,plain,(
    ! [C_105] :
      ( r1_waybel_7('#skF_1','#skF_2',C_105)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_105)
      | ~ m1_subset_1(C_105,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_480])).

tff(c_507,plain,
    ( r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_310,c_501])).

tff(c_511,plain,(
    r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_507])).

tff(c_513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_511])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:36:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.60  
% 3.18/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.60  %$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1
% 3.18/1.60  
% 3.18/1.60  %Foreground sorts:
% 3.18/1.60  
% 3.18/1.60  
% 3.18/1.60  %Background operators:
% 3.18/1.60  
% 3.18/1.60  
% 3.18/1.60  %Foreground operators:
% 3.18/1.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.18/1.60  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.18/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.60  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.18/1.60  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 3.18/1.60  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.18/1.60  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.18/1.60  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.18/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.18/1.60  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.18/1.60  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 3.18/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.18/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.18/1.60  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.18/1.60  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.18/1.60  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 3.18/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.18/1.60  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.18/1.60  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.18/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.60  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.18/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.60  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.18/1.60  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.18/1.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.18/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.18/1.60  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.18/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.18/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.18/1.60  
% 3.18/1.63  tff(f_199, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, k3_yellow19(A, k2_struct_0(A), B), C) <=> r1_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_yellow19)).
% 3.18/1.63  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.18/1.63  tff(f_29, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.18/1.63  tff(f_45, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.18/1.63  tff(f_33, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 3.18/1.63  tff(f_129, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow19)).
% 3.18/1.63  tff(f_101, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_yellow19)).
% 3.18/1.63  tff(f_73, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 3.18/1.63  tff(f_172, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 3.18/1.63  tff(f_153, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> r1_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_yellow19)).
% 3.18/1.63  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.18/1.63  tff(c_6, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.18/1.63  tff(c_73, plain, (![A_31]: (u1_struct_0(A_31)=k2_struct_0(A_31) | ~l1_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.18/1.63  tff(c_78, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_pre_topc(A_32))), inference(resolution, [status(thm)], [c_6, c_73])).
% 3.18/1.63  tff(c_82, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_78])).
% 3.18/1.63  tff(c_38, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.18/1.63  tff(c_83, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_38])).
% 3.18/1.63  tff(c_56, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.18/1.63  tff(c_108, plain, (~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 3.18/1.63  tff(c_62, plain, (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3') | r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.18/1.63  tff(c_115, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_108, c_62])).
% 3.18/1.63  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.18/1.63  tff(c_88, plain, (![A_33]: (~v1_xboole_0(u1_struct_0(A_33)) | ~l1_struct_0(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.18/1.63  tff(c_91, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_82, c_88])).
% 3.18/1.63  tff(c_92, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_91])).
% 3.18/1.63  tff(c_93, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_92])).
% 3.18/1.63  tff(c_96, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_93])).
% 3.18/1.63  tff(c_100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_96])).
% 3.18/1.63  tff(c_101, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_92])).
% 3.18/1.63  tff(c_48, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.18/1.63  tff(c_102, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_92])).
% 3.18/1.63  tff(c_109, plain, (![A_34]: (m1_subset_1(k2_struct_0(A_34), k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.18/1.63  tff(c_112, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_82, c_109])).
% 3.18/1.63  tff(c_114, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_112])).
% 3.18/1.63  tff(c_44, plain, (v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.18/1.63  tff(c_42, plain, (v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.18/1.63  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.18/1.63  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_struct_0(A_2), k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.18/1.63  tff(c_46, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.18/1.63  tff(c_238, plain, (![A_62, B_63, C_64]: (v7_waybel_0(k3_yellow19(A_62, B_63, C_64)) | ~m1_subset_1(C_64, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_63)))) | ~v13_waybel_0(C_64, k3_yellow_1(B_63)) | ~v2_waybel_0(C_64, k3_yellow_1(B_63)) | ~v1_subset_1(C_64, u1_struct_0(k3_yellow_1(B_63))) | v1_xboole_0(C_64) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | v1_xboole_0(B_63) | ~l1_struct_0(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.18/1.63  tff(c_243, plain, (![A_62]: (v7_waybel_0(k3_yellow19(A_62, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_62))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_62) | v2_struct_0(A_62))), inference(resolution, [status(thm)], [c_40, c_238])).
% 3.18/1.63  tff(c_247, plain, (![A_62]: (v7_waybel_0(k3_yellow19(A_62, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_62))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_62) | v2_struct_0(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_243])).
% 3.18/1.63  tff(c_265, plain, (![A_65]: (v7_waybel_0(k3_yellow19(A_65, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_struct_0(A_65) | v2_struct_0(A_65))), inference(negUnitSimplification, [status(thm)], [c_101, c_48, c_247])).
% 3.18/1.63  tff(c_269, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_4, c_265])).
% 3.18/1.63  tff(c_275, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_269])).
% 3.18/1.63  tff(c_276, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_275])).
% 3.18/1.63  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.18/1.63  tff(c_123, plain, (![A_44, B_45, C_46]: (v4_orders_2(k3_yellow19(A_44, B_45, C_46)) | ~m1_subset_1(C_46, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_45)))) | ~v13_waybel_0(C_46, k3_yellow_1(B_45)) | ~v2_waybel_0(C_46, k3_yellow_1(B_45)) | v1_xboole_0(C_46) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | v1_xboole_0(B_45) | ~l1_struct_0(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.18/1.63  tff(c_128, plain, (![A_44]: (v4_orders_2(k3_yellow19(A_44, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_44))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_44) | v2_struct_0(A_44))), inference(resolution, [status(thm)], [c_40, c_123])).
% 3.18/1.63  tff(c_132, plain, (![A_44]: (v4_orders_2(k3_yellow19(A_44, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_44))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_44) | v2_struct_0(A_44))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_128])).
% 3.18/1.63  tff(c_134, plain, (![A_47]: (v4_orders_2(k3_yellow19(A_47, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_struct_0(A_47) | v2_struct_0(A_47))), inference(negUnitSimplification, [status(thm)], [c_101, c_48, c_132])).
% 3.18/1.63  tff(c_138, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_4, c_134])).
% 3.18/1.63  tff(c_144, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_138])).
% 3.18/1.63  tff(c_145, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_144])).
% 3.18/1.63  tff(c_176, plain, (![A_52, B_53, C_54]: (l1_waybel_0(k3_yellow19(A_52, B_53, C_54), A_52) | ~m1_subset_1(C_54, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_53)))) | ~v13_waybel_0(C_54, k3_yellow_1(B_53)) | ~v2_waybel_0(C_54, k3_yellow_1(B_53)) | v1_xboole_0(C_54) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | v1_xboole_0(B_53) | ~l1_struct_0(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.18/1.63  tff(c_181, plain, (![A_52]: (l1_waybel_0(k3_yellow19(A_52, k2_struct_0('#skF_1'), '#skF_2'), A_52) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_52))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_52) | v2_struct_0(A_52))), inference(resolution, [status(thm)], [c_40, c_176])).
% 3.18/1.63  tff(c_185, plain, (![A_52]: (l1_waybel_0(k3_yellow19(A_52, k2_struct_0('#skF_1'), '#skF_2'), A_52) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_52))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_52) | v2_struct_0(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_181])).
% 3.18/1.63  tff(c_188, plain, (![A_55]: (l1_waybel_0(k3_yellow19(A_55, k2_struct_0('#skF_1'), '#skF_2'), A_55) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_struct_0(A_55) | v2_struct_0(A_55))), inference(negUnitSimplification, [status(thm)], [c_101, c_48, c_185])).
% 3.18/1.63  tff(c_191, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_4, c_188])).
% 3.18/1.63  tff(c_196, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_191])).
% 3.18/1.63  tff(c_197, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_196])).
% 3.18/1.63  tff(c_227, plain, (![A_60, B_61]: (k2_yellow19(A_60, k3_yellow19(A_60, k2_struct_0(A_60), B_61))=B_61 | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_60))))) | ~v13_waybel_0(B_61, k3_yellow_1(k2_struct_0(A_60))) | ~v2_waybel_0(B_61, k3_yellow_1(k2_struct_0(A_60))) | ~v1_subset_1(B_61, u1_struct_0(k3_yellow_1(k2_struct_0(A_60)))) | v1_xboole_0(B_61) | ~l1_struct_0(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.18/1.63  tff(c_232, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_227])).
% 3.18/1.63  tff(c_236, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_46, c_44, c_42, c_232])).
% 3.18/1.63  tff(c_237, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_236])).
% 3.18/1.63  tff(c_34, plain, (![A_15, B_19, C_21]: (r1_waybel_7(A_15, k2_yellow19(A_15, B_19), C_21) | ~r3_waybel_9(A_15, B_19, C_21) | ~m1_subset_1(C_21, u1_struct_0(A_15)) | ~l1_waybel_0(B_19, A_15) | ~v7_waybel_0(B_19) | ~v4_orders_2(B_19) | v2_struct_0(B_19) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.18/1.63  tff(c_252, plain, (![C_21]: (r1_waybel_7('#skF_1', '#skF_2', C_21) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_237, c_34])).
% 3.18/1.63  tff(c_259, plain, (![C_21]: (r1_waybel_7('#skF_1', '#skF_2', C_21) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_21) | ~m1_subset_1(C_21, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_145, c_197, c_82, c_252])).
% 3.18/1.63  tff(c_260, plain, (![C_21]: (r1_waybel_7('#skF_1', '#skF_2', C_21) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_21) | ~m1_subset_1(C_21, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_54, c_259])).
% 3.18/1.63  tff(c_282, plain, (![C_21]: (r1_waybel_7('#skF_1', '#skF_2', C_21) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_21) | ~m1_subset_1(C_21, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_260])).
% 3.18/1.63  tff(c_283, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_282])).
% 3.18/1.63  tff(c_24, plain, (![A_9, B_10, C_11]: (~v2_struct_0(k3_yellow19(A_9, B_10, C_11)) | ~m1_subset_1(C_11, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_10)))) | ~v13_waybel_0(C_11, k3_yellow_1(B_10)) | ~v2_waybel_0(C_11, k3_yellow_1(B_10)) | v1_xboole_0(C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_9))) | v1_xboole_0(B_10) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.18/1.63  tff(c_285, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_283, c_24])).
% 3.18/1.63  tff(c_288, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_114, c_82, c_44, c_42, c_40, c_285])).
% 3.18/1.63  tff(c_290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_101, c_48, c_288])).
% 3.18/1.63  tff(c_292, plain, (~v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_282])).
% 3.18/1.63  tff(c_32, plain, (![A_15, B_19, C_21]: (r3_waybel_9(A_15, B_19, C_21) | ~r1_waybel_7(A_15, k2_yellow19(A_15, B_19), C_21) | ~m1_subset_1(C_21, u1_struct_0(A_15)) | ~l1_waybel_0(B_19, A_15) | ~v7_waybel_0(B_19) | ~v4_orders_2(B_19) | v2_struct_0(B_19) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.18/1.63  tff(c_255, plain, (![C_21]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_21) | ~r1_waybel_7('#skF_1', '#skF_2', C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_237, c_32])).
% 3.18/1.63  tff(c_262, plain, (![C_21]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_21) | ~r1_waybel_7('#skF_1', '#skF_2', C_21) | ~m1_subset_1(C_21, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_145, c_197, c_82, c_255])).
% 3.18/1.63  tff(c_263, plain, (![C_21]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_21) | ~r1_waybel_7('#skF_1', '#skF_2', C_21) | ~m1_subset_1(C_21, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_54, c_262])).
% 3.18/1.63  tff(c_295, plain, (![C_21]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_21) | ~r1_waybel_7('#skF_1', '#skF_2', C_21) | ~m1_subset_1(C_21, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_263])).
% 3.18/1.63  tff(c_297, plain, (![C_67]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_67) | ~r1_waybel_7('#skF_1', '#skF_2', C_67) | ~m1_subset_1(C_67, k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_292, c_295])).
% 3.18/1.63  tff(c_303, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_297, c_108])).
% 3.18/1.63  tff(c_308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_115, c_303])).
% 3.18/1.63  tff(c_309, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 3.18/1.63  tff(c_310, plain, (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 3.18/1.63  tff(c_311, plain, (![A_68]: (m1_subset_1(k2_struct_0(A_68), k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.18/1.63  tff(c_314, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_82, c_311])).
% 3.18/1.63  tff(c_316, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_314])).
% 3.18/1.63  tff(c_337, plain, (![A_81, B_82, C_83]: (v4_orders_2(k3_yellow19(A_81, B_82, C_83)) | ~m1_subset_1(C_83, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_82)))) | ~v13_waybel_0(C_83, k3_yellow_1(B_82)) | ~v2_waybel_0(C_83, k3_yellow_1(B_82)) | v1_xboole_0(C_83) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | v1_xboole_0(B_82) | ~l1_struct_0(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.18/1.63  tff(c_342, plain, (![A_81]: (v4_orders_2(k3_yellow19(A_81, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_81))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_81) | v2_struct_0(A_81))), inference(resolution, [status(thm)], [c_40, c_337])).
% 3.18/1.63  tff(c_346, plain, (![A_81]: (v4_orders_2(k3_yellow19(A_81, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_81))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_81) | v2_struct_0(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_342])).
% 3.18/1.63  tff(c_364, plain, (![A_85]: (v4_orders_2(k3_yellow19(A_85, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_struct_0(A_85) | v2_struct_0(A_85))), inference(negUnitSimplification, [status(thm)], [c_101, c_48, c_346])).
% 3.18/1.63  tff(c_368, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_4, c_364])).
% 3.18/1.63  tff(c_374, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_368])).
% 3.18/1.63  tff(c_375, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_374])).
% 3.18/1.63  tff(c_430, plain, (![A_94, B_95, C_96]: (v7_waybel_0(k3_yellow19(A_94, B_95, C_96)) | ~m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_95)))) | ~v13_waybel_0(C_96, k3_yellow_1(B_95)) | ~v2_waybel_0(C_96, k3_yellow_1(B_95)) | ~v1_subset_1(C_96, u1_struct_0(k3_yellow_1(B_95))) | v1_xboole_0(C_96) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | v1_xboole_0(B_95) | ~l1_struct_0(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.18/1.63  tff(c_435, plain, (![A_94]: (v7_waybel_0(k3_yellow19(A_94, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_94))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_94) | v2_struct_0(A_94))), inference(resolution, [status(thm)], [c_40, c_430])).
% 3.18/1.63  tff(c_439, plain, (![A_94]: (v7_waybel_0(k3_yellow19(A_94, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_94))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_94) | v2_struct_0(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_435])).
% 3.18/1.63  tff(c_441, plain, (![A_97]: (v7_waybel_0(k3_yellow19(A_97, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_struct_0(A_97) | v2_struct_0(A_97))), inference(negUnitSimplification, [status(thm)], [c_101, c_48, c_439])).
% 3.18/1.63  tff(c_445, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_4, c_441])).
% 3.18/1.63  tff(c_451, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_445])).
% 3.18/1.63  tff(c_452, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_451])).
% 3.18/1.63  tff(c_380, plain, (![A_86, B_87, C_88]: (l1_waybel_0(k3_yellow19(A_86, B_87, C_88), A_86) | ~m1_subset_1(C_88, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_87)))) | ~v13_waybel_0(C_88, k3_yellow_1(B_87)) | ~v2_waybel_0(C_88, k3_yellow_1(B_87)) | v1_xboole_0(C_88) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | v1_xboole_0(B_87) | ~l1_struct_0(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.18/1.63  tff(c_385, plain, (![A_86]: (l1_waybel_0(k3_yellow19(A_86, k2_struct_0('#skF_1'), '#skF_2'), A_86) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_86))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_86) | v2_struct_0(A_86))), inference(resolution, [status(thm)], [c_40, c_380])).
% 3.18/1.63  tff(c_389, plain, (![A_86]: (l1_waybel_0(k3_yellow19(A_86, k2_struct_0('#skF_1'), '#skF_2'), A_86) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_86))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_86) | v2_struct_0(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_385])).
% 3.18/1.63  tff(c_391, plain, (![A_89]: (l1_waybel_0(k3_yellow19(A_89, k2_struct_0('#skF_1'), '#skF_2'), A_89) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_struct_0(A_89) | v2_struct_0(A_89))), inference(negUnitSimplification, [status(thm)], [c_101, c_48, c_389])).
% 3.18/1.63  tff(c_394, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_4, c_391])).
% 3.18/1.63  tff(c_399, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_394])).
% 3.18/1.63  tff(c_400, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_399])).
% 3.18/1.63  tff(c_457, plain, (![A_98, B_99]: (k2_yellow19(A_98, k3_yellow19(A_98, k2_struct_0(A_98), B_99))=B_99 | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_98))))) | ~v13_waybel_0(B_99, k3_yellow_1(k2_struct_0(A_98))) | ~v2_waybel_0(B_99, k3_yellow_1(k2_struct_0(A_98))) | ~v1_subset_1(B_99, u1_struct_0(k3_yellow_1(k2_struct_0(A_98)))) | v1_xboole_0(B_99) | ~l1_struct_0(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.18/1.63  tff(c_462, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_457])).
% 3.18/1.63  tff(c_466, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_46, c_44, c_42, c_462])).
% 3.18/1.63  tff(c_467, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_466])).
% 3.18/1.63  tff(c_472, plain, (![C_21]: (r1_waybel_7('#skF_1', '#skF_2', C_21) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_21) | ~m1_subset_1(C_21, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_467, c_34])).
% 3.18/1.63  tff(c_479, plain, (![C_21]: (r1_waybel_7('#skF_1', '#skF_2', C_21) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_21) | ~m1_subset_1(C_21, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_375, c_452, c_400, c_82, c_472])).
% 3.18/1.63  tff(c_480, plain, (![C_21]: (r1_waybel_7('#skF_1', '#skF_2', C_21) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_21) | ~m1_subset_1(C_21, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_54, c_479])).
% 3.18/1.63  tff(c_485, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_480])).
% 3.18/1.63  tff(c_487, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_485, c_24])).
% 3.18/1.63  tff(c_490, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_316, c_82, c_44, c_42, c_40, c_487])).
% 3.18/1.63  tff(c_492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_101, c_48, c_490])).
% 3.18/1.63  tff(c_501, plain, (![C_105]: (r1_waybel_7('#skF_1', '#skF_2', C_105) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_105) | ~m1_subset_1(C_105, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_480])).
% 3.18/1.63  tff(c_507, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_310, c_501])).
% 3.18/1.63  tff(c_511, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_507])).
% 3.18/1.63  tff(c_513, plain, $false, inference(negUnitSimplification, [status(thm)], [c_309, c_511])).
% 3.18/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.63  
% 3.18/1.63  Inference rules
% 3.18/1.63  ----------------------
% 3.18/1.63  #Ref     : 0
% 3.18/1.63  #Sup     : 71
% 3.18/1.63  #Fact    : 0
% 3.18/1.63  #Define  : 0
% 3.18/1.63  #Split   : 5
% 3.18/1.63  #Chain   : 0
% 3.18/1.63  #Close   : 0
% 3.18/1.63  
% 3.18/1.63  Ordering : KBO
% 3.18/1.63  
% 3.18/1.63  Simplification rules
% 3.18/1.63  ----------------------
% 3.18/1.63  #Subsume      : 5
% 3.18/1.63  #Demod        : 115
% 3.18/1.63  #Tautology    : 26
% 3.18/1.63  #SimpNegUnit  : 44
% 3.18/1.63  #BackRed      : 1
% 3.18/1.63  
% 3.18/1.63  #Partial instantiations: 0
% 3.18/1.63  #Strategies tried      : 1
% 3.18/1.63  
% 3.18/1.63  Timing (in seconds)
% 3.18/1.63  ----------------------
% 3.18/1.64  Preprocessing        : 0.39
% 3.18/1.64  Parsing              : 0.21
% 3.18/1.64  CNF conversion       : 0.03
% 3.18/1.64  Main loop            : 0.36
% 3.18/1.64  Inferencing          : 0.13
% 3.18/1.64  Reduction            : 0.11
% 3.18/1.64  Demodulation         : 0.08
% 3.18/1.64  BG Simplification    : 0.02
% 3.18/1.64  Subsumption          : 0.07
% 3.18/1.64  Abstraction          : 0.02
% 3.18/1.64  MUC search           : 0.00
% 3.18/1.64  Cooper               : 0.00
% 3.18/1.64  Total                : 0.81
% 3.18/1.64  Index Insertion      : 0.00
% 3.18/1.64  Index Deletion       : 0.00
% 3.18/1.64  Index Matching       : 0.00
% 3.18/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
