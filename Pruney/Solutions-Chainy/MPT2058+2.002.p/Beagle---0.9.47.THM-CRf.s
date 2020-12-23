%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:32 EST 2020

% Result     : Theorem 4.43s
% Output     : CNFRefutation 4.98s
% Verified   : 
% Statistics : Number of formulae       :  190 (3022 expanded)
%              Number of leaves         :   45 (1081 expanded)
%              Depth                    :   24
%              Number of atoms          :  594 (12458 expanded)
%              Number of equality atoms :   15 ( 558 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v4_pre_topc > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_213,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_115,axiom,(
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

tff(f_87,axiom,(
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

tff(f_186,axiom,(
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

tff(f_167,axiom,(
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

tff(f_143,axiom,(
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

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_10,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_92,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_97,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_10,c_92])).

tff(c_101,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_97])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_102,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_46])).

tff(c_64,plain,
    ( ~ r1_waybel_7('#skF_2','#skF_3','#skF_4')
    | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_118,plain,(
    ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,
    ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_4')
    | r1_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_136,plain,(
    r1_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_70])).

tff(c_121,plain,(
    ! [A_44] :
      ( m1_subset_1('#skF_1'(A_44),k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_127,plain,
    ( m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_121])).

tff(c_130,plain,
    ( m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_127])).

tff(c_131,plain,(
    m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_130])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( v1_xboole_0(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_135,plain,
    ( v1_xboole_0('#skF_1'('#skF_2'))
    | ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_131,c_6])).

tff(c_137,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_52,plain,(
    v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_50,plain,(
    v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_151,plain,(
    ! [A_52,B_53,C_54] :
      ( v4_orders_2(k3_yellow19(A_52,B_53,C_54))
      | ~ m1_subset_1(C_54,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_53))))
      | ~ v13_waybel_0(C_54,k3_yellow_1(B_53))
      | ~ v2_waybel_0(C_54,k3_yellow_1(B_53))
      | v1_xboole_0(C_54)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | v1_xboole_0(B_53)
      | ~ l1_struct_0(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_156,plain,(
    ! [A_52] :
      ( v4_orders_2(k3_yellow19(A_52,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_52)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_52)
      | v2_struct_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_48,c_151])).

tff(c_163,plain,(
    ! [A_52] :
      ( v4_orders_2(k3_yellow19(A_52,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_52)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_52)
      | v2_struct_0(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_156])).

tff(c_166,plain,(
    ! [A_55] :
      ( v4_orders_2(k3_yellow19(A_55,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_struct_0(A_55)
      | v2_struct_0(A_55) ) ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_56,c_163])).

tff(c_169,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_166])).

tff(c_171,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_169])).

tff(c_172,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_171])).

tff(c_173,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_176,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_173])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_176])).

tff(c_182,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_181,plain,(
    v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_211,plain,(
    ! [A_63,B_64,C_65] :
      ( l1_waybel_0(k3_yellow19(A_63,B_64,C_65),A_63)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_64))))
      | ~ v13_waybel_0(C_65,k3_yellow_1(B_64))
      | ~ v2_waybel_0(C_65,k3_yellow_1(B_64))
      | v1_xboole_0(C_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | v1_xboole_0(B_64)
      | ~ l1_struct_0(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_216,plain,(
    ! [A_63] :
      ( l1_waybel_0(k3_yellow19(A_63,k2_struct_0('#skF_2'),'#skF_3'),A_63)
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_63)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_63)
      | v2_struct_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_48,c_211])).

tff(c_223,plain,(
    ! [A_63] :
      ( l1_waybel_0(k3_yellow19(A_63,k2_struct_0('#skF_2'),'#skF_3'),A_63)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_63)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_63)
      | v2_struct_0(A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_216])).

tff(c_226,plain,(
    ! [A_66] :
      ( l1_waybel_0(k3_yellow19(A_66,k2_struct_0('#skF_2'),'#skF_3'),A_66)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_struct_0(A_66)
      | v2_struct_0(A_66) ) ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_56,c_223])).

tff(c_228,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_226])).

tff(c_230,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_71,c_228])).

tff(c_231,plain,(
    l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_230])).

tff(c_54,plain,(
    v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_247,plain,(
    ! [A_70,B_71] :
      ( k2_yellow19(A_70,k3_yellow19(A_70,k2_struct_0(A_70),B_71)) = B_71
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_70)))))
      | ~ v13_waybel_0(B_71,k3_yellow_1(k2_struct_0(A_70)))
      | ~ v2_waybel_0(B_71,k3_yellow_1(k2_struct_0(A_70)))
      | ~ v1_subset_1(B_71,u1_struct_0(k3_yellow_1(k2_struct_0(A_70))))
      | v1_xboole_0(B_71)
      | ~ l1_struct_0(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_252,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
    | v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_247])).

tff(c_259,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_54,c_52,c_50,c_252])).

tff(c_260,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_259])).

tff(c_40,plain,(
    ! [A_20,B_24,C_26] :
      ( r3_waybel_9(A_20,B_24,C_26)
      | ~ r1_waybel_7(A_20,k2_yellow19(A_20,B_24),C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_20))
      | ~ l1_waybel_0(B_24,A_20)
      | ~ v7_waybel_0(B_24)
      | ~ v4_orders_2(B_24)
      | v2_struct_0(B_24)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_265,plain,(
    ! [C_26] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_26)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_26)
      | ~ m1_subset_1(C_26,u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_40])).

tff(c_272,plain,(
    ! [C_26] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_26)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_26)
      | ~ m1_subset_1(C_26,k2_struct_0('#skF_2'))
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_181,c_231,c_101,c_265])).

tff(c_273,plain,(
    ! [C_26] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_26)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_26)
      | ~ m1_subset_1(C_26,k2_struct_0('#skF_2'))
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_272])).

tff(c_284,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_288,plain,(
    ! [A_79,B_80,C_81] :
      ( v7_waybel_0(k3_yellow19(A_79,B_80,C_81))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_80))))
      | ~ v13_waybel_0(C_81,k3_yellow_1(B_80))
      | ~ v2_waybel_0(C_81,k3_yellow_1(B_80))
      | ~ v1_subset_1(C_81,u1_struct_0(k3_yellow_1(B_80)))
      | v1_xboole_0(C_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | v1_xboole_0(B_80)
      | ~ l1_struct_0(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_293,plain,(
    ! [A_79] :
      ( v7_waybel_0(k3_yellow19(A_79,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_79)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_79)
      | v2_struct_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_48,c_288])).

tff(c_300,plain,(
    ! [A_79] :
      ( v7_waybel_0(k3_yellow19(A_79,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_79)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_79)
      | v2_struct_0(A_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_293])).

tff(c_303,plain,(
    ! [A_82] :
      ( v7_waybel_0(k3_yellow19(A_82,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_struct_0(A_82)
      | v2_struct_0(A_82) ) ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_56,c_300])).

tff(c_306,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_303])).

tff(c_308,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_71,c_306])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_284,c_308])).

tff(c_311,plain,(
    ! [C_26] :
      ( v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_26)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_26)
      | ~ m1_subset_1(C_26,k2_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_313,plain,(
    v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_311])).

tff(c_32,plain,(
    ! [A_14,B_15,C_16] :
      ( ~ v2_struct_0(k3_yellow19(A_14,B_15,C_16))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_15))))
      | ~ v13_waybel_0(C_16,k3_yellow_1(B_15))
      | ~ v2_waybel_0(C_16,k3_yellow_1(B_15))
      | v1_xboole_0(C_16)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | v1_xboole_0(B_15)
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_318,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_313,c_32])).

tff(c_321,plain,
    ( v1_xboole_0('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_71,c_101,c_52,c_50,c_48,c_318])).

tff(c_323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_137,c_56,c_321])).

tff(c_326,plain,(
    ! [C_83] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_83)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_83)
      | ~ m1_subset_1(C_83,k2_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_311])).

tff(c_329,plain,
    ( ~ r1_waybel_7('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_326,c_118])).

tff(c_333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_136,c_329])).

tff(c_334,plain,(
    v1_xboole_0('#skF_1'('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_14,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0('#skF_1'(A_8))
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_338,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_334,c_14])).

tff(c_341,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_338])).

tff(c_343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_341])).

tff(c_344,plain,(
    ~ r1_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_345,plain,(
    r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_348,plain,(
    ! [A_86] :
      ( m1_subset_1('#skF_1'(A_86),k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_354,plain,
    ( m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_348])).

tff(c_357,plain,
    ( m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_354])).

tff(c_358,plain,(
    m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_357])).

tff(c_364,plain,
    ( v1_xboole_0('#skF_1'('#skF_2'))
    | ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_358,c_6])).

tff(c_365,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_364])).

tff(c_379,plain,(
    ! [A_94,B_95,C_96] :
      ( v3_orders_2(k3_yellow19(A_94,B_95,C_96))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_95))))
      | ~ v13_waybel_0(C_96,k3_yellow_1(B_95))
      | ~ v2_waybel_0(C_96,k3_yellow_1(B_95))
      | v1_xboole_0(C_96)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | v1_xboole_0(B_95)
      | ~ l1_struct_0(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_384,plain,(
    ! [A_94] :
      ( v3_orders_2(k3_yellow19(A_94,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_94)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_94)
      | v2_struct_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_48,c_379])).

tff(c_391,plain,(
    ! [A_94] :
      ( v3_orders_2(k3_yellow19(A_94,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_94)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_94)
      | v2_struct_0(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_384])).

tff(c_394,plain,(
    ! [A_97] :
      ( v3_orders_2(k3_yellow19(A_97,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_struct_0(A_97)
      | v2_struct_0(A_97) ) ),
    inference(negUnitSimplification,[status(thm)],[c_365,c_56,c_391])).

tff(c_397,plain,
    ( v3_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_394])).

tff(c_399,plain,
    ( v3_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_397])).

tff(c_400,plain,
    ( v3_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_399])).

tff(c_401,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_400])).

tff(c_404,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_401])).

tff(c_408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_404])).

tff(c_410,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_400])).

tff(c_416,plain,(
    ! [A_98,B_99,C_100] :
      ( v4_orders_2(k3_yellow19(A_98,B_99,C_100))
      | ~ m1_subset_1(C_100,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_99))))
      | ~ v13_waybel_0(C_100,k3_yellow_1(B_99))
      | ~ v2_waybel_0(C_100,k3_yellow_1(B_99))
      | v1_xboole_0(C_100)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | v1_xboole_0(B_99)
      | ~ l1_struct_0(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_421,plain,(
    ! [A_98] :
      ( v4_orders_2(k3_yellow19(A_98,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_98)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_98)
      | v2_struct_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_48,c_416])).

tff(c_428,plain,(
    ! [A_98] :
      ( v4_orders_2(k3_yellow19(A_98,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_98)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_98)
      | v2_struct_0(A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_421])).

tff(c_431,plain,(
    ! [A_101] :
      ( v4_orders_2(k3_yellow19(A_101,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_struct_0(A_101)
      | v2_struct_0(A_101) ) ),
    inference(negUnitSimplification,[status(thm)],[c_365,c_56,c_428])).

tff(c_434,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_431])).

tff(c_436,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_71,c_434])).

tff(c_437,plain,(
    v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_436])).

tff(c_460,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_465,plain,(
    ! [A_109] :
      ( l1_waybel_0(k3_yellow19(A_109,k2_struct_0('#skF_2'),'#skF_3'),A_109)
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_109)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_109)
      | v2_struct_0(A_109) ) ),
    inference(resolution,[status(thm)],[c_48,c_460])).

tff(c_472,plain,(
    ! [A_109] :
      ( l1_waybel_0(k3_yellow19(A_109,k2_struct_0('#skF_2'),'#skF_3'),A_109)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_109)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_109)
      | v2_struct_0(A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_465])).

tff(c_475,plain,(
    ! [A_112] :
      ( l1_waybel_0(k3_yellow19(A_112,k2_struct_0('#skF_2'),'#skF_3'),A_112)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_struct_0(A_112)
      | v2_struct_0(A_112) ) ),
    inference(negUnitSimplification,[status(thm)],[c_365,c_56,c_472])).

tff(c_477,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_475])).

tff(c_479,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_71,c_477])).

tff(c_480,plain,(
    l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_479])).

tff(c_484,plain,(
    ! [A_119,B_120] :
      ( k2_yellow19(A_119,k3_yellow19(A_119,k2_struct_0(A_119),B_120)) = B_120
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_119)))))
      | ~ v13_waybel_0(B_120,k3_yellow_1(k2_struct_0(A_119)))
      | ~ v2_waybel_0(B_120,k3_yellow_1(k2_struct_0(A_119)))
      | ~ v1_subset_1(B_120,u1_struct_0(k3_yellow_1(k2_struct_0(A_119))))
      | v1_xboole_0(B_120)
      | ~ l1_struct_0(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_489,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
    | v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_484])).

tff(c_496,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_54,c_52,c_50,c_489])).

tff(c_497,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_496])).

tff(c_502,plain,(
    ! [C_26] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_26)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_26)
      | ~ m1_subset_1(C_26,u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_40])).

tff(c_509,plain,(
    ! [C_26] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_26)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_26)
      | ~ m1_subset_1(C_26,k2_struct_0('#skF_2'))
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_437,c_480,c_101,c_502])).

tff(c_510,plain,(
    ! [C_26] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_26)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_26)
      | ~ m1_subset_1(C_26,k2_struct_0('#skF_2'))
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_509])).

tff(c_515,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_510])).

tff(c_517,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_522,plain,(
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
    inference(resolution,[status(thm)],[c_48,c_517])).

tff(c_529,plain,(
    ! [A_123] :
      ( v7_waybel_0(k3_yellow19(A_123,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_123)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_123)
      | v2_struct_0(A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_522])).

tff(c_532,plain,(
    ! [A_126] :
      ( v7_waybel_0(k3_yellow19(A_126,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_struct_0(A_126)
      | v2_struct_0(A_126) ) ),
    inference(negUnitSimplification,[status(thm)],[c_365,c_56,c_529])).

tff(c_535,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_532])).

tff(c_537,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_71,c_535])).

tff(c_539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_515,c_537])).

tff(c_540,plain,(
    ! [C_26] :
      ( v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_26)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_26)
      | ~ m1_subset_1(C_26,k2_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_510])).

tff(c_542,plain,(
    v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_540])).

tff(c_559,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_542,c_32])).

tff(c_562,plain,
    ( v1_xboole_0('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_71,c_101,c_52,c_50,c_48,c_559])).

tff(c_564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_365,c_56,c_562])).

tff(c_566,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_540])).

tff(c_541,plain,(
    v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_510])).

tff(c_42,plain,(
    ! [A_20,B_24,C_26] :
      ( r1_waybel_7(A_20,k2_yellow19(A_20,B_24),C_26)
      | ~ r3_waybel_9(A_20,B_24,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_20))
      | ~ l1_waybel_0(B_24,A_20)
      | ~ v7_waybel_0(B_24)
      | ~ v4_orders_2(B_24)
      | v2_struct_0(B_24)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_505,plain,(
    ! [C_26] :
      ( r1_waybel_7('#skF_2','#skF_3',C_26)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_26)
      | ~ m1_subset_1(C_26,u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_42])).

tff(c_512,plain,(
    ! [C_26] :
      ( r1_waybel_7('#skF_2','#skF_3',C_26)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_26)
      | ~ m1_subset_1(C_26,k2_struct_0('#skF_2'))
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_437,c_480,c_101,c_505])).

tff(c_513,plain,(
    ! [C_26] :
      ( r1_waybel_7('#skF_2','#skF_3',C_26)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_26)
      | ~ m1_subset_1(C_26,k2_struct_0('#skF_2'))
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_512])).

tff(c_569,plain,(
    ! [C_26] :
      ( r1_waybel_7('#skF_2','#skF_3',C_26)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_26)
      | ~ m1_subset_1(C_26,k2_struct_0('#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_513])).

tff(c_571,plain,(
    ! [C_131] :
      ( r1_waybel_7('#skF_2','#skF_3',C_131)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_131)
      | ~ m1_subset_1(C_131,k2_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_566,c_569])).

tff(c_577,plain,
    ( r1_waybel_7('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_345,c_571])).

tff(c_581,plain,(
    r1_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_577])).

tff(c_583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_344,c_581])).

tff(c_584,plain,(
    v1_xboole_0('#skF_1'('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_364])).

tff(c_588,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_584,c_14])).

tff(c_591,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_588])).

tff(c_593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_591])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.43/2.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/2.08  
% 4.80/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.83/2.08  %$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v4_pre_topc > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 4.83/2.08  
% 4.83/2.08  %Foreground sorts:
% 4.83/2.08  
% 4.83/2.08  
% 4.83/2.08  %Background operators:
% 4.83/2.08  
% 4.83/2.08  
% 4.83/2.08  %Foreground operators:
% 4.83/2.08  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.83/2.08  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.83/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.83/2.08  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 4.83/2.08  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 4.83/2.08  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.83/2.08  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 4.83/2.08  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.83/2.08  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 4.83/2.08  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.83/2.08  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 4.83/2.08  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 4.83/2.08  tff('#skF_2', type, '#skF_2': $i).
% 4.83/2.08  tff('#skF_3', type, '#skF_3': $i).
% 4.83/2.08  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 4.83/2.08  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.83/2.08  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 4.83/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.83/2.08  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.83/2.08  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.83/2.08  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 4.83/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.83/2.08  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 4.83/2.08  tff('#skF_4', type, '#skF_4': $i).
% 4.83/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.83/2.08  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 4.83/2.08  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 4.83/2.08  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.83/2.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.83/2.08  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.83/2.08  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.83/2.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.83/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.83/2.08  
% 4.98/2.13  tff(f_213, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, k3_yellow19(A, k2_struct_0(A), B), C) <=> r1_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_yellow19)).
% 4.98/2.13  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.98/2.13  tff(f_40, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.98/2.13  tff(f_59, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 4.98/2.13  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.98/2.13  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.98/2.13  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.98/2.13  tff(f_115, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_yellow19)).
% 4.98/2.13  tff(f_87, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 4.98/2.13  tff(f_186, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 4.98/2.13  tff(f_167, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> r1_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_yellow19)).
% 4.98/2.13  tff(f_143, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow19)).
% 4.98/2.13  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.98/2.13  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.98/2.13  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.98/2.13  tff(c_10, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.98/2.13  tff(c_92, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.98/2.13  tff(c_97, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_pre_topc(A_39))), inference(resolution, [status(thm)], [c_10, c_92])).
% 4.98/2.13  tff(c_101, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_97])).
% 4.98/2.13  tff(c_46, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.98/2.13  tff(c_102, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_46])).
% 4.98/2.13  tff(c_64, plain, (~r1_waybel_7('#skF_2', '#skF_3', '#skF_4') | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.98/2.13  tff(c_118, plain, (~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_64])).
% 4.98/2.13  tff(c_70, plain, (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_4') | r1_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.98/2.13  tff(c_136, plain, (r1_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_118, c_70])).
% 4.98/2.13  tff(c_121, plain, (![A_44]: (m1_subset_1('#skF_1'(A_44), k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.98/2.13  tff(c_127, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_101, c_121])).
% 4.98/2.13  tff(c_130, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_127])).
% 4.98/2.13  tff(c_131, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_62, c_130])).
% 4.98/2.13  tff(c_6, plain, (![B_5, A_3]: (v1_xboole_0(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.98/2.13  tff(c_135, plain, (v1_xboole_0('#skF_1'('#skF_2')) | ~v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_131, c_6])).
% 4.98/2.13  tff(c_137, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_135])).
% 4.98/2.13  tff(c_56, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.98/2.13  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.98/2.13  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.98/2.13  tff(c_71, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 4.98/2.13  tff(c_52, plain, (v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.98/2.13  tff(c_50, plain, (v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.98/2.13  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.98/2.13  tff(c_151, plain, (![A_52, B_53, C_54]: (v4_orders_2(k3_yellow19(A_52, B_53, C_54)) | ~m1_subset_1(C_54, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_53)))) | ~v13_waybel_0(C_54, k3_yellow_1(B_53)) | ~v2_waybel_0(C_54, k3_yellow_1(B_53)) | v1_xboole_0(C_54) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | v1_xboole_0(B_53) | ~l1_struct_0(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.98/2.13  tff(c_156, plain, (![A_52]: (v4_orders_2(k3_yellow19(A_52, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_52))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_52) | v2_struct_0(A_52))), inference(resolution, [status(thm)], [c_48, c_151])).
% 4.98/2.13  tff(c_163, plain, (![A_52]: (v4_orders_2(k3_yellow19(A_52, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_52))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_52) | v2_struct_0(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_156])).
% 4.98/2.13  tff(c_166, plain, (![A_55]: (v4_orders_2(k3_yellow19(A_55, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_struct_0(A_55) | v2_struct_0(A_55))), inference(negUnitSimplification, [status(thm)], [c_137, c_56, c_163])).
% 4.98/2.13  tff(c_169, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_101, c_166])).
% 4.98/2.13  tff(c_171, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_169])).
% 4.98/2.13  tff(c_172, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_171])).
% 4.98/2.13  tff(c_173, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_172])).
% 4.98/2.13  tff(c_176, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_173])).
% 4.98/2.13  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_176])).
% 4.98/2.13  tff(c_182, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_172])).
% 4.98/2.13  tff(c_181, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitRight, [status(thm)], [c_172])).
% 4.98/2.13  tff(c_211, plain, (![A_63, B_64, C_65]: (l1_waybel_0(k3_yellow19(A_63, B_64, C_65), A_63) | ~m1_subset_1(C_65, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_64)))) | ~v13_waybel_0(C_65, k3_yellow_1(B_64)) | ~v2_waybel_0(C_65, k3_yellow_1(B_64)) | v1_xboole_0(C_65) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | v1_xboole_0(B_64) | ~l1_struct_0(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.98/2.13  tff(c_216, plain, (![A_63]: (l1_waybel_0(k3_yellow19(A_63, k2_struct_0('#skF_2'), '#skF_3'), A_63) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_63))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_63) | v2_struct_0(A_63))), inference(resolution, [status(thm)], [c_48, c_211])).
% 4.98/2.13  tff(c_223, plain, (![A_63]: (l1_waybel_0(k3_yellow19(A_63, k2_struct_0('#skF_2'), '#skF_3'), A_63) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_63))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_63) | v2_struct_0(A_63))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_216])).
% 4.98/2.13  tff(c_226, plain, (![A_66]: (l1_waybel_0(k3_yellow19(A_66, k2_struct_0('#skF_2'), '#skF_3'), A_66) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_struct_0(A_66) | v2_struct_0(A_66))), inference(negUnitSimplification, [status(thm)], [c_137, c_56, c_223])).
% 4.98/2.13  tff(c_228, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_101, c_226])).
% 4.98/2.13  tff(c_230, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_71, c_228])).
% 4.98/2.13  tff(c_231, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_230])).
% 4.98/2.13  tff(c_54, plain, (v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.98/2.13  tff(c_247, plain, (![A_70, B_71]: (k2_yellow19(A_70, k3_yellow19(A_70, k2_struct_0(A_70), B_71))=B_71 | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_70))))) | ~v13_waybel_0(B_71, k3_yellow_1(k2_struct_0(A_70))) | ~v2_waybel_0(B_71, k3_yellow_1(k2_struct_0(A_70))) | ~v1_subset_1(B_71, u1_struct_0(k3_yellow_1(k2_struct_0(A_70)))) | v1_xboole_0(B_71) | ~l1_struct_0(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.98/2.13  tff(c_252, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_247])).
% 4.98/2.13  tff(c_259, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_54, c_52, c_50, c_252])).
% 4.98/2.13  tff(c_260, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_259])).
% 4.98/2.13  tff(c_40, plain, (![A_20, B_24, C_26]: (r3_waybel_9(A_20, B_24, C_26) | ~r1_waybel_7(A_20, k2_yellow19(A_20, B_24), C_26) | ~m1_subset_1(C_26, u1_struct_0(A_20)) | ~l1_waybel_0(B_24, A_20) | ~v7_waybel_0(B_24) | ~v4_orders_2(B_24) | v2_struct_0(B_24) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.98/2.13  tff(c_265, plain, (![C_26]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_26) | ~r1_waybel_7('#skF_2', '#skF_3', C_26) | ~m1_subset_1(C_26, u1_struct_0('#skF_2')) | ~l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_260, c_40])).
% 4.98/2.13  tff(c_272, plain, (![C_26]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_26) | ~r1_waybel_7('#skF_2', '#skF_3', C_26) | ~m1_subset_1(C_26, k2_struct_0('#skF_2')) | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_181, c_231, c_101, c_265])).
% 4.98/2.13  tff(c_273, plain, (![C_26]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_26) | ~r1_waybel_7('#skF_2', '#skF_3', C_26) | ~m1_subset_1(C_26, k2_struct_0('#skF_2')) | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_272])).
% 4.98/2.13  tff(c_284, plain, (~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_273])).
% 4.98/2.13  tff(c_288, plain, (![A_79, B_80, C_81]: (v7_waybel_0(k3_yellow19(A_79, B_80, C_81)) | ~m1_subset_1(C_81, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_80)))) | ~v13_waybel_0(C_81, k3_yellow_1(B_80)) | ~v2_waybel_0(C_81, k3_yellow_1(B_80)) | ~v1_subset_1(C_81, u1_struct_0(k3_yellow_1(B_80))) | v1_xboole_0(C_81) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | v1_xboole_0(B_80) | ~l1_struct_0(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.98/2.13  tff(c_293, plain, (![A_79]: (v7_waybel_0(k3_yellow19(A_79, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_79))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_79) | v2_struct_0(A_79))), inference(resolution, [status(thm)], [c_48, c_288])).
% 4.98/2.13  tff(c_300, plain, (![A_79]: (v7_waybel_0(k3_yellow19(A_79, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_79))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_79) | v2_struct_0(A_79))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_293])).
% 4.98/2.13  tff(c_303, plain, (![A_82]: (v7_waybel_0(k3_yellow19(A_82, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_struct_0(A_82) | v2_struct_0(A_82))), inference(negUnitSimplification, [status(thm)], [c_137, c_56, c_300])).
% 4.98/2.13  tff(c_306, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_101, c_303])).
% 4.98/2.13  tff(c_308, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_71, c_306])).
% 4.98/2.13  tff(c_310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_284, c_308])).
% 4.98/2.13  tff(c_311, plain, (![C_26]: (v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_26) | ~r1_waybel_7('#skF_2', '#skF_3', C_26) | ~m1_subset_1(C_26, k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_273])).
% 4.98/2.13  tff(c_313, plain, (v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_311])).
% 4.98/2.13  tff(c_32, plain, (![A_14, B_15, C_16]: (~v2_struct_0(k3_yellow19(A_14, B_15, C_16)) | ~m1_subset_1(C_16, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_15)))) | ~v13_waybel_0(C_16, k3_yellow_1(B_15)) | ~v2_waybel_0(C_16, k3_yellow_1(B_15)) | v1_xboole_0(C_16) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | v1_xboole_0(B_15) | ~l1_struct_0(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.98/2.13  tff(c_318, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_313, c_32])).
% 4.98/2.13  tff(c_321, plain, (v1_xboole_0('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_71, c_101, c_52, c_50, c_48, c_318])).
% 4.98/2.13  tff(c_323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_137, c_56, c_321])).
% 4.98/2.13  tff(c_326, plain, (![C_83]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_83) | ~r1_waybel_7('#skF_2', '#skF_3', C_83) | ~m1_subset_1(C_83, k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_311])).
% 4.98/2.13  tff(c_329, plain, (~r1_waybel_7('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_326, c_118])).
% 4.98/2.13  tff(c_333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_136, c_329])).
% 4.98/2.13  tff(c_334, plain, (v1_xboole_0('#skF_1'('#skF_2'))), inference(splitRight, [status(thm)], [c_135])).
% 4.98/2.13  tff(c_14, plain, (![A_8]: (~v1_xboole_0('#skF_1'(A_8)) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.98/2.13  tff(c_338, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_334, c_14])).
% 4.98/2.13  tff(c_341, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_338])).
% 4.98/2.13  tff(c_343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_341])).
% 4.98/2.13  tff(c_344, plain, (~r1_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_64])).
% 4.98/2.13  tff(c_345, plain, (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_64])).
% 4.98/2.13  tff(c_348, plain, (![A_86]: (m1_subset_1('#skF_1'(A_86), k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.98/2.14  tff(c_354, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_101, c_348])).
% 4.98/2.14  tff(c_357, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_354])).
% 4.98/2.14  tff(c_358, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_62, c_357])).
% 4.98/2.14  tff(c_364, plain, (v1_xboole_0('#skF_1'('#skF_2')) | ~v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_358, c_6])).
% 4.98/2.14  tff(c_365, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_364])).
% 4.98/2.14  tff(c_379, plain, (![A_94, B_95, C_96]: (v3_orders_2(k3_yellow19(A_94, B_95, C_96)) | ~m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_95)))) | ~v13_waybel_0(C_96, k3_yellow_1(B_95)) | ~v2_waybel_0(C_96, k3_yellow_1(B_95)) | v1_xboole_0(C_96) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | v1_xboole_0(B_95) | ~l1_struct_0(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.98/2.14  tff(c_384, plain, (![A_94]: (v3_orders_2(k3_yellow19(A_94, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_94))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_94) | v2_struct_0(A_94))), inference(resolution, [status(thm)], [c_48, c_379])).
% 4.98/2.14  tff(c_391, plain, (![A_94]: (v3_orders_2(k3_yellow19(A_94, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_94))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_94) | v2_struct_0(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_384])).
% 4.98/2.14  tff(c_394, plain, (![A_97]: (v3_orders_2(k3_yellow19(A_97, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_struct_0(A_97) | v2_struct_0(A_97))), inference(negUnitSimplification, [status(thm)], [c_365, c_56, c_391])).
% 4.98/2.14  tff(c_397, plain, (v3_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_101, c_394])).
% 4.98/2.14  tff(c_399, plain, (v3_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_397])).
% 4.98/2.14  tff(c_400, plain, (v3_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_399])).
% 4.98/2.14  tff(c_401, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_400])).
% 4.98/2.14  tff(c_404, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_401])).
% 4.98/2.14  tff(c_408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_404])).
% 4.98/2.14  tff(c_410, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_400])).
% 4.98/2.14  tff(c_416, plain, (![A_98, B_99, C_100]: (v4_orders_2(k3_yellow19(A_98, B_99, C_100)) | ~m1_subset_1(C_100, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_99)))) | ~v13_waybel_0(C_100, k3_yellow_1(B_99)) | ~v2_waybel_0(C_100, k3_yellow_1(B_99)) | v1_xboole_0(C_100) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | v1_xboole_0(B_99) | ~l1_struct_0(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.98/2.14  tff(c_421, plain, (![A_98]: (v4_orders_2(k3_yellow19(A_98, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_98))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_98) | v2_struct_0(A_98))), inference(resolution, [status(thm)], [c_48, c_416])).
% 4.98/2.14  tff(c_428, plain, (![A_98]: (v4_orders_2(k3_yellow19(A_98, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_98))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_98) | v2_struct_0(A_98))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_421])).
% 4.98/2.14  tff(c_431, plain, (![A_101]: (v4_orders_2(k3_yellow19(A_101, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_struct_0(A_101) | v2_struct_0(A_101))), inference(negUnitSimplification, [status(thm)], [c_365, c_56, c_428])).
% 4.98/2.14  tff(c_434, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_101, c_431])).
% 4.98/2.14  tff(c_436, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_410, c_71, c_434])).
% 4.98/2.14  tff(c_437, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_436])).
% 4.98/2.14  tff(c_460, plain, (![A_109, B_110, C_111]: (l1_waybel_0(k3_yellow19(A_109, B_110, C_111), A_109) | ~m1_subset_1(C_111, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_110)))) | ~v13_waybel_0(C_111, k3_yellow_1(B_110)) | ~v2_waybel_0(C_111, k3_yellow_1(B_110)) | v1_xboole_0(C_111) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | v1_xboole_0(B_110) | ~l1_struct_0(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.98/2.14  tff(c_465, plain, (![A_109]: (l1_waybel_0(k3_yellow19(A_109, k2_struct_0('#skF_2'), '#skF_3'), A_109) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_109))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_109) | v2_struct_0(A_109))), inference(resolution, [status(thm)], [c_48, c_460])).
% 4.98/2.14  tff(c_472, plain, (![A_109]: (l1_waybel_0(k3_yellow19(A_109, k2_struct_0('#skF_2'), '#skF_3'), A_109) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_109))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_109) | v2_struct_0(A_109))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_465])).
% 4.98/2.14  tff(c_475, plain, (![A_112]: (l1_waybel_0(k3_yellow19(A_112, k2_struct_0('#skF_2'), '#skF_3'), A_112) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_struct_0(A_112) | v2_struct_0(A_112))), inference(negUnitSimplification, [status(thm)], [c_365, c_56, c_472])).
% 4.98/2.14  tff(c_477, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_101, c_475])).
% 4.98/2.14  tff(c_479, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_410, c_71, c_477])).
% 4.98/2.14  tff(c_480, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_479])).
% 4.98/2.14  tff(c_484, plain, (![A_119, B_120]: (k2_yellow19(A_119, k3_yellow19(A_119, k2_struct_0(A_119), B_120))=B_120 | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_119))))) | ~v13_waybel_0(B_120, k3_yellow_1(k2_struct_0(A_119))) | ~v2_waybel_0(B_120, k3_yellow_1(k2_struct_0(A_119))) | ~v1_subset_1(B_120, u1_struct_0(k3_yellow_1(k2_struct_0(A_119)))) | v1_xboole_0(B_120) | ~l1_struct_0(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.98/2.14  tff(c_489, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_484])).
% 4.98/2.14  tff(c_496, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_410, c_54, c_52, c_50, c_489])).
% 4.98/2.14  tff(c_497, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_496])).
% 4.98/2.14  tff(c_502, plain, (![C_26]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_26) | ~r1_waybel_7('#skF_2', '#skF_3', C_26) | ~m1_subset_1(C_26, u1_struct_0('#skF_2')) | ~l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_497, c_40])).
% 4.98/2.14  tff(c_509, plain, (![C_26]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_26) | ~r1_waybel_7('#skF_2', '#skF_3', C_26) | ~m1_subset_1(C_26, k2_struct_0('#skF_2')) | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_437, c_480, c_101, c_502])).
% 4.98/2.14  tff(c_510, plain, (![C_26]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_26) | ~r1_waybel_7('#skF_2', '#skF_3', C_26) | ~m1_subset_1(C_26, k2_struct_0('#skF_2')) | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_509])).
% 4.98/2.14  tff(c_515, plain, (~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_510])).
% 4.98/2.14  tff(c_517, plain, (![A_123, B_124, C_125]: (v7_waybel_0(k3_yellow19(A_123, B_124, C_125)) | ~m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_124)))) | ~v13_waybel_0(C_125, k3_yellow_1(B_124)) | ~v2_waybel_0(C_125, k3_yellow_1(B_124)) | ~v1_subset_1(C_125, u1_struct_0(k3_yellow_1(B_124))) | v1_xboole_0(C_125) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | v1_xboole_0(B_124) | ~l1_struct_0(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.98/2.14  tff(c_522, plain, (![A_123]: (v7_waybel_0(k3_yellow19(A_123, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_123))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_123) | v2_struct_0(A_123))), inference(resolution, [status(thm)], [c_48, c_517])).
% 4.98/2.14  tff(c_529, plain, (![A_123]: (v7_waybel_0(k3_yellow19(A_123, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_123))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_123) | v2_struct_0(A_123))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_522])).
% 4.98/2.14  tff(c_532, plain, (![A_126]: (v7_waybel_0(k3_yellow19(A_126, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_struct_0(A_126) | v2_struct_0(A_126))), inference(negUnitSimplification, [status(thm)], [c_365, c_56, c_529])).
% 4.98/2.14  tff(c_535, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_101, c_532])).
% 4.98/2.14  tff(c_537, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_410, c_71, c_535])).
% 4.98/2.14  tff(c_539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_515, c_537])).
% 4.98/2.14  tff(c_540, plain, (![C_26]: (v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_26) | ~r1_waybel_7('#skF_2', '#skF_3', C_26) | ~m1_subset_1(C_26, k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_510])).
% 4.98/2.14  tff(c_542, plain, (v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_540])).
% 4.98/2.14  tff(c_559, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_542, c_32])).
% 4.98/2.14  tff(c_562, plain, (v1_xboole_0('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_410, c_71, c_101, c_52, c_50, c_48, c_559])).
% 4.98/2.14  tff(c_564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_365, c_56, c_562])).
% 4.98/2.14  tff(c_566, plain, (~v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitRight, [status(thm)], [c_540])).
% 4.98/2.14  tff(c_541, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitRight, [status(thm)], [c_510])).
% 4.98/2.14  tff(c_42, plain, (![A_20, B_24, C_26]: (r1_waybel_7(A_20, k2_yellow19(A_20, B_24), C_26) | ~r3_waybel_9(A_20, B_24, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_20)) | ~l1_waybel_0(B_24, A_20) | ~v7_waybel_0(B_24) | ~v4_orders_2(B_24) | v2_struct_0(B_24) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.98/2.14  tff(c_505, plain, (![C_26]: (r1_waybel_7('#skF_2', '#skF_3', C_26) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_26) | ~m1_subset_1(C_26, u1_struct_0('#skF_2')) | ~l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_497, c_42])).
% 4.98/2.14  tff(c_512, plain, (![C_26]: (r1_waybel_7('#skF_2', '#skF_3', C_26) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_26) | ~m1_subset_1(C_26, k2_struct_0('#skF_2')) | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_437, c_480, c_101, c_505])).
% 4.98/2.14  tff(c_513, plain, (![C_26]: (r1_waybel_7('#skF_2', '#skF_3', C_26) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_26) | ~m1_subset_1(C_26, k2_struct_0('#skF_2')) | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_512])).
% 4.98/2.14  tff(c_569, plain, (![C_26]: (r1_waybel_7('#skF_2', '#skF_3', C_26) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_26) | ~m1_subset_1(C_26, k2_struct_0('#skF_2')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_541, c_513])).
% 4.98/2.14  tff(c_571, plain, (![C_131]: (r1_waybel_7('#skF_2', '#skF_3', C_131) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_131) | ~m1_subset_1(C_131, k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_566, c_569])).
% 4.98/2.14  tff(c_577, plain, (r1_waybel_7('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_345, c_571])).
% 4.98/2.14  tff(c_581, plain, (r1_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_577])).
% 4.98/2.14  tff(c_583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_344, c_581])).
% 4.98/2.14  tff(c_584, plain, (v1_xboole_0('#skF_1'('#skF_2'))), inference(splitRight, [status(thm)], [c_364])).
% 4.98/2.14  tff(c_588, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_584, c_14])).
% 4.98/2.14  tff(c_591, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_588])).
% 4.98/2.14  tff(c_593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_591])).
% 4.98/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.98/2.14  
% 4.98/2.14  Inference rules
% 4.98/2.14  ----------------------
% 4.98/2.14  #Ref     : 0
% 4.98/2.14  #Sup     : 88
% 4.98/2.14  #Fact    : 0
% 4.98/2.14  #Define  : 0
% 4.98/2.14  #Split   : 10
% 4.98/2.14  #Chain   : 0
% 4.98/2.14  #Close   : 0
% 4.98/2.14  
% 4.98/2.14  Ordering : KBO
% 4.98/2.14  
% 4.98/2.14  Simplification rules
% 4.98/2.14  ----------------------
% 4.98/2.14  #Subsume      : 8
% 4.98/2.14  #Demod        : 107
% 4.98/2.14  #Tautology    : 19
% 4.98/2.14  #SimpNegUnit  : 40
% 4.98/2.14  #BackRed      : 1
% 4.98/2.14  
% 4.98/2.14  #Partial instantiations: 0
% 4.98/2.14  #Strategies tried      : 1
% 4.98/2.14  
% 4.98/2.14  Timing (in seconds)
% 4.98/2.14  ----------------------
% 4.98/2.14  Preprocessing        : 0.56
% 4.98/2.14  Parsing              : 0.28
% 4.98/2.14  CNF conversion       : 0.04
% 4.98/2.14  Main loop            : 0.63
% 4.98/2.14  Inferencing          : 0.22
% 4.98/2.14  Reduction            : 0.20
% 4.98/2.14  Demodulation         : 0.14
% 4.98/2.14  BG Simplification    : 0.04
% 4.98/2.14  Subsumption          : 0.12
% 4.98/2.14  Abstraction          : 0.03
% 4.98/2.14  MUC search           : 0.00
% 4.98/2.14  Cooper               : 0.00
% 4.98/2.14  Total                : 1.30
% 4.98/2.14  Index Insertion      : 0.00
% 4.98/2.14  Index Deletion       : 0.00
% 4.98/2.14  Index Matching       : 0.00
% 4.98/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
