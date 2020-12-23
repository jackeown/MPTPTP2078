%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:35 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  189 (3722 expanded)
%              Number of leaves         :   46 (1336 expanded)
%              Depth                    :   24
%              Number of atoms          :  588 (15068 expanded)
%              Number of equality atoms :   15 ( 830 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k1_connsp_2 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k1_connsp_2,type,(
    k1_connsp_2: ( $i * $i ) > $i )).

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

tff(f_221,negated_conjecture,(
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

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_123,axiom,(
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

tff(f_95,axiom,(
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

tff(f_194,axiom,(
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

tff(f_175,axiom,(
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

tff(f_151,axiom,(
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

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_10,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_90,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_95,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(resolution,[status(thm)],[c_10,c_90])).

tff(c_99,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_95])).

tff(c_14,plain,(
    ! [B_12,A_10] :
      ( r2_hidden(B_12,k1_connsp_2(A_10,B_12))
      | ~ m1_subset_1(B_12,u1_struct_0(A_10))
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_100,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_44])).

tff(c_68,plain,
    ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3')
    | r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_113,plain,(
    r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_122,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(k1_connsp_2(A_50,B_51),k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_subset_1(B_51,u1_struct_0(A_50))
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_127,plain,(
    ! [B_51] :
      ( m1_subset_1(k1_connsp_2('#skF_1',B_51),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_122])).

tff(c_130,plain,(
    ! [B_51] :
      ( m1_subset_1(k1_connsp_2('#skF_1',B_51),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_51,k2_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_99,c_127])).

tff(c_132,plain,(
    ! [B_52] :
      ( m1_subset_1(k1_connsp_2('#skF_1',B_52),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_52,k2_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_130])).

tff(c_6,plain,(
    ! [C_5,B_4,A_3] :
      ( ~ v1_xboole_0(C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_135,plain,(
    ! [A_3,B_52] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ r2_hidden(A_3,k1_connsp_2('#skF_1',B_52))
      | ~ m1_subset_1(B_52,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_132,c_6])).

tff(c_136,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_50,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_48,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_167,plain,(
    ! [A_67,B_68,C_69] :
      ( v4_orders_2(k3_yellow19(A_67,B_68,C_69))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_68))))
      | ~ v13_waybel_0(C_69,k3_yellow_1(B_68))
      | ~ v2_waybel_0(C_69,k3_yellow_1(B_68))
      | v1_xboole_0(C_69)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | v1_xboole_0(B_68)
      | ~ l1_struct_0(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_172,plain,(
    ! [A_67] :
      ( v4_orders_2(k3_yellow19(A_67,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_67)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_67)
      | v2_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_46,c_167])).

tff(c_179,plain,(
    ! [A_67] :
      ( v4_orders_2(k3_yellow19(A_67,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_67)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_67)
      | v2_struct_0(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_172])).

tff(c_182,plain,(
    ! [A_70] :
      ( v4_orders_2(k3_yellow19(A_70,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_struct_0(A_70)
      | v2_struct_0(A_70) ) ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_54,c_179])).

tff(c_185,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_182])).

tff(c_187,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_185])).

tff(c_188,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_187])).

tff(c_189,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_192,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_189])).

tff(c_196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_192])).

tff(c_198,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_197,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_248,plain,(
    ! [A_82,B_83,C_84] :
      ( l1_waybel_0(k3_yellow19(A_82,B_83,C_84),A_82)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_83))))
      | ~ v13_waybel_0(C_84,k3_yellow_1(B_83))
      | ~ v2_waybel_0(C_84,k3_yellow_1(B_83))
      | v1_xboole_0(C_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | v1_xboole_0(B_83)
      | ~ l1_struct_0(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_253,plain,(
    ! [A_82] :
      ( l1_waybel_0(k3_yellow19(A_82,k2_struct_0('#skF_1'),'#skF_2'),A_82)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_82)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_82)
      | v2_struct_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_46,c_248])).

tff(c_260,plain,(
    ! [A_82] :
      ( l1_waybel_0(k3_yellow19(A_82,k2_struct_0('#skF_1'),'#skF_2'),A_82)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_82)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_82)
      | v2_struct_0(A_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_253])).

tff(c_263,plain,(
    ! [A_85] :
      ( l1_waybel_0(k3_yellow19(A_85,k2_struct_0('#skF_1'),'#skF_2'),A_85)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_struct_0(A_85)
      | v2_struct_0(A_85) ) ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_54,c_260])).

tff(c_265,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_263])).

tff(c_267,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_69,c_265])).

tff(c_268,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_267])).

tff(c_52,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_272,plain,(
    ! [A_92,B_93] :
      ( k2_yellow19(A_92,k3_yellow19(A_92,k2_struct_0(A_92),B_93)) = B_93
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_92)))))
      | ~ v13_waybel_0(B_93,k3_yellow_1(k2_struct_0(A_92)))
      | ~ v2_waybel_0(B_93,k3_yellow_1(k2_struct_0(A_92)))
      | ~ v1_subset_1(B_93,u1_struct_0(k3_yellow_1(k2_struct_0(A_92))))
      | v1_xboole_0(B_93)
      | ~ l1_struct_0(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_277,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_272])).

tff(c_284,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_52,c_50,c_48,c_277])).

tff(c_285,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_284])).

tff(c_38,plain,(
    ! [A_23,B_27,C_29] :
      ( r3_waybel_9(A_23,B_27,C_29)
      | ~ r1_waybel_7(A_23,k2_yellow19(A_23,B_27),C_29)
      | ~ m1_subset_1(C_29,u1_struct_0(A_23))
      | ~ l1_waybel_0(B_27,A_23)
      | ~ v7_waybel_0(B_27)
      | ~ v4_orders_2(B_27)
      | v2_struct_0(B_27)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_290,plain,(
    ! [C_29] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_38])).

tff(c_297,plain,(
    ! [C_29] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_197,c_268,c_99,c_290])).

tff(c_298,plain,(
    ! [C_29] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_297])).

tff(c_303,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_305,plain,(
    ! [A_96,B_97,C_98] :
      ( v7_waybel_0(k3_yellow19(A_96,B_97,C_98))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_97))))
      | ~ v13_waybel_0(C_98,k3_yellow_1(B_97))
      | ~ v2_waybel_0(C_98,k3_yellow_1(B_97))
      | ~ v1_subset_1(C_98,u1_struct_0(k3_yellow_1(B_97)))
      | v1_xboole_0(C_98)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | v1_xboole_0(B_97)
      | ~ l1_struct_0(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_310,plain,(
    ! [A_96] :
      ( v7_waybel_0(k3_yellow19(A_96,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_96)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_96)
      | v2_struct_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_46,c_305])).

tff(c_317,plain,(
    ! [A_96] :
      ( v7_waybel_0(k3_yellow19(A_96,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_96)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_96)
      | v2_struct_0(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_310])).

tff(c_320,plain,(
    ! [A_99] :
      ( v7_waybel_0(k3_yellow19(A_99,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_struct_0(A_99)
      | v2_struct_0(A_99) ) ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_54,c_317])).

tff(c_323,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_320])).

tff(c_325,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_69,c_323])).

tff(c_327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_303,c_325])).

tff(c_328,plain,(
    ! [C_29] :
      ( v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_330,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_328])).

tff(c_30,plain,(
    ! [A_17,B_18,C_19] :
      ( ~ v2_struct_0(k3_yellow19(A_17,B_18,C_19))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_18))))
      | ~ v13_waybel_0(C_19,k3_yellow_1(B_18))
      | ~ v2_waybel_0(C_19,k3_yellow_1(B_18))
      | v1_xboole_0(C_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | v1_xboole_0(B_18)
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_347,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_330,c_30])).

tff(c_350,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_69,c_99,c_50,c_48,c_46,c_347])).

tff(c_352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_136,c_54,c_350])).

tff(c_355,plain,(
    ! [C_103] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_103)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_103)
      | ~ m1_subset_1(C_103,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_328])).

tff(c_62,plain,
    ( ~ r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_116,plain,(
    ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_62])).

tff(c_358,plain,
    ( ~ r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_355,c_116])).

tff(c_362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_113,c_358])).

tff(c_365,plain,(
    ! [A_104,B_105] :
      ( ~ r2_hidden(A_104,k1_connsp_2('#skF_1',B_105))
      | ~ m1_subset_1(B_105,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_369,plain,(
    ! [B_12] :
      ( ~ m1_subset_1(B_12,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_12,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_365])).

tff(c_372,plain,(
    ! [B_12] :
      ( ~ m1_subset_1(B_12,k2_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_99,c_369])).

tff(c_373,plain,(
    ! [B_12] : ~ m1_subset_1(B_12,k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_372])).

tff(c_375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_373,c_100])).

tff(c_377,plain,(
    ~ r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_376,plain,(
    r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_398,plain,(
    ! [A_111,B_112] :
      ( m1_subset_1(k1_connsp_2(A_111,B_112),k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ m1_subset_1(B_112,u1_struct_0(A_111))
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_403,plain,(
    ! [B_112] :
      ( m1_subset_1(k1_connsp_2('#skF_1',B_112),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_398])).

tff(c_406,plain,(
    ! [B_112] :
      ( m1_subset_1(k1_connsp_2('#skF_1',B_112),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_112,k2_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_99,c_403])).

tff(c_408,plain,(
    ! [B_113] :
      ( m1_subset_1(k1_connsp_2('#skF_1',B_113),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_113,k2_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_406])).

tff(c_411,plain,(
    ! [A_3,B_113] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ r2_hidden(A_3,k1_connsp_2('#skF_1',B_113))
      | ~ m1_subset_1(B_113,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_408,c_6])).

tff(c_412,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_411])).

tff(c_431,plain,(
    ! [A_125,B_126,C_127] :
      ( v4_orders_2(k3_yellow19(A_125,B_126,C_127))
      | ~ m1_subset_1(C_127,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_126))))
      | ~ v13_waybel_0(C_127,k3_yellow_1(B_126))
      | ~ v2_waybel_0(C_127,k3_yellow_1(B_126))
      | v1_xboole_0(C_127)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | v1_xboole_0(B_126)
      | ~ l1_struct_0(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_436,plain,(
    ! [A_125] :
      ( v4_orders_2(k3_yellow19(A_125,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_125)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_125)
      | v2_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_46,c_431])).

tff(c_443,plain,(
    ! [A_125] :
      ( v4_orders_2(k3_yellow19(A_125,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_125)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_125)
      | v2_struct_0(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_436])).

tff(c_446,plain,(
    ! [A_128] :
      ( v4_orders_2(k3_yellow19(A_128,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_struct_0(A_128)
      | v2_struct_0(A_128) ) ),
    inference(negUnitSimplification,[status(thm)],[c_412,c_54,c_443])).

tff(c_449,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_446])).

tff(c_451,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_449])).

tff(c_452,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_451])).

tff(c_453,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_452])).

tff(c_456,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_453])).

tff(c_460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_456])).

tff(c_462,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_452])).

tff(c_461,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_452])).

tff(c_512,plain,(
    ! [A_140,B_141,C_142] :
      ( l1_waybel_0(k3_yellow19(A_140,B_141,C_142),A_140)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_141))))
      | ~ v13_waybel_0(C_142,k3_yellow_1(B_141))
      | ~ v2_waybel_0(C_142,k3_yellow_1(B_141))
      | v1_xboole_0(C_142)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | v1_xboole_0(B_141)
      | ~ l1_struct_0(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_517,plain,(
    ! [A_140] :
      ( l1_waybel_0(k3_yellow19(A_140,k2_struct_0('#skF_1'),'#skF_2'),A_140)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_140)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_140)
      | v2_struct_0(A_140) ) ),
    inference(resolution,[status(thm)],[c_46,c_512])).

tff(c_524,plain,(
    ! [A_140] :
      ( l1_waybel_0(k3_yellow19(A_140,k2_struct_0('#skF_1'),'#skF_2'),A_140)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_140)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_140)
      | v2_struct_0(A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_517])).

tff(c_527,plain,(
    ! [A_143] :
      ( l1_waybel_0(k3_yellow19(A_143,k2_struct_0('#skF_1'),'#skF_2'),A_143)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_struct_0(A_143)
      | v2_struct_0(A_143) ) ),
    inference(negUnitSimplification,[status(thm)],[c_412,c_54,c_524])).

tff(c_529,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_527])).

tff(c_531,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_69,c_529])).

tff(c_532,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_531])).

tff(c_533,plain,(
    ! [A_144,B_145] :
      ( k2_yellow19(A_144,k3_yellow19(A_144,k2_struct_0(A_144),B_145)) = B_145
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_144)))))
      | ~ v13_waybel_0(B_145,k3_yellow_1(k2_struct_0(A_144)))
      | ~ v2_waybel_0(B_145,k3_yellow_1(k2_struct_0(A_144)))
      | ~ v1_subset_1(B_145,u1_struct_0(k3_yellow_1(k2_struct_0(A_144))))
      | v1_xboole_0(B_145)
      | ~ l1_struct_0(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_538,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_533])).

tff(c_545,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_52,c_50,c_48,c_538])).

tff(c_546,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_545])).

tff(c_551,plain,(
    ! [C_29] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_38])).

tff(c_558,plain,(
    ! [C_29] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_461,c_532,c_99,c_551])).

tff(c_559,plain,(
    ! [C_29] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_558])).

tff(c_564,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_559])).

tff(c_569,plain,(
    ! [A_154,B_155,C_156] :
      ( v7_waybel_0(k3_yellow19(A_154,B_155,C_156))
      | ~ m1_subset_1(C_156,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_155))))
      | ~ v13_waybel_0(C_156,k3_yellow_1(B_155))
      | ~ v2_waybel_0(C_156,k3_yellow_1(B_155))
      | ~ v1_subset_1(C_156,u1_struct_0(k3_yellow_1(B_155)))
      | v1_xboole_0(C_156)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | v1_xboole_0(B_155)
      | ~ l1_struct_0(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_574,plain,(
    ! [A_154] :
      ( v7_waybel_0(k3_yellow19(A_154,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_154)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_154)
      | v2_struct_0(A_154) ) ),
    inference(resolution,[status(thm)],[c_46,c_569])).

tff(c_581,plain,(
    ! [A_154] :
      ( v7_waybel_0(k3_yellow19(A_154,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_154)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_154)
      | v2_struct_0(A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_574])).

tff(c_584,plain,(
    ! [A_157] :
      ( v7_waybel_0(k3_yellow19(A_157,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_struct_0(A_157)
      | v2_struct_0(A_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_412,c_54,c_581])).

tff(c_587,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_584])).

tff(c_589,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_69,c_587])).

tff(c_591,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_564,c_589])).

tff(c_592,plain,(
    ! [C_29] :
      ( v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_559])).

tff(c_594,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_592])).

tff(c_596,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_594,c_30])).

tff(c_599,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_69,c_99,c_50,c_48,c_46,c_596])).

tff(c_601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_412,c_54,c_599])).

tff(c_603,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_592])).

tff(c_593,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_559])).

tff(c_40,plain,(
    ! [A_23,B_27,C_29] :
      ( r1_waybel_7(A_23,k2_yellow19(A_23,B_27),C_29)
      | ~ r3_waybel_9(A_23,B_27,C_29)
      | ~ m1_subset_1(C_29,u1_struct_0(A_23))
      | ~ l1_waybel_0(B_27,A_23)
      | ~ v7_waybel_0(B_27)
      | ~ v4_orders_2(B_27)
      | v2_struct_0(B_27)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_554,plain,(
    ! [C_29] :
      ( r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_40])).

tff(c_561,plain,(
    ! [C_29] :
      ( r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_461,c_532,c_99,c_554])).

tff(c_562,plain,(
    ! [C_29] :
      ( r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_561])).

tff(c_605,plain,(
    ! [C_29] :
      ( r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_562])).

tff(c_606,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_605])).

tff(c_607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_603,c_606])).

tff(c_610,plain,(
    ! [C_158] :
      ( r1_waybel_7('#skF_1','#skF_2',C_158)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_158)
      | ~ m1_subset_1(C_158,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_605])).

tff(c_613,plain,
    ( r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_376,c_610])).

tff(c_616,plain,(
    r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_613])).

tff(c_618,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_377,c_616])).

tff(c_622,plain,(
    ! [A_162,B_163] :
      ( ~ r2_hidden(A_162,k1_connsp_2('#skF_1',B_163))
      | ~ m1_subset_1(B_163,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_411])).

tff(c_626,plain,(
    ! [B_12] :
      ( ~ m1_subset_1(B_12,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_12,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_622])).

tff(c_629,plain,(
    ! [B_12] :
      ( ~ m1_subset_1(B_12,k2_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_99,c_626])).

tff(c_630,plain,(
    ! [B_12] : ~ m1_subset_1(B_12,k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_629])).

tff(c_632,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_630,c_100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.50  
% 3.29/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.51  %$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k1_connsp_2 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1
% 3.29/1.51  
% 3.29/1.51  %Foreground sorts:
% 3.29/1.51  
% 3.29/1.51  
% 3.29/1.51  %Background operators:
% 3.29/1.51  
% 3.29/1.51  
% 3.29/1.51  %Foreground operators:
% 3.29/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.29/1.51  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.29/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.51  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.29/1.51  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 3.29/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.51  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.29/1.51  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.29/1.51  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 3.29/1.51  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.29/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.29/1.51  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.29/1.51  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 3.29/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.29/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.29/1.51  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.29/1.51  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.29/1.51  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 3.29/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.29/1.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.29/1.51  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.29/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.51  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.29/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.51  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.29/1.51  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.29/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.29/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.29/1.51  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.29/1.51  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.29/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.29/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.29/1.51  
% 3.52/1.53  tff(f_221, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, k3_yellow19(A, k2_struct_0(A), B), C) <=> r1_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_yellow19)).
% 3.52/1.53  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.52/1.53  tff(f_40, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.52/1.53  tff(f_67, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_connsp_2)).
% 3.52/1.53  tff(f_55, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 3.52/1.53  tff(f_36, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.52/1.53  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.52/1.53  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.52/1.53  tff(f_123, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_yellow19)).
% 3.52/1.53  tff(f_95, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 3.52/1.53  tff(f_194, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 3.52/1.53  tff(f_175, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> r1_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_yellow19)).
% 3.52/1.53  tff(f_151, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow19)).
% 3.52/1.54  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.52/1.54  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.52/1.54  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.52/1.54  tff(c_10, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.52/1.54  tff(c_90, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.52/1.54  tff(c_95, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_pre_topc(A_42))), inference(resolution, [status(thm)], [c_10, c_90])).
% 3.52/1.54  tff(c_99, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_95])).
% 3.52/1.54  tff(c_14, plain, (![B_12, A_10]: (r2_hidden(B_12, k1_connsp_2(A_10, B_12)) | ~m1_subset_1(B_12, u1_struct_0(A_10)) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.52/1.54  tff(c_44, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.52/1.54  tff(c_100, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_44])).
% 3.52/1.54  tff(c_68, plain, (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3') | r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.52/1.54  tff(c_113, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 3.52/1.54  tff(c_122, plain, (![A_50, B_51]: (m1_subset_1(k1_connsp_2(A_50, B_51), k1_zfmisc_1(u1_struct_0(A_50))) | ~m1_subset_1(B_51, u1_struct_0(A_50)) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.52/1.54  tff(c_127, plain, (![B_51]: (m1_subset_1(k1_connsp_2('#skF_1', B_51), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_51, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_122])).
% 3.52/1.54  tff(c_130, plain, (![B_51]: (m1_subset_1(k1_connsp_2('#skF_1', B_51), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_51, k2_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_99, c_127])).
% 3.52/1.54  tff(c_132, plain, (![B_52]: (m1_subset_1(k1_connsp_2('#skF_1', B_52), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_52, k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_60, c_130])).
% 3.52/1.54  tff(c_6, plain, (![C_5, B_4, A_3]: (~v1_xboole_0(C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.52/1.54  tff(c_135, plain, (![A_3, B_52]: (~v1_xboole_0(k2_struct_0('#skF_1')) | ~r2_hidden(A_3, k1_connsp_2('#skF_1', B_52)) | ~m1_subset_1(B_52, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_132, c_6])).
% 3.52/1.54  tff(c_136, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_135])).
% 3.52/1.54  tff(c_54, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.52/1.54  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.52/1.54  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.52/1.54  tff(c_69, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.52/1.54  tff(c_50, plain, (v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.52/1.54  tff(c_48, plain, (v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.52/1.54  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.52/1.54  tff(c_167, plain, (![A_67, B_68, C_69]: (v4_orders_2(k3_yellow19(A_67, B_68, C_69)) | ~m1_subset_1(C_69, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_68)))) | ~v13_waybel_0(C_69, k3_yellow_1(B_68)) | ~v2_waybel_0(C_69, k3_yellow_1(B_68)) | v1_xboole_0(C_69) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | v1_xboole_0(B_68) | ~l1_struct_0(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.52/1.54  tff(c_172, plain, (![A_67]: (v4_orders_2(k3_yellow19(A_67, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_67))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_67) | v2_struct_0(A_67))), inference(resolution, [status(thm)], [c_46, c_167])).
% 3.52/1.54  tff(c_179, plain, (![A_67]: (v4_orders_2(k3_yellow19(A_67, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_67))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_67) | v2_struct_0(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_172])).
% 3.52/1.54  tff(c_182, plain, (![A_70]: (v4_orders_2(k3_yellow19(A_70, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_struct_0(A_70) | v2_struct_0(A_70))), inference(negUnitSimplification, [status(thm)], [c_136, c_54, c_179])).
% 3.52/1.54  tff(c_185, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_99, c_182])).
% 3.52/1.54  tff(c_187, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_185])).
% 3.52/1.54  tff(c_188, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_187])).
% 3.52/1.54  tff(c_189, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_188])).
% 3.52/1.54  tff(c_192, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_189])).
% 3.52/1.54  tff(c_196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_192])).
% 3.52/1.54  tff(c_198, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_188])).
% 3.52/1.54  tff(c_197, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_188])).
% 3.52/1.54  tff(c_248, plain, (![A_82, B_83, C_84]: (l1_waybel_0(k3_yellow19(A_82, B_83, C_84), A_82) | ~m1_subset_1(C_84, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_83)))) | ~v13_waybel_0(C_84, k3_yellow_1(B_83)) | ~v2_waybel_0(C_84, k3_yellow_1(B_83)) | v1_xboole_0(C_84) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | v1_xboole_0(B_83) | ~l1_struct_0(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.52/1.54  tff(c_253, plain, (![A_82]: (l1_waybel_0(k3_yellow19(A_82, k2_struct_0('#skF_1'), '#skF_2'), A_82) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_82))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_82) | v2_struct_0(A_82))), inference(resolution, [status(thm)], [c_46, c_248])).
% 3.52/1.54  tff(c_260, plain, (![A_82]: (l1_waybel_0(k3_yellow19(A_82, k2_struct_0('#skF_1'), '#skF_2'), A_82) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_82))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_82) | v2_struct_0(A_82))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_253])).
% 3.52/1.54  tff(c_263, plain, (![A_85]: (l1_waybel_0(k3_yellow19(A_85, k2_struct_0('#skF_1'), '#skF_2'), A_85) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_struct_0(A_85) | v2_struct_0(A_85))), inference(negUnitSimplification, [status(thm)], [c_136, c_54, c_260])).
% 3.52/1.54  tff(c_265, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_99, c_263])).
% 3.52/1.54  tff(c_267, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_69, c_265])).
% 3.52/1.54  tff(c_268, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_267])).
% 3.52/1.54  tff(c_52, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.52/1.54  tff(c_272, plain, (![A_92, B_93]: (k2_yellow19(A_92, k3_yellow19(A_92, k2_struct_0(A_92), B_93))=B_93 | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_92))))) | ~v13_waybel_0(B_93, k3_yellow_1(k2_struct_0(A_92))) | ~v2_waybel_0(B_93, k3_yellow_1(k2_struct_0(A_92))) | ~v1_subset_1(B_93, u1_struct_0(k3_yellow_1(k2_struct_0(A_92)))) | v1_xboole_0(B_93) | ~l1_struct_0(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.52/1.54  tff(c_277, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_272])).
% 3.52/1.54  tff(c_284, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_52, c_50, c_48, c_277])).
% 3.52/1.54  tff(c_285, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_284])).
% 3.52/1.54  tff(c_38, plain, (![A_23, B_27, C_29]: (r3_waybel_9(A_23, B_27, C_29) | ~r1_waybel_7(A_23, k2_yellow19(A_23, B_27), C_29) | ~m1_subset_1(C_29, u1_struct_0(A_23)) | ~l1_waybel_0(B_27, A_23) | ~v7_waybel_0(B_27) | ~v4_orders_2(B_27) | v2_struct_0(B_27) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.52/1.54  tff(c_290, plain, (![C_29]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~r1_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_285, c_38])).
% 3.52/1.54  tff(c_297, plain, (![C_29]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~r1_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_197, c_268, c_99, c_290])).
% 3.52/1.54  tff(c_298, plain, (![C_29]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~r1_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_297])).
% 3.52/1.54  tff(c_303, plain, (~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_298])).
% 3.52/1.54  tff(c_305, plain, (![A_96, B_97, C_98]: (v7_waybel_0(k3_yellow19(A_96, B_97, C_98)) | ~m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_97)))) | ~v13_waybel_0(C_98, k3_yellow_1(B_97)) | ~v2_waybel_0(C_98, k3_yellow_1(B_97)) | ~v1_subset_1(C_98, u1_struct_0(k3_yellow_1(B_97))) | v1_xboole_0(C_98) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | v1_xboole_0(B_97) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.52/1.54  tff(c_310, plain, (![A_96]: (v7_waybel_0(k3_yellow19(A_96, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_96))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(resolution, [status(thm)], [c_46, c_305])).
% 3.52/1.54  tff(c_317, plain, (![A_96]: (v7_waybel_0(k3_yellow19(A_96, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_96))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_310])).
% 3.52/1.54  tff(c_320, plain, (![A_99]: (v7_waybel_0(k3_yellow19(A_99, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_struct_0(A_99) | v2_struct_0(A_99))), inference(negUnitSimplification, [status(thm)], [c_136, c_54, c_317])).
% 3.52/1.54  tff(c_323, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_99, c_320])).
% 3.52/1.54  tff(c_325, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_69, c_323])).
% 3.52/1.54  tff(c_327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_303, c_325])).
% 3.52/1.54  tff(c_328, plain, (![C_29]: (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~r1_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_298])).
% 3.52/1.54  tff(c_330, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_328])).
% 3.52/1.54  tff(c_30, plain, (![A_17, B_18, C_19]: (~v2_struct_0(k3_yellow19(A_17, B_18, C_19)) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_18)))) | ~v13_waybel_0(C_19, k3_yellow_1(B_18)) | ~v2_waybel_0(C_19, k3_yellow_1(B_18)) | v1_xboole_0(C_19) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | v1_xboole_0(B_18) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.52/1.54  tff(c_347, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_330, c_30])).
% 3.52/1.54  tff(c_350, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_69, c_99, c_50, c_48, c_46, c_347])).
% 3.52/1.54  tff(c_352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_136, c_54, c_350])).
% 3.52/1.54  tff(c_355, plain, (![C_103]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_103) | ~r1_waybel_7('#skF_1', '#skF_2', C_103) | ~m1_subset_1(C_103, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_328])).
% 3.52/1.54  tff(c_62, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.52/1.54  tff(c_116, plain, (~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_62])).
% 3.52/1.54  tff(c_358, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_355, c_116])).
% 3.52/1.54  tff(c_362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_113, c_358])).
% 3.52/1.54  tff(c_365, plain, (![A_104, B_105]: (~r2_hidden(A_104, k1_connsp_2('#skF_1', B_105)) | ~m1_subset_1(B_105, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_135])).
% 3.52/1.54  tff(c_369, plain, (![B_12]: (~m1_subset_1(B_12, k2_struct_0('#skF_1')) | ~m1_subset_1(B_12, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_365])).
% 3.52/1.54  tff(c_372, plain, (![B_12]: (~m1_subset_1(B_12, k2_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_99, c_369])).
% 3.52/1.54  tff(c_373, plain, (![B_12]: (~m1_subset_1(B_12, k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_60, c_372])).
% 3.52/1.54  tff(c_375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_373, c_100])).
% 3.52/1.54  tff(c_377, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_68])).
% 3.52/1.54  tff(c_376, plain, (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_68])).
% 3.52/1.54  tff(c_398, plain, (![A_111, B_112]: (m1_subset_1(k1_connsp_2(A_111, B_112), k1_zfmisc_1(u1_struct_0(A_111))) | ~m1_subset_1(B_112, u1_struct_0(A_111)) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.52/1.54  tff(c_403, plain, (![B_112]: (m1_subset_1(k1_connsp_2('#skF_1', B_112), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_112, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_398])).
% 3.52/1.54  tff(c_406, plain, (![B_112]: (m1_subset_1(k1_connsp_2('#skF_1', B_112), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_112, k2_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_99, c_403])).
% 3.52/1.54  tff(c_408, plain, (![B_113]: (m1_subset_1(k1_connsp_2('#skF_1', B_113), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_113, k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_60, c_406])).
% 3.52/1.54  tff(c_411, plain, (![A_3, B_113]: (~v1_xboole_0(k2_struct_0('#skF_1')) | ~r2_hidden(A_3, k1_connsp_2('#skF_1', B_113)) | ~m1_subset_1(B_113, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_408, c_6])).
% 3.52/1.54  tff(c_412, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_411])).
% 3.52/1.54  tff(c_431, plain, (![A_125, B_126, C_127]: (v4_orders_2(k3_yellow19(A_125, B_126, C_127)) | ~m1_subset_1(C_127, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_126)))) | ~v13_waybel_0(C_127, k3_yellow_1(B_126)) | ~v2_waybel_0(C_127, k3_yellow_1(B_126)) | v1_xboole_0(C_127) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | v1_xboole_0(B_126) | ~l1_struct_0(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.52/1.54  tff(c_436, plain, (![A_125]: (v4_orders_2(k3_yellow19(A_125, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_125))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_125) | v2_struct_0(A_125))), inference(resolution, [status(thm)], [c_46, c_431])).
% 3.52/1.54  tff(c_443, plain, (![A_125]: (v4_orders_2(k3_yellow19(A_125, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_125))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_125) | v2_struct_0(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_436])).
% 3.52/1.54  tff(c_446, plain, (![A_128]: (v4_orders_2(k3_yellow19(A_128, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_struct_0(A_128) | v2_struct_0(A_128))), inference(negUnitSimplification, [status(thm)], [c_412, c_54, c_443])).
% 3.52/1.54  tff(c_449, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_99, c_446])).
% 3.52/1.54  tff(c_451, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_449])).
% 3.52/1.54  tff(c_452, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_451])).
% 3.52/1.54  tff(c_453, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_452])).
% 3.52/1.54  tff(c_456, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_453])).
% 3.52/1.54  tff(c_460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_456])).
% 3.52/1.54  tff(c_462, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_452])).
% 3.52/1.54  tff(c_461, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_452])).
% 3.52/1.54  tff(c_512, plain, (![A_140, B_141, C_142]: (l1_waybel_0(k3_yellow19(A_140, B_141, C_142), A_140) | ~m1_subset_1(C_142, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_141)))) | ~v13_waybel_0(C_142, k3_yellow_1(B_141)) | ~v2_waybel_0(C_142, k3_yellow_1(B_141)) | v1_xboole_0(C_142) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | v1_xboole_0(B_141) | ~l1_struct_0(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.52/1.54  tff(c_517, plain, (![A_140]: (l1_waybel_0(k3_yellow19(A_140, k2_struct_0('#skF_1'), '#skF_2'), A_140) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_140))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_140) | v2_struct_0(A_140))), inference(resolution, [status(thm)], [c_46, c_512])).
% 3.52/1.54  tff(c_524, plain, (![A_140]: (l1_waybel_0(k3_yellow19(A_140, k2_struct_0('#skF_1'), '#skF_2'), A_140) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_140))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_140) | v2_struct_0(A_140))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_517])).
% 3.52/1.54  tff(c_527, plain, (![A_143]: (l1_waybel_0(k3_yellow19(A_143, k2_struct_0('#skF_1'), '#skF_2'), A_143) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_struct_0(A_143) | v2_struct_0(A_143))), inference(negUnitSimplification, [status(thm)], [c_412, c_54, c_524])).
% 3.52/1.54  tff(c_529, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_99, c_527])).
% 3.52/1.54  tff(c_531, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_462, c_69, c_529])).
% 3.52/1.54  tff(c_532, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_531])).
% 3.52/1.54  tff(c_533, plain, (![A_144, B_145]: (k2_yellow19(A_144, k3_yellow19(A_144, k2_struct_0(A_144), B_145))=B_145 | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_144))))) | ~v13_waybel_0(B_145, k3_yellow_1(k2_struct_0(A_144))) | ~v2_waybel_0(B_145, k3_yellow_1(k2_struct_0(A_144))) | ~v1_subset_1(B_145, u1_struct_0(k3_yellow_1(k2_struct_0(A_144)))) | v1_xboole_0(B_145) | ~l1_struct_0(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.52/1.54  tff(c_538, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_533])).
% 3.52/1.54  tff(c_545, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_462, c_52, c_50, c_48, c_538])).
% 3.52/1.54  tff(c_546, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_545])).
% 3.52/1.54  tff(c_551, plain, (![C_29]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~r1_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_546, c_38])).
% 3.52/1.54  tff(c_558, plain, (![C_29]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~r1_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_461, c_532, c_99, c_551])).
% 3.52/1.54  tff(c_559, plain, (![C_29]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~r1_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_558])).
% 3.52/1.54  tff(c_564, plain, (~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_559])).
% 3.52/1.54  tff(c_569, plain, (![A_154, B_155, C_156]: (v7_waybel_0(k3_yellow19(A_154, B_155, C_156)) | ~m1_subset_1(C_156, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_155)))) | ~v13_waybel_0(C_156, k3_yellow_1(B_155)) | ~v2_waybel_0(C_156, k3_yellow_1(B_155)) | ~v1_subset_1(C_156, u1_struct_0(k3_yellow_1(B_155))) | v1_xboole_0(C_156) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_154))) | v1_xboole_0(B_155) | ~l1_struct_0(A_154) | v2_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.52/1.54  tff(c_574, plain, (![A_154]: (v7_waybel_0(k3_yellow19(A_154, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_154))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_154) | v2_struct_0(A_154))), inference(resolution, [status(thm)], [c_46, c_569])).
% 3.52/1.54  tff(c_581, plain, (![A_154]: (v7_waybel_0(k3_yellow19(A_154, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_154))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_154) | v2_struct_0(A_154))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_574])).
% 3.52/1.54  tff(c_584, plain, (![A_157]: (v7_waybel_0(k3_yellow19(A_157, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_struct_0(A_157) | v2_struct_0(A_157))), inference(negUnitSimplification, [status(thm)], [c_412, c_54, c_581])).
% 3.52/1.54  tff(c_587, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_99, c_584])).
% 3.52/1.54  tff(c_589, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_462, c_69, c_587])).
% 3.52/1.54  tff(c_591, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_564, c_589])).
% 3.52/1.54  tff(c_592, plain, (![C_29]: (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~r1_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_559])).
% 3.52/1.54  tff(c_594, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_592])).
% 3.52/1.54  tff(c_596, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_594, c_30])).
% 3.52/1.54  tff(c_599, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_462, c_69, c_99, c_50, c_48, c_46, c_596])).
% 3.52/1.54  tff(c_601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_412, c_54, c_599])).
% 3.52/1.54  tff(c_603, plain, (~v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_592])).
% 3.52/1.54  tff(c_593, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_559])).
% 3.52/1.54  tff(c_40, plain, (![A_23, B_27, C_29]: (r1_waybel_7(A_23, k2_yellow19(A_23, B_27), C_29) | ~r3_waybel_9(A_23, B_27, C_29) | ~m1_subset_1(C_29, u1_struct_0(A_23)) | ~l1_waybel_0(B_27, A_23) | ~v7_waybel_0(B_27) | ~v4_orders_2(B_27) | v2_struct_0(B_27) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.52/1.54  tff(c_554, plain, (![C_29]: (r1_waybel_7('#skF_1', '#skF_2', C_29) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~m1_subset_1(C_29, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_546, c_40])).
% 3.52/1.54  tff(c_561, plain, (![C_29]: (r1_waybel_7('#skF_1', '#skF_2', C_29) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_461, c_532, c_99, c_554])).
% 3.52/1.54  tff(c_562, plain, (![C_29]: (r1_waybel_7('#skF_1', '#skF_2', C_29) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_561])).
% 3.52/1.54  tff(c_605, plain, (![C_29]: (r1_waybel_7('#skF_1', '#skF_2', C_29) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_593, c_562])).
% 3.52/1.54  tff(c_606, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_605])).
% 3.52/1.54  tff(c_607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_603, c_606])).
% 3.52/1.54  tff(c_610, plain, (![C_158]: (r1_waybel_7('#skF_1', '#skF_2', C_158) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_158) | ~m1_subset_1(C_158, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_605])).
% 3.52/1.54  tff(c_613, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_376, c_610])).
% 3.52/1.54  tff(c_616, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_613])).
% 3.52/1.54  tff(c_618, plain, $false, inference(negUnitSimplification, [status(thm)], [c_377, c_616])).
% 3.52/1.54  tff(c_622, plain, (![A_162, B_163]: (~r2_hidden(A_162, k1_connsp_2('#skF_1', B_163)) | ~m1_subset_1(B_163, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_411])).
% 3.52/1.54  tff(c_626, plain, (![B_12]: (~m1_subset_1(B_12, k2_struct_0('#skF_1')) | ~m1_subset_1(B_12, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_622])).
% 3.52/1.54  tff(c_629, plain, (![B_12]: (~m1_subset_1(B_12, k2_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_99, c_626])).
% 3.52/1.54  tff(c_630, plain, (![B_12]: (~m1_subset_1(B_12, k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_60, c_629])).
% 3.52/1.54  tff(c_632, plain, $false, inference(negUnitSimplification, [status(thm)], [c_630, c_100])).
% 3.52/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.54  
% 3.52/1.54  Inference rules
% 3.52/1.54  ----------------------
% 3.52/1.54  #Ref     : 0
% 3.52/1.54  #Sup     : 95
% 3.52/1.54  #Fact    : 0
% 3.52/1.54  #Define  : 0
% 3.52/1.54  #Split   : 12
% 3.52/1.54  #Chain   : 0
% 3.52/1.54  #Close   : 0
% 3.52/1.54  
% 3.52/1.54  Ordering : KBO
% 3.52/1.54  
% 3.52/1.54  Simplification rules
% 3.52/1.54  ----------------------
% 3.52/1.54  #Subsume      : 17
% 3.52/1.54  #Demod        : 117
% 3.52/1.54  #Tautology    : 16
% 3.52/1.54  #SimpNegUnit  : 41
% 3.52/1.54  #BackRed      : 3
% 3.52/1.54  
% 3.52/1.54  #Partial instantiations: 0
% 3.52/1.54  #Strategies tried      : 1
% 3.52/1.54  
% 3.52/1.54  Timing (in seconds)
% 3.52/1.54  ----------------------
% 3.52/1.54  Preprocessing        : 0.36
% 3.52/1.54  Parsing              : 0.19
% 3.52/1.54  CNF conversion       : 0.02
% 3.52/1.54  Main loop            : 0.38
% 3.52/1.54  Inferencing          : 0.14
% 3.52/1.54  Reduction            : 0.12
% 3.52/1.54  Demodulation         : 0.09
% 3.52/1.54  BG Simplification    : 0.02
% 3.52/1.54  Subsumption          : 0.06
% 3.52/1.54  Abstraction          : 0.02
% 3.52/1.54  MUC search           : 0.00
% 3.52/1.54  Cooper               : 0.00
% 3.52/1.54  Total                : 0.80
% 3.52/1.54  Index Insertion      : 0.00
% 3.52/1.54  Index Deletion       : 0.00
% 3.52/1.54  Index Matching       : 0.00
% 3.52/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
