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
% DateTime   : Thu Dec  3 10:31:37 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  187 (3144 expanded)
%              Number of leaves         :   46 (1132 expanded)
%              Depth                    :   24
%              Number of atoms          :  586 (12679 expanded)
%              Number of equality atoms :   15 ( 700 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k1_connsp_2 > k10_yellow_6 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1

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

tff(k10_yellow_6,type,(
    k10_yellow_6: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

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

tff(r2_waybel_7,type,(
    r2_waybel_7: ( $i * $i * $i ) > $o )).

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
               => ( r2_hidden(C,k10_yellow_6(A,k3_yellow19(A,k2_struct_0(A),B)))
                <=> r2_waybel_7(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow19)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

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
             => ( r2_hidden(C,k10_yellow_6(A,B))
              <=> r2_waybel_7(A,k2_yellow19(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).

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
    ( r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
    | r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_113,plain,(
    r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
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
    ! [C_29,A_23,B_27] :
      ( r2_hidden(C_29,k10_yellow_6(A_23,B_27))
      | ~ r2_waybel_7(A_23,k2_yellow19(A_23,B_27),C_29)
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
      ( r2_hidden(C_29,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_29)
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
      ( r2_hidden(C_29,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_29)
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_197,c_268,c_99,c_290])).

tff(c_298,plain,(
    ! [C_29] :
      ( r2_hidden(C_29,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_29)
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
      | r2_hidden(C_29,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_29)
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
      ( r2_hidden(C_103,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_103)
      | ~ m1_subset_1(C_103,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_328])).

tff(c_62,plain,
    ( ~ r2_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_116,plain,(
    ~ r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_62])).

tff(c_358,plain,
    ( ~ r2_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_355,c_116])).

tff(c_365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_113,c_358])).

tff(c_368,plain,(
    ! [A_104,B_105] :
      ( ~ r2_hidden(A_104,k1_connsp_2('#skF_1',B_105))
      | ~ m1_subset_1(B_105,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_372,plain,(
    ! [B_12] :
      ( ~ m1_subset_1(B_12,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_12,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_368])).

tff(c_375,plain,(
    ! [B_12] :
      ( ~ m1_subset_1(B_12,k2_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_99,c_372])).

tff(c_376,plain,(
    ! [B_12] : ~ m1_subset_1(B_12,k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_375])).

tff(c_378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_376,c_100])).

tff(c_380,plain,(
    ~ r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_379,plain,(
    r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_393,plain,(
    ! [A_108,B_109] :
      ( m1_subset_1(k1_connsp_2(A_108,B_109),k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ m1_subset_1(B_109,u1_struct_0(A_108))
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_398,plain,(
    ! [B_109] :
      ( m1_subset_1(k1_connsp_2('#skF_1',B_109),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_109,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_393])).

tff(c_401,plain,(
    ! [B_109] :
      ( m1_subset_1(k1_connsp_2('#skF_1',B_109),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_109,k2_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_99,c_398])).

tff(c_403,plain,(
    ! [B_110] :
      ( m1_subset_1(k1_connsp_2('#skF_1',B_110),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_110,k2_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_401])).

tff(c_406,plain,(
    ! [A_3,B_110] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ r2_hidden(A_3,k1_connsp_2('#skF_1',B_110))
      | ~ m1_subset_1(B_110,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_403,c_6])).

tff(c_407,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_406])).

tff(c_439,plain,(
    ! [A_128,B_129,C_130] :
      ( v4_orders_2(k3_yellow19(A_128,B_129,C_130))
      | ~ m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_129))))
      | ~ v13_waybel_0(C_130,k3_yellow_1(B_129))
      | ~ v2_waybel_0(C_130,k3_yellow_1(B_129))
      | v1_xboole_0(C_130)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | v1_xboole_0(B_129)
      | ~ l1_struct_0(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_444,plain,(
    ! [A_128] :
      ( v4_orders_2(k3_yellow19(A_128,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_128)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_128)
      | v2_struct_0(A_128) ) ),
    inference(resolution,[status(thm)],[c_46,c_439])).

tff(c_451,plain,(
    ! [A_128] :
      ( v4_orders_2(k3_yellow19(A_128,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_128)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_128)
      | v2_struct_0(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_444])).

tff(c_454,plain,(
    ! [A_131] :
      ( v4_orders_2(k3_yellow19(A_131,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_struct_0(A_131)
      | v2_struct_0(A_131) ) ),
    inference(negUnitSimplification,[status(thm)],[c_407,c_54,c_451])).

tff(c_457,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_454])).

tff(c_459,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_457])).

tff(c_460,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_459])).

tff(c_461,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_460])).

tff(c_464,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_461])).

tff(c_468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_464])).

tff(c_470,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_460])).

tff(c_469,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_460])).

tff(c_519,plain,(
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

tff(c_524,plain,(
    ! [A_140] :
      ( l1_waybel_0(k3_yellow19(A_140,k2_struct_0('#skF_1'),'#skF_2'),A_140)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_140)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_140)
      | v2_struct_0(A_140) ) ),
    inference(resolution,[status(thm)],[c_46,c_519])).

tff(c_531,plain,(
    ! [A_140] :
      ( l1_waybel_0(k3_yellow19(A_140,k2_struct_0('#skF_1'),'#skF_2'),A_140)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_140)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_140)
      | v2_struct_0(A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_524])).

tff(c_534,plain,(
    ! [A_143] :
      ( l1_waybel_0(k3_yellow19(A_143,k2_struct_0('#skF_1'),'#skF_2'),A_143)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_struct_0(A_143)
      | v2_struct_0(A_143) ) ),
    inference(negUnitSimplification,[status(thm)],[c_407,c_54,c_531])).

tff(c_536,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_534])).

tff(c_538,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_69,c_536])).

tff(c_539,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_538])).

tff(c_540,plain,(
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

tff(c_545,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_540])).

tff(c_552,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_52,c_50,c_48,c_545])).

tff(c_553,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_552])).

tff(c_558,plain,(
    ! [C_29] :
      ( r2_hidden(C_29,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_29)
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_38])).

tff(c_565,plain,(
    ! [C_29] :
      ( r2_hidden(C_29,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_29)
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_469,c_539,c_99,c_558])).

tff(c_566,plain,(
    ! [C_29] :
      ( r2_hidden(C_29,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_29)
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_565])).

tff(c_571,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_566])).

tff(c_576,plain,(
    ! [A_152,B_153,C_154] :
      ( v7_waybel_0(k3_yellow19(A_152,B_153,C_154))
      | ~ m1_subset_1(C_154,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_153))))
      | ~ v13_waybel_0(C_154,k3_yellow_1(B_153))
      | ~ v2_waybel_0(C_154,k3_yellow_1(B_153))
      | ~ v1_subset_1(C_154,u1_struct_0(k3_yellow_1(B_153)))
      | v1_xboole_0(C_154)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | v1_xboole_0(B_153)
      | ~ l1_struct_0(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_581,plain,(
    ! [A_152] :
      ( v7_waybel_0(k3_yellow19(A_152,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_152)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_152)
      | v2_struct_0(A_152) ) ),
    inference(resolution,[status(thm)],[c_46,c_576])).

tff(c_588,plain,(
    ! [A_152] :
      ( v7_waybel_0(k3_yellow19(A_152,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_152)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_152)
      | v2_struct_0(A_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_581])).

tff(c_591,plain,(
    ! [A_155] :
      ( v7_waybel_0(k3_yellow19(A_155,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_struct_0(A_155)
      | v2_struct_0(A_155) ) ),
    inference(negUnitSimplification,[status(thm)],[c_407,c_54,c_588])).

tff(c_594,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_591])).

tff(c_596,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_69,c_594])).

tff(c_598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_571,c_596])).

tff(c_599,plain,(
    ! [C_29] :
      ( v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | r2_hidden(C_29,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_29)
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_566])).

tff(c_601,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_599])).

tff(c_606,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_601,c_30])).

tff(c_609,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_69,c_99,c_50,c_48,c_46,c_606])).

tff(c_611,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_407,c_54,c_609])).

tff(c_613,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_599])).

tff(c_600,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_566])).

tff(c_40,plain,(
    ! [A_23,B_27,C_29] :
      ( r2_waybel_7(A_23,k2_yellow19(A_23,B_27),C_29)
      | ~ r2_hidden(C_29,k10_yellow_6(A_23,B_27))
      | ~ m1_subset_1(C_29,u1_struct_0(A_23))
      | ~ l1_waybel_0(B_27,A_23)
      | ~ v7_waybel_0(B_27)
      | ~ v4_orders_2(B_27)
      | v2_struct_0(B_27)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_561,plain,(
    ! [C_29] :
      ( r2_waybel_7('#skF_1','#skF_2',C_29)
      | ~ r2_hidden(C_29,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_40])).

tff(c_568,plain,(
    ! [C_29] :
      ( r2_waybel_7('#skF_1','#skF_2',C_29)
      | ~ r2_hidden(C_29,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_469,c_539,c_99,c_561])).

tff(c_569,plain,(
    ! [C_29] :
      ( r2_waybel_7('#skF_1','#skF_2',C_29)
      | ~ r2_hidden(C_29,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_568])).

tff(c_620,plain,(
    ! [C_29] :
      ( r2_waybel_7('#skF_1','#skF_2',C_29)
      | ~ r2_hidden(C_29,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_569])).

tff(c_622,plain,(
    ! [C_157] :
      ( r2_waybel_7('#skF_1','#skF_2',C_157)
      | ~ r2_hidden(C_157,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_157,k2_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_613,c_620])).

tff(c_628,plain,
    ( r2_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_379,c_622])).

tff(c_632,plain,(
    r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_628])).

tff(c_634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_380,c_632])).

tff(c_638,plain,(
    ! [A_161,B_162] :
      ( ~ r2_hidden(A_161,k1_connsp_2('#skF_1',B_162))
      | ~ m1_subset_1(B_162,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_406])).

tff(c_642,plain,(
    ! [B_12] :
      ( ~ m1_subset_1(B_12,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_12,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_638])).

tff(c_645,plain,(
    ! [B_12] :
      ( ~ m1_subset_1(B_12,k2_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_99,c_642])).

tff(c_646,plain,(
    ! [B_12] : ~ m1_subset_1(B_12,k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_645])).

tff(c_648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_646,c_100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:55:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.55  
% 3.35/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.55  %$ r2_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k1_connsp_2 > k10_yellow_6 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1
% 3.35/1.55  
% 3.35/1.55  %Foreground sorts:
% 3.35/1.55  
% 3.35/1.55  
% 3.35/1.55  %Background operators:
% 3.35/1.55  
% 3.35/1.55  
% 3.35/1.55  %Foreground operators:
% 3.35/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.35/1.55  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.35/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.55  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.35/1.55  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 3.35/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.35/1.55  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.35/1.55  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.35/1.55  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 3.35/1.55  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.35/1.55  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 3.35/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.35/1.55  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.35/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.35/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.35/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.35/1.55  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.35/1.55  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.35/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.35/1.55  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.35/1.55  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.35/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.55  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.35/1.55  tff(r2_waybel_7, type, r2_waybel_7: ($i * $i * $i) > $o).
% 3.35/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.55  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.35/1.55  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.35/1.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.35/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.35/1.55  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.35/1.55  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.35/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.35/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.35/1.55  
% 3.49/1.58  tff(f_221, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, k3_yellow19(A, k2_struct_0(A), B))) <=> r2_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_yellow19)).
% 3.49/1.58  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.49/1.58  tff(f_40, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.49/1.58  tff(f_67, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_connsp_2)).
% 3.49/1.58  tff(f_55, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 3.49/1.58  tff(f_36, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.49/1.58  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.49/1.58  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.49/1.58  tff(f_123, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_yellow19)).
% 3.49/1.58  tff(f_95, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 3.49/1.58  tff(f_194, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 3.49/1.58  tff(f_175, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, B)) <=> r2_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow19)).
% 3.49/1.58  tff(f_151, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow19)).
% 3.49/1.58  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.49/1.58  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.49/1.58  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.49/1.58  tff(c_10, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.49/1.58  tff(c_90, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.49/1.58  tff(c_95, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_pre_topc(A_42))), inference(resolution, [status(thm)], [c_10, c_90])).
% 3.49/1.58  tff(c_99, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_95])).
% 3.49/1.58  tff(c_14, plain, (![B_12, A_10]: (r2_hidden(B_12, k1_connsp_2(A_10, B_12)) | ~m1_subset_1(B_12, u1_struct_0(A_10)) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.49/1.58  tff(c_44, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.49/1.58  tff(c_100, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_44])).
% 3.49/1.58  tff(c_68, plain, (r2_hidden('#skF_3', k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | r2_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.49/1.58  tff(c_113, plain, (r2_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 3.49/1.58  tff(c_122, plain, (![A_50, B_51]: (m1_subset_1(k1_connsp_2(A_50, B_51), k1_zfmisc_1(u1_struct_0(A_50))) | ~m1_subset_1(B_51, u1_struct_0(A_50)) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.49/1.58  tff(c_127, plain, (![B_51]: (m1_subset_1(k1_connsp_2('#skF_1', B_51), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_51, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_122])).
% 3.49/1.58  tff(c_130, plain, (![B_51]: (m1_subset_1(k1_connsp_2('#skF_1', B_51), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_51, k2_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_99, c_127])).
% 3.49/1.58  tff(c_132, plain, (![B_52]: (m1_subset_1(k1_connsp_2('#skF_1', B_52), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_52, k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_60, c_130])).
% 3.49/1.58  tff(c_6, plain, (![C_5, B_4, A_3]: (~v1_xboole_0(C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.49/1.58  tff(c_135, plain, (![A_3, B_52]: (~v1_xboole_0(k2_struct_0('#skF_1')) | ~r2_hidden(A_3, k1_connsp_2('#skF_1', B_52)) | ~m1_subset_1(B_52, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_132, c_6])).
% 3.49/1.58  tff(c_136, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_135])).
% 3.49/1.58  tff(c_54, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.49/1.58  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.49/1.58  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.49/1.58  tff(c_69, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.49/1.58  tff(c_50, plain, (v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.49/1.58  tff(c_48, plain, (v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.49/1.58  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.49/1.58  tff(c_167, plain, (![A_67, B_68, C_69]: (v4_orders_2(k3_yellow19(A_67, B_68, C_69)) | ~m1_subset_1(C_69, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_68)))) | ~v13_waybel_0(C_69, k3_yellow_1(B_68)) | ~v2_waybel_0(C_69, k3_yellow_1(B_68)) | v1_xboole_0(C_69) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | v1_xboole_0(B_68) | ~l1_struct_0(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.49/1.58  tff(c_172, plain, (![A_67]: (v4_orders_2(k3_yellow19(A_67, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_67))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_67) | v2_struct_0(A_67))), inference(resolution, [status(thm)], [c_46, c_167])).
% 3.49/1.58  tff(c_179, plain, (![A_67]: (v4_orders_2(k3_yellow19(A_67, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_67))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_67) | v2_struct_0(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_172])).
% 3.49/1.58  tff(c_182, plain, (![A_70]: (v4_orders_2(k3_yellow19(A_70, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_struct_0(A_70) | v2_struct_0(A_70))), inference(negUnitSimplification, [status(thm)], [c_136, c_54, c_179])).
% 3.49/1.58  tff(c_185, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_99, c_182])).
% 3.49/1.58  tff(c_187, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_185])).
% 3.49/1.58  tff(c_188, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_187])).
% 3.49/1.58  tff(c_189, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_188])).
% 3.49/1.58  tff(c_192, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_189])).
% 3.49/1.58  tff(c_196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_192])).
% 3.49/1.58  tff(c_198, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_188])).
% 3.49/1.58  tff(c_197, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_188])).
% 3.49/1.58  tff(c_248, plain, (![A_82, B_83, C_84]: (l1_waybel_0(k3_yellow19(A_82, B_83, C_84), A_82) | ~m1_subset_1(C_84, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_83)))) | ~v13_waybel_0(C_84, k3_yellow_1(B_83)) | ~v2_waybel_0(C_84, k3_yellow_1(B_83)) | v1_xboole_0(C_84) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | v1_xboole_0(B_83) | ~l1_struct_0(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.49/1.58  tff(c_253, plain, (![A_82]: (l1_waybel_0(k3_yellow19(A_82, k2_struct_0('#skF_1'), '#skF_2'), A_82) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_82))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_82) | v2_struct_0(A_82))), inference(resolution, [status(thm)], [c_46, c_248])).
% 3.49/1.58  tff(c_260, plain, (![A_82]: (l1_waybel_0(k3_yellow19(A_82, k2_struct_0('#skF_1'), '#skF_2'), A_82) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_82))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_82) | v2_struct_0(A_82))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_253])).
% 3.49/1.58  tff(c_263, plain, (![A_85]: (l1_waybel_0(k3_yellow19(A_85, k2_struct_0('#skF_1'), '#skF_2'), A_85) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_struct_0(A_85) | v2_struct_0(A_85))), inference(negUnitSimplification, [status(thm)], [c_136, c_54, c_260])).
% 3.49/1.58  tff(c_265, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_99, c_263])).
% 3.49/1.58  tff(c_267, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_69, c_265])).
% 3.49/1.58  tff(c_268, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_267])).
% 3.49/1.58  tff(c_52, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.49/1.58  tff(c_272, plain, (![A_92, B_93]: (k2_yellow19(A_92, k3_yellow19(A_92, k2_struct_0(A_92), B_93))=B_93 | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_92))))) | ~v13_waybel_0(B_93, k3_yellow_1(k2_struct_0(A_92))) | ~v2_waybel_0(B_93, k3_yellow_1(k2_struct_0(A_92))) | ~v1_subset_1(B_93, u1_struct_0(k3_yellow_1(k2_struct_0(A_92)))) | v1_xboole_0(B_93) | ~l1_struct_0(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.49/1.58  tff(c_277, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_272])).
% 3.49/1.58  tff(c_284, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_52, c_50, c_48, c_277])).
% 3.49/1.58  tff(c_285, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_284])).
% 3.49/1.58  tff(c_38, plain, (![C_29, A_23, B_27]: (r2_hidden(C_29, k10_yellow_6(A_23, B_27)) | ~r2_waybel_7(A_23, k2_yellow19(A_23, B_27), C_29) | ~m1_subset_1(C_29, u1_struct_0(A_23)) | ~l1_waybel_0(B_27, A_23) | ~v7_waybel_0(B_27) | ~v4_orders_2(B_27) | v2_struct_0(B_27) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.49/1.58  tff(c_290, plain, (![C_29]: (r2_hidden(C_29, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_285, c_38])).
% 3.49/1.58  tff(c_297, plain, (![C_29]: (r2_hidden(C_29, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_197, c_268, c_99, c_290])).
% 3.49/1.58  tff(c_298, plain, (![C_29]: (r2_hidden(C_29, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_297])).
% 3.49/1.58  tff(c_303, plain, (~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_298])).
% 3.49/1.58  tff(c_305, plain, (![A_96, B_97, C_98]: (v7_waybel_0(k3_yellow19(A_96, B_97, C_98)) | ~m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_97)))) | ~v13_waybel_0(C_98, k3_yellow_1(B_97)) | ~v2_waybel_0(C_98, k3_yellow_1(B_97)) | ~v1_subset_1(C_98, u1_struct_0(k3_yellow_1(B_97))) | v1_xboole_0(C_98) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | v1_xboole_0(B_97) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.49/1.58  tff(c_310, plain, (![A_96]: (v7_waybel_0(k3_yellow19(A_96, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_96))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(resolution, [status(thm)], [c_46, c_305])).
% 3.49/1.58  tff(c_317, plain, (![A_96]: (v7_waybel_0(k3_yellow19(A_96, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_96))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_310])).
% 3.49/1.58  tff(c_320, plain, (![A_99]: (v7_waybel_0(k3_yellow19(A_99, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_struct_0(A_99) | v2_struct_0(A_99))), inference(negUnitSimplification, [status(thm)], [c_136, c_54, c_317])).
% 3.49/1.58  tff(c_323, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_99, c_320])).
% 3.49/1.58  tff(c_325, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_69, c_323])).
% 3.49/1.58  tff(c_327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_303, c_325])).
% 3.49/1.58  tff(c_328, plain, (![C_29]: (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | r2_hidden(C_29, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_298])).
% 3.49/1.58  tff(c_330, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_328])).
% 3.49/1.58  tff(c_30, plain, (![A_17, B_18, C_19]: (~v2_struct_0(k3_yellow19(A_17, B_18, C_19)) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_18)))) | ~v13_waybel_0(C_19, k3_yellow_1(B_18)) | ~v2_waybel_0(C_19, k3_yellow_1(B_18)) | v1_xboole_0(C_19) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | v1_xboole_0(B_18) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.49/1.58  tff(c_347, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_330, c_30])).
% 3.49/1.58  tff(c_350, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_69, c_99, c_50, c_48, c_46, c_347])).
% 3.49/1.58  tff(c_352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_136, c_54, c_350])).
% 3.49/1.58  tff(c_355, plain, (![C_103]: (r2_hidden(C_103, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_103) | ~m1_subset_1(C_103, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_328])).
% 3.49/1.58  tff(c_62, plain, (~r2_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.49/1.58  tff(c_116, plain, (~r2_hidden('#skF_3', k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_62])).
% 3.49/1.58  tff(c_358, plain, (~r2_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_355, c_116])).
% 3.49/1.58  tff(c_365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_113, c_358])).
% 3.49/1.58  tff(c_368, plain, (![A_104, B_105]: (~r2_hidden(A_104, k1_connsp_2('#skF_1', B_105)) | ~m1_subset_1(B_105, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_135])).
% 3.49/1.58  tff(c_372, plain, (![B_12]: (~m1_subset_1(B_12, k2_struct_0('#skF_1')) | ~m1_subset_1(B_12, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_368])).
% 3.49/1.58  tff(c_375, plain, (![B_12]: (~m1_subset_1(B_12, k2_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_99, c_372])).
% 3.49/1.58  tff(c_376, plain, (![B_12]: (~m1_subset_1(B_12, k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_60, c_375])).
% 3.49/1.58  tff(c_378, plain, $false, inference(negUnitSimplification, [status(thm)], [c_376, c_100])).
% 3.49/1.58  tff(c_380, plain, (~r2_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_68])).
% 3.49/1.58  tff(c_379, plain, (r2_hidden('#skF_3', k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(splitRight, [status(thm)], [c_68])).
% 3.49/1.58  tff(c_393, plain, (![A_108, B_109]: (m1_subset_1(k1_connsp_2(A_108, B_109), k1_zfmisc_1(u1_struct_0(A_108))) | ~m1_subset_1(B_109, u1_struct_0(A_108)) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.49/1.58  tff(c_398, plain, (![B_109]: (m1_subset_1(k1_connsp_2('#skF_1', B_109), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_109, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_393])).
% 3.49/1.58  tff(c_401, plain, (![B_109]: (m1_subset_1(k1_connsp_2('#skF_1', B_109), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_109, k2_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_99, c_398])).
% 3.49/1.58  tff(c_403, plain, (![B_110]: (m1_subset_1(k1_connsp_2('#skF_1', B_110), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_110, k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_60, c_401])).
% 3.49/1.58  tff(c_406, plain, (![A_3, B_110]: (~v1_xboole_0(k2_struct_0('#skF_1')) | ~r2_hidden(A_3, k1_connsp_2('#skF_1', B_110)) | ~m1_subset_1(B_110, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_403, c_6])).
% 3.49/1.58  tff(c_407, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_406])).
% 3.49/1.58  tff(c_439, plain, (![A_128, B_129, C_130]: (v4_orders_2(k3_yellow19(A_128, B_129, C_130)) | ~m1_subset_1(C_130, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_129)))) | ~v13_waybel_0(C_130, k3_yellow_1(B_129)) | ~v2_waybel_0(C_130, k3_yellow_1(B_129)) | v1_xboole_0(C_130) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | v1_xboole_0(B_129) | ~l1_struct_0(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.49/1.58  tff(c_444, plain, (![A_128]: (v4_orders_2(k3_yellow19(A_128, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_128))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_128) | v2_struct_0(A_128))), inference(resolution, [status(thm)], [c_46, c_439])).
% 3.49/1.58  tff(c_451, plain, (![A_128]: (v4_orders_2(k3_yellow19(A_128, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_128))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_128) | v2_struct_0(A_128))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_444])).
% 3.49/1.58  tff(c_454, plain, (![A_131]: (v4_orders_2(k3_yellow19(A_131, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_struct_0(A_131) | v2_struct_0(A_131))), inference(negUnitSimplification, [status(thm)], [c_407, c_54, c_451])).
% 3.49/1.58  tff(c_457, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_99, c_454])).
% 3.49/1.58  tff(c_459, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_457])).
% 3.49/1.58  tff(c_460, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_459])).
% 3.49/1.58  tff(c_461, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_460])).
% 3.49/1.58  tff(c_464, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_461])).
% 3.49/1.58  tff(c_468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_464])).
% 3.49/1.58  tff(c_470, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_460])).
% 3.49/1.58  tff(c_469, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_460])).
% 3.49/1.58  tff(c_519, plain, (![A_140, B_141, C_142]: (l1_waybel_0(k3_yellow19(A_140, B_141, C_142), A_140) | ~m1_subset_1(C_142, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_141)))) | ~v13_waybel_0(C_142, k3_yellow_1(B_141)) | ~v2_waybel_0(C_142, k3_yellow_1(B_141)) | v1_xboole_0(C_142) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | v1_xboole_0(B_141) | ~l1_struct_0(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.49/1.58  tff(c_524, plain, (![A_140]: (l1_waybel_0(k3_yellow19(A_140, k2_struct_0('#skF_1'), '#skF_2'), A_140) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_140))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_140) | v2_struct_0(A_140))), inference(resolution, [status(thm)], [c_46, c_519])).
% 3.49/1.58  tff(c_531, plain, (![A_140]: (l1_waybel_0(k3_yellow19(A_140, k2_struct_0('#skF_1'), '#skF_2'), A_140) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_140))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_140) | v2_struct_0(A_140))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_524])).
% 3.49/1.58  tff(c_534, plain, (![A_143]: (l1_waybel_0(k3_yellow19(A_143, k2_struct_0('#skF_1'), '#skF_2'), A_143) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_struct_0(A_143) | v2_struct_0(A_143))), inference(negUnitSimplification, [status(thm)], [c_407, c_54, c_531])).
% 3.49/1.58  tff(c_536, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_99, c_534])).
% 3.49/1.58  tff(c_538, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_470, c_69, c_536])).
% 3.49/1.58  tff(c_539, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_538])).
% 3.49/1.58  tff(c_540, plain, (![A_144, B_145]: (k2_yellow19(A_144, k3_yellow19(A_144, k2_struct_0(A_144), B_145))=B_145 | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_144))))) | ~v13_waybel_0(B_145, k3_yellow_1(k2_struct_0(A_144))) | ~v2_waybel_0(B_145, k3_yellow_1(k2_struct_0(A_144))) | ~v1_subset_1(B_145, u1_struct_0(k3_yellow_1(k2_struct_0(A_144)))) | v1_xboole_0(B_145) | ~l1_struct_0(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.49/1.58  tff(c_545, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_540])).
% 3.49/1.58  tff(c_552, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_470, c_52, c_50, c_48, c_545])).
% 3.49/1.58  tff(c_553, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_552])).
% 3.49/1.58  tff(c_558, plain, (![C_29]: (r2_hidden(C_29, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_553, c_38])).
% 3.49/1.58  tff(c_565, plain, (![C_29]: (r2_hidden(C_29, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_469, c_539, c_99, c_558])).
% 3.49/1.58  tff(c_566, plain, (![C_29]: (r2_hidden(C_29, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_565])).
% 3.49/1.58  tff(c_571, plain, (~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_566])).
% 3.49/1.58  tff(c_576, plain, (![A_152, B_153, C_154]: (v7_waybel_0(k3_yellow19(A_152, B_153, C_154)) | ~m1_subset_1(C_154, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_153)))) | ~v13_waybel_0(C_154, k3_yellow_1(B_153)) | ~v2_waybel_0(C_154, k3_yellow_1(B_153)) | ~v1_subset_1(C_154, u1_struct_0(k3_yellow_1(B_153))) | v1_xboole_0(C_154) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | v1_xboole_0(B_153) | ~l1_struct_0(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.49/1.58  tff(c_581, plain, (![A_152]: (v7_waybel_0(k3_yellow19(A_152, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_152))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_152) | v2_struct_0(A_152))), inference(resolution, [status(thm)], [c_46, c_576])).
% 3.49/1.58  tff(c_588, plain, (![A_152]: (v7_waybel_0(k3_yellow19(A_152, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_152))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_152) | v2_struct_0(A_152))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_581])).
% 3.49/1.58  tff(c_591, plain, (![A_155]: (v7_waybel_0(k3_yellow19(A_155, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_struct_0(A_155) | v2_struct_0(A_155))), inference(negUnitSimplification, [status(thm)], [c_407, c_54, c_588])).
% 3.49/1.58  tff(c_594, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_99, c_591])).
% 3.49/1.58  tff(c_596, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_470, c_69, c_594])).
% 3.49/1.58  tff(c_598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_571, c_596])).
% 3.49/1.58  tff(c_599, plain, (![C_29]: (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | r2_hidden(C_29, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_566])).
% 3.49/1.58  tff(c_601, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_599])).
% 3.49/1.58  tff(c_606, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_601, c_30])).
% 3.49/1.58  tff(c_609, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_470, c_69, c_99, c_50, c_48, c_46, c_606])).
% 3.49/1.58  tff(c_611, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_407, c_54, c_609])).
% 3.49/1.58  tff(c_613, plain, (~v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_599])).
% 3.49/1.58  tff(c_600, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_566])).
% 3.49/1.58  tff(c_40, plain, (![A_23, B_27, C_29]: (r2_waybel_7(A_23, k2_yellow19(A_23, B_27), C_29) | ~r2_hidden(C_29, k10_yellow_6(A_23, B_27)) | ~m1_subset_1(C_29, u1_struct_0(A_23)) | ~l1_waybel_0(B_27, A_23) | ~v7_waybel_0(B_27) | ~v4_orders_2(B_27) | v2_struct_0(B_27) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.49/1.58  tff(c_561, plain, (![C_29]: (r2_waybel_7('#skF_1', '#skF_2', C_29) | ~r2_hidden(C_29, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_29, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_553, c_40])).
% 3.49/1.58  tff(c_568, plain, (![C_29]: (r2_waybel_7('#skF_1', '#skF_2', C_29) | ~r2_hidden(C_29, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_469, c_539, c_99, c_561])).
% 3.49/1.58  tff(c_569, plain, (![C_29]: (r2_waybel_7('#skF_1', '#skF_2', C_29) | ~r2_hidden(C_29, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_568])).
% 3.49/1.58  tff(c_620, plain, (![C_29]: (r2_waybel_7('#skF_1', '#skF_2', C_29) | ~r2_hidden(C_29, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_600, c_569])).
% 3.49/1.58  tff(c_622, plain, (![C_157]: (r2_waybel_7('#skF_1', '#skF_2', C_157) | ~r2_hidden(C_157, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_157, k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_613, c_620])).
% 3.49/1.58  tff(c_628, plain, (r2_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_379, c_622])).
% 3.49/1.58  tff(c_632, plain, (r2_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_628])).
% 3.49/1.58  tff(c_634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_380, c_632])).
% 3.49/1.58  tff(c_638, plain, (![A_161, B_162]: (~r2_hidden(A_161, k1_connsp_2('#skF_1', B_162)) | ~m1_subset_1(B_162, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_406])).
% 3.49/1.58  tff(c_642, plain, (![B_12]: (~m1_subset_1(B_12, k2_struct_0('#skF_1')) | ~m1_subset_1(B_12, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_638])).
% 3.49/1.58  tff(c_645, plain, (![B_12]: (~m1_subset_1(B_12, k2_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_99, c_642])).
% 3.49/1.58  tff(c_646, plain, (![B_12]: (~m1_subset_1(B_12, k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_60, c_645])).
% 3.49/1.58  tff(c_648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_646, c_100])).
% 3.49/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.58  
% 3.49/1.58  Inference rules
% 3.49/1.58  ----------------------
% 3.49/1.58  #Ref     : 0
% 3.49/1.58  #Sup     : 99
% 3.49/1.58  #Fact    : 0
% 3.49/1.58  #Define  : 0
% 3.49/1.58  #Split   : 13
% 3.49/1.58  #Chain   : 0
% 3.49/1.58  #Close   : 0
% 3.49/1.58  
% 3.49/1.58  Ordering : KBO
% 3.49/1.58  
% 3.49/1.58  Simplification rules
% 3.49/1.58  ----------------------
% 3.49/1.58  #Subsume      : 16
% 3.49/1.58  #Demod        : 118
% 3.49/1.58  #Tautology    : 17
% 3.49/1.58  #SimpNegUnit  : 41
% 3.49/1.58  #BackRed      : 3
% 3.49/1.58  
% 3.49/1.58  #Partial instantiations: 0
% 3.49/1.58  #Strategies tried      : 1
% 3.49/1.58  
% 3.49/1.58  Timing (in seconds)
% 3.49/1.58  ----------------------
% 3.49/1.59  Preprocessing        : 0.38
% 3.49/1.59  Parsing              : 0.21
% 3.49/1.59  CNF conversion       : 0.02
% 3.49/1.59  Main loop            : 0.38
% 3.49/1.59  Inferencing          : 0.14
% 3.49/1.59  Reduction            : 0.12
% 3.49/1.59  Demodulation         : 0.08
% 3.49/1.59  BG Simplification    : 0.03
% 3.49/1.59  Subsumption          : 0.07
% 3.49/1.59  Abstraction          : 0.02
% 3.49/1.59  MUC search           : 0.00
% 3.49/1.59  Cooper               : 0.00
% 3.49/1.59  Total                : 0.82
% 3.49/1.59  Index Insertion      : 0.00
% 3.49/1.59  Index Deletion       : 0.00
% 3.49/1.59  Index Matching       : 0.00
% 3.49/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
