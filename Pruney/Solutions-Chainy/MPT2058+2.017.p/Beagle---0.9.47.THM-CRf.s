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
% DateTime   : Thu Dec  3 10:31:35 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :  180 (1903 expanded)
%              Number of leaves         :   42 ( 681 expanded)
%              Depth                    :   20
%              Number of atoms          :  568 (8741 expanded)
%              Number of equality atoms :   15 ( 308 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow19)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).

tff(f_45,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).

tff(c_64,plain,
    ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3')
    | r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_102,plain,(
    r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_8,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_86,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_91,plain,(
    ! [A_35] :
      ( u1_struct_0(A_35) = k2_struct_0(A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(resolution,[status(thm)],[c_8,c_86])).

tff(c_95,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_91])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_96,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_40])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_46,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_44,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_111,plain,(
    ! [A_46,B_47,C_48] :
      ( v3_orders_2(k3_yellow19(A_46,B_47,C_48))
      | ~ m1_subset_1(C_48,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_47))))
      | ~ v13_waybel_0(C_48,k3_yellow_1(B_47))
      | ~ v2_waybel_0(C_48,k3_yellow_1(B_47))
      | v1_xboole_0(C_48)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | v1_xboole_0(B_47)
      | ~ l1_struct_0(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_113,plain,(
    ! [A_46] :
      ( v3_orders_2(k3_yellow19(A_46,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_46)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_46)
      | v2_struct_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_42,c_111])).

tff(c_119,plain,(
    ! [A_46] :
      ( v3_orders_2(k3_yellow19(A_46,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_46)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_46)
      | v2_struct_0(A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_113])).

tff(c_120,plain,(
    ! [A_46] :
      ( v3_orders_2(k3_yellow19(A_46,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_46)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_46)
      | v2_struct_0(A_46) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_119])).

tff(c_122,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_10,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(k2_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_125,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_122,c_10])).

tff(c_128,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_125])).

tff(c_131,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_128])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_131])).

tff(c_137,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_65,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_138,plain,(
    ! [A_49] :
      ( v3_orders_2(k3_yellow19(A_49,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_struct_0(A_49)
      | v2_struct_0(A_49) ) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_141,plain,
    ( v3_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_138])).

tff(c_143,plain,
    ( v3_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_141])).

tff(c_144,plain,
    ( v3_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_143])).

tff(c_145,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_148,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_145])).

tff(c_152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_148])).

tff(c_154,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_160,plain,(
    ! [A_50,B_51,C_52] :
      ( v4_orders_2(k3_yellow19(A_50,B_51,C_52))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_51))))
      | ~ v13_waybel_0(C_52,k3_yellow_1(B_51))
      | ~ v2_waybel_0(C_52,k3_yellow_1(B_51))
      | v1_xboole_0(C_52)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | v1_xboole_0(B_51)
      | ~ l1_struct_0(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_162,plain,(
    ! [A_50] :
      ( v4_orders_2(k3_yellow19(A_50,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_50)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_50)
      | v2_struct_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_42,c_160])).

tff(c_168,plain,(
    ! [A_50] :
      ( v4_orders_2(k3_yellow19(A_50,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_50)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_50)
      | v2_struct_0(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_162])).

tff(c_171,plain,(
    ! [A_53] :
      ( v4_orders_2(k3_yellow19(A_53,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_struct_0(A_53)
      | v2_struct_0(A_53) ) ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_50,c_168])).

tff(c_174,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_171])).

tff(c_176,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_65,c_174])).

tff(c_177,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_176])).

tff(c_195,plain,(
    ! [A_58,B_59,C_60] :
      ( l1_waybel_0(k3_yellow19(A_58,B_59,C_60),A_58)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_59))))
      | ~ v13_waybel_0(C_60,k3_yellow_1(B_59))
      | ~ v2_waybel_0(C_60,k3_yellow_1(B_59))
      | v1_xboole_0(C_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | v1_xboole_0(B_59)
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_197,plain,(
    ! [A_58] :
      ( l1_waybel_0(k3_yellow19(A_58,k2_struct_0('#skF_1'),'#skF_2'),A_58)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_58)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_42,c_195])).

tff(c_203,plain,(
    ! [A_58] :
      ( l1_waybel_0(k3_yellow19(A_58,k2_struct_0('#skF_1'),'#skF_2'),A_58)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_58)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_197])).

tff(c_206,plain,(
    ! [A_61] :
      ( l1_waybel_0(k3_yellow19(A_61,k2_struct_0('#skF_1'),'#skF_2'),A_61)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_struct_0(A_61)
      | v2_struct_0(A_61) ) ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_50,c_203])).

tff(c_208,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_206])).

tff(c_210,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_65,c_208])).

tff(c_211,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_210])).

tff(c_48,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_213,plain,(
    ! [A_64,B_65] :
      ( k2_yellow19(A_64,k3_yellow19(A_64,k2_struct_0(A_64),B_65)) = B_65
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_64)))))
      | ~ v13_waybel_0(B_65,k3_yellow_1(k2_struct_0(A_64)))
      | ~ v2_waybel_0(B_65,k3_yellow_1(k2_struct_0(A_64)))
      | ~ v1_subset_1(B_65,u1_struct_0(k3_yellow_1(k2_struct_0(A_64))))
      | v1_xboole_0(B_65)
      | ~ l1_struct_0(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_215,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_213])).

tff(c_221,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_48,c_46,c_44,c_215])).

tff(c_222,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_221])).

tff(c_34,plain,(
    ! [A_16,B_20,C_22] :
      ( r3_waybel_9(A_16,B_20,C_22)
      | ~ r1_waybel_7(A_16,k2_yellow19(A_16,B_20),C_22)
      | ~ m1_subset_1(C_22,u1_struct_0(A_16))
      | ~ l1_waybel_0(B_20,A_16)
      | ~ v7_waybel_0(B_20)
      | ~ v4_orders_2(B_20)
      | v2_struct_0(B_20)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_227,plain,(
    ! [C_22] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_22)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_22)
      | ~ m1_subset_1(C_22,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_34])).

tff(c_234,plain,(
    ! [C_22] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_22)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_22)
      | ~ m1_subset_1(C_22,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_177,c_211,c_95,c_227])).

tff(c_235,plain,(
    ! [C_22] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_22)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_22)
      | ~ m1_subset_1(C_22,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_234])).

tff(c_240,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_235])).

tff(c_244,plain,(
    ! [A_72,B_73,C_74] :
      ( v7_waybel_0(k3_yellow19(A_72,B_73,C_74))
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_73))))
      | ~ v13_waybel_0(C_74,k3_yellow_1(B_73))
      | ~ v2_waybel_0(C_74,k3_yellow_1(B_73))
      | ~ v1_subset_1(C_74,u1_struct_0(k3_yellow_1(B_73)))
      | v1_xboole_0(C_74)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | v1_xboole_0(B_73)
      | ~ l1_struct_0(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_246,plain,(
    ! [A_72] :
      ( v7_waybel_0(k3_yellow19(A_72,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_72)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_72)
      | v2_struct_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_42,c_244])).

tff(c_252,plain,(
    ! [A_72] :
      ( v7_waybel_0(k3_yellow19(A_72,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_72)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_72)
      | v2_struct_0(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_246])).

tff(c_255,plain,(
    ! [A_75] :
      ( v7_waybel_0(k3_yellow19(A_75,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_struct_0(A_75)
      | v2_struct_0(A_75) ) ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_50,c_252])).

tff(c_258,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_255])).

tff(c_260,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_65,c_258])).

tff(c_262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_240,c_260])).

tff(c_263,plain,(
    ! [C_22] :
      ( v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_22)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_22)
      | ~ m1_subset_1(C_22,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_283,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_26,plain,(
    ! [A_10,B_11,C_12] :
      ( ~ v2_struct_0(k3_yellow19(A_10,B_11,C_12))
      | ~ m1_subset_1(C_12,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_11))))
      | ~ v13_waybel_0(C_12,k3_yellow_1(B_11))
      | ~ v2_waybel_0(C_12,k3_yellow_1(B_11))
      | v1_xboole_0(C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_10)))
      | v1_xboole_0(B_11)
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_288,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_283,c_26])).

tff(c_291,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_65,c_95,c_46,c_44,c_42,c_288])).

tff(c_293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_137,c_50,c_291])).

tff(c_296,plain,(
    ! [C_80] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_80)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_80)
      | ~ m1_subset_1(C_80,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_58,plain,
    ( ~ r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_103,plain,(
    ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_299,plain,
    ( ~ r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_296,c_103])).

tff(c_303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_102,c_299])).

tff(c_304,plain,(
    ~ r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_304])).

tff(c_309,plain,(
    ~ r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_308,plain,(
    r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_318,plain,(
    ! [A_87,B_88,C_89] :
      ( v4_orders_2(k3_yellow19(A_87,B_88,C_89))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_88))))
      | ~ v13_waybel_0(C_89,k3_yellow_1(B_88))
      | ~ v2_waybel_0(C_89,k3_yellow_1(B_88))
      | v1_xboole_0(C_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | v1_xboole_0(B_88)
      | ~ l1_struct_0(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_320,plain,(
    ! [A_87] :
      ( v4_orders_2(k3_yellow19(A_87,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_87)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_87)
      | v2_struct_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_42,c_318])).

tff(c_326,plain,(
    ! [A_87] :
      ( v4_orders_2(k3_yellow19(A_87,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_87)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_87)
      | v2_struct_0(A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_320])).

tff(c_327,plain,(
    ! [A_87] :
      ( v4_orders_2(k3_yellow19(A_87,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_87)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_87)
      | v2_struct_0(A_87) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_326])).

tff(c_329,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_327])).

tff(c_332,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_329,c_10])).

tff(c_335,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_332])).

tff(c_338,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_335])).

tff(c_342,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_338])).

tff(c_344,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_346,plain,(
    ! [A_93] :
      ( v4_orders_2(k3_yellow19(A_93,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_349,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_346])).

tff(c_351,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_349])).

tff(c_352,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_351])).

tff(c_353,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_352])).

tff(c_356,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_353])).

tff(c_360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_356])).

tff(c_362,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_352])).

tff(c_424,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_426,plain,(
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
    inference(resolution,[status(thm)],[c_42,c_424])).

tff(c_432,plain,(
    ! [A_114] :
      ( v7_waybel_0(k3_yellow19(A_114,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_114)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_114)
      | v2_struct_0(A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_426])).

tff(c_462,plain,(
    ! [A_119] :
      ( v7_waybel_0(k3_yellow19(A_119,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_struct_0(A_119)
      | v2_struct_0(A_119) ) ),
    inference(negUnitSimplification,[status(thm)],[c_344,c_50,c_432])).

tff(c_465,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_462])).

tff(c_467,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_65,c_465])).

tff(c_468,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_467])).

tff(c_361,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_352])).

tff(c_397,plain,(
    ! [A_101,B_102,C_103] :
      ( l1_waybel_0(k3_yellow19(A_101,B_102,C_103),A_101)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_102))))
      | ~ v13_waybel_0(C_103,k3_yellow_1(B_102))
      | ~ v2_waybel_0(C_103,k3_yellow_1(B_102))
      | v1_xboole_0(C_103)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | v1_xboole_0(B_102)
      | ~ l1_struct_0(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_399,plain,(
    ! [A_101] :
      ( l1_waybel_0(k3_yellow19(A_101,k2_struct_0('#skF_1'),'#skF_2'),A_101)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_101)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_101)
      | v2_struct_0(A_101) ) ),
    inference(resolution,[status(thm)],[c_42,c_397])).

tff(c_405,plain,(
    ! [A_101] :
      ( l1_waybel_0(k3_yellow19(A_101,k2_struct_0('#skF_1'),'#skF_2'),A_101)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_101)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_101)
      | v2_struct_0(A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_399])).

tff(c_414,plain,(
    ! [A_105] :
      ( l1_waybel_0(k3_yellow19(A_105,k2_struct_0('#skF_1'),'#skF_2'),A_105)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_struct_0(A_105)
      | v2_struct_0(A_105) ) ),
    inference(negUnitSimplification,[status(thm)],[c_344,c_50,c_405])).

tff(c_416,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_414])).

tff(c_418,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_65,c_416])).

tff(c_419,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_418])).

tff(c_435,plain,(
    ! [A_117,B_118] :
      ( k2_yellow19(A_117,k3_yellow19(A_117,k2_struct_0(A_117),B_118)) = B_118
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_117)))))
      | ~ v13_waybel_0(B_118,k3_yellow_1(k2_struct_0(A_117)))
      | ~ v2_waybel_0(B_118,k3_yellow_1(k2_struct_0(A_117)))
      | ~ v1_subset_1(B_118,u1_struct_0(k3_yellow_1(k2_struct_0(A_117))))
      | v1_xboole_0(B_118)
      | ~ l1_struct_0(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_437,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_435])).

tff(c_443,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_48,c_46,c_44,c_437])).

tff(c_444,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_443])).

tff(c_449,plain,(
    ! [C_22] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_22)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_22)
      | ~ m1_subset_1(C_22,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_34])).

tff(c_456,plain,(
    ! [C_22] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_22)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_22)
      | ~ m1_subset_1(C_22,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_361,c_419,c_95,c_449])).

tff(c_457,plain,(
    ! [C_22] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_22)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_22)
      | ~ m1_subset_1(C_22,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_456])).

tff(c_470,plain,(
    ! [C_22] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_22)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_22)
      | ~ m1_subset_1(C_22,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_457])).

tff(c_471,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_470])).

tff(c_473,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_471,c_26])).

tff(c_476,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_65,c_95,c_46,c_44,c_42,c_473])).

tff(c_478,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_344,c_50,c_476])).

tff(c_480,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_470])).

tff(c_36,plain,(
    ! [A_16,B_20,C_22] :
      ( r1_waybel_7(A_16,k2_yellow19(A_16,B_20),C_22)
      | ~ r3_waybel_9(A_16,B_20,C_22)
      | ~ m1_subset_1(C_22,u1_struct_0(A_16))
      | ~ l1_waybel_0(B_20,A_16)
      | ~ v7_waybel_0(B_20)
      | ~ v4_orders_2(B_20)
      | v2_struct_0(B_20)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_452,plain,(
    ! [C_22] :
      ( r1_waybel_7('#skF_1','#skF_2',C_22)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_22)
      | ~ m1_subset_1(C_22,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_36])).

tff(c_459,plain,(
    ! [C_22] :
      ( r1_waybel_7('#skF_1','#skF_2',C_22)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_22)
      | ~ m1_subset_1(C_22,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_361,c_419,c_95,c_452])).

tff(c_460,plain,(
    ! [C_22] :
      ( r1_waybel_7('#skF_1','#skF_2',C_22)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_22)
      | ~ m1_subset_1(C_22,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_459])).

tff(c_483,plain,(
    ! [C_22] :
      ( r1_waybel_7('#skF_1','#skF_2',C_22)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_22)
      | ~ m1_subset_1(C_22,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_460])).

tff(c_485,plain,(
    ! [C_121] :
      ( r1_waybel_7('#skF_1','#skF_2',C_121)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_121)
      | ~ m1_subset_1(C_121,k2_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_480,c_483])).

tff(c_491,plain,
    ( r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_308,c_485])).

tff(c_495,plain,(
    r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_491])).

tff(c_497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_495])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.54  
% 3.10/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.54  %$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1
% 3.10/1.54  
% 3.10/1.54  %Foreground sorts:
% 3.10/1.54  
% 3.10/1.54  
% 3.10/1.54  %Background operators:
% 3.10/1.54  
% 3.10/1.54  
% 3.10/1.54  %Foreground operators:
% 3.10/1.54  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.10/1.54  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.10/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.54  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.10/1.54  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 3.10/1.54  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.10/1.54  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.10/1.54  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.10/1.54  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.10/1.54  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.10/1.54  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 3.10/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.10/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.10/1.54  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.10/1.54  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.10/1.54  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 3.10/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.10/1.54  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.10/1.54  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.10/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.54  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.10/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.54  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.10/1.54  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.10/1.54  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.10/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.10/1.54  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.10/1.54  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.10/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.10/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.10/1.54  
% 3.10/1.58  tff(f_199, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, k3_yellow19(A, k2_struct_0(A), B), C) <=> r1_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_yellow19)).
% 3.10/1.58  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.10/1.58  tff(f_33, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.10/1.58  tff(f_101, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_yellow19)).
% 3.10/1.58  tff(f_45, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.10/1.58  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.10/1.58  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.10/1.58  tff(f_73, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 3.10/1.58  tff(f_172, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 3.10/1.58  tff(f_153, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> r1_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_yellow19)).
% 3.10/1.58  tff(f_129, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow19)).
% 3.10/1.58  tff(c_64, plain, (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3') | r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.10/1.58  tff(c_102, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_64])).
% 3.10/1.58  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.10/1.58  tff(c_8, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.10/1.58  tff(c_86, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.10/1.58  tff(c_91, plain, (![A_35]: (u1_struct_0(A_35)=k2_struct_0(A_35) | ~l1_pre_topc(A_35))), inference(resolution, [status(thm)], [c_8, c_86])).
% 3.10/1.58  tff(c_95, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_91])).
% 3.10/1.58  tff(c_40, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.10/1.58  tff(c_96, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_40])).
% 3.10/1.58  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.10/1.58  tff(c_50, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.10/1.58  tff(c_46, plain, (v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.10/1.58  tff(c_44, plain, (v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.10/1.58  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.10/1.58  tff(c_111, plain, (![A_46, B_47, C_48]: (v3_orders_2(k3_yellow19(A_46, B_47, C_48)) | ~m1_subset_1(C_48, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_47)))) | ~v13_waybel_0(C_48, k3_yellow_1(B_47)) | ~v2_waybel_0(C_48, k3_yellow_1(B_47)) | v1_xboole_0(C_48) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | v1_xboole_0(B_47) | ~l1_struct_0(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.10/1.58  tff(c_113, plain, (![A_46]: (v3_orders_2(k3_yellow19(A_46, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_46))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_46) | v2_struct_0(A_46))), inference(resolution, [status(thm)], [c_42, c_111])).
% 3.10/1.58  tff(c_119, plain, (![A_46]: (v3_orders_2(k3_yellow19(A_46, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_46))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_46) | v2_struct_0(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_113])).
% 3.10/1.58  tff(c_120, plain, (![A_46]: (v3_orders_2(k3_yellow19(A_46, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_46))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_46) | v2_struct_0(A_46))), inference(negUnitSimplification, [status(thm)], [c_50, c_119])).
% 3.10/1.58  tff(c_122, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_120])).
% 3.10/1.58  tff(c_10, plain, (![A_5]: (~v1_xboole_0(k2_struct_0(A_5)) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.10/1.58  tff(c_125, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_122, c_10])).
% 3.10/1.58  tff(c_128, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_125])).
% 3.10/1.58  tff(c_131, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_128])).
% 3.10/1.58  tff(c_135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_131])).
% 3.10/1.58  tff(c_137, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_120])).
% 3.10/1.58  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.10/1.58  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.10/1.58  tff(c_65, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.10/1.58  tff(c_138, plain, (![A_49]: (v3_orders_2(k3_yellow19(A_49, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_struct_0(A_49) | v2_struct_0(A_49))), inference(splitRight, [status(thm)], [c_120])).
% 3.10/1.58  tff(c_141, plain, (v3_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_95, c_138])).
% 3.10/1.58  tff(c_143, plain, (v3_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_141])).
% 3.10/1.58  tff(c_144, plain, (v3_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_143])).
% 3.10/1.58  tff(c_145, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_144])).
% 3.10/1.58  tff(c_148, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_145])).
% 3.10/1.58  tff(c_152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_148])).
% 3.10/1.58  tff(c_154, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_144])).
% 3.10/1.58  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.10/1.58  tff(c_160, plain, (![A_50, B_51, C_52]: (v4_orders_2(k3_yellow19(A_50, B_51, C_52)) | ~m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_51)))) | ~v13_waybel_0(C_52, k3_yellow_1(B_51)) | ~v2_waybel_0(C_52, k3_yellow_1(B_51)) | v1_xboole_0(C_52) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | v1_xboole_0(B_51) | ~l1_struct_0(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.10/1.58  tff(c_162, plain, (![A_50]: (v4_orders_2(k3_yellow19(A_50, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_50))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_50) | v2_struct_0(A_50))), inference(resolution, [status(thm)], [c_42, c_160])).
% 3.10/1.58  tff(c_168, plain, (![A_50]: (v4_orders_2(k3_yellow19(A_50, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_50))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_50) | v2_struct_0(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_162])).
% 3.10/1.58  tff(c_171, plain, (![A_53]: (v4_orders_2(k3_yellow19(A_53, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_struct_0(A_53) | v2_struct_0(A_53))), inference(negUnitSimplification, [status(thm)], [c_137, c_50, c_168])).
% 3.10/1.58  tff(c_174, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_95, c_171])).
% 3.10/1.58  tff(c_176, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_65, c_174])).
% 3.10/1.58  tff(c_177, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_176])).
% 3.10/1.58  tff(c_195, plain, (![A_58, B_59, C_60]: (l1_waybel_0(k3_yellow19(A_58, B_59, C_60), A_58) | ~m1_subset_1(C_60, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_59)))) | ~v13_waybel_0(C_60, k3_yellow_1(B_59)) | ~v2_waybel_0(C_60, k3_yellow_1(B_59)) | v1_xboole_0(C_60) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | v1_xboole_0(B_59) | ~l1_struct_0(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.10/1.58  tff(c_197, plain, (![A_58]: (l1_waybel_0(k3_yellow19(A_58, k2_struct_0('#skF_1'), '#skF_2'), A_58) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_58))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_58) | v2_struct_0(A_58))), inference(resolution, [status(thm)], [c_42, c_195])).
% 3.10/1.58  tff(c_203, plain, (![A_58]: (l1_waybel_0(k3_yellow19(A_58, k2_struct_0('#skF_1'), '#skF_2'), A_58) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_58))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_58) | v2_struct_0(A_58))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_197])).
% 3.10/1.58  tff(c_206, plain, (![A_61]: (l1_waybel_0(k3_yellow19(A_61, k2_struct_0('#skF_1'), '#skF_2'), A_61) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_struct_0(A_61) | v2_struct_0(A_61))), inference(negUnitSimplification, [status(thm)], [c_137, c_50, c_203])).
% 3.10/1.58  tff(c_208, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_95, c_206])).
% 3.10/1.58  tff(c_210, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_65, c_208])).
% 3.10/1.58  tff(c_211, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_210])).
% 3.10/1.58  tff(c_48, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.10/1.58  tff(c_213, plain, (![A_64, B_65]: (k2_yellow19(A_64, k3_yellow19(A_64, k2_struct_0(A_64), B_65))=B_65 | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_64))))) | ~v13_waybel_0(B_65, k3_yellow_1(k2_struct_0(A_64))) | ~v2_waybel_0(B_65, k3_yellow_1(k2_struct_0(A_64))) | ~v1_subset_1(B_65, u1_struct_0(k3_yellow_1(k2_struct_0(A_64)))) | v1_xboole_0(B_65) | ~l1_struct_0(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.10/1.58  tff(c_215, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_213])).
% 3.10/1.58  tff(c_221, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_48, c_46, c_44, c_215])).
% 3.10/1.58  tff(c_222, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_56, c_50, c_221])).
% 3.10/1.58  tff(c_34, plain, (![A_16, B_20, C_22]: (r3_waybel_9(A_16, B_20, C_22) | ~r1_waybel_7(A_16, k2_yellow19(A_16, B_20), C_22) | ~m1_subset_1(C_22, u1_struct_0(A_16)) | ~l1_waybel_0(B_20, A_16) | ~v7_waybel_0(B_20) | ~v4_orders_2(B_20) | v2_struct_0(B_20) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.10/1.58  tff(c_227, plain, (![C_22]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_22) | ~r1_waybel_7('#skF_1', '#skF_2', C_22) | ~m1_subset_1(C_22, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_222, c_34])).
% 3.10/1.58  tff(c_234, plain, (![C_22]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_22) | ~r1_waybel_7('#skF_1', '#skF_2', C_22) | ~m1_subset_1(C_22, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_177, c_211, c_95, c_227])).
% 3.10/1.58  tff(c_235, plain, (![C_22]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_22) | ~r1_waybel_7('#skF_1', '#skF_2', C_22) | ~m1_subset_1(C_22, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_234])).
% 3.10/1.58  tff(c_240, plain, (~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_235])).
% 3.10/1.58  tff(c_244, plain, (![A_72, B_73, C_74]: (v7_waybel_0(k3_yellow19(A_72, B_73, C_74)) | ~m1_subset_1(C_74, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_73)))) | ~v13_waybel_0(C_74, k3_yellow_1(B_73)) | ~v2_waybel_0(C_74, k3_yellow_1(B_73)) | ~v1_subset_1(C_74, u1_struct_0(k3_yellow_1(B_73))) | v1_xboole_0(C_74) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | v1_xboole_0(B_73) | ~l1_struct_0(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.10/1.58  tff(c_246, plain, (![A_72]: (v7_waybel_0(k3_yellow19(A_72, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_72))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_72) | v2_struct_0(A_72))), inference(resolution, [status(thm)], [c_42, c_244])).
% 3.10/1.58  tff(c_252, plain, (![A_72]: (v7_waybel_0(k3_yellow19(A_72, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_72))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_72) | v2_struct_0(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_246])).
% 3.10/1.58  tff(c_255, plain, (![A_75]: (v7_waybel_0(k3_yellow19(A_75, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_struct_0(A_75) | v2_struct_0(A_75))), inference(negUnitSimplification, [status(thm)], [c_137, c_50, c_252])).
% 3.10/1.58  tff(c_258, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_95, c_255])).
% 3.10/1.58  tff(c_260, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_65, c_258])).
% 3.10/1.58  tff(c_262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_240, c_260])).
% 3.10/1.58  tff(c_263, plain, (![C_22]: (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_22) | ~r1_waybel_7('#skF_1', '#skF_2', C_22) | ~m1_subset_1(C_22, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_235])).
% 3.10/1.58  tff(c_283, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_263])).
% 3.10/1.58  tff(c_26, plain, (![A_10, B_11, C_12]: (~v2_struct_0(k3_yellow19(A_10, B_11, C_12)) | ~m1_subset_1(C_12, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_11)))) | ~v13_waybel_0(C_12, k3_yellow_1(B_11)) | ~v2_waybel_0(C_12, k3_yellow_1(B_11)) | v1_xboole_0(C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0(A_10))) | v1_xboole_0(B_11) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.10/1.58  tff(c_288, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_283, c_26])).
% 3.10/1.58  tff(c_291, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_65, c_95, c_46, c_44, c_42, c_288])).
% 3.10/1.58  tff(c_293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_137, c_50, c_291])).
% 3.10/1.58  tff(c_296, plain, (![C_80]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_80) | ~r1_waybel_7('#skF_1', '#skF_2', C_80) | ~m1_subset_1(C_80, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_263])).
% 3.10/1.58  tff(c_58, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.10/1.58  tff(c_103, plain, (~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 3.10/1.58  tff(c_299, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_296, c_103])).
% 3.10/1.58  tff(c_303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_102, c_299])).
% 3.10/1.58  tff(c_304, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 3.10/1.58  tff(c_307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_304])).
% 3.10/1.58  tff(c_309, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_64])).
% 3.10/1.58  tff(c_308, plain, (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_64])).
% 3.10/1.58  tff(c_318, plain, (![A_87, B_88, C_89]: (v4_orders_2(k3_yellow19(A_87, B_88, C_89)) | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_88)))) | ~v13_waybel_0(C_89, k3_yellow_1(B_88)) | ~v2_waybel_0(C_89, k3_yellow_1(B_88)) | v1_xboole_0(C_89) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | v1_xboole_0(B_88) | ~l1_struct_0(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.10/1.58  tff(c_320, plain, (![A_87]: (v4_orders_2(k3_yellow19(A_87, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_87))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_87) | v2_struct_0(A_87))), inference(resolution, [status(thm)], [c_42, c_318])).
% 3.10/1.58  tff(c_326, plain, (![A_87]: (v4_orders_2(k3_yellow19(A_87, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_87))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_87) | v2_struct_0(A_87))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_320])).
% 3.10/1.58  tff(c_327, plain, (![A_87]: (v4_orders_2(k3_yellow19(A_87, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_87))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_87) | v2_struct_0(A_87))), inference(negUnitSimplification, [status(thm)], [c_50, c_326])).
% 3.10/1.58  tff(c_329, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_327])).
% 3.10/1.58  tff(c_332, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_329, c_10])).
% 3.10/1.58  tff(c_335, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_332])).
% 3.10/1.58  tff(c_338, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_335])).
% 3.10/1.58  tff(c_342, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_338])).
% 3.10/1.58  tff(c_344, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_327])).
% 3.10/1.58  tff(c_346, plain, (![A_93]: (v4_orders_2(k3_yellow19(A_93, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_struct_0(A_93) | v2_struct_0(A_93))), inference(splitRight, [status(thm)], [c_327])).
% 3.10/1.58  tff(c_349, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_95, c_346])).
% 3.10/1.58  tff(c_351, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_349])).
% 3.10/1.58  tff(c_352, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_351])).
% 3.10/1.58  tff(c_353, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_352])).
% 3.10/1.58  tff(c_356, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_353])).
% 3.10/1.58  tff(c_360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_356])).
% 3.10/1.58  tff(c_362, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_352])).
% 3.10/1.58  tff(c_424, plain, (![A_114, B_115, C_116]: (v7_waybel_0(k3_yellow19(A_114, B_115, C_116)) | ~m1_subset_1(C_116, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_115)))) | ~v13_waybel_0(C_116, k3_yellow_1(B_115)) | ~v2_waybel_0(C_116, k3_yellow_1(B_115)) | ~v1_subset_1(C_116, u1_struct_0(k3_yellow_1(B_115))) | v1_xboole_0(C_116) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | v1_xboole_0(B_115) | ~l1_struct_0(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.10/1.58  tff(c_426, plain, (![A_114]: (v7_waybel_0(k3_yellow19(A_114, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_114))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_114) | v2_struct_0(A_114))), inference(resolution, [status(thm)], [c_42, c_424])).
% 3.10/1.58  tff(c_432, plain, (![A_114]: (v7_waybel_0(k3_yellow19(A_114, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_114))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_114) | v2_struct_0(A_114))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_426])).
% 3.10/1.58  tff(c_462, plain, (![A_119]: (v7_waybel_0(k3_yellow19(A_119, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_struct_0(A_119) | v2_struct_0(A_119))), inference(negUnitSimplification, [status(thm)], [c_344, c_50, c_432])).
% 3.10/1.58  tff(c_465, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_95, c_462])).
% 3.10/1.58  tff(c_467, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_362, c_65, c_465])).
% 3.10/1.58  tff(c_468, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_467])).
% 3.10/1.58  tff(c_361, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_352])).
% 3.10/1.58  tff(c_397, plain, (![A_101, B_102, C_103]: (l1_waybel_0(k3_yellow19(A_101, B_102, C_103), A_101) | ~m1_subset_1(C_103, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_102)))) | ~v13_waybel_0(C_103, k3_yellow_1(B_102)) | ~v2_waybel_0(C_103, k3_yellow_1(B_102)) | v1_xboole_0(C_103) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | v1_xboole_0(B_102) | ~l1_struct_0(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.10/1.58  tff(c_399, plain, (![A_101]: (l1_waybel_0(k3_yellow19(A_101, k2_struct_0('#skF_1'), '#skF_2'), A_101) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_101))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_101) | v2_struct_0(A_101))), inference(resolution, [status(thm)], [c_42, c_397])).
% 3.10/1.58  tff(c_405, plain, (![A_101]: (l1_waybel_0(k3_yellow19(A_101, k2_struct_0('#skF_1'), '#skF_2'), A_101) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_101))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_101) | v2_struct_0(A_101))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_399])).
% 3.10/1.58  tff(c_414, plain, (![A_105]: (l1_waybel_0(k3_yellow19(A_105, k2_struct_0('#skF_1'), '#skF_2'), A_105) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_struct_0(A_105) | v2_struct_0(A_105))), inference(negUnitSimplification, [status(thm)], [c_344, c_50, c_405])).
% 3.10/1.58  tff(c_416, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_95, c_414])).
% 3.10/1.58  tff(c_418, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_362, c_65, c_416])).
% 3.10/1.58  tff(c_419, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_418])).
% 3.10/1.58  tff(c_435, plain, (![A_117, B_118]: (k2_yellow19(A_117, k3_yellow19(A_117, k2_struct_0(A_117), B_118))=B_118 | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_117))))) | ~v13_waybel_0(B_118, k3_yellow_1(k2_struct_0(A_117))) | ~v2_waybel_0(B_118, k3_yellow_1(k2_struct_0(A_117))) | ~v1_subset_1(B_118, u1_struct_0(k3_yellow_1(k2_struct_0(A_117)))) | v1_xboole_0(B_118) | ~l1_struct_0(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.10/1.58  tff(c_437, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_435])).
% 3.10/1.58  tff(c_443, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_362, c_48, c_46, c_44, c_437])).
% 3.10/1.58  tff(c_444, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_56, c_50, c_443])).
% 3.10/1.58  tff(c_449, plain, (![C_22]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_22) | ~r1_waybel_7('#skF_1', '#skF_2', C_22) | ~m1_subset_1(C_22, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_444, c_34])).
% 3.10/1.58  tff(c_456, plain, (![C_22]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_22) | ~r1_waybel_7('#skF_1', '#skF_2', C_22) | ~m1_subset_1(C_22, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_361, c_419, c_95, c_449])).
% 3.10/1.58  tff(c_457, plain, (![C_22]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_22) | ~r1_waybel_7('#skF_1', '#skF_2', C_22) | ~m1_subset_1(C_22, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_456])).
% 3.10/1.58  tff(c_470, plain, (![C_22]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_22) | ~r1_waybel_7('#skF_1', '#skF_2', C_22) | ~m1_subset_1(C_22, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_468, c_457])).
% 3.10/1.58  tff(c_471, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_470])).
% 3.10/1.58  tff(c_473, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_471, c_26])).
% 3.10/1.58  tff(c_476, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_362, c_65, c_95, c_46, c_44, c_42, c_473])).
% 3.10/1.58  tff(c_478, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_344, c_50, c_476])).
% 3.10/1.58  tff(c_480, plain, (~v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_470])).
% 3.10/1.58  tff(c_36, plain, (![A_16, B_20, C_22]: (r1_waybel_7(A_16, k2_yellow19(A_16, B_20), C_22) | ~r3_waybel_9(A_16, B_20, C_22) | ~m1_subset_1(C_22, u1_struct_0(A_16)) | ~l1_waybel_0(B_20, A_16) | ~v7_waybel_0(B_20) | ~v4_orders_2(B_20) | v2_struct_0(B_20) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.10/1.58  tff(c_452, plain, (![C_22]: (r1_waybel_7('#skF_1', '#skF_2', C_22) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_22) | ~m1_subset_1(C_22, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_444, c_36])).
% 3.10/1.58  tff(c_459, plain, (![C_22]: (r1_waybel_7('#skF_1', '#skF_2', C_22) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_22) | ~m1_subset_1(C_22, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_361, c_419, c_95, c_452])).
% 3.10/1.58  tff(c_460, plain, (![C_22]: (r1_waybel_7('#skF_1', '#skF_2', C_22) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_22) | ~m1_subset_1(C_22, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_459])).
% 3.10/1.58  tff(c_483, plain, (![C_22]: (r1_waybel_7('#skF_1', '#skF_2', C_22) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_22) | ~m1_subset_1(C_22, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_468, c_460])).
% 3.10/1.58  tff(c_485, plain, (![C_121]: (r1_waybel_7('#skF_1', '#skF_2', C_121) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_121) | ~m1_subset_1(C_121, k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_480, c_483])).
% 3.10/1.58  tff(c_491, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_308, c_485])).
% 3.10/1.58  tff(c_495, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_491])).
% 3.10/1.58  tff(c_497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_309, c_495])).
% 3.10/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.58  
% 3.10/1.58  Inference rules
% 3.10/1.58  ----------------------
% 3.10/1.58  #Ref     : 0
% 3.10/1.58  #Sup     : 68
% 3.10/1.58  #Fact    : 0
% 3.10/1.58  #Define  : 0
% 3.10/1.58  #Split   : 10
% 3.10/1.58  #Chain   : 0
% 3.10/1.58  #Close   : 0
% 3.10/1.58  
% 3.10/1.58  Ordering : KBO
% 3.10/1.58  
% 3.10/1.58  Simplification rules
% 3.10/1.58  ----------------------
% 3.10/1.58  #Subsume      : 6
% 3.10/1.58  #Demod        : 102
% 3.10/1.58  #Tautology    : 18
% 3.10/1.58  #SimpNegUnit  : 34
% 3.10/1.58  #BackRed      : 1
% 3.10/1.58  
% 3.10/1.58  #Partial instantiations: 0
% 3.10/1.58  #Strategies tried      : 1
% 3.10/1.58  
% 3.10/1.58  Timing (in seconds)
% 3.10/1.58  ----------------------
% 3.10/1.58  Preprocessing        : 0.35
% 3.10/1.58  Parsing              : 0.18
% 3.10/1.58  CNF conversion       : 0.02
% 3.10/1.58  Main loop            : 0.34
% 3.10/1.58  Inferencing          : 0.13
% 3.10/1.58  Reduction            : 0.11
% 3.10/1.58  Demodulation         : 0.08
% 3.10/1.58  BG Simplification    : 0.02
% 3.10/1.58  Subsumption          : 0.06
% 3.10/1.58  Abstraction          : 0.02
% 3.10/1.58  MUC search           : 0.00
% 3.10/1.58  Cooper               : 0.00
% 3.10/1.58  Total                : 0.75
% 3.10/1.58  Index Insertion      : 0.00
% 3.10/1.58  Index Deletion       : 0.00
% 3.10/1.58  Index Matching       : 0.00
% 3.10/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
