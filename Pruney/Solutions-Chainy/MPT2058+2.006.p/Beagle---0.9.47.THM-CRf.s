%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:33 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  165 (1909 expanded)
%              Number of leaves         :   42 ( 669 expanded)
%              Depth                    :   19
%              Number of atoms          :  521 (7571 expanded)
%              Number of equality atoms :   14 ( 402 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_205,negated_conjecture,(
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

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_107,axiom,(
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

tff(f_135,axiom,(
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

tff(f_79,axiom,(
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

tff(f_178,axiom,(
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

tff(f_159,axiom,(
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

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_14,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_83,plain,(
    ! [A_35] :
      ( u1_struct_0(A_35) = k2_struct_0(A_35)
      | ~ l1_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_88,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(resolution,[status(thm)],[c_14,c_83])).

tff(c_92,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_88])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_93,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_46])).

tff(c_64,plain,
    ( ~ r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_113,plain,(
    ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,
    ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3')
    | r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_140,plain,(
    r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_70])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_98,plain,(
    ! [A_37] :
      ( ~ v1_xboole_0(u1_struct_0(A_37))
      | ~ l1_struct_0(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_101,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_98])).

tff(c_102,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_101])).

tff(c_103,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_106,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_103])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_106])).

tff(c_111,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_112,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_52,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_50,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_147,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_152,plain,(
    ! [A_50] :
      ( v4_orders_2(k3_yellow19(A_50,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_50)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_50)
      | v2_struct_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_48,c_147])).

tff(c_156,plain,(
    ! [A_50] :
      ( v4_orders_2(k3_yellow19(A_50,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_50)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_50)
      | v2_struct_0(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_152])).

tff(c_158,plain,(
    ! [A_53] :
      ( v4_orders_2(k3_yellow19(A_53,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_struct_0(A_53)
      | v2_struct_0(A_53) ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_56,c_156])).

tff(c_164,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_158])).

tff(c_167,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_164])).

tff(c_168,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_167])).

tff(c_169,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_183,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_169])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_183])).

tff(c_189,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_188,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_54,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_393,plain,(
    ! [A_101,B_102,C_103] :
      ( v7_waybel_0(k3_yellow19(A_101,B_102,C_103))
      | ~ m1_subset_1(C_103,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_102))))
      | ~ v13_waybel_0(C_103,k3_yellow_1(B_102))
      | ~ v2_waybel_0(C_103,k3_yellow_1(B_102))
      | ~ v1_subset_1(C_103,u1_struct_0(k3_yellow_1(B_102)))
      | v1_xboole_0(C_103)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | v1_xboole_0(B_102)
      | ~ l1_struct_0(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_398,plain,(
    ! [A_101] :
      ( v7_waybel_0(k3_yellow19(A_101,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_101)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_101)
      | v2_struct_0(A_101) ) ),
    inference(resolution,[status(thm)],[c_48,c_393])).

tff(c_402,plain,(
    ! [A_101] :
      ( v7_waybel_0(k3_yellow19(A_101,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_101)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_101)
      | v2_struct_0(A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_398])).

tff(c_404,plain,(
    ! [A_104] :
      ( v7_waybel_0(k3_yellow19(A_104,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_struct_0(A_104)
      | v2_struct_0(A_104) ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_56,c_402])).

tff(c_410,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_404])).

tff(c_413,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_189,c_410])).

tff(c_414,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_413])).

tff(c_316,plain,(
    ! [A_84,B_85,C_86] :
      ( l1_waybel_0(k3_yellow19(A_84,B_85,C_86),A_84)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_85))))
      | ~ v13_waybel_0(C_86,k3_yellow_1(B_85))
      | ~ v2_waybel_0(C_86,k3_yellow_1(B_85))
      | v1_xboole_0(C_86)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | v1_xboole_0(B_85)
      | ~ l1_struct_0(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_321,plain,(
    ! [A_84] :
      ( l1_waybel_0(k3_yellow19(A_84,k2_struct_0('#skF_1'),'#skF_2'),A_84)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_84)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_84)
      | v2_struct_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_48,c_316])).

tff(c_325,plain,(
    ! [A_84] :
      ( l1_waybel_0(k3_yellow19(A_84,k2_struct_0('#skF_1'),'#skF_2'),A_84)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_84)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_84)
      | v2_struct_0(A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_321])).

tff(c_327,plain,(
    ! [A_87] :
      ( l1_waybel_0(k3_yellow19(A_87,k2_struct_0('#skF_1'),'#skF_2'),A_87)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_struct_0(A_87)
      | v2_struct_0(A_87) ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_56,c_325])).

tff(c_332,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_327])).

tff(c_335,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_189,c_332])).

tff(c_336,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_335])).

tff(c_471,plain,(
    ! [A_116,B_117] :
      ( k2_yellow19(A_116,k3_yellow19(A_116,k2_struct_0(A_116),B_117)) = B_117
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_116)))))
      | ~ v13_waybel_0(B_117,k3_yellow_1(k2_struct_0(A_116)))
      | ~ v2_waybel_0(B_117,k3_yellow_1(k2_struct_0(A_116)))
      | ~ v1_subset_1(B_117,u1_struct_0(k3_yellow_1(k2_struct_0(A_116))))
      | v1_xboole_0(B_117)
      | ~ l1_struct_0(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_476,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_471])).

tff(c_480,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_54,c_52,c_50,c_476])).

tff(c_481,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_480])).

tff(c_40,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_485,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_481,c_40])).

tff(c_492,plain,(
    ! [C_24] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_24)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_24)
      | ~ m1_subset_1(C_24,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_188,c_414,c_336,c_92,c_485])).

tff(c_493,plain,(
    ! [C_24] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_24)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_24)
      | ~ m1_subset_1(C_24,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_492])).

tff(c_498,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_493])).

tff(c_32,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_500,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_498,c_32])).

tff(c_503,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_189,c_92,c_52,c_50,c_48,c_500])).

tff(c_505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_111,c_56,c_503])).

tff(c_520,plain,(
    ! [C_121] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_121)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_121)
      | ~ m1_subset_1(C_121,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_493])).

tff(c_526,plain,
    ( ~ r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_520,c_113])).

tff(c_531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_140,c_526])).

tff(c_532,plain,(
    ~ r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_539,plain,(
    r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_532,c_539])).

tff(c_541,plain,(
    r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_571,plain,(
    ! [A_134,B_135,C_136] :
      ( v3_orders_2(k3_yellow19(A_134,B_135,C_136))
      | ~ m1_subset_1(C_136,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_135))))
      | ~ v13_waybel_0(C_136,k3_yellow_1(B_135))
      | ~ v2_waybel_0(C_136,k3_yellow_1(B_135))
      | v1_xboole_0(C_136)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | v1_xboole_0(B_135)
      | ~ l1_struct_0(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_576,plain,(
    ! [A_134] :
      ( v3_orders_2(k3_yellow19(A_134,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_134)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_134)
      | v2_struct_0(A_134) ) ),
    inference(resolution,[status(thm)],[c_48,c_571])).

tff(c_580,plain,(
    ! [A_134] :
      ( v3_orders_2(k3_yellow19(A_134,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_134)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_134)
      | v2_struct_0(A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_576])).

tff(c_593,plain,(
    ! [A_140] :
      ( v3_orders_2(k3_yellow19(A_140,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_struct_0(A_140)
      | v2_struct_0(A_140) ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_56,c_580])).

tff(c_599,plain,
    ( v3_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_593])).

tff(c_602,plain,
    ( v3_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_599])).

tff(c_603,plain,
    ( v3_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_602])).

tff(c_604,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_603])).

tff(c_607,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_604])).

tff(c_611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_607])).

tff(c_613,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_603])).

tff(c_582,plain,(
    ! [A_137,B_138,C_139] :
      ( v4_orders_2(k3_yellow19(A_137,B_138,C_139))
      | ~ m1_subset_1(C_139,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_138))))
      | ~ v13_waybel_0(C_139,k3_yellow_1(B_138))
      | ~ v2_waybel_0(C_139,k3_yellow_1(B_138))
      | v1_xboole_0(C_139)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | v1_xboole_0(B_138)
      | ~ l1_struct_0(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_587,plain,(
    ! [A_137] :
      ( v4_orders_2(k3_yellow19(A_137,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_137)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_137)
      | v2_struct_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_48,c_582])).

tff(c_591,plain,(
    ! [A_137] :
      ( v4_orders_2(k3_yellow19(A_137,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_137)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_137)
      | v2_struct_0(A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_587])).

tff(c_614,plain,(
    ! [A_141] :
      ( v4_orders_2(k3_yellow19(A_141,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_struct_0(A_141)
      | v2_struct_0(A_141) ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_56,c_591])).

tff(c_620,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_614])).

tff(c_623,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_620])).

tff(c_624,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_623])).

tff(c_631,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_624])).

tff(c_819,plain,(
    ! [A_184,B_185,C_186] :
      ( v7_waybel_0(k3_yellow19(A_184,B_185,C_186))
      | ~ m1_subset_1(C_186,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_185))))
      | ~ v13_waybel_0(C_186,k3_yellow_1(B_185))
      | ~ v2_waybel_0(C_186,k3_yellow_1(B_185))
      | ~ v1_subset_1(C_186,u1_struct_0(k3_yellow_1(B_185)))
      | v1_xboole_0(C_186)
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0(A_184)))
      | v1_xboole_0(B_185)
      | ~ l1_struct_0(A_184)
      | v2_struct_0(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_824,plain,(
    ! [A_184] :
      ( v7_waybel_0(k3_yellow19(A_184,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_184)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_184)
      | v2_struct_0(A_184) ) ),
    inference(resolution,[status(thm)],[c_48,c_819])).

tff(c_828,plain,(
    ! [A_184] :
      ( v7_waybel_0(k3_yellow19(A_184,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_184)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_184)
      | v2_struct_0(A_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_824])).

tff(c_830,plain,(
    ! [A_187] :
      ( v7_waybel_0(k3_yellow19(A_187,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ l1_struct_0(A_187)
      | v2_struct_0(A_187) ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_56,c_828])).

tff(c_836,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_830])).

tff(c_839,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_613,c_836])).

tff(c_840,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_839])).

tff(c_719,plain,(
    ! [A_161,B_162,C_163] :
      ( l1_waybel_0(k3_yellow19(A_161,B_162,C_163),A_161)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_162))))
      | ~ v13_waybel_0(C_163,k3_yellow_1(B_162))
      | ~ v2_waybel_0(C_163,k3_yellow_1(B_162))
      | v1_xboole_0(C_163)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_161)))
      | v1_xboole_0(B_162)
      | ~ l1_struct_0(A_161)
      | v2_struct_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_724,plain,(
    ! [A_161] :
      ( l1_waybel_0(k3_yellow19(A_161,k2_struct_0('#skF_1'),'#skF_2'),A_161)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_161)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_161)
      | v2_struct_0(A_161) ) ),
    inference(resolution,[status(thm)],[c_48,c_719])).

tff(c_728,plain,(
    ! [A_161] :
      ( l1_waybel_0(k3_yellow19(A_161,k2_struct_0('#skF_1'),'#skF_2'),A_161)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_161)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_161)
      | v2_struct_0(A_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_724])).

tff(c_730,plain,(
    ! [A_164] :
      ( l1_waybel_0(k3_yellow19(A_164,k2_struct_0('#skF_1'),'#skF_2'),A_164)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_struct_0(A_164)
      | v2_struct_0(A_164) ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_56,c_728])).

tff(c_735,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_730])).

tff(c_738,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_613,c_735])).

tff(c_739,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_738])).

tff(c_875,plain,(
    ! [A_194,B_195] :
      ( k2_yellow19(A_194,k3_yellow19(A_194,k2_struct_0(A_194),B_195)) = B_195
      | ~ m1_subset_1(B_195,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_194)))))
      | ~ v13_waybel_0(B_195,k3_yellow_1(k2_struct_0(A_194)))
      | ~ v2_waybel_0(B_195,k3_yellow_1(k2_struct_0(A_194)))
      | ~ v1_subset_1(B_195,u1_struct_0(k3_yellow_1(k2_struct_0(A_194))))
      | v1_xboole_0(B_195)
      | ~ l1_struct_0(A_194)
      | v2_struct_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_880,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_875])).

tff(c_884,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_54,c_52,c_50,c_880])).

tff(c_885,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_884])).

tff(c_42,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_889,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_885,c_42])).

tff(c_896,plain,(
    ! [C_24] :
      ( r1_waybel_7('#skF_1','#skF_2',C_24)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_24)
      | ~ m1_subset_1(C_24,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_631,c_840,c_739,c_92,c_889])).

tff(c_897,plain,(
    ! [C_24] :
      ( r1_waybel_7('#skF_1','#skF_2',C_24)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_24)
      | ~ m1_subset_1(C_24,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_896])).

tff(c_902,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_897])).

tff(c_904,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_902,c_32])).

tff(c_907,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_613,c_92,c_52,c_50,c_48,c_904])).

tff(c_909,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_111,c_56,c_907])).

tff(c_924,plain,(
    ! [C_199] :
      ( r1_waybel_7('#skF_1','#skF_2',C_199)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_199)
      | ~ m1_subset_1(C_199,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_897])).

tff(c_930,plain,
    ( r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_541,c_924])).

tff(c_934,plain,(
    r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_930])).

tff(c_936,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_532,c_934])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:09:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.56  
% 3.47/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.56  %$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1
% 3.66/1.56  
% 3.66/1.56  %Foreground sorts:
% 3.66/1.56  
% 3.66/1.56  
% 3.66/1.56  %Background operators:
% 3.66/1.56  
% 3.66/1.56  
% 3.66/1.56  %Foreground operators:
% 3.66/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.66/1.56  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.66/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.56  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.66/1.56  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 3.66/1.56  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.66/1.56  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.66/1.56  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.66/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.66/1.56  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.66/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.66/1.56  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 3.66/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.66/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.66/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.66/1.56  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.66/1.56  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.66/1.56  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 3.66/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.66/1.56  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.66/1.56  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.66/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.56  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.66/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.56  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.66/1.56  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.66/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.66/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.66/1.56  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.66/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.66/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.66/1.56  
% 3.66/1.59  tff(f_205, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, k3_yellow19(A, k2_struct_0(A), B), C) <=> r1_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_yellow19)).
% 3.66/1.59  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.66/1.59  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.66/1.59  tff(f_51, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.66/1.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.66/1.59  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.66/1.59  tff(f_107, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_yellow19)).
% 3.66/1.59  tff(f_135, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow19)).
% 3.66/1.59  tff(f_79, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 3.66/1.59  tff(f_178, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 3.66/1.59  tff(f_159, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> r1_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_yellow19)).
% 3.66/1.59  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.66/1.59  tff(c_14, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.66/1.59  tff(c_83, plain, (![A_35]: (u1_struct_0(A_35)=k2_struct_0(A_35) | ~l1_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.66/1.59  tff(c_88, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_pre_topc(A_36))), inference(resolution, [status(thm)], [c_14, c_83])).
% 3.66/1.59  tff(c_92, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_88])).
% 3.66/1.59  tff(c_46, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.66/1.59  tff(c_93, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_46])).
% 3.66/1.59  tff(c_64, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.66/1.59  tff(c_113, plain, (~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_64])).
% 3.66/1.59  tff(c_70, plain, (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3') | r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.66/1.59  tff(c_140, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_113, c_70])).
% 3.66/1.59  tff(c_62, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.66/1.59  tff(c_98, plain, (![A_37]: (~v1_xboole_0(u1_struct_0(A_37)) | ~l1_struct_0(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.66/1.59  tff(c_101, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_92, c_98])).
% 3.66/1.59  tff(c_102, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_101])).
% 3.66/1.59  tff(c_103, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_102])).
% 3.66/1.59  tff(c_106, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_103])).
% 3.66/1.59  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_106])).
% 3.66/1.59  tff(c_111, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_102])).
% 3.66/1.59  tff(c_56, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.66/1.59  tff(c_112, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_102])).
% 3.66/1.59  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.66/1.59  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.66/1.59  tff(c_52, plain, (v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.66/1.59  tff(c_50, plain, (v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.66/1.59  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.66/1.59  tff(c_147, plain, (![A_50, B_51, C_52]: (v4_orders_2(k3_yellow19(A_50, B_51, C_52)) | ~m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_51)))) | ~v13_waybel_0(C_52, k3_yellow_1(B_51)) | ~v2_waybel_0(C_52, k3_yellow_1(B_51)) | v1_xboole_0(C_52) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | v1_xboole_0(B_51) | ~l1_struct_0(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.66/1.59  tff(c_152, plain, (![A_50]: (v4_orders_2(k3_yellow19(A_50, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_50))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_50) | v2_struct_0(A_50))), inference(resolution, [status(thm)], [c_48, c_147])).
% 3.66/1.59  tff(c_156, plain, (![A_50]: (v4_orders_2(k3_yellow19(A_50, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_50))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_50) | v2_struct_0(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_152])).
% 3.66/1.59  tff(c_158, plain, (![A_53]: (v4_orders_2(k3_yellow19(A_53, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_struct_0(A_53) | v2_struct_0(A_53))), inference(negUnitSimplification, [status(thm)], [c_111, c_56, c_156])).
% 3.66/1.59  tff(c_164, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_92, c_158])).
% 3.66/1.59  tff(c_167, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_164])).
% 3.66/1.59  tff(c_168, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_62, c_167])).
% 3.66/1.59  tff(c_169, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_168])).
% 3.66/1.59  tff(c_183, plain, (~r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_169])).
% 3.66/1.59  tff(c_187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_183])).
% 3.66/1.59  tff(c_189, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_168])).
% 3.66/1.59  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.66/1.59  tff(c_188, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_168])).
% 3.66/1.59  tff(c_54, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.66/1.59  tff(c_393, plain, (![A_101, B_102, C_103]: (v7_waybel_0(k3_yellow19(A_101, B_102, C_103)) | ~m1_subset_1(C_103, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_102)))) | ~v13_waybel_0(C_103, k3_yellow_1(B_102)) | ~v2_waybel_0(C_103, k3_yellow_1(B_102)) | ~v1_subset_1(C_103, u1_struct_0(k3_yellow_1(B_102))) | v1_xboole_0(C_103) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | v1_xboole_0(B_102) | ~l1_struct_0(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.66/1.59  tff(c_398, plain, (![A_101]: (v7_waybel_0(k3_yellow19(A_101, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_101))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_101) | v2_struct_0(A_101))), inference(resolution, [status(thm)], [c_48, c_393])).
% 3.66/1.59  tff(c_402, plain, (![A_101]: (v7_waybel_0(k3_yellow19(A_101, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_101))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_101) | v2_struct_0(A_101))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_398])).
% 3.66/1.59  tff(c_404, plain, (![A_104]: (v7_waybel_0(k3_yellow19(A_104, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_struct_0(A_104) | v2_struct_0(A_104))), inference(negUnitSimplification, [status(thm)], [c_111, c_56, c_402])).
% 3.66/1.59  tff(c_410, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_92, c_404])).
% 3.66/1.59  tff(c_413, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_189, c_410])).
% 3.66/1.59  tff(c_414, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_413])).
% 3.66/1.59  tff(c_316, plain, (![A_84, B_85, C_86]: (l1_waybel_0(k3_yellow19(A_84, B_85, C_86), A_84) | ~m1_subset_1(C_86, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_85)))) | ~v13_waybel_0(C_86, k3_yellow_1(B_85)) | ~v2_waybel_0(C_86, k3_yellow_1(B_85)) | v1_xboole_0(C_86) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | v1_xboole_0(B_85) | ~l1_struct_0(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.66/1.59  tff(c_321, plain, (![A_84]: (l1_waybel_0(k3_yellow19(A_84, k2_struct_0('#skF_1'), '#skF_2'), A_84) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_84))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_84) | v2_struct_0(A_84))), inference(resolution, [status(thm)], [c_48, c_316])).
% 3.66/1.59  tff(c_325, plain, (![A_84]: (l1_waybel_0(k3_yellow19(A_84, k2_struct_0('#skF_1'), '#skF_2'), A_84) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_84))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_84) | v2_struct_0(A_84))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_321])).
% 3.66/1.59  tff(c_327, plain, (![A_87]: (l1_waybel_0(k3_yellow19(A_87, k2_struct_0('#skF_1'), '#skF_2'), A_87) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_struct_0(A_87) | v2_struct_0(A_87))), inference(negUnitSimplification, [status(thm)], [c_111, c_56, c_325])).
% 3.66/1.59  tff(c_332, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_92, c_327])).
% 3.66/1.59  tff(c_335, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_189, c_332])).
% 3.66/1.59  tff(c_336, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_335])).
% 3.66/1.59  tff(c_471, plain, (![A_116, B_117]: (k2_yellow19(A_116, k3_yellow19(A_116, k2_struct_0(A_116), B_117))=B_117 | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_116))))) | ~v13_waybel_0(B_117, k3_yellow_1(k2_struct_0(A_116))) | ~v2_waybel_0(B_117, k3_yellow_1(k2_struct_0(A_116))) | ~v1_subset_1(B_117, u1_struct_0(k3_yellow_1(k2_struct_0(A_116)))) | v1_xboole_0(B_117) | ~l1_struct_0(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.66/1.59  tff(c_476, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_471])).
% 3.66/1.59  tff(c_480, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_54, c_52, c_50, c_476])).
% 3.66/1.59  tff(c_481, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_480])).
% 3.66/1.59  tff(c_40, plain, (![A_18, B_22, C_24]: (r3_waybel_9(A_18, B_22, C_24) | ~r1_waybel_7(A_18, k2_yellow19(A_18, B_22), C_24) | ~m1_subset_1(C_24, u1_struct_0(A_18)) | ~l1_waybel_0(B_22, A_18) | ~v7_waybel_0(B_22) | ~v4_orders_2(B_22) | v2_struct_0(B_22) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.66/1.59  tff(c_485, plain, (![C_24]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_24) | ~r1_waybel_7('#skF_1', '#skF_2', C_24) | ~m1_subset_1(C_24, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_481, c_40])).
% 3.66/1.59  tff(c_492, plain, (![C_24]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_24) | ~r1_waybel_7('#skF_1', '#skF_2', C_24) | ~m1_subset_1(C_24, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_188, c_414, c_336, c_92, c_485])).
% 3.66/1.59  tff(c_493, plain, (![C_24]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_24) | ~r1_waybel_7('#skF_1', '#skF_2', C_24) | ~m1_subset_1(C_24, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_62, c_492])).
% 3.66/1.59  tff(c_498, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_493])).
% 3.66/1.59  tff(c_32, plain, (![A_12, B_13, C_14]: (~v2_struct_0(k3_yellow19(A_12, B_13, C_14)) | ~m1_subset_1(C_14, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_13)))) | ~v13_waybel_0(C_14, k3_yellow_1(B_13)) | ~v2_waybel_0(C_14, k3_yellow_1(B_13)) | v1_xboole_0(C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_12))) | v1_xboole_0(B_13) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.66/1.59  tff(c_500, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_498, c_32])).
% 3.66/1.59  tff(c_503, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_189, c_92, c_52, c_50, c_48, c_500])).
% 3.66/1.59  tff(c_505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_111, c_56, c_503])).
% 3.66/1.59  tff(c_520, plain, (![C_121]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_121) | ~r1_waybel_7('#skF_1', '#skF_2', C_121) | ~m1_subset_1(C_121, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_493])).
% 3.66/1.59  tff(c_526, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_520, c_113])).
% 3.66/1.59  tff(c_531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_140, c_526])).
% 3.66/1.59  tff(c_532, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_64])).
% 3.66/1.59  tff(c_539, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_70])).
% 3.66/1.59  tff(c_540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_532, c_539])).
% 3.66/1.59  tff(c_541, plain, (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_70])).
% 3.66/1.59  tff(c_571, plain, (![A_134, B_135, C_136]: (v3_orders_2(k3_yellow19(A_134, B_135, C_136)) | ~m1_subset_1(C_136, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_135)))) | ~v13_waybel_0(C_136, k3_yellow_1(B_135)) | ~v2_waybel_0(C_136, k3_yellow_1(B_135)) | v1_xboole_0(C_136) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | v1_xboole_0(B_135) | ~l1_struct_0(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.66/1.59  tff(c_576, plain, (![A_134]: (v3_orders_2(k3_yellow19(A_134, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_134))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_134) | v2_struct_0(A_134))), inference(resolution, [status(thm)], [c_48, c_571])).
% 3.66/1.59  tff(c_580, plain, (![A_134]: (v3_orders_2(k3_yellow19(A_134, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_134))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_134) | v2_struct_0(A_134))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_576])).
% 3.66/1.59  tff(c_593, plain, (![A_140]: (v3_orders_2(k3_yellow19(A_140, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_struct_0(A_140) | v2_struct_0(A_140))), inference(negUnitSimplification, [status(thm)], [c_111, c_56, c_580])).
% 3.66/1.59  tff(c_599, plain, (v3_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_92, c_593])).
% 3.66/1.59  tff(c_602, plain, (v3_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_599])).
% 3.66/1.59  tff(c_603, plain, (v3_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_62, c_602])).
% 3.66/1.59  tff(c_604, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_603])).
% 3.66/1.59  tff(c_607, plain, (~r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_604])).
% 3.66/1.59  tff(c_611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_607])).
% 3.66/1.59  tff(c_613, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_603])).
% 3.66/1.59  tff(c_582, plain, (![A_137, B_138, C_139]: (v4_orders_2(k3_yellow19(A_137, B_138, C_139)) | ~m1_subset_1(C_139, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_138)))) | ~v13_waybel_0(C_139, k3_yellow_1(B_138)) | ~v2_waybel_0(C_139, k3_yellow_1(B_138)) | v1_xboole_0(C_139) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_137))) | v1_xboole_0(B_138) | ~l1_struct_0(A_137) | v2_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.66/1.59  tff(c_587, plain, (![A_137]: (v4_orders_2(k3_yellow19(A_137, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_137))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_137) | v2_struct_0(A_137))), inference(resolution, [status(thm)], [c_48, c_582])).
% 3.66/1.59  tff(c_591, plain, (![A_137]: (v4_orders_2(k3_yellow19(A_137, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_137))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_137) | v2_struct_0(A_137))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_587])).
% 3.66/1.59  tff(c_614, plain, (![A_141]: (v4_orders_2(k3_yellow19(A_141, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_struct_0(A_141) | v2_struct_0(A_141))), inference(negUnitSimplification, [status(thm)], [c_111, c_56, c_591])).
% 3.66/1.59  tff(c_620, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_92, c_614])).
% 3.66/1.59  tff(c_623, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_620])).
% 3.66/1.59  tff(c_624, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_62, c_623])).
% 3.66/1.59  tff(c_631, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_613, c_624])).
% 3.66/1.59  tff(c_819, plain, (![A_184, B_185, C_186]: (v7_waybel_0(k3_yellow19(A_184, B_185, C_186)) | ~m1_subset_1(C_186, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_185)))) | ~v13_waybel_0(C_186, k3_yellow_1(B_185)) | ~v2_waybel_0(C_186, k3_yellow_1(B_185)) | ~v1_subset_1(C_186, u1_struct_0(k3_yellow_1(B_185))) | v1_xboole_0(C_186) | ~m1_subset_1(B_185, k1_zfmisc_1(u1_struct_0(A_184))) | v1_xboole_0(B_185) | ~l1_struct_0(A_184) | v2_struct_0(A_184))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.66/1.59  tff(c_824, plain, (![A_184]: (v7_waybel_0(k3_yellow19(A_184, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_184))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_184) | v2_struct_0(A_184))), inference(resolution, [status(thm)], [c_48, c_819])).
% 3.66/1.59  tff(c_828, plain, (![A_184]: (v7_waybel_0(k3_yellow19(A_184, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_184))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_184) | v2_struct_0(A_184))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_824])).
% 3.66/1.59  tff(c_830, plain, (![A_187]: (v7_waybel_0(k3_yellow19(A_187, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_187))) | ~l1_struct_0(A_187) | v2_struct_0(A_187))), inference(negUnitSimplification, [status(thm)], [c_111, c_56, c_828])).
% 3.66/1.59  tff(c_836, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_92, c_830])).
% 3.66/1.59  tff(c_839, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_613, c_836])).
% 3.66/1.59  tff(c_840, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_839])).
% 3.66/1.59  tff(c_719, plain, (![A_161, B_162, C_163]: (l1_waybel_0(k3_yellow19(A_161, B_162, C_163), A_161) | ~m1_subset_1(C_163, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_162)))) | ~v13_waybel_0(C_163, k3_yellow_1(B_162)) | ~v2_waybel_0(C_163, k3_yellow_1(B_162)) | v1_xboole_0(C_163) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_161))) | v1_xboole_0(B_162) | ~l1_struct_0(A_161) | v2_struct_0(A_161))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.66/1.59  tff(c_724, plain, (![A_161]: (l1_waybel_0(k3_yellow19(A_161, k2_struct_0('#skF_1'), '#skF_2'), A_161) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_161))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_161) | v2_struct_0(A_161))), inference(resolution, [status(thm)], [c_48, c_719])).
% 3.66/1.59  tff(c_728, plain, (![A_161]: (l1_waybel_0(k3_yellow19(A_161, k2_struct_0('#skF_1'), '#skF_2'), A_161) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_161))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_161) | v2_struct_0(A_161))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_724])).
% 3.66/1.59  tff(c_730, plain, (![A_164]: (l1_waybel_0(k3_yellow19(A_164, k2_struct_0('#skF_1'), '#skF_2'), A_164) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_164))) | ~l1_struct_0(A_164) | v2_struct_0(A_164))), inference(negUnitSimplification, [status(thm)], [c_111, c_56, c_728])).
% 3.66/1.59  tff(c_735, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_92, c_730])).
% 3.66/1.59  tff(c_738, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_613, c_735])).
% 3.66/1.59  tff(c_739, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_738])).
% 3.66/1.59  tff(c_875, plain, (![A_194, B_195]: (k2_yellow19(A_194, k3_yellow19(A_194, k2_struct_0(A_194), B_195))=B_195 | ~m1_subset_1(B_195, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_194))))) | ~v13_waybel_0(B_195, k3_yellow_1(k2_struct_0(A_194))) | ~v2_waybel_0(B_195, k3_yellow_1(k2_struct_0(A_194))) | ~v1_subset_1(B_195, u1_struct_0(k3_yellow_1(k2_struct_0(A_194)))) | v1_xboole_0(B_195) | ~l1_struct_0(A_194) | v2_struct_0(A_194))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.66/1.59  tff(c_880, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_875])).
% 3.66/1.59  tff(c_884, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_54, c_52, c_50, c_880])).
% 3.66/1.59  tff(c_885, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_884])).
% 3.66/1.59  tff(c_42, plain, (![A_18, B_22, C_24]: (r1_waybel_7(A_18, k2_yellow19(A_18, B_22), C_24) | ~r3_waybel_9(A_18, B_22, C_24) | ~m1_subset_1(C_24, u1_struct_0(A_18)) | ~l1_waybel_0(B_22, A_18) | ~v7_waybel_0(B_22) | ~v4_orders_2(B_22) | v2_struct_0(B_22) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.66/1.59  tff(c_889, plain, (![C_24]: (r1_waybel_7('#skF_1', '#skF_2', C_24) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_24) | ~m1_subset_1(C_24, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_885, c_42])).
% 3.66/1.59  tff(c_896, plain, (![C_24]: (r1_waybel_7('#skF_1', '#skF_2', C_24) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_24) | ~m1_subset_1(C_24, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_631, c_840, c_739, c_92, c_889])).
% 3.66/1.59  tff(c_897, plain, (![C_24]: (r1_waybel_7('#skF_1', '#skF_2', C_24) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_24) | ~m1_subset_1(C_24, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_62, c_896])).
% 3.66/1.59  tff(c_902, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_897])).
% 3.66/1.59  tff(c_904, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_902, c_32])).
% 3.66/1.59  tff(c_907, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_613, c_92, c_52, c_50, c_48, c_904])).
% 3.66/1.59  tff(c_909, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_111, c_56, c_907])).
% 3.66/1.59  tff(c_924, plain, (![C_199]: (r1_waybel_7('#skF_1', '#skF_2', C_199) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_199) | ~m1_subset_1(C_199, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_897])).
% 3.66/1.59  tff(c_930, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_541, c_924])).
% 3.66/1.59  tff(c_934, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_930])).
% 3.66/1.59  tff(c_936, plain, $false, inference(negUnitSimplification, [status(thm)], [c_532, c_934])).
% 3.66/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.59  
% 3.66/1.59  Inference rules
% 3.66/1.59  ----------------------
% 3.66/1.59  #Ref     : 0
% 3.66/1.59  #Sup     : 150
% 3.66/1.59  #Fact    : 0
% 3.66/1.59  #Define  : 0
% 3.66/1.59  #Split   : 13
% 3.66/1.59  #Chain   : 0
% 3.66/1.59  #Close   : 0
% 3.66/1.59  
% 3.66/1.59  Ordering : KBO
% 3.66/1.59  
% 3.66/1.59  Simplification rules
% 3.66/1.59  ----------------------
% 3.66/1.59  #Subsume      : 20
% 3.66/1.59  #Demod        : 189
% 3.66/1.59  #Tautology    : 42
% 3.66/1.59  #SimpNegUnit  : 76
% 3.66/1.59  #BackRed      : 1
% 3.66/1.59  
% 3.66/1.59  #Partial instantiations: 0
% 3.66/1.59  #Strategies tried      : 1
% 3.66/1.59  
% 3.66/1.59  Timing (in seconds)
% 3.66/1.59  ----------------------
% 3.66/1.59  Preprocessing        : 0.36
% 3.66/1.59  Parsing              : 0.19
% 3.66/1.59  CNF conversion       : 0.03
% 3.66/1.59  Main loop            : 0.43
% 3.66/1.59  Inferencing          : 0.16
% 3.66/1.59  Reduction            : 0.14
% 3.66/1.59  Demodulation         : 0.10
% 3.66/1.59  BG Simplification    : 0.02
% 3.66/1.59  Subsumption          : 0.08
% 3.66/1.59  Abstraction          : 0.02
% 3.66/1.59  MUC search           : 0.00
% 3.66/1.59  Cooper               : 0.00
% 3.66/1.59  Total                : 0.85
% 3.66/1.59  Index Insertion      : 0.00
% 3.66/1.59  Index Deletion       : 0.00
% 3.66/1.59  Index Matching       : 0.00
% 3.66/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
