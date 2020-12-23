%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:34 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 4.28s
% Verified   : 
% Statistics : Number of formulae       :  201 (5070 expanded)
%              Number of leaves         :   49 (1761 expanded)
%              Depth                    :   23
%              Number of atoms          :  646 (20948 expanded)
%              Number of equality atoms :   43 (2407 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v4_pre_topc > v2_waybel_0 > v1_tops_1 > v1_subset_1 > v13_waybel_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k2_pre_topc > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_238,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_66,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_45,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_140,axiom,(
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

tff(f_168,axiom,(
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

tff(f_112,axiom,(
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

tff(f_211,axiom,(
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

tff(f_192,axiom,(
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

tff(c_66,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_8,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_12,plain,(
    ! [A_6] :
      ( v4_pre_topc(k2_struct_0(A_6),A_6)
      | ~ l1_pre_topc(A_6)
      | ~ v2_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_3] :
      ( m1_subset_1(k2_struct_0(A_3),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_106,plain,(
    ! [A_47,B_48] :
      ( k2_pre_topc(A_47,B_48) = B_48
      | ~ v4_pre_topc(B_48,A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_121,plain,(
    ! [A_50] :
      ( k2_pre_topc(A_50,k2_struct_0(A_50)) = k2_struct_0(A_50)
      | ~ v4_pre_topc(k2_struct_0(A_50),A_50)
      | ~ l1_pre_topc(A_50)
      | ~ l1_struct_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_125,plain,(
    ! [A_6] :
      ( k2_pre_topc(A_6,k2_struct_0(A_6)) = k2_struct_0(A_6)
      | ~ l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6)
      | ~ v2_pre_topc(A_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_121])).

tff(c_150,plain,(
    ! [B_55,A_56] :
      ( v1_tops_1(B_55,A_56)
      | k2_pre_topc(A_56,B_55) != k2_struct_0(A_56)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_170,plain,(
    ! [A_59] :
      ( v1_tops_1(k2_struct_0(A_59),A_59)
      | k2_pre_topc(A_59,k2_struct_0(A_59)) != k2_struct_0(A_59)
      | ~ l1_pre_topc(A_59)
      | ~ l1_struct_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_150])).

tff(c_135,plain,(
    ! [A_52,B_53] :
      ( k2_pre_topc(A_52,B_53) = u1_struct_0(A_52)
      | ~ v1_tops_1(B_53,A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_146,plain,(
    ! [A_3] :
      ( k2_pre_topc(A_3,k2_struct_0(A_3)) = u1_struct_0(A_3)
      | ~ v1_tops_1(k2_struct_0(A_3),A_3)
      | ~ l1_pre_topc(A_3)
      | ~ l1_struct_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_135])).

tff(c_253,plain,(
    ! [A_73] :
      ( k2_pre_topc(A_73,k2_struct_0(A_73)) = u1_struct_0(A_73)
      | k2_pre_topc(A_73,k2_struct_0(A_73)) != k2_struct_0(A_73)
      | ~ l1_pre_topc(A_73)
      | ~ l1_struct_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_170,c_146])).

tff(c_258,plain,(
    ! [A_74] :
      ( k2_pre_topc(A_74,k2_struct_0(A_74)) = u1_struct_0(A_74)
      | ~ l1_struct_0(A_74)
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_253])).

tff(c_285,plain,(
    ! [A_79] :
      ( u1_struct_0(A_79) = k2_struct_0(A_79)
      | ~ l1_struct_0(A_79)
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | ~ l1_struct_0(A_79)
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_125])).

tff(c_287,plain,
    ( u1_struct_0('#skF_1') = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_285])).

tff(c_290,plain,
    ( u1_struct_0('#skF_1') = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_287])).

tff(c_291,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_294,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_291])).

tff(c_298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_294])).

tff(c_299,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_301,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_54])).

tff(c_78,plain,
    ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3')
    | r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_103,plain,(
    r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_300,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_10,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_350,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_10])).

tff(c_384,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_350])).

tff(c_385,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_384])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_79,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_60,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_58,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_56,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_540,plain,(
    ! [A_97,B_98,C_99] :
      ( v4_orders_2(k3_yellow19(A_97,B_98,C_99))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_98))))
      | ~ v13_waybel_0(C_99,k3_yellow_1(B_98))
      | ~ v2_waybel_0(C_99,k3_yellow_1(B_98))
      | v1_xboole_0(C_99)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | v1_xboole_0(B_98)
      | ~ l1_struct_0(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_545,plain,(
    ! [A_97] :
      ( v4_orders_2(k3_yellow19(A_97,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_97)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_97)
      | v2_struct_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_56,c_540])).

tff(c_552,plain,(
    ! [A_97] :
      ( v4_orders_2(k3_yellow19(A_97,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_97)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_97)
      | v2_struct_0(A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_545])).

tff(c_555,plain,(
    ! [A_100] :
      ( v4_orders_2(k3_yellow19(A_100,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_struct_0(A_100)
      | v2_struct_0(A_100) ) ),
    inference(negUnitSimplification,[status(thm)],[c_385,c_64,c_552])).

tff(c_562,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_555])).

tff(c_568,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_562])).

tff(c_569,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_568])).

tff(c_62,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_633,plain,(
    ! [A_117,B_118,C_119] :
      ( v7_waybel_0(k3_yellow19(A_117,B_118,C_119))
      | ~ m1_subset_1(C_119,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_118))))
      | ~ v13_waybel_0(C_119,k3_yellow_1(B_118))
      | ~ v2_waybel_0(C_119,k3_yellow_1(B_118))
      | ~ v1_subset_1(C_119,u1_struct_0(k3_yellow_1(B_118)))
      | v1_xboole_0(C_119)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | v1_xboole_0(B_118)
      | ~ l1_struct_0(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_638,plain,(
    ! [A_117] :
      ( v7_waybel_0(k3_yellow19(A_117,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_117)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_117)
      | v2_struct_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_56,c_633])).

tff(c_645,plain,(
    ! [A_117] :
      ( v7_waybel_0(k3_yellow19(A_117,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_117)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_117)
      | v2_struct_0(A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_638])).

tff(c_648,plain,(
    ! [A_120] :
      ( v7_waybel_0(k3_yellow19(A_120,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_struct_0(A_120)
      | v2_struct_0(A_120) ) ),
    inference(negUnitSimplification,[status(thm)],[c_385,c_64,c_645])).

tff(c_655,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_648])).

tff(c_661,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_655])).

tff(c_662,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_661])).

tff(c_599,plain,(
    ! [A_105,B_106,C_107] :
      ( l1_waybel_0(k3_yellow19(A_105,B_106,C_107),A_105)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_106))))
      | ~ v13_waybel_0(C_107,k3_yellow_1(B_106))
      | ~ v2_waybel_0(C_107,k3_yellow_1(B_106))
      | v1_xboole_0(C_107)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | v1_xboole_0(B_106)
      | ~ l1_struct_0(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_604,plain,(
    ! [A_105] :
      ( l1_waybel_0(k3_yellow19(A_105,k2_struct_0('#skF_1'),'#skF_2'),A_105)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_105)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_105)
      | v2_struct_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_56,c_599])).

tff(c_611,plain,(
    ! [A_105] :
      ( l1_waybel_0(k3_yellow19(A_105,k2_struct_0('#skF_1'),'#skF_2'),A_105)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_105)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_105)
      | v2_struct_0(A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_604])).

tff(c_615,plain,(
    ! [A_108] :
      ( l1_waybel_0(k3_yellow19(A_108,k2_struct_0('#skF_1'),'#skF_2'),A_108)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_struct_0(A_108)
      | v2_struct_0(A_108) ) ),
    inference(negUnitSimplification,[status(thm)],[c_385,c_64,c_611])).

tff(c_620,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_615])).

tff(c_626,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_620])).

tff(c_627,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_626])).

tff(c_664,plain,(
    ! [A_121,B_122] :
      ( k2_yellow19(A_121,k3_yellow19(A_121,k2_struct_0(A_121),B_122)) = B_122
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_121)))))
      | ~ v13_waybel_0(B_122,k3_yellow_1(k2_struct_0(A_121)))
      | ~ v2_waybel_0(B_122,k3_yellow_1(k2_struct_0(A_121)))
      | ~ v1_subset_1(B_122,u1_struct_0(k3_yellow_1(k2_struct_0(A_121))))
      | v1_xboole_0(B_122)
      | ~ l1_struct_0(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_669,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_664])).

tff(c_676,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_62,c_60,c_58,c_669])).

tff(c_677,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_676])).

tff(c_50,plain,(
    ! [A_26,B_30,C_32] :
      ( r1_waybel_7(A_26,k2_yellow19(A_26,B_30),C_32)
      | ~ r3_waybel_9(A_26,B_30,C_32)
      | ~ m1_subset_1(C_32,u1_struct_0(A_26))
      | ~ l1_waybel_0(B_30,A_26)
      | ~ v7_waybel_0(B_30)
      | ~ v4_orders_2(B_30)
      | v2_struct_0(B_30)
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_682,plain,(
    ! [C_32] :
      ( r1_waybel_7('#skF_1','#skF_2',C_32)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_32)
      | ~ m1_subset_1(C_32,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_677,c_50])).

tff(c_689,plain,(
    ! [C_32] :
      ( r1_waybel_7('#skF_1','#skF_2',C_32)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_32)
      | ~ m1_subset_1(C_32,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_569,c_662,c_627,c_299,c_682])).

tff(c_690,plain,(
    ! [C_32] :
      ( r1_waybel_7('#skF_1','#skF_2',C_32)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_32)
      | ~ m1_subset_1(C_32,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_689])).

tff(c_695,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_690])).

tff(c_40,plain,(
    ! [A_20,B_21,C_22] :
      ( ~ v2_struct_0(k3_yellow19(A_20,B_21,C_22))
      | ~ m1_subset_1(C_22,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_21))))
      | ~ v13_waybel_0(C_22,k3_yellow_1(B_21))
      | ~ v2_waybel_0(C_22,k3_yellow_1(B_21))
      | v1_xboole_0(C_22)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_20)))
      | v1_xboole_0(B_21)
      | ~ l1_struct_0(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_697,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_695,c_40])).

tff(c_700,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_79,c_299,c_60,c_58,c_56,c_697])).

tff(c_702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_385,c_64,c_700])).

tff(c_704,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_690])).

tff(c_48,plain,(
    ! [A_26,B_30,C_32] :
      ( r3_waybel_9(A_26,B_30,C_32)
      | ~ r1_waybel_7(A_26,k2_yellow19(A_26,B_30),C_32)
      | ~ m1_subset_1(C_32,u1_struct_0(A_26))
      | ~ l1_waybel_0(B_30,A_26)
      | ~ v7_waybel_0(B_30)
      | ~ v4_orders_2(B_30)
      | v2_struct_0(B_30)
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_685,plain,(
    ! [C_32] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_32)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_32)
      | ~ m1_subset_1(C_32,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_677,c_48])).

tff(c_692,plain,(
    ! [C_32] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_32)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_32)
      | ~ m1_subset_1(C_32,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_569,c_662,c_627,c_299,c_685])).

tff(c_693,plain,(
    ! [C_32] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_32)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_32)
      | ~ m1_subset_1(C_32,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_692])).

tff(c_708,plain,(
    ! [C_126] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_126)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_126)
      | ~ m1_subset_1(C_126,k2_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_704,c_693])).

tff(c_72,plain,
    ( ~ r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_105,plain,(
    ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72])).

tff(c_714,plain,
    ( ~ r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_708,c_105])).

tff(c_719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_103,c_714])).

tff(c_721,plain,(
    ~ r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_724,plain,(
    ! [A_127,B_128] :
      ( k2_pre_topc(A_127,B_128) = B_128
      | ~ v4_pre_topc(B_128,A_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_739,plain,(
    ! [A_130] :
      ( k2_pre_topc(A_130,k2_struct_0(A_130)) = k2_struct_0(A_130)
      | ~ v4_pre_topc(k2_struct_0(A_130),A_130)
      | ~ l1_pre_topc(A_130)
      | ~ l1_struct_0(A_130) ) ),
    inference(resolution,[status(thm)],[c_6,c_724])).

tff(c_743,plain,(
    ! [A_6] :
      ( k2_pre_topc(A_6,k2_struct_0(A_6)) = k2_struct_0(A_6)
      | ~ l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6)
      | ~ v2_pre_topc(A_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_739])).

tff(c_753,plain,(
    ! [B_132,A_133] :
      ( v1_tops_1(B_132,A_133)
      | k2_pre_topc(A_133,B_132) != k2_struct_0(A_133)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_764,plain,(
    ! [A_3] :
      ( v1_tops_1(k2_struct_0(A_3),A_3)
      | k2_pre_topc(A_3,k2_struct_0(A_3)) != k2_struct_0(A_3)
      | ~ l1_pre_topc(A_3)
      | ~ l1_struct_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_753])).

tff(c_786,plain,(
    ! [A_140,B_141] :
      ( k2_pre_topc(A_140,B_141) = u1_struct_0(A_140)
      | ~ v1_tops_1(B_141,A_140)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_809,plain,(
    ! [A_143] :
      ( k2_pre_topc(A_143,k2_struct_0(A_143)) = u1_struct_0(A_143)
      | ~ v1_tops_1(k2_struct_0(A_143),A_143)
      | ~ l1_pre_topc(A_143)
      | ~ l1_struct_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_6,c_786])).

tff(c_875,plain,(
    ! [A_154] :
      ( k2_pre_topc(A_154,k2_struct_0(A_154)) = u1_struct_0(A_154)
      | k2_pre_topc(A_154,k2_struct_0(A_154)) != k2_struct_0(A_154)
      | ~ l1_pre_topc(A_154)
      | ~ l1_struct_0(A_154) ) ),
    inference(resolution,[status(thm)],[c_764,c_809])).

tff(c_881,plain,(
    ! [A_158] :
      ( k2_pre_topc(A_158,k2_struct_0(A_158)) = u1_struct_0(A_158)
      | ~ l1_struct_0(A_158)
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_743,c_875])).

tff(c_903,plain,(
    ! [A_159] :
      ( u1_struct_0(A_159) = k2_struct_0(A_159)
      | ~ l1_struct_0(A_159)
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159)
      | ~ l1_struct_0(A_159)
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_881,c_743])).

tff(c_905,plain,
    ( u1_struct_0('#skF_1') = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_903])).

tff(c_908,plain,
    ( u1_struct_0('#skF_1') = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_905])).

tff(c_909,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_908])).

tff(c_912,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_909])).

tff(c_916,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_912])).

tff(c_917,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_908])).

tff(c_919,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_917,c_54])).

tff(c_720,plain,(
    r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_918,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_908])).

tff(c_968,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_917,c_10])).

tff(c_1002,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_968])).

tff(c_1003,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1002])).

tff(c_1147,plain,(
    ! [A_169,B_170,C_171] :
      ( v4_orders_2(k3_yellow19(A_169,B_170,C_171))
      | ~ m1_subset_1(C_171,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_170))))
      | ~ v13_waybel_0(C_171,k3_yellow_1(B_170))
      | ~ v2_waybel_0(C_171,k3_yellow_1(B_170))
      | v1_xboole_0(C_171)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_169)))
      | v1_xboole_0(B_170)
      | ~ l1_struct_0(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1152,plain,(
    ! [A_169] :
      ( v4_orders_2(k3_yellow19(A_169,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_169)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_169)
      | v2_struct_0(A_169) ) ),
    inference(resolution,[status(thm)],[c_56,c_1147])).

tff(c_1159,plain,(
    ! [A_169] :
      ( v4_orders_2(k3_yellow19(A_169,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_169)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_169)
      | v2_struct_0(A_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1152])).

tff(c_1178,plain,(
    ! [A_174] :
      ( v4_orders_2(k3_yellow19(A_174,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_struct_0(A_174)
      | v2_struct_0(A_174) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1003,c_64,c_1159])).

tff(c_1185,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_1178])).

tff(c_1191,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_1185])).

tff(c_1192,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1191])).

tff(c_1195,plain,(
    ! [A_178,B_179,C_180] :
      ( l1_waybel_0(k3_yellow19(A_178,B_179,C_180),A_178)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_179))))
      | ~ v13_waybel_0(C_180,k3_yellow_1(B_179))
      | ~ v2_waybel_0(C_180,k3_yellow_1(B_179))
      | v1_xboole_0(C_180)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | v1_xboole_0(B_179)
      | ~ l1_struct_0(A_178)
      | v2_struct_0(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1200,plain,(
    ! [A_178] :
      ( l1_waybel_0(k3_yellow19(A_178,k2_struct_0('#skF_1'),'#skF_2'),A_178)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_178)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_178)
      | v2_struct_0(A_178) ) ),
    inference(resolution,[status(thm)],[c_56,c_1195])).

tff(c_1207,plain,(
    ! [A_178] :
      ( l1_waybel_0(k3_yellow19(A_178,k2_struct_0('#skF_1'),'#skF_2'),A_178)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_178)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_178)
      | v2_struct_0(A_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1200])).

tff(c_1210,plain,(
    ! [A_181] :
      ( l1_waybel_0(k3_yellow19(A_181,k2_struct_0('#skF_1'),'#skF_2'),A_181)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ l1_struct_0(A_181)
      | v2_struct_0(A_181) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1003,c_64,c_1207])).

tff(c_1215,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_1210])).

tff(c_1221,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_1215])).

tff(c_1222,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1221])).

tff(c_1255,plain,(
    ! [A_190,B_191] :
      ( k2_yellow19(A_190,k3_yellow19(A_190,k2_struct_0(A_190),B_191)) = B_191
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_190)))))
      | ~ v13_waybel_0(B_191,k3_yellow_1(k2_struct_0(A_190)))
      | ~ v2_waybel_0(B_191,k3_yellow_1(k2_struct_0(A_190)))
      | ~ v1_subset_1(B_191,u1_struct_0(k3_yellow_1(k2_struct_0(A_190))))
      | v1_xboole_0(B_191)
      | ~ l1_struct_0(A_190)
      | v2_struct_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_1260,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_1255])).

tff(c_1267,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_62,c_60,c_58,c_1260])).

tff(c_1268,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_1267])).

tff(c_1273,plain,(
    ! [C_32] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_32)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_32)
      | ~ m1_subset_1(C_32,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1268,c_48])).

tff(c_1280,plain,(
    ! [C_32] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_32)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_32)
      | ~ m1_subset_1(C_32,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1192,c_1222,c_917,c_1273])).

tff(c_1281,plain,(
    ! [C_32] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_32)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_32)
      | ~ m1_subset_1(C_32,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1280])).

tff(c_1286,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1281])).

tff(c_1289,plain,(
    ! [A_196,B_197,C_198] :
      ( v7_waybel_0(k3_yellow19(A_196,B_197,C_198))
      | ~ m1_subset_1(C_198,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_197))))
      | ~ v13_waybel_0(C_198,k3_yellow_1(B_197))
      | ~ v2_waybel_0(C_198,k3_yellow_1(B_197))
      | ~ v1_subset_1(C_198,u1_struct_0(k3_yellow_1(B_197)))
      | v1_xboole_0(C_198)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0(A_196)))
      | v1_xboole_0(B_197)
      | ~ l1_struct_0(A_196)
      | v2_struct_0(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_1294,plain,(
    ! [A_196] :
      ( v7_waybel_0(k3_yellow19(A_196,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_196)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_196)
      | v2_struct_0(A_196) ) ),
    inference(resolution,[status(thm)],[c_56,c_1289])).

tff(c_1301,plain,(
    ! [A_196] :
      ( v7_waybel_0(k3_yellow19(A_196,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_196)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_196)
      | v2_struct_0(A_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_1294])).

tff(c_1304,plain,(
    ! [A_199] :
      ( v7_waybel_0(k3_yellow19(A_199,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ l1_struct_0(A_199)
      | v2_struct_0(A_199) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1003,c_64,c_1301])).

tff(c_1307,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_917,c_1304])).

tff(c_1313,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_79,c_1307])).

tff(c_1315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1286,c_1313])).

tff(c_1316,plain,(
    ! [C_32] :
      ( v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_32)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_32)
      | ~ m1_subset_1(C_32,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_1281])).

tff(c_1348,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1316])).

tff(c_1350,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1348,c_40])).

tff(c_1353,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_79,c_917,c_60,c_58,c_56,c_1350])).

tff(c_1355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1003,c_64,c_1353])).

tff(c_1357,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1316])).

tff(c_1317,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1281])).

tff(c_1276,plain,(
    ! [C_32] :
      ( r1_waybel_7('#skF_1','#skF_2',C_32)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_32)
      | ~ m1_subset_1(C_32,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1268,c_50])).

tff(c_1283,plain,(
    ! [C_32] :
      ( r1_waybel_7('#skF_1','#skF_2',C_32)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_32)
      | ~ m1_subset_1(C_32,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1192,c_1222,c_917,c_1276])).

tff(c_1284,plain,(
    ! [C_32] :
      ( r1_waybel_7('#skF_1','#skF_2',C_32)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_32)
      | ~ m1_subset_1(C_32,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1283])).

tff(c_1359,plain,(
    ! [C_32] :
      ( r1_waybel_7('#skF_1','#skF_2',C_32)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_32)
      | ~ m1_subset_1(C_32,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1317,c_1284])).

tff(c_1360,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1359])).

tff(c_1361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1357,c_1360])).

tff(c_1364,plain,(
    ! [C_204] :
      ( r1_waybel_7('#skF_1','#skF_2',C_204)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_204)
      | ~ m1_subset_1(C_204,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_1359])).

tff(c_1367,plain,
    ( r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_720,c_1364])).

tff(c_1370,plain,(
    r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_919,c_1367])).

tff(c_1372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_721,c_1370])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:52:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.70  
% 4.28/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.70  %$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v4_pre_topc > v2_waybel_0 > v1_tops_1 > v1_subset_1 > v13_waybel_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k2_pre_topc > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1
% 4.28/1.70  
% 4.28/1.70  %Foreground sorts:
% 4.28/1.70  
% 4.28/1.70  
% 4.28/1.70  %Background operators:
% 4.28/1.70  
% 4.28/1.70  
% 4.28/1.70  %Foreground operators:
% 4.28/1.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.28/1.70  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.28/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.28/1.70  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 4.28/1.70  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 4.28/1.70  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.28/1.70  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 4.28/1.70  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 4.28/1.70  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.28/1.70  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 4.28/1.70  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.28/1.70  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 4.28/1.70  tff('#skF_2', type, '#skF_2': $i).
% 4.28/1.70  tff('#skF_3', type, '#skF_3': $i).
% 4.28/1.70  tff('#skF_1', type, '#skF_1': $i).
% 4.28/1.70  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 4.28/1.70  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.28/1.70  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 4.28/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.28/1.70  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.28/1.70  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.28/1.70  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 4.28/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.28/1.70  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 4.28/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.28/1.70  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 4.28/1.70  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 4.28/1.70  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.28/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.28/1.70  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.28/1.70  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.28/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.28/1.70  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.28/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.28/1.70  
% 4.28/1.74  tff(f_238, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, k3_yellow19(A, k2_struct_0(A), B), C) <=> r1_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_yellow19)).
% 4.28/1.74  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.28/1.74  tff(f_51, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 4.28/1.74  tff(f_33, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 4.28/1.74  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.28/1.74  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 4.28/1.74  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 4.28/1.74  tff(f_45, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.28/1.74  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.28/1.74  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.28/1.74  tff(f_140, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_yellow19)).
% 4.28/1.74  tff(f_168, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow19)).
% 4.28/1.74  tff(f_112, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 4.28/1.74  tff(f_211, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 4.28/1.74  tff(f_192, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> r1_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_yellow19)).
% 4.28/1.74  tff(c_66, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.28/1.74  tff(c_8, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.28/1.74  tff(c_68, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.28/1.74  tff(c_12, plain, (![A_6]: (v4_pre_topc(k2_struct_0(A_6), A_6) | ~l1_pre_topc(A_6) | ~v2_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.28/1.74  tff(c_6, plain, (![A_3]: (m1_subset_1(k2_struct_0(A_3), k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.28/1.74  tff(c_106, plain, (![A_47, B_48]: (k2_pre_topc(A_47, B_48)=B_48 | ~v4_pre_topc(B_48, A_47) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.28/1.74  tff(c_121, plain, (![A_50]: (k2_pre_topc(A_50, k2_struct_0(A_50))=k2_struct_0(A_50) | ~v4_pre_topc(k2_struct_0(A_50), A_50) | ~l1_pre_topc(A_50) | ~l1_struct_0(A_50))), inference(resolution, [status(thm)], [c_6, c_106])).
% 4.28/1.74  tff(c_125, plain, (![A_6]: (k2_pre_topc(A_6, k2_struct_0(A_6))=k2_struct_0(A_6) | ~l1_struct_0(A_6) | ~l1_pre_topc(A_6) | ~v2_pre_topc(A_6))), inference(resolution, [status(thm)], [c_12, c_121])).
% 4.28/1.74  tff(c_150, plain, (![B_55, A_56]: (v1_tops_1(B_55, A_56) | k2_pre_topc(A_56, B_55)!=k2_struct_0(A_56) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.28/1.74  tff(c_170, plain, (![A_59]: (v1_tops_1(k2_struct_0(A_59), A_59) | k2_pre_topc(A_59, k2_struct_0(A_59))!=k2_struct_0(A_59) | ~l1_pre_topc(A_59) | ~l1_struct_0(A_59))), inference(resolution, [status(thm)], [c_6, c_150])).
% 4.28/1.74  tff(c_135, plain, (![A_52, B_53]: (k2_pre_topc(A_52, B_53)=u1_struct_0(A_52) | ~v1_tops_1(B_53, A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.28/1.74  tff(c_146, plain, (![A_3]: (k2_pre_topc(A_3, k2_struct_0(A_3))=u1_struct_0(A_3) | ~v1_tops_1(k2_struct_0(A_3), A_3) | ~l1_pre_topc(A_3) | ~l1_struct_0(A_3))), inference(resolution, [status(thm)], [c_6, c_135])).
% 4.28/1.74  tff(c_253, plain, (![A_73]: (k2_pre_topc(A_73, k2_struct_0(A_73))=u1_struct_0(A_73) | k2_pre_topc(A_73, k2_struct_0(A_73))!=k2_struct_0(A_73) | ~l1_pre_topc(A_73) | ~l1_struct_0(A_73))), inference(resolution, [status(thm)], [c_170, c_146])).
% 4.28/1.74  tff(c_258, plain, (![A_74]: (k2_pre_topc(A_74, k2_struct_0(A_74))=u1_struct_0(A_74) | ~l1_struct_0(A_74) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(superposition, [status(thm), theory('equality')], [c_125, c_253])).
% 4.28/1.74  tff(c_285, plain, (![A_79]: (u1_struct_0(A_79)=k2_struct_0(A_79) | ~l1_struct_0(A_79) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79) | ~l1_struct_0(A_79) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79))), inference(superposition, [status(thm), theory('equality')], [c_258, c_125])).
% 4.28/1.74  tff(c_287, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_285])).
% 4.28/1.74  tff(c_290, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_287])).
% 4.28/1.74  tff(c_291, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_290])).
% 4.28/1.74  tff(c_294, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_291])).
% 4.28/1.74  tff(c_298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_294])).
% 4.28/1.74  tff(c_299, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_290])).
% 4.28/1.74  tff(c_54, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.28/1.74  tff(c_301, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_54])).
% 4.28/1.74  tff(c_78, plain, (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3') | r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.28/1.74  tff(c_103, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_78])).
% 4.28/1.74  tff(c_70, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.28/1.74  tff(c_300, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_290])).
% 4.28/1.74  tff(c_10, plain, (![A_5]: (~v1_xboole_0(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.28/1.74  tff(c_350, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_299, c_10])).
% 4.28/1.74  tff(c_384, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_300, c_350])).
% 4.28/1.74  tff(c_385, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_70, c_384])).
% 4.28/1.74  tff(c_64, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.28/1.74  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.28/1.74  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.28/1.74  tff(c_79, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 4.28/1.74  tff(c_60, plain, (v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.28/1.74  tff(c_58, plain, (v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.28/1.74  tff(c_56, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.28/1.74  tff(c_540, plain, (![A_97, B_98, C_99]: (v4_orders_2(k3_yellow19(A_97, B_98, C_99)) | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_98)))) | ~v13_waybel_0(C_99, k3_yellow_1(B_98)) | ~v2_waybel_0(C_99, k3_yellow_1(B_98)) | v1_xboole_0(C_99) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | v1_xboole_0(B_98) | ~l1_struct_0(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.28/1.74  tff(c_545, plain, (![A_97]: (v4_orders_2(k3_yellow19(A_97, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_97))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_97) | v2_struct_0(A_97))), inference(resolution, [status(thm)], [c_56, c_540])).
% 4.28/1.74  tff(c_552, plain, (![A_97]: (v4_orders_2(k3_yellow19(A_97, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_97))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_97) | v2_struct_0(A_97))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_545])).
% 4.28/1.74  tff(c_555, plain, (![A_100]: (v4_orders_2(k3_yellow19(A_100, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_struct_0(A_100) | v2_struct_0(A_100))), inference(negUnitSimplification, [status(thm)], [c_385, c_64, c_552])).
% 4.28/1.74  tff(c_562, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6, c_555])).
% 4.28/1.74  tff(c_568, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_300, c_562])).
% 4.28/1.74  tff(c_569, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_70, c_568])).
% 4.28/1.74  tff(c_62, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.28/1.74  tff(c_633, plain, (![A_117, B_118, C_119]: (v7_waybel_0(k3_yellow19(A_117, B_118, C_119)) | ~m1_subset_1(C_119, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_118)))) | ~v13_waybel_0(C_119, k3_yellow_1(B_118)) | ~v2_waybel_0(C_119, k3_yellow_1(B_118)) | ~v1_subset_1(C_119, u1_struct_0(k3_yellow_1(B_118))) | v1_xboole_0(C_119) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | v1_xboole_0(B_118) | ~l1_struct_0(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.28/1.74  tff(c_638, plain, (![A_117]: (v7_waybel_0(k3_yellow19(A_117, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_117))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_117) | v2_struct_0(A_117))), inference(resolution, [status(thm)], [c_56, c_633])).
% 4.28/1.74  tff(c_645, plain, (![A_117]: (v7_waybel_0(k3_yellow19(A_117, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_117))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_117) | v2_struct_0(A_117))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_638])).
% 4.28/1.74  tff(c_648, plain, (![A_120]: (v7_waybel_0(k3_yellow19(A_120, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_struct_0(A_120) | v2_struct_0(A_120))), inference(negUnitSimplification, [status(thm)], [c_385, c_64, c_645])).
% 4.28/1.74  tff(c_655, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6, c_648])).
% 4.28/1.74  tff(c_661, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_300, c_655])).
% 4.28/1.74  tff(c_662, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_70, c_661])).
% 4.28/1.74  tff(c_599, plain, (![A_105, B_106, C_107]: (l1_waybel_0(k3_yellow19(A_105, B_106, C_107), A_105) | ~m1_subset_1(C_107, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_106)))) | ~v13_waybel_0(C_107, k3_yellow_1(B_106)) | ~v2_waybel_0(C_107, k3_yellow_1(B_106)) | v1_xboole_0(C_107) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | v1_xboole_0(B_106) | ~l1_struct_0(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.28/1.74  tff(c_604, plain, (![A_105]: (l1_waybel_0(k3_yellow19(A_105, k2_struct_0('#skF_1'), '#skF_2'), A_105) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_105))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_105) | v2_struct_0(A_105))), inference(resolution, [status(thm)], [c_56, c_599])).
% 4.28/1.74  tff(c_611, plain, (![A_105]: (l1_waybel_0(k3_yellow19(A_105, k2_struct_0('#skF_1'), '#skF_2'), A_105) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_105))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_105) | v2_struct_0(A_105))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_604])).
% 4.28/1.74  tff(c_615, plain, (![A_108]: (l1_waybel_0(k3_yellow19(A_108, k2_struct_0('#skF_1'), '#skF_2'), A_108) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_struct_0(A_108) | v2_struct_0(A_108))), inference(negUnitSimplification, [status(thm)], [c_385, c_64, c_611])).
% 4.28/1.74  tff(c_620, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6, c_615])).
% 4.28/1.74  tff(c_626, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_300, c_620])).
% 4.28/1.74  tff(c_627, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_70, c_626])).
% 4.28/1.74  tff(c_664, plain, (![A_121, B_122]: (k2_yellow19(A_121, k3_yellow19(A_121, k2_struct_0(A_121), B_122))=B_122 | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_121))))) | ~v13_waybel_0(B_122, k3_yellow_1(k2_struct_0(A_121))) | ~v2_waybel_0(B_122, k3_yellow_1(k2_struct_0(A_121))) | ~v1_subset_1(B_122, u1_struct_0(k3_yellow_1(k2_struct_0(A_121)))) | v1_xboole_0(B_122) | ~l1_struct_0(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.28/1.74  tff(c_669, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_664])).
% 4.28/1.74  tff(c_676, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_300, c_62, c_60, c_58, c_669])).
% 4.28/1.74  tff(c_677, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_676])).
% 4.28/1.74  tff(c_50, plain, (![A_26, B_30, C_32]: (r1_waybel_7(A_26, k2_yellow19(A_26, B_30), C_32) | ~r3_waybel_9(A_26, B_30, C_32) | ~m1_subset_1(C_32, u1_struct_0(A_26)) | ~l1_waybel_0(B_30, A_26) | ~v7_waybel_0(B_30) | ~v4_orders_2(B_30) | v2_struct_0(B_30) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.28/1.74  tff(c_682, plain, (![C_32]: (r1_waybel_7('#skF_1', '#skF_2', C_32) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_32) | ~m1_subset_1(C_32, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_677, c_50])).
% 4.28/1.74  tff(c_689, plain, (![C_32]: (r1_waybel_7('#skF_1', '#skF_2', C_32) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_32) | ~m1_subset_1(C_32, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_569, c_662, c_627, c_299, c_682])).
% 4.28/1.74  tff(c_690, plain, (![C_32]: (r1_waybel_7('#skF_1', '#skF_2', C_32) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_32) | ~m1_subset_1(C_32, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_70, c_689])).
% 4.28/1.74  tff(c_695, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_690])).
% 4.28/1.74  tff(c_40, plain, (![A_20, B_21, C_22]: (~v2_struct_0(k3_yellow19(A_20, B_21, C_22)) | ~m1_subset_1(C_22, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_21)))) | ~v13_waybel_0(C_22, k3_yellow_1(B_21)) | ~v2_waybel_0(C_22, k3_yellow_1(B_21)) | v1_xboole_0(C_22) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_20))) | v1_xboole_0(B_21) | ~l1_struct_0(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.28/1.74  tff(c_697, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_695, c_40])).
% 4.28/1.74  tff(c_700, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_300, c_79, c_299, c_60, c_58, c_56, c_697])).
% 4.28/1.74  tff(c_702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_385, c_64, c_700])).
% 4.28/1.74  tff(c_704, plain, (~v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_690])).
% 4.28/1.74  tff(c_48, plain, (![A_26, B_30, C_32]: (r3_waybel_9(A_26, B_30, C_32) | ~r1_waybel_7(A_26, k2_yellow19(A_26, B_30), C_32) | ~m1_subset_1(C_32, u1_struct_0(A_26)) | ~l1_waybel_0(B_30, A_26) | ~v7_waybel_0(B_30) | ~v4_orders_2(B_30) | v2_struct_0(B_30) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.28/1.74  tff(c_685, plain, (![C_32]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_32) | ~r1_waybel_7('#skF_1', '#skF_2', C_32) | ~m1_subset_1(C_32, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_677, c_48])).
% 4.28/1.74  tff(c_692, plain, (![C_32]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_32) | ~r1_waybel_7('#skF_1', '#skF_2', C_32) | ~m1_subset_1(C_32, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_569, c_662, c_627, c_299, c_685])).
% 4.28/1.74  tff(c_693, plain, (![C_32]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_32) | ~r1_waybel_7('#skF_1', '#skF_2', C_32) | ~m1_subset_1(C_32, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_70, c_692])).
% 4.28/1.74  tff(c_708, plain, (![C_126]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_126) | ~r1_waybel_7('#skF_1', '#skF_2', C_126) | ~m1_subset_1(C_126, k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_704, c_693])).
% 4.28/1.74  tff(c_72, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.28/1.74  tff(c_105, plain, (~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_72])).
% 4.28/1.74  tff(c_714, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_708, c_105])).
% 4.28/1.74  tff(c_719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_301, c_103, c_714])).
% 4.28/1.74  tff(c_721, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_78])).
% 4.28/1.74  tff(c_724, plain, (![A_127, B_128]: (k2_pre_topc(A_127, B_128)=B_128 | ~v4_pre_topc(B_128, A_127) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.28/1.74  tff(c_739, plain, (![A_130]: (k2_pre_topc(A_130, k2_struct_0(A_130))=k2_struct_0(A_130) | ~v4_pre_topc(k2_struct_0(A_130), A_130) | ~l1_pre_topc(A_130) | ~l1_struct_0(A_130))), inference(resolution, [status(thm)], [c_6, c_724])).
% 4.28/1.74  tff(c_743, plain, (![A_6]: (k2_pre_topc(A_6, k2_struct_0(A_6))=k2_struct_0(A_6) | ~l1_struct_0(A_6) | ~l1_pre_topc(A_6) | ~v2_pre_topc(A_6))), inference(resolution, [status(thm)], [c_12, c_739])).
% 4.28/1.74  tff(c_753, plain, (![B_132, A_133]: (v1_tops_1(B_132, A_133) | k2_pre_topc(A_133, B_132)!=k2_struct_0(A_133) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.28/1.74  tff(c_764, plain, (![A_3]: (v1_tops_1(k2_struct_0(A_3), A_3) | k2_pre_topc(A_3, k2_struct_0(A_3))!=k2_struct_0(A_3) | ~l1_pre_topc(A_3) | ~l1_struct_0(A_3))), inference(resolution, [status(thm)], [c_6, c_753])).
% 4.28/1.74  tff(c_786, plain, (![A_140, B_141]: (k2_pre_topc(A_140, B_141)=u1_struct_0(A_140) | ~v1_tops_1(B_141, A_140) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.28/1.74  tff(c_809, plain, (![A_143]: (k2_pre_topc(A_143, k2_struct_0(A_143))=u1_struct_0(A_143) | ~v1_tops_1(k2_struct_0(A_143), A_143) | ~l1_pre_topc(A_143) | ~l1_struct_0(A_143))), inference(resolution, [status(thm)], [c_6, c_786])).
% 4.28/1.74  tff(c_875, plain, (![A_154]: (k2_pre_topc(A_154, k2_struct_0(A_154))=u1_struct_0(A_154) | k2_pre_topc(A_154, k2_struct_0(A_154))!=k2_struct_0(A_154) | ~l1_pre_topc(A_154) | ~l1_struct_0(A_154))), inference(resolution, [status(thm)], [c_764, c_809])).
% 4.28/1.74  tff(c_881, plain, (![A_158]: (k2_pre_topc(A_158, k2_struct_0(A_158))=u1_struct_0(A_158) | ~l1_struct_0(A_158) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158))), inference(superposition, [status(thm), theory('equality')], [c_743, c_875])).
% 4.28/1.74  tff(c_903, plain, (![A_159]: (u1_struct_0(A_159)=k2_struct_0(A_159) | ~l1_struct_0(A_159) | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159) | ~l1_struct_0(A_159) | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159))), inference(superposition, [status(thm), theory('equality')], [c_881, c_743])).
% 4.28/1.74  tff(c_905, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_903])).
% 4.28/1.74  tff(c_908, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_905])).
% 4.28/1.74  tff(c_909, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_908])).
% 4.28/1.74  tff(c_912, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_909])).
% 4.28/1.74  tff(c_916, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_912])).
% 4.28/1.74  tff(c_917, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_908])).
% 4.28/1.74  tff(c_919, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_917, c_54])).
% 4.28/1.74  tff(c_720, plain, (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_78])).
% 4.28/1.74  tff(c_918, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_908])).
% 4.28/1.74  tff(c_968, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_917, c_10])).
% 4.28/1.74  tff(c_1002, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_918, c_968])).
% 4.28/1.74  tff(c_1003, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_70, c_1002])).
% 4.28/1.74  tff(c_1147, plain, (![A_169, B_170, C_171]: (v4_orders_2(k3_yellow19(A_169, B_170, C_171)) | ~m1_subset_1(C_171, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_170)))) | ~v13_waybel_0(C_171, k3_yellow_1(B_170)) | ~v2_waybel_0(C_171, k3_yellow_1(B_170)) | v1_xboole_0(C_171) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0(A_169))) | v1_xboole_0(B_170) | ~l1_struct_0(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.28/1.74  tff(c_1152, plain, (![A_169]: (v4_orders_2(k3_yellow19(A_169, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_169))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_169) | v2_struct_0(A_169))), inference(resolution, [status(thm)], [c_56, c_1147])).
% 4.28/1.74  tff(c_1159, plain, (![A_169]: (v4_orders_2(k3_yellow19(A_169, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_169))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_169) | v2_struct_0(A_169))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1152])).
% 4.28/1.74  tff(c_1178, plain, (![A_174]: (v4_orders_2(k3_yellow19(A_174, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_struct_0(A_174) | v2_struct_0(A_174))), inference(negUnitSimplification, [status(thm)], [c_1003, c_64, c_1159])).
% 4.28/1.74  tff(c_1185, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6, c_1178])).
% 4.28/1.74  tff(c_1191, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_918, c_1185])).
% 4.28/1.74  tff(c_1192, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_70, c_1191])).
% 4.28/1.74  tff(c_1195, plain, (![A_178, B_179, C_180]: (l1_waybel_0(k3_yellow19(A_178, B_179, C_180), A_178) | ~m1_subset_1(C_180, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_179)))) | ~v13_waybel_0(C_180, k3_yellow_1(B_179)) | ~v2_waybel_0(C_180, k3_yellow_1(B_179)) | v1_xboole_0(C_180) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_178))) | v1_xboole_0(B_179) | ~l1_struct_0(A_178) | v2_struct_0(A_178))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.28/1.74  tff(c_1200, plain, (![A_178]: (l1_waybel_0(k3_yellow19(A_178, k2_struct_0('#skF_1'), '#skF_2'), A_178) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_178))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_178) | v2_struct_0(A_178))), inference(resolution, [status(thm)], [c_56, c_1195])).
% 4.28/1.74  tff(c_1207, plain, (![A_178]: (l1_waybel_0(k3_yellow19(A_178, k2_struct_0('#skF_1'), '#skF_2'), A_178) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_178))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_178) | v2_struct_0(A_178))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1200])).
% 4.28/1.74  tff(c_1210, plain, (![A_181]: (l1_waybel_0(k3_yellow19(A_181, k2_struct_0('#skF_1'), '#skF_2'), A_181) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_181))) | ~l1_struct_0(A_181) | v2_struct_0(A_181))), inference(negUnitSimplification, [status(thm)], [c_1003, c_64, c_1207])).
% 4.28/1.74  tff(c_1215, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6, c_1210])).
% 4.28/1.74  tff(c_1221, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_918, c_1215])).
% 4.28/1.74  tff(c_1222, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_70, c_1221])).
% 4.28/1.74  tff(c_1255, plain, (![A_190, B_191]: (k2_yellow19(A_190, k3_yellow19(A_190, k2_struct_0(A_190), B_191))=B_191 | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_190))))) | ~v13_waybel_0(B_191, k3_yellow_1(k2_struct_0(A_190))) | ~v2_waybel_0(B_191, k3_yellow_1(k2_struct_0(A_190))) | ~v1_subset_1(B_191, u1_struct_0(k3_yellow_1(k2_struct_0(A_190)))) | v1_xboole_0(B_191) | ~l1_struct_0(A_190) | v2_struct_0(A_190))), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.28/1.74  tff(c_1260, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_1255])).
% 4.28/1.74  tff(c_1267, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_918, c_62, c_60, c_58, c_1260])).
% 4.28/1.74  tff(c_1268, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_1267])).
% 4.28/1.74  tff(c_1273, plain, (![C_32]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_32) | ~r1_waybel_7('#skF_1', '#skF_2', C_32) | ~m1_subset_1(C_32, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1268, c_48])).
% 4.28/1.74  tff(c_1280, plain, (![C_32]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_32) | ~r1_waybel_7('#skF_1', '#skF_2', C_32) | ~m1_subset_1(C_32, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1192, c_1222, c_917, c_1273])).
% 4.28/1.74  tff(c_1281, plain, (![C_32]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_32) | ~r1_waybel_7('#skF_1', '#skF_2', C_32) | ~m1_subset_1(C_32, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_70, c_1280])).
% 4.28/1.74  tff(c_1286, plain, (~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_1281])).
% 4.28/1.74  tff(c_1289, plain, (![A_196, B_197, C_198]: (v7_waybel_0(k3_yellow19(A_196, B_197, C_198)) | ~m1_subset_1(C_198, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_197)))) | ~v13_waybel_0(C_198, k3_yellow_1(B_197)) | ~v2_waybel_0(C_198, k3_yellow_1(B_197)) | ~v1_subset_1(C_198, u1_struct_0(k3_yellow_1(B_197))) | v1_xboole_0(C_198) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0(A_196))) | v1_xboole_0(B_197) | ~l1_struct_0(A_196) | v2_struct_0(A_196))), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.28/1.74  tff(c_1294, plain, (![A_196]: (v7_waybel_0(k3_yellow19(A_196, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_196))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_196) | v2_struct_0(A_196))), inference(resolution, [status(thm)], [c_56, c_1289])).
% 4.28/1.74  tff(c_1301, plain, (![A_196]: (v7_waybel_0(k3_yellow19(A_196, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_196))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_196) | v2_struct_0(A_196))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_1294])).
% 4.28/1.74  tff(c_1304, plain, (![A_199]: (v7_waybel_0(k3_yellow19(A_199, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_199))) | ~l1_struct_0(A_199) | v2_struct_0(A_199))), inference(negUnitSimplification, [status(thm)], [c_1003, c_64, c_1301])).
% 4.28/1.74  tff(c_1307, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_917, c_1304])).
% 4.28/1.74  tff(c_1313, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_918, c_79, c_1307])).
% 4.28/1.74  tff(c_1315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1286, c_1313])).
% 4.28/1.74  tff(c_1316, plain, (![C_32]: (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_32) | ~r1_waybel_7('#skF_1', '#skF_2', C_32) | ~m1_subset_1(C_32, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1281])).
% 4.28/1.74  tff(c_1348, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_1316])).
% 4.28/1.74  tff(c_1350, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1348, c_40])).
% 4.28/1.74  tff(c_1353, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_918, c_79, c_917, c_60, c_58, c_56, c_1350])).
% 4.28/1.74  tff(c_1355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1003, c_64, c_1353])).
% 4.28/1.74  tff(c_1357, plain, (~v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_1316])).
% 4.28/1.74  tff(c_1317, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_1281])).
% 4.28/1.74  tff(c_1276, plain, (![C_32]: (r1_waybel_7('#skF_1', '#skF_2', C_32) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_32) | ~m1_subset_1(C_32, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1268, c_50])).
% 4.28/1.74  tff(c_1283, plain, (![C_32]: (r1_waybel_7('#skF_1', '#skF_2', C_32) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_32) | ~m1_subset_1(C_32, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1192, c_1222, c_917, c_1276])).
% 4.28/1.74  tff(c_1284, plain, (![C_32]: (r1_waybel_7('#skF_1', '#skF_2', C_32) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_32) | ~m1_subset_1(C_32, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_70, c_1283])).
% 4.28/1.74  tff(c_1359, plain, (![C_32]: (r1_waybel_7('#skF_1', '#skF_2', C_32) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_32) | ~m1_subset_1(C_32, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1317, c_1284])).
% 4.28/1.74  tff(c_1360, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_1359])).
% 4.28/1.74  tff(c_1361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1357, c_1360])).
% 4.28/1.74  tff(c_1364, plain, (![C_204]: (r1_waybel_7('#skF_1', '#skF_2', C_204) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_204) | ~m1_subset_1(C_204, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1359])).
% 4.28/1.74  tff(c_1367, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_720, c_1364])).
% 4.28/1.74  tff(c_1370, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_919, c_1367])).
% 4.28/1.74  tff(c_1372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_721, c_1370])).
% 4.28/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.74  
% 4.28/1.74  Inference rules
% 4.28/1.74  ----------------------
% 4.28/1.74  #Ref     : 0
% 4.28/1.74  #Sup     : 233
% 4.28/1.74  #Fact    : 0
% 4.28/1.74  #Define  : 0
% 4.28/1.74  #Split   : 11
% 4.28/1.74  #Chain   : 0
% 4.28/1.74  #Close   : 0
% 4.28/1.74  
% 4.28/1.74  Ordering : KBO
% 4.28/1.74  
% 4.28/1.74  Simplification rules
% 4.28/1.74  ----------------------
% 4.28/1.74  #Subsume      : 32
% 4.28/1.74  #Demod        : 305
% 4.28/1.74  #Tautology    : 91
% 4.28/1.74  #SimpNegUnit  : 45
% 4.28/1.74  #BackRed      : 2
% 4.28/1.74  
% 4.28/1.74  #Partial instantiations: 0
% 4.28/1.74  #Strategies tried      : 1
% 4.28/1.74  
% 4.28/1.74  Timing (in seconds)
% 4.28/1.74  ----------------------
% 4.28/1.74  Preprocessing        : 0.40
% 4.28/1.74  Parsing              : 0.22
% 4.28/1.74  CNF conversion       : 0.03
% 4.28/1.74  Main loop            : 0.51
% 4.28/1.74  Inferencing          : 0.19
% 4.28/1.74  Reduction            : 0.16
% 4.28/1.74  Demodulation         : 0.11
% 4.28/1.74  BG Simplification    : 0.03
% 4.28/1.74  Subsumption          : 0.09
% 4.28/1.74  Abstraction          : 0.03
% 4.28/1.74  MUC search           : 0.00
% 4.28/1.74  Cooper               : 0.00
% 4.28/1.74  Total                : 0.99
% 4.28/1.74  Index Insertion      : 0.00
% 4.28/1.74  Index Deletion       : 0.00
% 4.28/1.74  Index Matching       : 0.00
% 4.28/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
