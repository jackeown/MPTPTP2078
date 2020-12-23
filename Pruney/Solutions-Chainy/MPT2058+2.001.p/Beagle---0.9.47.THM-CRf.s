%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:32 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.65s
% Verified   : 
% Statistics : Number of formulae       :  209 (2703 expanded)
%              Number of leaves         :   50 ( 961 expanded)
%              Depth                    :   25
%              Number of atoms          :  662 (11266 expanded)
%              Number of equality atoms :   35 ( 815 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v4_pre_topc > v2_waybel_0 > v1_tops_1 > v1_subset_1 > v13_waybel_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k2_pre_topc > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_235,negated_conjecture,(
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

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

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

tff(f_137,axiom,(
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

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_165,axiom,(
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
        & v6_waybel_0(k3_yellow19(A,B,C),A)
        & l1_waybel_0(k3_yellow19(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow19)).

tff(f_208,axiom,(
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

tff(f_189,axiom,(
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

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_10,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22,plain,(
    ! [A_13] :
      ( k2_pre_topc(A_13,k2_struct_0(A_13)) = k2_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [A_6] :
      ( m1_subset_1(k2_struct_0(A_6),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_183,plain,(
    ! [B_62,A_63] :
      ( v1_tops_1(B_62,A_63)
      | k2_pre_topc(A_63,B_62) != k2_struct_0(A_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_198,plain,(
    ! [A_6] :
      ( v1_tops_1(k2_struct_0(A_6),A_6)
      | k2_pre_topc(A_6,k2_struct_0(A_6)) != k2_struct_0(A_6)
      | ~ l1_pre_topc(A_6)
      | ~ l1_struct_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_183])).

tff(c_206,plain,(
    ! [A_65,B_66] :
      ( k2_pre_topc(A_65,B_66) = u1_struct_0(A_65)
      | ~ v1_tops_1(B_66,A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_234,plain,(
    ! [A_69] :
      ( k2_pre_topc(A_69,k2_struct_0(A_69)) = u1_struct_0(A_69)
      | ~ v1_tops_1(k2_struct_0(A_69),A_69)
      | ~ l1_pre_topc(A_69)
      | ~ l1_struct_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_8,c_206])).

tff(c_265,plain,(
    ! [A_78] :
      ( k2_pre_topc(A_78,k2_struct_0(A_78)) = u1_struct_0(A_78)
      | k2_pre_topc(A_78,k2_struct_0(A_78)) != k2_struct_0(A_78)
      | ~ l1_pre_topc(A_78)
      | ~ l1_struct_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_198,c_234])).

tff(c_270,plain,(
    ! [A_79] :
      ( k2_pre_topc(A_79,k2_struct_0(A_79)) = u1_struct_0(A_79)
      | ~ l1_struct_0(A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_265])).

tff(c_285,plain,(
    ! [A_80] :
      ( u1_struct_0(A_80) = k2_struct_0(A_80)
      | ~ l1_pre_topc(A_80)
      | ~ l1_struct_0(A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_22])).

tff(c_295,plain,(
    ! [A_84] :
      ( u1_struct_0(A_84) = k2_struct_0(A_84)
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_10,c_285])).

tff(c_299,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_295])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_300,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_56])).

tff(c_74,plain,
    ( ~ r1_waybel_7('#skF_2','#skF_3','#skF_4')
    | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_129,plain,(
    ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_80,plain,
    ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_4')
    | r1_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_131,plain,(
    r1_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_80])).

tff(c_132,plain,(
    ! [A_52] :
      ( m1_subset_1('#skF_1'(A_52),k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( v1_xboole_0(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_136,plain,(
    ! [A_52] :
      ( v1_xboole_0('#skF_1'(A_52))
      | ~ v1_xboole_0(u1_struct_0(A_52))
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_132,c_6])).

tff(c_334,plain,
    ( v1_xboole_0('#skF_1'('#skF_2'))
    | ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_136])).

tff(c_367,plain,
    ( v1_xboole_0('#skF_1'('#skF_2'))
    | ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_334])).

tff(c_368,plain,
    ( v1_xboole_0('#skF_1'('#skF_2'))
    | ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_367])).

tff(c_374,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_62,plain,(
    v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_60,plain,(
    v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_436,plain,(
    ! [A_88,B_89,C_90] :
      ( v3_orders_2(k3_yellow19(A_88,B_89,C_90))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_89))))
      | ~ v13_waybel_0(C_90,k3_yellow_1(B_89))
      | ~ v2_waybel_0(C_90,k3_yellow_1(B_89))
      | v1_xboole_0(C_90)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | v1_xboole_0(B_89)
      | ~ l1_struct_0(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_444,plain,(
    ! [A_88] :
      ( v3_orders_2(k3_yellow19(A_88,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_88)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_88)
      | v2_struct_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_58,c_436])).

tff(c_452,plain,(
    ! [A_88] :
      ( v3_orders_2(k3_yellow19(A_88,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_88)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_88)
      | v2_struct_0(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_444])).

tff(c_471,plain,(
    ! [A_92] :
      ( v3_orders_2(k3_yellow19(A_92,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_struct_0(A_92)
      | v2_struct_0(A_92) ) ),
    inference(negUnitSimplification,[status(thm)],[c_374,c_66,c_452])).

tff(c_478,plain,
    ( v3_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_471])).

tff(c_484,plain,
    ( v3_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_478])).

tff(c_485,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_484])).

tff(c_488,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_485])).

tff(c_492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_488])).

tff(c_494,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_484])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_497,plain,(
    ! [A_93,B_94,C_95] :
      ( v4_orders_2(k3_yellow19(A_93,B_94,C_95))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_94))))
      | ~ v13_waybel_0(C_95,k3_yellow_1(B_94))
      | ~ v2_waybel_0(C_95,k3_yellow_1(B_94))
      | v1_xboole_0(C_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | v1_xboole_0(B_94)
      | ~ l1_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_505,plain,(
    ! [A_93] :
      ( v4_orders_2(k3_yellow19(A_93,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_93)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_58,c_497])).

tff(c_513,plain,(
    ! [A_93] :
      ( v4_orders_2(k3_yellow19(A_93,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_93)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_505])).

tff(c_517,plain,(
    ! [A_96] :
      ( v4_orders_2(k3_yellow19(A_96,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_struct_0(A_96)
      | v2_struct_0(A_96) ) ),
    inference(negUnitSimplification,[status(thm)],[c_374,c_66,c_513])).

tff(c_524,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_517])).

tff(c_530,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_524])).

tff(c_531,plain,(
    v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_530])).

tff(c_64,plain,(
    v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_629,plain,(
    ! [A_108,B_109,C_110] :
      ( v7_waybel_0(k3_yellow19(A_108,B_109,C_110))
      | ~ m1_subset_1(C_110,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_109))))
      | ~ v13_waybel_0(C_110,k3_yellow_1(B_109))
      | ~ v2_waybel_0(C_110,k3_yellow_1(B_109))
      | ~ v1_subset_1(C_110,u1_struct_0(k3_yellow_1(B_109)))
      | v1_xboole_0(C_110)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | v1_xboole_0(B_109)
      | ~ l1_struct_0(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_637,plain,(
    ! [A_108] :
      ( v7_waybel_0(k3_yellow19(A_108,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_108)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_108)
      | v2_struct_0(A_108) ) ),
    inference(resolution,[status(thm)],[c_58,c_629])).

tff(c_645,plain,(
    ! [A_108] :
      ( v7_waybel_0(k3_yellow19(A_108,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_108)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_108)
      | v2_struct_0(A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_637])).

tff(c_648,plain,(
    ! [A_111] :
      ( v7_waybel_0(k3_yellow19(A_111,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_struct_0(A_111)
      | v2_struct_0(A_111) ) ),
    inference(negUnitSimplification,[status(thm)],[c_374,c_66,c_645])).

tff(c_655,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_648])).

tff(c_661,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_655])).

tff(c_662,plain,(
    v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_661])).

tff(c_594,plain,(
    ! [A_102,B_103,C_104] :
      ( l1_waybel_0(k3_yellow19(A_102,B_103,C_104),A_102)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_103))))
      | ~ v13_waybel_0(C_104,k3_yellow_1(B_103))
      | ~ v2_waybel_0(C_104,k3_yellow_1(B_103))
      | v1_xboole_0(C_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | v1_xboole_0(B_103)
      | ~ l1_struct_0(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_602,plain,(
    ! [A_102] :
      ( l1_waybel_0(k3_yellow19(A_102,k2_struct_0('#skF_2'),'#skF_3'),A_102)
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_102)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_102)
      | v2_struct_0(A_102) ) ),
    inference(resolution,[status(thm)],[c_58,c_594])).

tff(c_610,plain,(
    ! [A_102] :
      ( l1_waybel_0(k3_yellow19(A_102,k2_struct_0('#skF_2'),'#skF_3'),A_102)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_102)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_102)
      | v2_struct_0(A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_602])).

tff(c_613,plain,(
    ! [A_105] :
      ( l1_waybel_0(k3_yellow19(A_105,k2_struct_0('#skF_2'),'#skF_3'),A_105)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_struct_0(A_105)
      | v2_struct_0(A_105) ) ),
    inference(negUnitSimplification,[status(thm)],[c_374,c_66,c_610])).

tff(c_618,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_613])).

tff(c_624,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_618])).

tff(c_625,plain,(
    l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_624])).

tff(c_664,plain,(
    ! [A_112,B_113] :
      ( k2_yellow19(A_112,k3_yellow19(A_112,k2_struct_0(A_112),B_113)) = B_113
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_112)))))
      | ~ v13_waybel_0(B_113,k3_yellow_1(k2_struct_0(A_112)))
      | ~ v2_waybel_0(B_113,k3_yellow_1(k2_struct_0(A_112)))
      | ~ v1_subset_1(B_113,u1_struct_0(k3_yellow_1(k2_struct_0(A_112))))
      | v1_xboole_0(B_113)
      | ~ l1_struct_0(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_672,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
    | v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_664])).

tff(c_680,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_64,c_62,c_60,c_672])).

tff(c_681,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_680])).

tff(c_50,plain,(
    ! [A_27,B_31,C_33] :
      ( r3_waybel_9(A_27,B_31,C_33)
      | ~ r1_waybel_7(A_27,k2_yellow19(A_27,B_31),C_33)
      | ~ m1_subset_1(C_33,u1_struct_0(A_27))
      | ~ l1_waybel_0(B_31,A_27)
      | ~ v7_waybel_0(B_31)
      | ~ v4_orders_2(B_31)
      | v2_struct_0(B_31)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_686,plain,(
    ! [C_33] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_33)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_33)
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_50])).

tff(c_693,plain,(
    ! [C_33] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_33)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_33)
      | ~ m1_subset_1(C_33,k2_struct_0('#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_531,c_662,c_625,c_299,c_686])).

tff(c_694,plain,(
    ! [C_33] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_33)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_33)
      | ~ m1_subset_1(C_33,k2_struct_0('#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_693])).

tff(c_699,plain,(
    v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_694])).

tff(c_42,plain,(
    ! [A_21,B_22,C_23] :
      ( ~ v2_struct_0(k3_yellow19(A_21,B_22,C_23))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_22))))
      | ~ v13_waybel_0(C_23,k3_yellow_1(B_22))
      | ~ v2_waybel_0(C_23,k3_yellow_1(B_22))
      | v1_xboole_0(C_23)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_21)))
      | v1_xboole_0(B_22)
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_701,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_699,c_42])).

tff(c_704,plain,
    ( v1_xboole_0('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_81,c_299,c_62,c_60,c_58,c_701])).

tff(c_706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_374,c_66,c_704])).

tff(c_709,plain,(
    ! [C_114] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_114)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_114)
      | ~ m1_subset_1(C_114,k2_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_694])).

tff(c_712,plain,
    ( ~ r1_waybel_7('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_709,c_129])).

tff(c_716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_131,c_712])).

tff(c_717,plain,(
    v1_xboole_0('#skF_1'('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_14,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0('#skF_1'(A_8))
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_722,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_717,c_14])).

tff(c_725,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_722])).

tff(c_727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_725])).

tff(c_728,plain,(
    ~ r1_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_784,plain,(
    ! [B_129,A_130] :
      ( v1_tops_1(B_129,A_130)
      | k2_pre_topc(A_130,B_129) != k2_struct_0(A_130)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_799,plain,(
    ! [A_6] :
      ( v1_tops_1(k2_struct_0(A_6),A_6)
      | k2_pre_topc(A_6,k2_struct_0(A_6)) != k2_struct_0(A_6)
      | ~ l1_pre_topc(A_6)
      | ~ l1_struct_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_784])).

tff(c_808,plain,(
    ! [A_133,B_134] :
      ( k2_pre_topc(A_133,B_134) = u1_struct_0(A_133)
      | ~ v1_tops_1(B_134,A_133)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_836,plain,(
    ! [A_139] :
      ( k2_pre_topc(A_139,k2_struct_0(A_139)) = u1_struct_0(A_139)
      | ~ v1_tops_1(k2_struct_0(A_139),A_139)
      | ~ l1_pre_topc(A_139)
      | ~ l1_struct_0(A_139) ) ),
    inference(resolution,[status(thm)],[c_8,c_808])).

tff(c_866,plain,(
    ! [A_145] :
      ( k2_pre_topc(A_145,k2_struct_0(A_145)) = u1_struct_0(A_145)
      | k2_pre_topc(A_145,k2_struct_0(A_145)) != k2_struct_0(A_145)
      | ~ l1_pre_topc(A_145)
      | ~ l1_struct_0(A_145) ) ),
    inference(resolution,[status(thm)],[c_799,c_836])).

tff(c_876,plain,(
    ! [A_149] :
      ( k2_pre_topc(A_149,k2_struct_0(A_149)) = u1_struct_0(A_149)
      | ~ l1_struct_0(A_149)
      | ~ l1_pre_topc(A_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_866])).

tff(c_891,plain,(
    ! [A_150] :
      ( u1_struct_0(A_150) = k2_struct_0(A_150)
      | ~ l1_pre_topc(A_150)
      | ~ l1_struct_0(A_150)
      | ~ l1_pre_topc(A_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_876,c_22])).

tff(c_896,plain,(
    ! [A_151] :
      ( u1_struct_0(A_151) = k2_struct_0(A_151)
      | ~ l1_pre_topc(A_151) ) ),
    inference(resolution,[status(thm)],[c_10,c_891])).

tff(c_900,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_896])).

tff(c_901,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_900,c_56])).

tff(c_729,plain,(
    r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_733,plain,(
    ! [A_119] :
      ( m1_subset_1('#skF_1'(A_119),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_737,plain,(
    ! [A_119] :
      ( v1_xboole_0('#skF_1'(A_119))
      | ~ v1_xboole_0(u1_struct_0(A_119))
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_733,c_6])).

tff(c_935,plain,
    ( v1_xboole_0('#skF_1'('#skF_2'))
    | ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_900,c_737])).

tff(c_968,plain,
    ( v1_xboole_0('#skF_1'('#skF_2'))
    | ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_935])).

tff(c_969,plain,
    ( v1_xboole_0('#skF_1'('#skF_2'))
    | ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_968])).

tff(c_975,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_969])).

tff(c_1073,plain,(
    ! [A_156,B_157,C_158] :
      ( v3_orders_2(k3_yellow19(A_156,B_157,C_158))
      | ~ m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_157))))
      | ~ v13_waybel_0(C_158,k3_yellow_1(B_157))
      | ~ v2_waybel_0(C_158,k3_yellow_1(B_157))
      | v1_xboole_0(C_158)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | v1_xboole_0(B_157)
      | ~ l1_struct_0(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1081,plain,(
    ! [A_156] :
      ( v3_orders_2(k3_yellow19(A_156,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_156)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_156)
      | v2_struct_0(A_156) ) ),
    inference(resolution,[status(thm)],[c_58,c_1073])).

tff(c_1089,plain,(
    ! [A_156] :
      ( v3_orders_2(k3_yellow19(A_156,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_156)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_156)
      | v2_struct_0(A_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1081])).

tff(c_1098,plain,(
    ! [A_159] :
      ( v3_orders_2(k3_yellow19(A_159,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_struct_0(A_159)
      | v2_struct_0(A_159) ) ),
    inference(negUnitSimplification,[status(thm)],[c_975,c_66,c_1089])).

tff(c_1105,plain,
    ( v3_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_1098])).

tff(c_1111,plain,
    ( v3_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1105])).

tff(c_1112,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1111])).

tff(c_1115,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_1112])).

tff(c_1119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1115])).

tff(c_1121,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1111])).

tff(c_980,plain,(
    ! [A_152,B_153,C_154] :
      ( v4_orders_2(k3_yellow19(A_152,B_153,C_154))
      | ~ m1_subset_1(C_154,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_153))))
      | ~ v13_waybel_0(C_154,k3_yellow_1(B_153))
      | ~ v2_waybel_0(C_154,k3_yellow_1(B_153))
      | v1_xboole_0(C_154)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | v1_xboole_0(B_153)
      | ~ l1_struct_0(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_988,plain,(
    ! [A_152] :
      ( v4_orders_2(k3_yellow19(A_152,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_152)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_152)
      | v2_struct_0(A_152) ) ),
    inference(resolution,[status(thm)],[c_58,c_980])).

tff(c_996,plain,(
    ! [A_152] :
      ( v4_orders_2(k3_yellow19(A_152,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_152)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_152)
      | v2_struct_0(A_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_988])).

tff(c_1165,plain,(
    ! [A_165] :
      ( v4_orders_2(k3_yellow19(A_165,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_struct_0(A_165)
      | v2_struct_0(A_165) ) ),
    inference(negUnitSimplification,[status(thm)],[c_975,c_66,c_996])).

tff(c_1172,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_1165])).

tff(c_1178,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_1172])).

tff(c_1179,plain,(
    v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1178])).

tff(c_1216,plain,(
    ! [A_172,B_173,C_174] :
      ( l1_waybel_0(k3_yellow19(A_172,B_173,C_174),A_172)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_173))))
      | ~ v13_waybel_0(C_174,k3_yellow_1(B_173))
      | ~ v2_waybel_0(C_174,k3_yellow_1(B_173))
      | v1_xboole_0(C_174)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | v1_xboole_0(B_173)
      | ~ l1_struct_0(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1224,plain,(
    ! [A_172] :
      ( l1_waybel_0(k3_yellow19(A_172,k2_struct_0('#skF_2'),'#skF_3'),A_172)
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_172)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_172)
      | v2_struct_0(A_172) ) ),
    inference(resolution,[status(thm)],[c_58,c_1216])).

tff(c_1232,plain,(
    ! [A_172] :
      ( l1_waybel_0(k3_yellow19(A_172,k2_struct_0('#skF_2'),'#skF_3'),A_172)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_172)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_172)
      | v2_struct_0(A_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1224])).

tff(c_1235,plain,(
    ! [A_175] :
      ( l1_waybel_0(k3_yellow19(A_175,k2_struct_0('#skF_2'),'#skF_3'),A_175)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_struct_0(A_175)
      | v2_struct_0(A_175) ) ),
    inference(negUnitSimplification,[status(thm)],[c_975,c_66,c_1232])).

tff(c_1240,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_1235])).

tff(c_1246,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_1240])).

tff(c_1247,plain,(
    l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1246])).

tff(c_1248,plain,(
    ! [A_176,B_177] :
      ( k2_yellow19(A_176,k3_yellow19(A_176,k2_struct_0(A_176),B_177)) = B_177
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_176)))))
      | ~ v13_waybel_0(B_177,k3_yellow_1(k2_struct_0(A_176)))
      | ~ v2_waybel_0(B_177,k3_yellow_1(k2_struct_0(A_176)))
      | ~ v1_subset_1(B_177,u1_struct_0(k3_yellow_1(k2_struct_0(A_176))))
      | v1_xboole_0(B_177)
      | ~ l1_struct_0(A_176)
      | v2_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_1256,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
    | v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_1248])).

tff(c_1264,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_64,c_62,c_60,c_1256])).

tff(c_1265,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_1264])).

tff(c_52,plain,(
    ! [A_27,B_31,C_33] :
      ( r1_waybel_7(A_27,k2_yellow19(A_27,B_31),C_33)
      | ~ r3_waybel_9(A_27,B_31,C_33)
      | ~ m1_subset_1(C_33,u1_struct_0(A_27))
      | ~ l1_waybel_0(B_31,A_27)
      | ~ v7_waybel_0(B_31)
      | ~ v4_orders_2(B_31)
      | v2_struct_0(B_31)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_1271,plain,(
    ! [C_33] :
      ( r1_waybel_7('#skF_2','#skF_3',C_33)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_33)
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1265,c_52])).

tff(c_1278,plain,(
    ! [C_33] :
      ( r1_waybel_7('#skF_2','#skF_3',C_33)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_33)
      | ~ m1_subset_1(C_33,k2_struct_0('#skF_2'))
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1179,c_1247,c_900,c_1271])).

tff(c_1279,plain,(
    ! [C_33] :
      ( r1_waybel_7('#skF_2','#skF_3',C_33)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_33)
      | ~ m1_subset_1(C_33,k2_struct_0('#skF_2'))
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1278])).

tff(c_1284,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1279])).

tff(c_1288,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1296,plain,(
    ! [A_184] :
      ( v7_waybel_0(k3_yellow19(A_184,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_184)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_184)
      | v2_struct_0(A_184) ) ),
    inference(resolution,[status(thm)],[c_58,c_1288])).

tff(c_1304,plain,(
    ! [A_184] :
      ( v7_waybel_0(k3_yellow19(A_184,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_184)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_184)
      | v2_struct_0(A_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_1296])).

tff(c_1307,plain,(
    ! [A_187] :
      ( v7_waybel_0(k3_yellow19(A_187,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ l1_struct_0(A_187)
      | v2_struct_0(A_187) ) ),
    inference(negUnitSimplification,[status(thm)],[c_975,c_66,c_1304])).

tff(c_1310,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_900,c_1307])).

tff(c_1316,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_81,c_1310])).

tff(c_1318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1284,c_1316])).

tff(c_1319,plain,(
    ! [C_33] :
      ( v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | r1_waybel_7('#skF_2','#skF_3',C_33)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_33)
      | ~ m1_subset_1(C_33,k2_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_1279])).

tff(c_1321,plain,(
    v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1319])).

tff(c_1326,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1321,c_42])).

tff(c_1329,plain,
    ( v1_xboole_0('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_81,c_900,c_62,c_60,c_58,c_1326])).

tff(c_1331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_975,c_66,c_1329])).

tff(c_1334,plain,(
    ! [C_188] :
      ( r1_waybel_7('#skF_2','#skF_3',C_188)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_188)
      | ~ m1_subset_1(C_188,k2_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_1319])).

tff(c_1337,plain,
    ( r1_waybel_7('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_729,c_1334])).

tff(c_1340,plain,(
    r1_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_901,c_1337])).

tff(c_1342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_728,c_1340])).

tff(c_1343,plain,(
    v1_xboole_0('#skF_1'('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_969])).

tff(c_1347,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1343,c_14])).

tff(c_1350,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1347])).

tff(c_1352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1350])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.10/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.76  
% 4.48/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.77  %$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v4_pre_topc > v2_waybel_0 > v1_tops_1 > v1_subset_1 > v13_waybel_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k2_pre_topc > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 4.48/1.77  
% 4.48/1.77  %Foreground sorts:
% 4.48/1.77  
% 4.48/1.77  
% 4.48/1.77  %Background operators:
% 4.48/1.77  
% 4.48/1.77  
% 4.48/1.77  %Foreground operators:
% 4.48/1.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.48/1.77  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.48/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.48/1.77  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 4.48/1.77  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 4.48/1.77  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.48/1.77  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 4.48/1.77  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.48/1.77  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 4.48/1.77  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.48/1.77  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 4.48/1.77  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.48/1.77  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 4.48/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.48/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.48/1.77  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 4.48/1.77  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.48/1.77  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 4.48/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.48/1.77  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.48/1.77  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.48/1.77  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 4.48/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.48/1.77  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 4.48/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.48/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.48/1.77  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 4.48/1.77  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 4.48/1.77  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.48/1.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.48/1.77  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.48/1.77  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.48/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.48/1.77  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.48/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.48/1.77  
% 4.65/1.80  tff(f_235, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, k3_yellow19(A, k2_struct_0(A), B), C) <=> r1_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_yellow19)).
% 4.65/1.80  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.65/1.80  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tops_1)).
% 4.65/1.80  tff(f_40, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 4.65/1.80  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 4.65/1.80  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 4.65/1.80  tff(f_59, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 4.65/1.80  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.65/1.80  tff(f_137, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_yellow19)).
% 4.65/1.80  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.65/1.80  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.65/1.80  tff(f_165, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow19)).
% 4.65/1.80  tff(f_109, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 4.65/1.80  tff(f_208, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 4.65/1.80  tff(f_189, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> r1_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_yellow19)).
% 4.65/1.80  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_235])).
% 4.65/1.80  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_235])).
% 4.65/1.80  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_235])).
% 4.65/1.80  tff(c_10, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.65/1.80  tff(c_22, plain, (![A_13]: (k2_pre_topc(A_13, k2_struct_0(A_13))=k2_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.65/1.80  tff(c_8, plain, (![A_6]: (m1_subset_1(k2_struct_0(A_6), k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.65/1.80  tff(c_183, plain, (![B_62, A_63]: (v1_tops_1(B_62, A_63) | k2_pre_topc(A_63, B_62)!=k2_struct_0(A_63) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.65/1.80  tff(c_198, plain, (![A_6]: (v1_tops_1(k2_struct_0(A_6), A_6) | k2_pre_topc(A_6, k2_struct_0(A_6))!=k2_struct_0(A_6) | ~l1_pre_topc(A_6) | ~l1_struct_0(A_6))), inference(resolution, [status(thm)], [c_8, c_183])).
% 4.65/1.80  tff(c_206, plain, (![A_65, B_66]: (k2_pre_topc(A_65, B_66)=u1_struct_0(A_65) | ~v1_tops_1(B_66, A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.65/1.80  tff(c_234, plain, (![A_69]: (k2_pre_topc(A_69, k2_struct_0(A_69))=u1_struct_0(A_69) | ~v1_tops_1(k2_struct_0(A_69), A_69) | ~l1_pre_topc(A_69) | ~l1_struct_0(A_69))), inference(resolution, [status(thm)], [c_8, c_206])).
% 4.65/1.80  tff(c_265, plain, (![A_78]: (k2_pre_topc(A_78, k2_struct_0(A_78))=u1_struct_0(A_78) | k2_pre_topc(A_78, k2_struct_0(A_78))!=k2_struct_0(A_78) | ~l1_pre_topc(A_78) | ~l1_struct_0(A_78))), inference(resolution, [status(thm)], [c_198, c_234])).
% 4.65/1.80  tff(c_270, plain, (![A_79]: (k2_pre_topc(A_79, k2_struct_0(A_79))=u1_struct_0(A_79) | ~l1_struct_0(A_79) | ~l1_pre_topc(A_79))), inference(superposition, [status(thm), theory('equality')], [c_22, c_265])).
% 4.65/1.80  tff(c_285, plain, (![A_80]: (u1_struct_0(A_80)=k2_struct_0(A_80) | ~l1_pre_topc(A_80) | ~l1_struct_0(A_80) | ~l1_pre_topc(A_80))), inference(superposition, [status(thm), theory('equality')], [c_270, c_22])).
% 4.65/1.80  tff(c_295, plain, (![A_84]: (u1_struct_0(A_84)=k2_struct_0(A_84) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_10, c_285])).
% 4.65/1.80  tff(c_299, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_295])).
% 4.65/1.80  tff(c_56, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_235])).
% 4.65/1.80  tff(c_300, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_56])).
% 4.65/1.80  tff(c_74, plain, (~r1_waybel_7('#skF_2', '#skF_3', '#skF_4') | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_235])).
% 4.65/1.80  tff(c_129, plain, (~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_74])).
% 4.65/1.80  tff(c_80, plain, (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_4') | r1_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_235])).
% 4.65/1.80  tff(c_131, plain, (r1_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_129, c_80])).
% 4.65/1.80  tff(c_132, plain, (![A_52]: (m1_subset_1('#skF_1'(A_52), k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.65/1.80  tff(c_6, plain, (![B_5, A_3]: (v1_xboole_0(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.65/1.80  tff(c_136, plain, (![A_52]: (v1_xboole_0('#skF_1'(A_52)) | ~v1_xboole_0(u1_struct_0(A_52)) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52) | v2_struct_0(A_52))), inference(resolution, [status(thm)], [c_132, c_6])).
% 4.65/1.80  tff(c_334, plain, (v1_xboole_0('#skF_1'('#skF_2')) | ~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_299, c_136])).
% 4.65/1.80  tff(c_367, plain, (v1_xboole_0('#skF_1'('#skF_2')) | ~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_334])).
% 4.65/1.80  tff(c_368, plain, (v1_xboole_0('#skF_1'('#skF_2')) | ~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_72, c_367])).
% 4.65/1.80  tff(c_374, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_368])).
% 4.65/1.80  tff(c_66, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_235])).
% 4.65/1.80  tff(c_62, plain, (v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_235])).
% 4.65/1.80  tff(c_60, plain, (v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_235])).
% 4.65/1.80  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))), inference(cnfTransformation, [status(thm)], [f_235])).
% 4.65/1.80  tff(c_436, plain, (![A_88, B_89, C_90]: (v3_orders_2(k3_yellow19(A_88, B_89, C_90)) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_89)))) | ~v13_waybel_0(C_90, k3_yellow_1(B_89)) | ~v2_waybel_0(C_90, k3_yellow_1(B_89)) | v1_xboole_0(C_90) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | v1_xboole_0(B_89) | ~l1_struct_0(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.65/1.80  tff(c_444, plain, (![A_88]: (v3_orders_2(k3_yellow19(A_88, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_88))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_88) | v2_struct_0(A_88))), inference(resolution, [status(thm)], [c_58, c_436])).
% 4.65/1.80  tff(c_452, plain, (![A_88]: (v3_orders_2(k3_yellow19(A_88, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_88))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_88) | v2_struct_0(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_444])).
% 4.65/1.80  tff(c_471, plain, (![A_92]: (v3_orders_2(k3_yellow19(A_92, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_struct_0(A_92) | v2_struct_0(A_92))), inference(negUnitSimplification, [status(thm)], [c_374, c_66, c_452])).
% 4.65/1.80  tff(c_478, plain, (v3_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_8, c_471])).
% 4.65/1.80  tff(c_484, plain, (v3_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_72, c_478])).
% 4.65/1.80  tff(c_485, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_484])).
% 4.65/1.80  tff(c_488, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_485])).
% 4.65/1.80  tff(c_492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_488])).
% 4.65/1.80  tff(c_494, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_484])).
% 4.65/1.80  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.65/1.80  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.65/1.80  tff(c_81, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 4.65/1.80  tff(c_497, plain, (![A_93, B_94, C_95]: (v4_orders_2(k3_yellow19(A_93, B_94, C_95)) | ~m1_subset_1(C_95, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_94)))) | ~v13_waybel_0(C_95, k3_yellow_1(B_94)) | ~v2_waybel_0(C_95, k3_yellow_1(B_94)) | v1_xboole_0(C_95) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | v1_xboole_0(B_94) | ~l1_struct_0(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.65/1.80  tff(c_505, plain, (![A_93]: (v4_orders_2(k3_yellow19(A_93, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_93))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_93) | v2_struct_0(A_93))), inference(resolution, [status(thm)], [c_58, c_497])).
% 4.65/1.80  tff(c_513, plain, (![A_93]: (v4_orders_2(k3_yellow19(A_93, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_93))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_93) | v2_struct_0(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_505])).
% 4.65/1.80  tff(c_517, plain, (![A_96]: (v4_orders_2(k3_yellow19(A_96, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(negUnitSimplification, [status(thm)], [c_374, c_66, c_513])).
% 4.65/1.80  tff(c_524, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_8, c_517])).
% 4.65/1.80  tff(c_530, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_494, c_524])).
% 4.65/1.80  tff(c_531, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_72, c_530])).
% 4.65/1.80  tff(c_64, plain, (v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_235])).
% 4.65/1.80  tff(c_629, plain, (![A_108, B_109, C_110]: (v7_waybel_0(k3_yellow19(A_108, B_109, C_110)) | ~m1_subset_1(C_110, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_109)))) | ~v13_waybel_0(C_110, k3_yellow_1(B_109)) | ~v2_waybel_0(C_110, k3_yellow_1(B_109)) | ~v1_subset_1(C_110, u1_struct_0(k3_yellow_1(B_109))) | v1_xboole_0(C_110) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | v1_xboole_0(B_109) | ~l1_struct_0(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.65/1.80  tff(c_637, plain, (![A_108]: (v7_waybel_0(k3_yellow19(A_108, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_108))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_108) | v2_struct_0(A_108))), inference(resolution, [status(thm)], [c_58, c_629])).
% 4.65/1.80  tff(c_645, plain, (![A_108]: (v7_waybel_0(k3_yellow19(A_108, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_108))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_108) | v2_struct_0(A_108))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_637])).
% 4.65/1.80  tff(c_648, plain, (![A_111]: (v7_waybel_0(k3_yellow19(A_111, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_struct_0(A_111) | v2_struct_0(A_111))), inference(negUnitSimplification, [status(thm)], [c_374, c_66, c_645])).
% 4.65/1.80  tff(c_655, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_8, c_648])).
% 4.65/1.80  tff(c_661, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_494, c_655])).
% 4.65/1.80  tff(c_662, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_72, c_661])).
% 4.65/1.80  tff(c_594, plain, (![A_102, B_103, C_104]: (l1_waybel_0(k3_yellow19(A_102, B_103, C_104), A_102) | ~m1_subset_1(C_104, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_103)))) | ~v13_waybel_0(C_104, k3_yellow_1(B_103)) | ~v2_waybel_0(C_104, k3_yellow_1(B_103)) | v1_xboole_0(C_104) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | v1_xboole_0(B_103) | ~l1_struct_0(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.65/1.80  tff(c_602, plain, (![A_102]: (l1_waybel_0(k3_yellow19(A_102, k2_struct_0('#skF_2'), '#skF_3'), A_102) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_102))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_102) | v2_struct_0(A_102))), inference(resolution, [status(thm)], [c_58, c_594])).
% 4.65/1.80  tff(c_610, plain, (![A_102]: (l1_waybel_0(k3_yellow19(A_102, k2_struct_0('#skF_2'), '#skF_3'), A_102) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_102))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_102) | v2_struct_0(A_102))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_602])).
% 4.65/1.80  tff(c_613, plain, (![A_105]: (l1_waybel_0(k3_yellow19(A_105, k2_struct_0('#skF_2'), '#skF_3'), A_105) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_struct_0(A_105) | v2_struct_0(A_105))), inference(negUnitSimplification, [status(thm)], [c_374, c_66, c_610])).
% 4.65/1.80  tff(c_618, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_8, c_613])).
% 4.65/1.80  tff(c_624, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_494, c_618])).
% 4.65/1.80  tff(c_625, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_72, c_624])).
% 4.65/1.80  tff(c_664, plain, (![A_112, B_113]: (k2_yellow19(A_112, k3_yellow19(A_112, k2_struct_0(A_112), B_113))=B_113 | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_112))))) | ~v13_waybel_0(B_113, k3_yellow_1(k2_struct_0(A_112))) | ~v2_waybel_0(B_113, k3_yellow_1(k2_struct_0(A_112))) | ~v1_subset_1(B_113, u1_struct_0(k3_yellow_1(k2_struct_0(A_112)))) | v1_xboole_0(B_113) | ~l1_struct_0(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.65/1.80  tff(c_672, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_664])).
% 4.65/1.80  tff(c_680, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_494, c_64, c_62, c_60, c_672])).
% 4.65/1.80  tff(c_681, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_680])).
% 4.65/1.80  tff(c_50, plain, (![A_27, B_31, C_33]: (r3_waybel_9(A_27, B_31, C_33) | ~r1_waybel_7(A_27, k2_yellow19(A_27, B_31), C_33) | ~m1_subset_1(C_33, u1_struct_0(A_27)) | ~l1_waybel_0(B_31, A_27) | ~v7_waybel_0(B_31) | ~v4_orders_2(B_31) | v2_struct_0(B_31) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.65/1.80  tff(c_686, plain, (![C_33]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_33) | ~r1_waybel_7('#skF_2', '#skF_3', C_33) | ~m1_subset_1(C_33, u1_struct_0('#skF_2')) | ~l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_681, c_50])).
% 4.65/1.80  tff(c_693, plain, (![C_33]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_33) | ~r1_waybel_7('#skF_2', '#skF_3', C_33) | ~m1_subset_1(C_33, k2_struct_0('#skF_2')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_531, c_662, c_625, c_299, c_686])).
% 4.65/1.80  tff(c_694, plain, (![C_33]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_33) | ~r1_waybel_7('#skF_2', '#skF_3', C_33) | ~m1_subset_1(C_33, k2_struct_0('#skF_2')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_72, c_693])).
% 4.65/1.80  tff(c_699, plain, (v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_694])).
% 4.65/1.80  tff(c_42, plain, (![A_21, B_22, C_23]: (~v2_struct_0(k3_yellow19(A_21, B_22, C_23)) | ~m1_subset_1(C_23, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_22)))) | ~v13_waybel_0(C_23, k3_yellow_1(B_22)) | ~v2_waybel_0(C_23, k3_yellow_1(B_22)) | v1_xboole_0(C_23) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_21))) | v1_xboole_0(B_22) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.65/1.80  tff(c_701, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_699, c_42])).
% 4.65/1.80  tff(c_704, plain, (v1_xboole_0('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_494, c_81, c_299, c_62, c_60, c_58, c_701])).
% 4.65/1.80  tff(c_706, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_374, c_66, c_704])).
% 4.65/1.80  tff(c_709, plain, (![C_114]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_114) | ~r1_waybel_7('#skF_2', '#skF_3', C_114) | ~m1_subset_1(C_114, k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_694])).
% 4.65/1.80  tff(c_712, plain, (~r1_waybel_7('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_709, c_129])).
% 4.65/1.80  tff(c_716, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_300, c_131, c_712])).
% 4.65/1.80  tff(c_717, plain, (v1_xboole_0('#skF_1'('#skF_2'))), inference(splitRight, [status(thm)], [c_368])).
% 4.65/1.80  tff(c_14, plain, (![A_8]: (~v1_xboole_0('#skF_1'(A_8)) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.65/1.80  tff(c_722, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_717, c_14])).
% 4.65/1.80  tff(c_725, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_722])).
% 4.65/1.80  tff(c_727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_725])).
% 4.65/1.80  tff(c_728, plain, (~r1_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_74])).
% 4.65/1.80  tff(c_784, plain, (![B_129, A_130]: (v1_tops_1(B_129, A_130) | k2_pre_topc(A_130, B_129)!=k2_struct_0(A_130) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.65/1.80  tff(c_799, plain, (![A_6]: (v1_tops_1(k2_struct_0(A_6), A_6) | k2_pre_topc(A_6, k2_struct_0(A_6))!=k2_struct_0(A_6) | ~l1_pre_topc(A_6) | ~l1_struct_0(A_6))), inference(resolution, [status(thm)], [c_8, c_784])).
% 4.65/1.80  tff(c_808, plain, (![A_133, B_134]: (k2_pre_topc(A_133, B_134)=u1_struct_0(A_133) | ~v1_tops_1(B_134, A_133) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.65/1.80  tff(c_836, plain, (![A_139]: (k2_pre_topc(A_139, k2_struct_0(A_139))=u1_struct_0(A_139) | ~v1_tops_1(k2_struct_0(A_139), A_139) | ~l1_pre_topc(A_139) | ~l1_struct_0(A_139))), inference(resolution, [status(thm)], [c_8, c_808])).
% 4.65/1.80  tff(c_866, plain, (![A_145]: (k2_pre_topc(A_145, k2_struct_0(A_145))=u1_struct_0(A_145) | k2_pre_topc(A_145, k2_struct_0(A_145))!=k2_struct_0(A_145) | ~l1_pre_topc(A_145) | ~l1_struct_0(A_145))), inference(resolution, [status(thm)], [c_799, c_836])).
% 4.65/1.80  tff(c_876, plain, (![A_149]: (k2_pre_topc(A_149, k2_struct_0(A_149))=u1_struct_0(A_149) | ~l1_struct_0(A_149) | ~l1_pre_topc(A_149))), inference(superposition, [status(thm), theory('equality')], [c_22, c_866])).
% 4.65/1.80  tff(c_891, plain, (![A_150]: (u1_struct_0(A_150)=k2_struct_0(A_150) | ~l1_pre_topc(A_150) | ~l1_struct_0(A_150) | ~l1_pre_topc(A_150))), inference(superposition, [status(thm), theory('equality')], [c_876, c_22])).
% 4.65/1.80  tff(c_896, plain, (![A_151]: (u1_struct_0(A_151)=k2_struct_0(A_151) | ~l1_pre_topc(A_151))), inference(resolution, [status(thm)], [c_10, c_891])).
% 4.65/1.80  tff(c_900, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_896])).
% 4.65/1.80  tff(c_901, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_900, c_56])).
% 4.65/1.80  tff(c_729, plain, (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_74])).
% 4.65/1.80  tff(c_733, plain, (![A_119]: (m1_subset_1('#skF_1'(A_119), k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.65/1.80  tff(c_737, plain, (![A_119]: (v1_xboole_0('#skF_1'(A_119)) | ~v1_xboole_0(u1_struct_0(A_119)) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119))), inference(resolution, [status(thm)], [c_733, c_6])).
% 4.65/1.80  tff(c_935, plain, (v1_xboole_0('#skF_1'('#skF_2')) | ~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_900, c_737])).
% 4.65/1.80  tff(c_968, plain, (v1_xboole_0('#skF_1'('#skF_2')) | ~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_935])).
% 4.65/1.80  tff(c_969, plain, (v1_xboole_0('#skF_1'('#skF_2')) | ~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_72, c_968])).
% 4.65/1.80  tff(c_975, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_969])).
% 4.65/1.80  tff(c_1073, plain, (![A_156, B_157, C_158]: (v3_orders_2(k3_yellow19(A_156, B_157, C_158)) | ~m1_subset_1(C_158, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_157)))) | ~v13_waybel_0(C_158, k3_yellow_1(B_157)) | ~v2_waybel_0(C_158, k3_yellow_1(B_157)) | v1_xboole_0(C_158) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | v1_xboole_0(B_157) | ~l1_struct_0(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.65/1.80  tff(c_1081, plain, (![A_156]: (v3_orders_2(k3_yellow19(A_156, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_156))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_156) | v2_struct_0(A_156))), inference(resolution, [status(thm)], [c_58, c_1073])).
% 4.65/1.80  tff(c_1089, plain, (![A_156]: (v3_orders_2(k3_yellow19(A_156, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_156))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_156) | v2_struct_0(A_156))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1081])).
% 4.65/1.80  tff(c_1098, plain, (![A_159]: (v3_orders_2(k3_yellow19(A_159, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_struct_0(A_159) | v2_struct_0(A_159))), inference(negUnitSimplification, [status(thm)], [c_975, c_66, c_1089])).
% 4.65/1.80  tff(c_1105, plain, (v3_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_8, c_1098])).
% 4.65/1.80  tff(c_1111, plain, (v3_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_72, c_1105])).
% 4.65/1.80  tff(c_1112, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1111])).
% 4.65/1.80  tff(c_1115, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_1112])).
% 4.65/1.80  tff(c_1119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_1115])).
% 4.65/1.80  tff(c_1121, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_1111])).
% 4.65/1.80  tff(c_980, plain, (![A_152, B_153, C_154]: (v4_orders_2(k3_yellow19(A_152, B_153, C_154)) | ~m1_subset_1(C_154, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_153)))) | ~v13_waybel_0(C_154, k3_yellow_1(B_153)) | ~v2_waybel_0(C_154, k3_yellow_1(B_153)) | v1_xboole_0(C_154) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | v1_xboole_0(B_153) | ~l1_struct_0(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.65/1.80  tff(c_988, plain, (![A_152]: (v4_orders_2(k3_yellow19(A_152, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_152))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_152) | v2_struct_0(A_152))), inference(resolution, [status(thm)], [c_58, c_980])).
% 4.65/1.80  tff(c_996, plain, (![A_152]: (v4_orders_2(k3_yellow19(A_152, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_152))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_152) | v2_struct_0(A_152))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_988])).
% 4.65/1.80  tff(c_1165, plain, (![A_165]: (v4_orders_2(k3_yellow19(A_165, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_struct_0(A_165) | v2_struct_0(A_165))), inference(negUnitSimplification, [status(thm)], [c_975, c_66, c_996])).
% 4.65/1.80  tff(c_1172, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_8, c_1165])).
% 4.65/1.80  tff(c_1178, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_1172])).
% 4.65/1.80  tff(c_1179, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_72, c_1178])).
% 4.65/1.80  tff(c_1216, plain, (![A_172, B_173, C_174]: (l1_waybel_0(k3_yellow19(A_172, B_173, C_174), A_172) | ~m1_subset_1(C_174, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_173)))) | ~v13_waybel_0(C_174, k3_yellow_1(B_173)) | ~v2_waybel_0(C_174, k3_yellow_1(B_173)) | v1_xboole_0(C_174) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_172))) | v1_xboole_0(B_173) | ~l1_struct_0(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.65/1.80  tff(c_1224, plain, (![A_172]: (l1_waybel_0(k3_yellow19(A_172, k2_struct_0('#skF_2'), '#skF_3'), A_172) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_172))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_172) | v2_struct_0(A_172))), inference(resolution, [status(thm)], [c_58, c_1216])).
% 4.65/1.80  tff(c_1232, plain, (![A_172]: (l1_waybel_0(k3_yellow19(A_172, k2_struct_0('#skF_2'), '#skF_3'), A_172) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_172))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_172) | v2_struct_0(A_172))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1224])).
% 4.65/1.80  tff(c_1235, plain, (![A_175]: (l1_waybel_0(k3_yellow19(A_175, k2_struct_0('#skF_2'), '#skF_3'), A_175) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_struct_0(A_175) | v2_struct_0(A_175))), inference(negUnitSimplification, [status(thm)], [c_975, c_66, c_1232])).
% 4.65/1.80  tff(c_1240, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_8, c_1235])).
% 4.65/1.80  tff(c_1246, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_1240])).
% 4.65/1.80  tff(c_1247, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_72, c_1246])).
% 4.65/1.80  tff(c_1248, plain, (![A_176, B_177]: (k2_yellow19(A_176, k3_yellow19(A_176, k2_struct_0(A_176), B_177))=B_177 | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_176))))) | ~v13_waybel_0(B_177, k3_yellow_1(k2_struct_0(A_176))) | ~v2_waybel_0(B_177, k3_yellow_1(k2_struct_0(A_176))) | ~v1_subset_1(B_177, u1_struct_0(k3_yellow_1(k2_struct_0(A_176)))) | v1_xboole_0(B_177) | ~l1_struct_0(A_176) | v2_struct_0(A_176))), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.65/1.80  tff(c_1256, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_1248])).
% 4.65/1.80  tff(c_1264, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_64, c_62, c_60, c_1256])).
% 4.65/1.80  tff(c_1265, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_1264])).
% 4.65/1.80  tff(c_52, plain, (![A_27, B_31, C_33]: (r1_waybel_7(A_27, k2_yellow19(A_27, B_31), C_33) | ~r3_waybel_9(A_27, B_31, C_33) | ~m1_subset_1(C_33, u1_struct_0(A_27)) | ~l1_waybel_0(B_31, A_27) | ~v7_waybel_0(B_31) | ~v4_orders_2(B_31) | v2_struct_0(B_31) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.65/1.80  tff(c_1271, plain, (![C_33]: (r1_waybel_7('#skF_2', '#skF_3', C_33) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_33) | ~m1_subset_1(C_33, u1_struct_0('#skF_2')) | ~l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1265, c_52])).
% 4.65/1.80  tff(c_1278, plain, (![C_33]: (r1_waybel_7('#skF_2', '#skF_3', C_33) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_33) | ~m1_subset_1(C_33, k2_struct_0('#skF_2')) | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1179, c_1247, c_900, c_1271])).
% 4.65/1.80  tff(c_1279, plain, (![C_33]: (r1_waybel_7('#skF_2', '#skF_3', C_33) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_33) | ~m1_subset_1(C_33, k2_struct_0('#skF_2')) | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_72, c_1278])).
% 4.65/1.80  tff(c_1284, plain, (~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_1279])).
% 4.65/1.80  tff(c_1288, plain, (![A_184, B_185, C_186]: (v7_waybel_0(k3_yellow19(A_184, B_185, C_186)) | ~m1_subset_1(C_186, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_185)))) | ~v13_waybel_0(C_186, k3_yellow_1(B_185)) | ~v2_waybel_0(C_186, k3_yellow_1(B_185)) | ~v1_subset_1(C_186, u1_struct_0(k3_yellow_1(B_185))) | v1_xboole_0(C_186) | ~m1_subset_1(B_185, k1_zfmisc_1(u1_struct_0(A_184))) | v1_xboole_0(B_185) | ~l1_struct_0(A_184) | v2_struct_0(A_184))), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.65/1.80  tff(c_1296, plain, (![A_184]: (v7_waybel_0(k3_yellow19(A_184, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_184))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_184) | v2_struct_0(A_184))), inference(resolution, [status(thm)], [c_58, c_1288])).
% 4.65/1.80  tff(c_1304, plain, (![A_184]: (v7_waybel_0(k3_yellow19(A_184, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_184))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_184) | v2_struct_0(A_184))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_1296])).
% 4.65/1.80  tff(c_1307, plain, (![A_187]: (v7_waybel_0(k3_yellow19(A_187, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_187))) | ~l1_struct_0(A_187) | v2_struct_0(A_187))), inference(negUnitSimplification, [status(thm)], [c_975, c_66, c_1304])).
% 4.65/1.80  tff(c_1310, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_900, c_1307])).
% 4.65/1.80  tff(c_1316, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_81, c_1310])).
% 4.65/1.80  tff(c_1318, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1284, c_1316])).
% 4.65/1.80  tff(c_1319, plain, (![C_33]: (v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | r1_waybel_7('#skF_2', '#skF_3', C_33) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_33) | ~m1_subset_1(C_33, k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_1279])).
% 4.65/1.80  tff(c_1321, plain, (v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_1319])).
% 4.65/1.80  tff(c_1326, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1321, c_42])).
% 4.65/1.80  tff(c_1329, plain, (v1_xboole_0('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_81, c_900, c_62, c_60, c_58, c_1326])).
% 4.65/1.80  tff(c_1331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_975, c_66, c_1329])).
% 4.65/1.80  tff(c_1334, plain, (![C_188]: (r1_waybel_7('#skF_2', '#skF_3', C_188) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_188) | ~m1_subset_1(C_188, k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_1319])).
% 4.65/1.80  tff(c_1337, plain, (r1_waybel_7('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_729, c_1334])).
% 4.65/1.80  tff(c_1340, plain, (r1_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_901, c_1337])).
% 4.65/1.80  tff(c_1342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_728, c_1340])).
% 4.65/1.80  tff(c_1343, plain, (v1_xboole_0('#skF_1'('#skF_2'))), inference(splitRight, [status(thm)], [c_969])).
% 4.65/1.80  tff(c_1347, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1343, c_14])).
% 4.65/1.80  tff(c_1350, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1347])).
% 4.65/1.80  tff(c_1352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1350])).
% 4.65/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.65/1.80  
% 4.65/1.80  Inference rules
% 4.65/1.80  ----------------------
% 4.65/1.80  #Ref     : 0
% 4.65/1.80  #Sup     : 232
% 4.65/1.80  #Fact    : 0
% 4.65/1.80  #Define  : 0
% 4.65/1.80  #Split   : 17
% 4.65/1.80  #Chain   : 0
% 4.65/1.80  #Close   : 0
% 4.65/1.80  
% 4.65/1.80  Ordering : KBO
% 4.65/1.80  
% 4.65/1.80  Simplification rules
% 4.65/1.80  ----------------------
% 4.65/1.80  #Subsume      : 31
% 4.65/1.80  #Demod        : 224
% 4.65/1.80  #Tautology    : 73
% 4.65/1.80  #SimpNegUnit  : 55
% 4.65/1.80  #BackRed      : 2
% 4.65/1.80  
% 4.65/1.80  #Partial instantiations: 0
% 4.65/1.80  #Strategies tried      : 1
% 4.65/1.80  
% 4.65/1.80  Timing (in seconds)
% 4.65/1.80  ----------------------
% 4.65/1.80  Preprocessing        : 0.39
% 4.65/1.80  Parsing              : 0.20
% 4.65/1.80  CNF conversion       : 0.03
% 4.65/1.80  Main loop            : 0.58
% 4.65/1.80  Inferencing          : 0.21
% 4.65/1.80  Reduction            : 0.18
% 4.65/1.80  Demodulation         : 0.12
% 4.65/1.80  BG Simplification    : 0.03
% 4.65/1.80  Subsumption          : 0.11
% 4.65/1.80  Abstraction          : 0.03
% 4.65/1.80  MUC search           : 0.00
% 4.65/1.81  Cooper               : 0.00
% 4.65/1.81  Total                : 1.05
% 4.65/1.81  Index Insertion      : 0.00
% 4.65/1.81  Index Deletion       : 0.00
% 4.65/1.81  Index Matching       : 0.00
% 4.65/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
