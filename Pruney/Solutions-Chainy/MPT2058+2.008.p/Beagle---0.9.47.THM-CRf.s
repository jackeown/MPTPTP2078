%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:33 EST 2020

% Result     : Theorem 4.50s
% Output     : CNFRefutation 4.77s
% Verified   : 
% Statistics : Number of formulae       :  220 (3362 expanded)
%              Number of leaves         :   54 (1182 expanded)
%              Depth                    :   24
%              Number of atoms          :  709 (14129 expanded)
%              Number of equality atoms :   43 (1386 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v4_pre_topc > v2_waybel_0 > v1_tops_1 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k2_pre_topc > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

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

tff(f_258,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_160,axiom,(
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

tff(f_188,axiom,(
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

tff(f_132,axiom,(
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

tff(f_231,axiom,(
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

tff(f_212,axiom,(
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

tff(c_80,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_78,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_76,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_14,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    ! [A_12] :
      ( v4_pre_topc(k2_struct_0(A_12),A_12)
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [A_10] :
      ( m1_subset_1(k2_struct_0(A_10),k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_151,plain,(
    ! [A_68,B_69] :
      ( k2_pre_topc(A_68,B_69) = B_69
      | ~ v4_pre_topc(B_69,A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_171,plain,(
    ! [A_72] :
      ( k2_pre_topc(A_72,k2_struct_0(A_72)) = k2_struct_0(A_72)
      | ~ v4_pre_topc(k2_struct_0(A_72),A_72)
      | ~ l1_pre_topc(A_72)
      | ~ l1_struct_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_12,c_151])).

tff(c_175,plain,(
    ! [A_12] :
      ( k2_pre_topc(A_12,k2_struct_0(A_12)) = k2_struct_0(A_12)
      | ~ l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_171])).

tff(c_226,plain,(
    ! [B_82,A_83] :
      ( v1_tops_1(B_82,A_83)
      | k2_pre_topc(A_83,B_82) != k2_struct_0(A_83)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_253,plain,(
    ! [A_85] :
      ( v1_tops_1(k2_struct_0(A_85),A_85)
      | k2_pre_topc(A_85,k2_struct_0(A_85)) != k2_struct_0(A_85)
      | ~ l1_pre_topc(A_85)
      | ~ l1_struct_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_12,c_226])).

tff(c_203,plain,(
    ! [A_76,B_77] :
      ( k2_pre_topc(A_76,B_77) = u1_struct_0(A_76)
      | ~ v1_tops_1(B_77,A_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_218,plain,(
    ! [A_10] :
      ( k2_pre_topc(A_10,k2_struct_0(A_10)) = u1_struct_0(A_10)
      | ~ v1_tops_1(k2_struct_0(A_10),A_10)
      | ~ l1_pre_topc(A_10)
      | ~ l1_struct_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_203])).

tff(c_362,plain,(
    ! [A_105] :
      ( k2_pre_topc(A_105,k2_struct_0(A_105)) = u1_struct_0(A_105)
      | k2_pre_topc(A_105,k2_struct_0(A_105)) != k2_struct_0(A_105)
      | ~ l1_pre_topc(A_105)
      | ~ l1_struct_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_253,c_218])).

tff(c_367,plain,(
    ! [A_106] :
      ( k2_pre_topc(A_106,k2_struct_0(A_106)) = u1_struct_0(A_106)
      | ~ l1_struct_0(A_106)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_362])).

tff(c_389,plain,(
    ! [A_107] :
      ( u1_struct_0(A_107) = k2_struct_0(A_107)
      | ~ l1_struct_0(A_107)
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | ~ l1_struct_0(A_107)
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_175])).

tff(c_391,plain,
    ( u1_struct_0('#skF_3') = k2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_389])).

tff(c_394,plain,
    ( u1_struct_0('#skF_3') = k2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_391])).

tff(c_400,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_403,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_400])).

tff(c_407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_403])).

tff(c_408,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_410,plain,(
    m1_subset_1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_64])).

tff(c_88,plain,
    ( r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_5')
    | r1_waybel_7('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_129,plain,(
    r1_waybel_7('#skF_3','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,(
    ! [A_65] :
      ( m1_subset_1('#skF_2'(A_65),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    ! [C_9,B_8,A_7] :
      ( ~ v1_xboole_0(C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_145,plain,(
    ! [A_66,A_67] :
      ( ~ v1_xboole_0(u1_struct_0(A_66))
      | ~ r2_hidden(A_67,'#skF_2'(A_66))
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_139,c_10])).

tff(c_150,plain,(
    ! [A_66] :
      ( ~ v1_xboole_0(u1_struct_0(A_66))
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66)
      | v1_xboole_0('#skF_2'(A_66)) ) ),
    inference(resolution,[status(thm)],[c_4,c_145])).

tff(c_450,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_150])).

tff(c_493,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | v2_struct_0('#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_450])).

tff(c_494,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | v1_xboole_0('#skF_2'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_493])).

tff(c_507,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_494])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_409,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_6,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_6] : m1_subset_1(k2_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    ! [A_6] : m1_subset_1(A_6,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_70,plain,(
    v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_68,plain,(
    v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_736,plain,(
    ! [A_124,B_125,C_126] :
      ( v4_orders_2(k3_yellow19(A_124,B_125,C_126))
      | ~ m1_subset_1(C_126,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_125))))
      | ~ v13_waybel_0(C_126,k3_yellow_1(B_125))
      | ~ v2_waybel_0(C_126,k3_yellow_1(B_125))
      | v1_xboole_0(C_126)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | v1_xboole_0(B_125)
      | ~ l1_struct_0(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_744,plain,(
    ! [A_124] :
      ( v4_orders_2(k3_yellow19(A_124,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_124)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_124)
      | v2_struct_0(A_124) ) ),
    inference(resolution,[status(thm)],[c_66,c_736])).

tff(c_752,plain,(
    ! [A_124] :
      ( v4_orders_2(k3_yellow19(A_124,k2_struct_0('#skF_3'),'#skF_4'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_124)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_124)
      | v2_struct_0(A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_744])).

tff(c_783,plain,(
    ! [A_128] :
      ( v4_orders_2(k3_yellow19(A_128,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_struct_0(A_128)
      | v2_struct_0(A_128) ) ),
    inference(negUnitSimplification,[status(thm)],[c_507,c_74,c_752])).

tff(c_790,plain,
    ( v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_783])).

tff(c_796,plain,
    ( v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_790])).

tff(c_797,plain,(
    v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_796])).

tff(c_72,plain,(
    v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_919,plain,(
    ! [A_140,B_141,C_142] :
      ( v7_waybel_0(k3_yellow19(A_140,B_141,C_142))
      | ~ m1_subset_1(C_142,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_141))))
      | ~ v13_waybel_0(C_142,k3_yellow_1(B_141))
      | ~ v2_waybel_0(C_142,k3_yellow_1(B_141))
      | ~ v1_subset_1(C_142,u1_struct_0(k3_yellow_1(B_141)))
      | v1_xboole_0(C_142)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | v1_xboole_0(B_141)
      | ~ l1_struct_0(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_927,plain,(
    ! [A_140] :
      ( v7_waybel_0(k3_yellow19(A_140,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_140)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_140)
      | v2_struct_0(A_140) ) ),
    inference(resolution,[status(thm)],[c_66,c_919])).

tff(c_935,plain,(
    ! [A_140] :
      ( v7_waybel_0(k3_yellow19(A_140,k2_struct_0('#skF_3'),'#skF_4'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_140)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_140)
      | v2_struct_0(A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_927])).

tff(c_938,plain,(
    ! [A_143] :
      ( v7_waybel_0(k3_yellow19(A_143,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_struct_0(A_143)
      | v2_struct_0(A_143) ) ),
    inference(negUnitSimplification,[status(thm)],[c_507,c_74,c_935])).

tff(c_945,plain,
    ( v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_938])).

tff(c_951,plain,
    ( v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_945])).

tff(c_952,plain,(
    v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_951])).

tff(c_809,plain,(
    ! [A_130,B_131,C_132] :
      ( l1_waybel_0(k3_yellow19(A_130,B_131,C_132),A_130)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_131))))
      | ~ v13_waybel_0(C_132,k3_yellow_1(B_131))
      | ~ v2_waybel_0(C_132,k3_yellow_1(B_131))
      | v1_xboole_0(C_132)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | v1_xboole_0(B_131)
      | ~ l1_struct_0(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_817,plain,(
    ! [A_130] :
      ( l1_waybel_0(k3_yellow19(A_130,k2_struct_0('#skF_3'),'#skF_4'),A_130)
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_130)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_130)
      | v2_struct_0(A_130) ) ),
    inference(resolution,[status(thm)],[c_66,c_809])).

tff(c_825,plain,(
    ! [A_130] :
      ( l1_waybel_0(k3_yellow19(A_130,k2_struct_0('#skF_3'),'#skF_4'),A_130)
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_130)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_130)
      | v2_struct_0(A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_817])).

tff(c_828,plain,(
    ! [A_133] :
      ( l1_waybel_0(k3_yellow19(A_133,k2_struct_0('#skF_3'),'#skF_4'),A_133)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_struct_0(A_133)
      | v2_struct_0(A_133) ) ),
    inference(negUnitSimplification,[status(thm)],[c_507,c_74,c_825])).

tff(c_833,plain,
    ( l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_828])).

tff(c_839,plain,
    ( l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_833])).

tff(c_840,plain,(
    l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_839])).

tff(c_954,plain,(
    ! [A_144,B_145] :
      ( k2_yellow19(A_144,k3_yellow19(A_144,k2_struct_0(A_144),B_145)) = B_145
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_144)))))
      | ~ v13_waybel_0(B_145,k3_yellow_1(k2_struct_0(A_144)))
      | ~ v2_waybel_0(B_145,k3_yellow_1(k2_struct_0(A_144)))
      | ~ v1_subset_1(B_145,u1_struct_0(k3_yellow_1(k2_struct_0(A_144))))
      | v1_xboole_0(B_145)
      | ~ l1_struct_0(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_962,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = '#skF_4'
    | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_954])).

tff(c_970,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_72,c_70,c_68,c_962])).

tff(c_971,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_970])).

tff(c_60,plain,(
    ! [A_34,B_38,C_40] :
      ( r1_waybel_7(A_34,k2_yellow19(A_34,B_38),C_40)
      | ~ r3_waybel_9(A_34,B_38,C_40)
      | ~ m1_subset_1(C_40,u1_struct_0(A_34))
      | ~ l1_waybel_0(B_38,A_34)
      | ~ v7_waybel_0(B_38)
      | ~ v4_orders_2(B_38)
      | v2_struct_0(B_38)
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_976,plain,(
    ! [C_40] :
      ( r1_waybel_7('#skF_3','#skF_4',C_40)
      | ~ r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),C_40)
      | ~ m1_subset_1(C_40,u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_971,c_60])).

tff(c_983,plain,(
    ! [C_40] :
      ( r1_waybel_7('#skF_3','#skF_4',C_40)
      | ~ r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),C_40)
      | ~ m1_subset_1(C_40,k2_struct_0('#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_797,c_952,c_840,c_408,c_976])).

tff(c_984,plain,(
    ! [C_40] :
      ( r1_waybel_7('#skF_3','#skF_4',C_40)
      | ~ r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),C_40)
      | ~ m1_subset_1(C_40,k2_struct_0('#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_983])).

tff(c_1131,plain,(
    v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_984])).

tff(c_50,plain,(
    ! [A_28,B_29,C_30] :
      ( ~ v2_struct_0(k3_yellow19(A_28,B_29,C_30))
      | ~ m1_subset_1(C_30,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_29))))
      | ~ v13_waybel_0(C_30,k3_yellow_1(B_29))
      | ~ v2_waybel_0(C_30,k3_yellow_1(B_29))
      | v1_xboole_0(C_30)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | v1_xboole_0(B_29)
      | ~ l1_struct_0(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1134,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1131,c_50])).

tff(c_1137,plain,
    ( v1_xboole_0('#skF_4')
    | v1_xboole_0(k2_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_89,c_408,c_70,c_68,c_66,c_1134])).

tff(c_1139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_507,c_74,c_1137])).

tff(c_1141,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_984])).

tff(c_58,plain,(
    ! [A_34,B_38,C_40] :
      ( r3_waybel_9(A_34,B_38,C_40)
      | ~ r1_waybel_7(A_34,k2_yellow19(A_34,B_38),C_40)
      | ~ m1_subset_1(C_40,u1_struct_0(A_34))
      | ~ l1_waybel_0(B_38,A_34)
      | ~ v7_waybel_0(B_38)
      | ~ v4_orders_2(B_38)
      | v2_struct_0(B_38)
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_979,plain,(
    ! [C_40] :
      ( r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),C_40)
      | ~ r1_waybel_7('#skF_3','#skF_4',C_40)
      | ~ m1_subset_1(C_40,u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_971,c_58])).

tff(c_986,plain,(
    ! [C_40] :
      ( r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),C_40)
      | ~ r1_waybel_7('#skF_3','#skF_4',C_40)
      | ~ m1_subset_1(C_40,k2_struct_0('#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_797,c_952,c_840,c_408,c_979])).

tff(c_987,plain,(
    ! [C_40] :
      ( r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),C_40)
      | ~ r1_waybel_7('#skF_3','#skF_4',C_40)
      | ~ m1_subset_1(C_40,k2_struct_0('#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_986])).

tff(c_1144,plain,(
    ! [C_152] :
      ( r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),C_152)
      | ~ r1_waybel_7('#skF_3','#skF_4',C_152)
      | ~ m1_subset_1(C_152,k2_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1141,c_987])).

tff(c_82,plain,
    ( ~ r1_waybel_7('#skF_3','#skF_4','#skF_5')
    | ~ r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_144,plain,(
    ~ r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_82])).

tff(c_1150,plain,
    ( ~ r1_waybel_7('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1144,c_144])).

tff(c_1155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_129,c_1150])).

tff(c_1156,plain,(
    v1_xboole_0('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_494])).

tff(c_20,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0('#skF_2'(A_13))
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1160,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1156,c_20])).

tff(c_1163,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1160])).

tff(c_1165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1163])).

tff(c_1167,plain,(
    ~ r1_waybel_7('#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_1190,plain,(
    ! [A_161,B_162] :
      ( k2_pre_topc(A_161,B_162) = B_162
      | ~ v4_pre_topc(B_162,A_161)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_pre_topc(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1209,plain,(
    ! [A_164] :
      ( k2_pre_topc(A_164,k2_struct_0(A_164)) = k2_struct_0(A_164)
      | ~ v4_pre_topc(k2_struct_0(A_164),A_164)
      | ~ l1_pre_topc(A_164)
      | ~ l1_struct_0(A_164) ) ),
    inference(resolution,[status(thm)],[c_12,c_1190])).

tff(c_1213,plain,(
    ! [A_12] :
      ( k2_pre_topc(A_12,k2_struct_0(A_12)) = k2_struct_0(A_12)
      | ~ l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_1209])).

tff(c_1214,plain,(
    ! [B_165,A_166] :
      ( v1_tops_1(B_165,A_166)
      | k2_pre_topc(A_166,B_165) != k2_struct_0(A_166)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1229,plain,(
    ! [A_10] :
      ( v1_tops_1(k2_struct_0(A_10),A_10)
      | k2_pre_topc(A_10,k2_struct_0(A_10)) != k2_struct_0(A_10)
      | ~ l1_pre_topc(A_10)
      | ~ l1_struct_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_1214])).

tff(c_1264,plain,(
    ! [A_174,B_175] :
      ( k2_pre_topc(A_174,B_175) = u1_struct_0(A_174)
      | ~ v1_tops_1(B_175,A_174)
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_pre_topc(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1327,plain,(
    ! [A_181] :
      ( k2_pre_topc(A_181,k2_struct_0(A_181)) = u1_struct_0(A_181)
      | ~ v1_tops_1(k2_struct_0(A_181),A_181)
      | ~ l1_pre_topc(A_181)
      | ~ l1_struct_0(A_181) ) ),
    inference(resolution,[status(thm)],[c_12,c_1264])).

tff(c_1401,plain,(
    ! [A_199] :
      ( k2_pre_topc(A_199,k2_struct_0(A_199)) = u1_struct_0(A_199)
      | k2_pre_topc(A_199,k2_struct_0(A_199)) != k2_struct_0(A_199)
      | ~ l1_pre_topc(A_199)
      | ~ l1_struct_0(A_199) ) ),
    inference(resolution,[status(thm)],[c_1229,c_1327])).

tff(c_1406,plain,(
    ! [A_200] :
      ( k2_pre_topc(A_200,k2_struct_0(A_200)) = u1_struct_0(A_200)
      | ~ l1_struct_0(A_200)
      | ~ l1_pre_topc(A_200)
      | ~ v2_pre_topc(A_200) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1213,c_1401])).

tff(c_1433,plain,(
    ! [A_205] :
      ( u1_struct_0(A_205) = k2_struct_0(A_205)
      | ~ l1_struct_0(A_205)
      | ~ l1_pre_topc(A_205)
      | ~ v2_pre_topc(A_205)
      | ~ l1_struct_0(A_205)
      | ~ l1_pre_topc(A_205)
      | ~ v2_pre_topc(A_205) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1213,c_1406])).

tff(c_1435,plain,
    ( u1_struct_0('#skF_3') = k2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1433])).

tff(c_1438,plain,
    ( u1_struct_0('#skF_3') = k2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1435])).

tff(c_1439,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1438])).

tff(c_1442,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_1439])).

tff(c_1446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1442])).

tff(c_1447,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1438])).

tff(c_1449,plain,(
    m1_subset_1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1447,c_64])).

tff(c_1166,plain,(
    r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_1177,plain,(
    ! [A_157] :
      ( m1_subset_1('#skF_2'(A_157),k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1183,plain,(
    ! [A_158,A_159] :
      ( ~ v1_xboole_0(u1_struct_0(A_158))
      | ~ r2_hidden(A_159,'#skF_2'(A_158))
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(resolution,[status(thm)],[c_1177,c_10])).

tff(c_1188,plain,(
    ! [A_158] :
      ( ~ v1_xboole_0(u1_struct_0(A_158))
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158)
      | v1_xboole_0('#skF_2'(A_158)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1183])).

tff(c_1495,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1447,c_1188])).

tff(c_1536,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | v2_struct_0('#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1495])).

tff(c_1537,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | v1_xboole_0('#skF_2'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1536])).

tff(c_1546,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1537])).

tff(c_1448,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1438])).

tff(c_1940,plain,(
    ! [A_230,B_231,C_232] :
      ( v7_waybel_0(k3_yellow19(A_230,B_231,C_232))
      | ~ m1_subset_1(C_232,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_231))))
      | ~ v13_waybel_0(C_232,k3_yellow_1(B_231))
      | ~ v2_waybel_0(C_232,k3_yellow_1(B_231))
      | ~ v1_subset_1(C_232,u1_struct_0(k3_yellow_1(B_231)))
      | v1_xboole_0(C_232)
      | ~ m1_subset_1(B_231,k1_zfmisc_1(u1_struct_0(A_230)))
      | v1_xboole_0(B_231)
      | ~ l1_struct_0(A_230)
      | v2_struct_0(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1948,plain,(
    ! [A_230] :
      ( v7_waybel_0(k3_yellow19(A_230,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_230)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_230)
      | v2_struct_0(A_230) ) ),
    inference(resolution,[status(thm)],[c_66,c_1940])).

tff(c_1956,plain,(
    ! [A_230] :
      ( v7_waybel_0(k3_yellow19(A_230,k2_struct_0('#skF_3'),'#skF_4'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_230)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_230)
      | v2_struct_0(A_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1948])).

tff(c_1959,plain,(
    ! [A_233] :
      ( v7_waybel_0(k3_yellow19(A_233,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ l1_struct_0(A_233)
      | v2_struct_0(A_233) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1546,c_74,c_1956])).

tff(c_1966,plain,
    ( v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1959])).

tff(c_1972,plain,
    ( v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_1966])).

tff(c_1973,plain,(
    v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1972])).

tff(c_1709,plain,(
    ! [A_214,B_215,C_216] :
      ( l1_waybel_0(k3_yellow19(A_214,B_215,C_216),A_214)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_215))))
      | ~ v13_waybel_0(C_216,k3_yellow_1(B_215))
      | ~ v2_waybel_0(C_216,k3_yellow_1(B_215))
      | v1_xboole_0(C_216)
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0(A_214)))
      | v1_xboole_0(B_215)
      | ~ l1_struct_0(A_214)
      | v2_struct_0(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1717,plain,(
    ! [A_214] :
      ( l1_waybel_0(k3_yellow19(A_214,k2_struct_0('#skF_3'),'#skF_4'),A_214)
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_214)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_214)
      | v2_struct_0(A_214) ) ),
    inference(resolution,[status(thm)],[c_66,c_1709])).

tff(c_1725,plain,(
    ! [A_214] :
      ( l1_waybel_0(k3_yellow19(A_214,k2_struct_0('#skF_3'),'#skF_4'),A_214)
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_214)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_214)
      | v2_struct_0(A_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1717])).

tff(c_1912,plain,(
    ! [A_228] :
      ( l1_waybel_0(k3_yellow19(A_228,k2_struct_0('#skF_3'),'#skF_4'),A_228)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ l1_struct_0(A_228)
      | v2_struct_0(A_228) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1546,c_74,c_1725])).

tff(c_1917,plain,
    ( l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1912])).

tff(c_1923,plain,
    ( l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_1917])).

tff(c_1924,plain,(
    l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1923])).

tff(c_1658,plain,(
    ! [A_210,B_211,C_212] :
      ( v4_orders_2(k3_yellow19(A_210,B_211,C_212))
      | ~ m1_subset_1(C_212,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_211))))
      | ~ v13_waybel_0(C_212,k3_yellow_1(B_211))
      | ~ v2_waybel_0(C_212,k3_yellow_1(B_211))
      | v1_xboole_0(C_212)
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0(A_210)))
      | v1_xboole_0(B_211)
      | ~ l1_struct_0(A_210)
      | v2_struct_0(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1666,plain,(
    ! [A_210] :
      ( v4_orders_2(k3_yellow19(A_210,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_210)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_210)
      | v2_struct_0(A_210) ) ),
    inference(resolution,[status(thm)],[c_66,c_1658])).

tff(c_1674,plain,(
    ! [A_210] :
      ( v4_orders_2(k3_yellow19(A_210,k2_struct_0('#skF_3'),'#skF_4'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_210)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_210)
      | v2_struct_0(A_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1666])).

tff(c_1861,plain,(
    ! [A_225] :
      ( v4_orders_2(k3_yellow19(A_225,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_225)))
      | ~ l1_struct_0(A_225)
      | v2_struct_0(A_225) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1546,c_74,c_1674])).

tff(c_1868,plain,
    ( v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1861])).

tff(c_1874,plain,
    ( v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_1868])).

tff(c_1875,plain,(
    v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1874])).

tff(c_1876,plain,(
    ! [A_226,B_227] :
      ( k2_yellow19(A_226,k3_yellow19(A_226,k2_struct_0(A_226),B_227)) = B_227
      | ~ m1_subset_1(B_227,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_226)))))
      | ~ v13_waybel_0(B_227,k3_yellow_1(k2_struct_0(A_226)))
      | ~ v2_waybel_0(B_227,k3_yellow_1(k2_struct_0(A_226)))
      | ~ v1_subset_1(B_227,u1_struct_0(k3_yellow_1(k2_struct_0(A_226))))
      | v1_xboole_0(B_227)
      | ~ l1_struct_0(A_226)
      | v2_struct_0(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_1884,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = '#skF_4'
    | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1876])).

tff(c_1892,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_72,c_70,c_68,c_1884])).

tff(c_1893,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_1892])).

tff(c_1899,plain,(
    ! [C_40] :
      ( r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),C_40)
      | ~ r1_waybel_7('#skF_3','#skF_4',C_40)
      | ~ m1_subset_1(C_40,u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1893,c_58])).

tff(c_1906,plain,(
    ! [C_40] :
      ( r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),C_40)
      | ~ r1_waybel_7('#skF_3','#skF_4',C_40)
      | ~ m1_subset_1(C_40,k2_struct_0('#skF_3'))
      | ~ l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1875,c_1447,c_1899])).

tff(c_1907,plain,(
    ! [C_40] :
      ( r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),C_40)
      | ~ r1_waybel_7('#skF_3','#skF_4',C_40)
      | ~ m1_subset_1(C_40,k2_struct_0('#skF_3'))
      | ~ l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1906])).

tff(c_1976,plain,(
    ! [C_40] :
      ( r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),C_40)
      | ~ r1_waybel_7('#skF_3','#skF_4',C_40)
      | ~ m1_subset_1(C_40,k2_struct_0('#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1973,c_1924,c_1907])).

tff(c_1977,plain,(
    v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1976])).

tff(c_1979,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1977,c_50])).

tff(c_1982,plain,
    ( v1_xboole_0('#skF_4')
    | v1_xboole_0(k2_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_89,c_1447,c_70,c_68,c_66,c_1979])).

tff(c_1984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1546,c_74,c_1982])).

tff(c_1986,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1976])).

tff(c_1902,plain,(
    ! [C_40] :
      ( r1_waybel_7('#skF_3','#skF_4',C_40)
      | ~ r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),C_40)
      | ~ m1_subset_1(C_40,u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1893,c_60])).

tff(c_1909,plain,(
    ! [C_40] :
      ( r1_waybel_7('#skF_3','#skF_4',C_40)
      | ~ r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),C_40)
      | ~ m1_subset_1(C_40,k2_struct_0('#skF_3'))
      | ~ l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1875,c_1447,c_1902])).

tff(c_1910,plain,(
    ! [C_40] :
      ( r1_waybel_7('#skF_3','#skF_4',C_40)
      | ~ r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),C_40)
      | ~ m1_subset_1(C_40,k2_struct_0('#skF_3'))
      | ~ l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1909])).

tff(c_2132,plain,(
    ! [C_40] :
      ( r1_waybel_7('#skF_3','#skF_4',C_40)
      | ~ r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),C_40)
      | ~ m1_subset_1(C_40,k2_struct_0('#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1973,c_1924,c_1910])).

tff(c_2134,plain,(
    ! [C_242] :
      ( r1_waybel_7('#skF_3','#skF_4',C_242)
      | ~ r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),C_242)
      | ~ m1_subset_1(C_242,k2_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1986,c_2132])).

tff(c_2140,plain,
    ( r1_waybel_7('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1166,c_2134])).

tff(c_2144,plain,(
    r1_waybel_7('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1449,c_2140])).

tff(c_2146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1167,c_2144])).

tff(c_2147,plain,(
    v1_xboole_0('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1537])).

tff(c_2151,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2147,c_20])).

tff(c_2154,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_2151])).

tff(c_2156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:54:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.50/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/1.83  
% 4.69/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/1.83  %$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v4_pre_topc > v2_waybel_0 > v1_tops_1 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k2_pre_topc > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 4.69/1.83  
% 4.69/1.83  %Foreground sorts:
% 4.69/1.83  
% 4.69/1.83  
% 4.69/1.83  %Background operators:
% 4.69/1.83  
% 4.69/1.83  
% 4.69/1.83  %Foreground operators:
% 4.69/1.83  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.69/1.83  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.69/1.83  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.69/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.69/1.83  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 4.69/1.83  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 4.69/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.69/1.83  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.69/1.83  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 4.69/1.83  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.69/1.83  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 4.69/1.83  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.69/1.83  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 4.69/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.69/1.83  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.69/1.83  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 4.69/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.69/1.83  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 4.69/1.83  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.69/1.83  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 4.69/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.69/1.83  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.69/1.83  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.69/1.83  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 4.69/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.69/1.83  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 4.69/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.69/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.69/1.83  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 4.69/1.83  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 4.69/1.83  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.69/1.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.69/1.83  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.69/1.83  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.69/1.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.69/1.83  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.69/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.69/1.83  
% 4.77/1.87  tff(f_258, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, k3_yellow19(A, k2_struct_0(A), B), C) <=> r1_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_yellow19)).
% 4.77/1.87  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.77/1.87  tff(f_56, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 4.77/1.87  tff(f_46, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 4.77/1.87  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.77/1.87  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 4.77/1.87  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 4.77/1.87  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.77/1.87  tff(f_71, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 4.77/1.87  tff(f_42, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.77/1.87  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.77/1.87  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.77/1.87  tff(f_160, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_yellow19)).
% 4.77/1.87  tff(f_188, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow19)).
% 4.77/1.87  tff(f_132, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 4.77/1.87  tff(f_231, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 4.77/1.87  tff(f_212, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> r1_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_yellow19)).
% 4.77/1.87  tff(c_80, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_258])).
% 4.77/1.87  tff(c_78, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_258])).
% 4.77/1.87  tff(c_76, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_258])).
% 4.77/1.87  tff(c_14, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.77/1.87  tff(c_16, plain, (![A_12]: (v4_pre_topc(k2_struct_0(A_12), A_12) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.77/1.87  tff(c_12, plain, (![A_10]: (m1_subset_1(k2_struct_0(A_10), k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.77/1.87  tff(c_151, plain, (![A_68, B_69]: (k2_pre_topc(A_68, B_69)=B_69 | ~v4_pre_topc(B_69, A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.77/1.87  tff(c_171, plain, (![A_72]: (k2_pre_topc(A_72, k2_struct_0(A_72))=k2_struct_0(A_72) | ~v4_pre_topc(k2_struct_0(A_72), A_72) | ~l1_pre_topc(A_72) | ~l1_struct_0(A_72))), inference(resolution, [status(thm)], [c_12, c_151])).
% 4.77/1.87  tff(c_175, plain, (![A_12]: (k2_pre_topc(A_12, k2_struct_0(A_12))=k2_struct_0(A_12) | ~l1_struct_0(A_12) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12))), inference(resolution, [status(thm)], [c_16, c_171])).
% 4.77/1.87  tff(c_226, plain, (![B_82, A_83]: (v1_tops_1(B_82, A_83) | k2_pre_topc(A_83, B_82)!=k2_struct_0(A_83) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.77/1.87  tff(c_253, plain, (![A_85]: (v1_tops_1(k2_struct_0(A_85), A_85) | k2_pre_topc(A_85, k2_struct_0(A_85))!=k2_struct_0(A_85) | ~l1_pre_topc(A_85) | ~l1_struct_0(A_85))), inference(resolution, [status(thm)], [c_12, c_226])).
% 4.77/1.87  tff(c_203, plain, (![A_76, B_77]: (k2_pre_topc(A_76, B_77)=u1_struct_0(A_76) | ~v1_tops_1(B_77, A_76) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.77/1.87  tff(c_218, plain, (![A_10]: (k2_pre_topc(A_10, k2_struct_0(A_10))=u1_struct_0(A_10) | ~v1_tops_1(k2_struct_0(A_10), A_10) | ~l1_pre_topc(A_10) | ~l1_struct_0(A_10))), inference(resolution, [status(thm)], [c_12, c_203])).
% 4.77/1.87  tff(c_362, plain, (![A_105]: (k2_pre_topc(A_105, k2_struct_0(A_105))=u1_struct_0(A_105) | k2_pre_topc(A_105, k2_struct_0(A_105))!=k2_struct_0(A_105) | ~l1_pre_topc(A_105) | ~l1_struct_0(A_105))), inference(resolution, [status(thm)], [c_253, c_218])).
% 4.77/1.87  tff(c_367, plain, (![A_106]: (k2_pre_topc(A_106, k2_struct_0(A_106))=u1_struct_0(A_106) | ~l1_struct_0(A_106) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106))), inference(superposition, [status(thm), theory('equality')], [c_175, c_362])).
% 4.77/1.87  tff(c_389, plain, (![A_107]: (u1_struct_0(A_107)=k2_struct_0(A_107) | ~l1_struct_0(A_107) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107) | ~l1_struct_0(A_107) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107))), inference(superposition, [status(thm), theory('equality')], [c_367, c_175])).
% 4.77/1.87  tff(c_391, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3') | ~l1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_78, c_389])).
% 4.77/1.87  tff(c_394, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_391])).
% 4.77/1.87  tff(c_400, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_394])).
% 4.77/1.87  tff(c_403, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_400])).
% 4.77/1.87  tff(c_407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_403])).
% 4.77/1.87  tff(c_408, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_394])).
% 4.77/1.87  tff(c_64, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_258])).
% 4.77/1.87  tff(c_410, plain, (m1_subset_1('#skF_5', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_408, c_64])).
% 4.77/1.87  tff(c_88, plain, (r3_waybel_9('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_5') | r1_waybel_7('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_258])).
% 4.77/1.87  tff(c_129, plain, (r1_waybel_7('#skF_3', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_88])).
% 4.77/1.87  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.77/1.87  tff(c_139, plain, (![A_65]: (m1_subset_1('#skF_2'(A_65), k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.77/1.87  tff(c_10, plain, (![C_9, B_8, A_7]: (~v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.77/1.87  tff(c_145, plain, (![A_66, A_67]: (~v1_xboole_0(u1_struct_0(A_66)) | ~r2_hidden(A_67, '#skF_2'(A_66)) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66))), inference(resolution, [status(thm)], [c_139, c_10])).
% 4.77/1.87  tff(c_150, plain, (![A_66]: (~v1_xboole_0(u1_struct_0(A_66)) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66) | v1_xboole_0('#skF_2'(A_66)))), inference(resolution, [status(thm)], [c_4, c_145])).
% 4.77/1.87  tff(c_450, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0('#skF_2'('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_408, c_150])).
% 4.77/1.87  tff(c_493, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | v2_struct_0('#skF_3') | v1_xboole_0('#skF_2'('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_450])).
% 4.77/1.87  tff(c_494, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | v1_xboole_0('#skF_2'('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_80, c_493])).
% 4.77/1.87  tff(c_507, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_494])).
% 4.77/1.87  tff(c_74, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_258])).
% 4.77/1.87  tff(c_409, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_394])).
% 4.77/1.87  tff(c_6, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.77/1.87  tff(c_8, plain, (![A_6]: (m1_subset_1(k2_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.77/1.87  tff(c_89, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 4.77/1.87  tff(c_70, plain, (v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_258])).
% 4.77/1.87  tff(c_68, plain, (v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_258])).
% 4.77/1.87  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))), inference(cnfTransformation, [status(thm)], [f_258])).
% 4.77/1.87  tff(c_736, plain, (![A_124, B_125, C_126]: (v4_orders_2(k3_yellow19(A_124, B_125, C_126)) | ~m1_subset_1(C_126, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_125)))) | ~v13_waybel_0(C_126, k3_yellow_1(B_125)) | ~v2_waybel_0(C_126, k3_yellow_1(B_125)) | v1_xboole_0(C_126) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | v1_xboole_0(B_125) | ~l1_struct_0(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.77/1.87  tff(c_744, plain, (![A_124]: (v4_orders_2(k3_yellow19(A_124, k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_124))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_124) | v2_struct_0(A_124))), inference(resolution, [status(thm)], [c_66, c_736])).
% 4.77/1.87  tff(c_752, plain, (![A_124]: (v4_orders_2(k3_yellow19(A_124, k2_struct_0('#skF_3'), '#skF_4')) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_124))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_124) | v2_struct_0(A_124))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_744])).
% 4.77/1.87  tff(c_783, plain, (![A_128]: (v4_orders_2(k3_yellow19(A_128, k2_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_struct_0(A_128) | v2_struct_0(A_128))), inference(negUnitSimplification, [status(thm)], [c_507, c_74, c_752])).
% 4.77/1.87  tff(c_790, plain, (v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_12, c_783])).
% 4.77/1.87  tff(c_796, plain, (v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_409, c_790])).
% 4.77/1.87  tff(c_797, plain, (v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_80, c_796])).
% 4.77/1.87  tff(c_72, plain, (v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_258])).
% 4.77/1.87  tff(c_919, plain, (![A_140, B_141, C_142]: (v7_waybel_0(k3_yellow19(A_140, B_141, C_142)) | ~m1_subset_1(C_142, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_141)))) | ~v13_waybel_0(C_142, k3_yellow_1(B_141)) | ~v2_waybel_0(C_142, k3_yellow_1(B_141)) | ~v1_subset_1(C_142, u1_struct_0(k3_yellow_1(B_141))) | v1_xboole_0(C_142) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | v1_xboole_0(B_141) | ~l1_struct_0(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.77/1.87  tff(c_927, plain, (![A_140]: (v7_waybel_0(k3_yellow19(A_140, k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_140))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_140) | v2_struct_0(A_140))), inference(resolution, [status(thm)], [c_66, c_919])).
% 4.77/1.87  tff(c_935, plain, (![A_140]: (v7_waybel_0(k3_yellow19(A_140, k2_struct_0('#skF_3'), '#skF_4')) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_140))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_140) | v2_struct_0(A_140))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_927])).
% 4.77/1.87  tff(c_938, plain, (![A_143]: (v7_waybel_0(k3_yellow19(A_143, k2_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_struct_0(A_143) | v2_struct_0(A_143))), inference(negUnitSimplification, [status(thm)], [c_507, c_74, c_935])).
% 4.77/1.87  tff(c_945, plain, (v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_12, c_938])).
% 4.77/1.87  tff(c_951, plain, (v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_409, c_945])).
% 4.77/1.87  tff(c_952, plain, (v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_80, c_951])).
% 4.77/1.87  tff(c_809, plain, (![A_130, B_131, C_132]: (l1_waybel_0(k3_yellow19(A_130, B_131, C_132), A_130) | ~m1_subset_1(C_132, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_131)))) | ~v13_waybel_0(C_132, k3_yellow_1(B_131)) | ~v2_waybel_0(C_132, k3_yellow_1(B_131)) | v1_xboole_0(C_132) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | v1_xboole_0(B_131) | ~l1_struct_0(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.77/1.87  tff(c_817, plain, (![A_130]: (l1_waybel_0(k3_yellow19(A_130, k2_struct_0('#skF_3'), '#skF_4'), A_130) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_130))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_130) | v2_struct_0(A_130))), inference(resolution, [status(thm)], [c_66, c_809])).
% 4.77/1.87  tff(c_825, plain, (![A_130]: (l1_waybel_0(k3_yellow19(A_130, k2_struct_0('#skF_3'), '#skF_4'), A_130) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_130))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_130) | v2_struct_0(A_130))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_817])).
% 4.77/1.87  tff(c_828, plain, (![A_133]: (l1_waybel_0(k3_yellow19(A_133, k2_struct_0('#skF_3'), '#skF_4'), A_133) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_struct_0(A_133) | v2_struct_0(A_133))), inference(negUnitSimplification, [status(thm)], [c_507, c_74, c_825])).
% 4.77/1.87  tff(c_833, plain, (l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_12, c_828])).
% 4.77/1.87  tff(c_839, plain, (l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_409, c_833])).
% 4.77/1.87  tff(c_840, plain, (l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_80, c_839])).
% 4.77/1.87  tff(c_954, plain, (![A_144, B_145]: (k2_yellow19(A_144, k3_yellow19(A_144, k2_struct_0(A_144), B_145))=B_145 | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_144))))) | ~v13_waybel_0(B_145, k3_yellow_1(k2_struct_0(A_144))) | ~v2_waybel_0(B_145, k3_yellow_1(k2_struct_0(A_144))) | ~v1_subset_1(B_145, u1_struct_0(k3_yellow_1(k2_struct_0(A_144)))) | v1_xboole_0(B_145) | ~l1_struct_0(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_231])).
% 4.77/1.87  tff(c_962, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))='#skF_4' | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) | v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_954])).
% 4.77/1.87  tff(c_970, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))='#skF_4' | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_409, c_72, c_70, c_68, c_962])).
% 4.77/1.87  tff(c_971, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_970])).
% 4.77/1.87  tff(c_60, plain, (![A_34, B_38, C_40]: (r1_waybel_7(A_34, k2_yellow19(A_34, B_38), C_40) | ~r3_waybel_9(A_34, B_38, C_40) | ~m1_subset_1(C_40, u1_struct_0(A_34)) | ~l1_waybel_0(B_38, A_34) | ~v7_waybel_0(B_38) | ~v4_orders_2(B_38) | v2_struct_0(B_38) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_212])).
% 4.77/1.87  tff(c_976, plain, (![C_40]: (r1_waybel_7('#skF_3', '#skF_4', C_40) | ~r3_waybel_9('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), C_40) | ~m1_subset_1(C_40, u1_struct_0('#skF_3')) | ~l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_971, c_60])).
% 4.77/1.87  tff(c_983, plain, (![C_40]: (r1_waybel_7('#skF_3', '#skF_4', C_40) | ~r3_waybel_9('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), C_40) | ~m1_subset_1(C_40, k2_struct_0('#skF_3')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_797, c_952, c_840, c_408, c_976])).
% 4.77/1.87  tff(c_984, plain, (![C_40]: (r1_waybel_7('#skF_3', '#skF_4', C_40) | ~r3_waybel_9('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), C_40) | ~m1_subset_1(C_40, k2_struct_0('#skF_3')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_80, c_983])).
% 4.77/1.87  tff(c_1131, plain, (v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_984])).
% 4.77/1.87  tff(c_50, plain, (![A_28, B_29, C_30]: (~v2_struct_0(k3_yellow19(A_28, B_29, C_30)) | ~m1_subset_1(C_30, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_29)))) | ~v13_waybel_0(C_30, k3_yellow_1(B_29)) | ~v2_waybel_0(C_30, k3_yellow_1(B_29)) | v1_xboole_0(C_30) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | v1_xboole_0(B_29) | ~l1_struct_0(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.77/1.87  tff(c_1134, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1131, c_50])).
% 4.77/1.87  tff(c_1137, plain, (v1_xboole_0('#skF_4') | v1_xboole_0(k2_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_409, c_89, c_408, c_70, c_68, c_66, c_1134])).
% 4.77/1.87  tff(c_1139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_507, c_74, c_1137])).
% 4.77/1.87  tff(c_1141, plain, (~v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(splitRight, [status(thm)], [c_984])).
% 4.77/1.87  tff(c_58, plain, (![A_34, B_38, C_40]: (r3_waybel_9(A_34, B_38, C_40) | ~r1_waybel_7(A_34, k2_yellow19(A_34, B_38), C_40) | ~m1_subset_1(C_40, u1_struct_0(A_34)) | ~l1_waybel_0(B_38, A_34) | ~v7_waybel_0(B_38) | ~v4_orders_2(B_38) | v2_struct_0(B_38) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_212])).
% 4.77/1.87  tff(c_979, plain, (![C_40]: (r3_waybel_9('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), C_40) | ~r1_waybel_7('#skF_3', '#skF_4', C_40) | ~m1_subset_1(C_40, u1_struct_0('#skF_3')) | ~l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_971, c_58])).
% 4.77/1.87  tff(c_986, plain, (![C_40]: (r3_waybel_9('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), C_40) | ~r1_waybel_7('#skF_3', '#skF_4', C_40) | ~m1_subset_1(C_40, k2_struct_0('#skF_3')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_797, c_952, c_840, c_408, c_979])).
% 4.77/1.87  tff(c_987, plain, (![C_40]: (r3_waybel_9('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), C_40) | ~r1_waybel_7('#skF_3', '#skF_4', C_40) | ~m1_subset_1(C_40, k2_struct_0('#skF_3')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_80, c_986])).
% 4.77/1.87  tff(c_1144, plain, (![C_152]: (r3_waybel_9('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), C_152) | ~r1_waybel_7('#skF_3', '#skF_4', C_152) | ~m1_subset_1(C_152, k2_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_1141, c_987])).
% 4.77/1.87  tff(c_82, plain, (~r1_waybel_7('#skF_3', '#skF_4', '#skF_5') | ~r3_waybel_9('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_258])).
% 4.77/1.87  tff(c_144, plain, (~r3_waybel_9('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_82])).
% 4.77/1.87  tff(c_1150, plain, (~r1_waybel_7('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1144, c_144])).
% 4.77/1.87  tff(c_1155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_410, c_129, c_1150])).
% 4.77/1.87  tff(c_1156, plain, (v1_xboole_0('#skF_2'('#skF_3'))), inference(splitRight, [status(thm)], [c_494])).
% 4.77/1.87  tff(c_20, plain, (![A_13]: (~v1_xboole_0('#skF_2'(A_13)) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.77/1.87  tff(c_1160, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1156, c_20])).
% 4.77/1.87  tff(c_1163, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1160])).
% 4.77/1.87  tff(c_1165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_1163])).
% 4.77/1.87  tff(c_1167, plain, (~r1_waybel_7('#skF_3', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_88])).
% 4.77/1.87  tff(c_1190, plain, (![A_161, B_162]: (k2_pre_topc(A_161, B_162)=B_162 | ~v4_pre_topc(B_162, A_161) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_161))) | ~l1_pre_topc(A_161))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.77/1.87  tff(c_1209, plain, (![A_164]: (k2_pre_topc(A_164, k2_struct_0(A_164))=k2_struct_0(A_164) | ~v4_pre_topc(k2_struct_0(A_164), A_164) | ~l1_pre_topc(A_164) | ~l1_struct_0(A_164))), inference(resolution, [status(thm)], [c_12, c_1190])).
% 4.77/1.87  tff(c_1213, plain, (![A_12]: (k2_pre_topc(A_12, k2_struct_0(A_12))=k2_struct_0(A_12) | ~l1_struct_0(A_12) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12))), inference(resolution, [status(thm)], [c_16, c_1209])).
% 4.77/1.87  tff(c_1214, plain, (![B_165, A_166]: (v1_tops_1(B_165, A_166) | k2_pre_topc(A_166, B_165)!=k2_struct_0(A_166) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.77/1.87  tff(c_1229, plain, (![A_10]: (v1_tops_1(k2_struct_0(A_10), A_10) | k2_pre_topc(A_10, k2_struct_0(A_10))!=k2_struct_0(A_10) | ~l1_pre_topc(A_10) | ~l1_struct_0(A_10))), inference(resolution, [status(thm)], [c_12, c_1214])).
% 4.77/1.87  tff(c_1264, plain, (![A_174, B_175]: (k2_pre_topc(A_174, B_175)=u1_struct_0(A_174) | ~v1_tops_1(B_175, A_174) | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_pre_topc(A_174))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.77/1.87  tff(c_1327, plain, (![A_181]: (k2_pre_topc(A_181, k2_struct_0(A_181))=u1_struct_0(A_181) | ~v1_tops_1(k2_struct_0(A_181), A_181) | ~l1_pre_topc(A_181) | ~l1_struct_0(A_181))), inference(resolution, [status(thm)], [c_12, c_1264])).
% 4.77/1.87  tff(c_1401, plain, (![A_199]: (k2_pre_topc(A_199, k2_struct_0(A_199))=u1_struct_0(A_199) | k2_pre_topc(A_199, k2_struct_0(A_199))!=k2_struct_0(A_199) | ~l1_pre_topc(A_199) | ~l1_struct_0(A_199))), inference(resolution, [status(thm)], [c_1229, c_1327])).
% 4.77/1.87  tff(c_1406, plain, (![A_200]: (k2_pre_topc(A_200, k2_struct_0(A_200))=u1_struct_0(A_200) | ~l1_struct_0(A_200) | ~l1_pre_topc(A_200) | ~v2_pre_topc(A_200))), inference(superposition, [status(thm), theory('equality')], [c_1213, c_1401])).
% 4.77/1.87  tff(c_1433, plain, (![A_205]: (u1_struct_0(A_205)=k2_struct_0(A_205) | ~l1_struct_0(A_205) | ~l1_pre_topc(A_205) | ~v2_pre_topc(A_205) | ~l1_struct_0(A_205) | ~l1_pre_topc(A_205) | ~v2_pre_topc(A_205))), inference(superposition, [status(thm), theory('equality')], [c_1213, c_1406])).
% 4.77/1.87  tff(c_1435, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3') | ~l1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1433])).
% 4.77/1.87  tff(c_1438, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1435])).
% 4.77/1.87  tff(c_1439, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1438])).
% 4.77/1.87  tff(c_1442, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_1439])).
% 4.77/1.87  tff(c_1446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_1442])).
% 4.77/1.87  tff(c_1447, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1438])).
% 4.77/1.87  tff(c_1449, plain, (m1_subset_1('#skF_5', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1447, c_64])).
% 4.77/1.87  tff(c_1166, plain, (r3_waybel_9('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_88])).
% 4.77/1.87  tff(c_1177, plain, (![A_157]: (m1_subset_1('#skF_2'(A_157), k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.77/1.87  tff(c_1183, plain, (![A_158, A_159]: (~v1_xboole_0(u1_struct_0(A_158)) | ~r2_hidden(A_159, '#skF_2'(A_158)) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158))), inference(resolution, [status(thm)], [c_1177, c_10])).
% 4.77/1.87  tff(c_1188, plain, (![A_158]: (~v1_xboole_0(u1_struct_0(A_158)) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158) | v1_xboole_0('#skF_2'(A_158)))), inference(resolution, [status(thm)], [c_4, c_1183])).
% 4.77/1.87  tff(c_1495, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0('#skF_2'('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1447, c_1188])).
% 4.77/1.87  tff(c_1536, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | v2_struct_0('#skF_3') | v1_xboole_0('#skF_2'('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1495])).
% 4.77/1.87  tff(c_1537, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | v1_xboole_0('#skF_2'('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_80, c_1536])).
% 4.77/1.87  tff(c_1546, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1537])).
% 4.77/1.87  tff(c_1448, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1438])).
% 4.77/1.87  tff(c_1940, plain, (![A_230, B_231, C_232]: (v7_waybel_0(k3_yellow19(A_230, B_231, C_232)) | ~m1_subset_1(C_232, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_231)))) | ~v13_waybel_0(C_232, k3_yellow_1(B_231)) | ~v2_waybel_0(C_232, k3_yellow_1(B_231)) | ~v1_subset_1(C_232, u1_struct_0(k3_yellow_1(B_231))) | v1_xboole_0(C_232) | ~m1_subset_1(B_231, k1_zfmisc_1(u1_struct_0(A_230))) | v1_xboole_0(B_231) | ~l1_struct_0(A_230) | v2_struct_0(A_230))), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.77/1.87  tff(c_1948, plain, (![A_230]: (v7_waybel_0(k3_yellow19(A_230, k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_230))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_230) | v2_struct_0(A_230))), inference(resolution, [status(thm)], [c_66, c_1940])).
% 4.77/1.87  tff(c_1956, plain, (![A_230]: (v7_waybel_0(k3_yellow19(A_230, k2_struct_0('#skF_3'), '#skF_4')) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_230))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_230) | v2_struct_0(A_230))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1948])).
% 4.77/1.87  tff(c_1959, plain, (![A_233]: (v7_waybel_0(k3_yellow19(A_233, k2_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_233))) | ~l1_struct_0(A_233) | v2_struct_0(A_233))), inference(negUnitSimplification, [status(thm)], [c_1546, c_74, c_1956])).
% 4.77/1.87  tff(c_1966, plain, (v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_12, c_1959])).
% 4.77/1.87  tff(c_1972, plain, (v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_1966])).
% 4.77/1.87  tff(c_1973, plain, (v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_80, c_1972])).
% 4.77/1.87  tff(c_1709, plain, (![A_214, B_215, C_216]: (l1_waybel_0(k3_yellow19(A_214, B_215, C_216), A_214) | ~m1_subset_1(C_216, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_215)))) | ~v13_waybel_0(C_216, k3_yellow_1(B_215)) | ~v2_waybel_0(C_216, k3_yellow_1(B_215)) | v1_xboole_0(C_216) | ~m1_subset_1(B_215, k1_zfmisc_1(u1_struct_0(A_214))) | v1_xboole_0(B_215) | ~l1_struct_0(A_214) | v2_struct_0(A_214))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.77/1.87  tff(c_1717, plain, (![A_214]: (l1_waybel_0(k3_yellow19(A_214, k2_struct_0('#skF_3'), '#skF_4'), A_214) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_214))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_214) | v2_struct_0(A_214))), inference(resolution, [status(thm)], [c_66, c_1709])).
% 4.77/1.87  tff(c_1725, plain, (![A_214]: (l1_waybel_0(k3_yellow19(A_214, k2_struct_0('#skF_3'), '#skF_4'), A_214) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_214))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_214) | v2_struct_0(A_214))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1717])).
% 4.77/1.87  tff(c_1912, plain, (![A_228]: (l1_waybel_0(k3_yellow19(A_228, k2_struct_0('#skF_3'), '#skF_4'), A_228) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_228))) | ~l1_struct_0(A_228) | v2_struct_0(A_228))), inference(negUnitSimplification, [status(thm)], [c_1546, c_74, c_1725])).
% 4.77/1.87  tff(c_1917, plain, (l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_12, c_1912])).
% 4.77/1.87  tff(c_1923, plain, (l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_1917])).
% 4.77/1.87  tff(c_1924, plain, (l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_80, c_1923])).
% 4.77/1.87  tff(c_1658, plain, (![A_210, B_211, C_212]: (v4_orders_2(k3_yellow19(A_210, B_211, C_212)) | ~m1_subset_1(C_212, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_211)))) | ~v13_waybel_0(C_212, k3_yellow_1(B_211)) | ~v2_waybel_0(C_212, k3_yellow_1(B_211)) | v1_xboole_0(C_212) | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0(A_210))) | v1_xboole_0(B_211) | ~l1_struct_0(A_210) | v2_struct_0(A_210))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.77/1.87  tff(c_1666, plain, (![A_210]: (v4_orders_2(k3_yellow19(A_210, k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_210))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_210) | v2_struct_0(A_210))), inference(resolution, [status(thm)], [c_66, c_1658])).
% 4.77/1.87  tff(c_1674, plain, (![A_210]: (v4_orders_2(k3_yellow19(A_210, k2_struct_0('#skF_3'), '#skF_4')) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_210))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_210) | v2_struct_0(A_210))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1666])).
% 4.77/1.87  tff(c_1861, plain, (![A_225]: (v4_orders_2(k3_yellow19(A_225, k2_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_225))) | ~l1_struct_0(A_225) | v2_struct_0(A_225))), inference(negUnitSimplification, [status(thm)], [c_1546, c_74, c_1674])).
% 4.77/1.87  tff(c_1868, plain, (v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_12, c_1861])).
% 4.77/1.87  tff(c_1874, plain, (v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_1868])).
% 4.77/1.87  tff(c_1875, plain, (v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_80, c_1874])).
% 4.77/1.87  tff(c_1876, plain, (![A_226, B_227]: (k2_yellow19(A_226, k3_yellow19(A_226, k2_struct_0(A_226), B_227))=B_227 | ~m1_subset_1(B_227, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_226))))) | ~v13_waybel_0(B_227, k3_yellow_1(k2_struct_0(A_226))) | ~v2_waybel_0(B_227, k3_yellow_1(k2_struct_0(A_226))) | ~v1_subset_1(B_227, u1_struct_0(k3_yellow_1(k2_struct_0(A_226)))) | v1_xboole_0(B_227) | ~l1_struct_0(A_226) | v2_struct_0(A_226))), inference(cnfTransformation, [status(thm)], [f_231])).
% 4.77/1.87  tff(c_1884, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))='#skF_4' | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) | v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1876])).
% 4.77/1.87  tff(c_1892, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))='#skF_4' | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_72, c_70, c_68, c_1884])).
% 4.77/1.87  tff(c_1893, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_1892])).
% 4.77/1.87  tff(c_1899, plain, (![C_40]: (r3_waybel_9('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), C_40) | ~r1_waybel_7('#skF_3', '#skF_4', C_40) | ~m1_subset_1(C_40, u1_struct_0('#skF_3')) | ~l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1893, c_58])).
% 4.77/1.87  tff(c_1906, plain, (![C_40]: (r3_waybel_9('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), C_40) | ~r1_waybel_7('#skF_3', '#skF_4', C_40) | ~m1_subset_1(C_40, k2_struct_0('#skF_3')) | ~l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1875, c_1447, c_1899])).
% 4.77/1.87  tff(c_1907, plain, (![C_40]: (r3_waybel_9('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), C_40) | ~r1_waybel_7('#skF_3', '#skF_4', C_40) | ~m1_subset_1(C_40, k2_struct_0('#skF_3')) | ~l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_80, c_1906])).
% 4.77/1.87  tff(c_1976, plain, (![C_40]: (r3_waybel_9('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), C_40) | ~r1_waybel_7('#skF_3', '#skF_4', C_40) | ~m1_subset_1(C_40, k2_struct_0('#skF_3')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1973, c_1924, c_1907])).
% 4.77/1.87  tff(c_1977, plain, (v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_1976])).
% 4.77/1.87  tff(c_1979, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1977, c_50])).
% 4.77/1.87  tff(c_1982, plain, (v1_xboole_0('#skF_4') | v1_xboole_0(k2_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_89, c_1447, c_70, c_68, c_66, c_1979])).
% 4.77/1.87  tff(c_1984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_1546, c_74, c_1982])).
% 4.77/1.87  tff(c_1986, plain, (~v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(splitRight, [status(thm)], [c_1976])).
% 4.77/1.87  tff(c_1902, plain, (![C_40]: (r1_waybel_7('#skF_3', '#skF_4', C_40) | ~r3_waybel_9('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), C_40) | ~m1_subset_1(C_40, u1_struct_0('#skF_3')) | ~l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1893, c_60])).
% 4.77/1.87  tff(c_1909, plain, (![C_40]: (r1_waybel_7('#skF_3', '#skF_4', C_40) | ~r3_waybel_9('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), C_40) | ~m1_subset_1(C_40, k2_struct_0('#skF_3')) | ~l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1875, c_1447, c_1902])).
% 4.77/1.87  tff(c_1910, plain, (![C_40]: (r1_waybel_7('#skF_3', '#skF_4', C_40) | ~r3_waybel_9('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), C_40) | ~m1_subset_1(C_40, k2_struct_0('#skF_3')) | ~l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_80, c_1909])).
% 4.77/1.87  tff(c_2132, plain, (![C_40]: (r1_waybel_7('#skF_3', '#skF_4', C_40) | ~r3_waybel_9('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), C_40) | ~m1_subset_1(C_40, k2_struct_0('#skF_3')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1973, c_1924, c_1910])).
% 4.77/1.87  tff(c_2134, plain, (![C_242]: (r1_waybel_7('#skF_3', '#skF_4', C_242) | ~r3_waybel_9('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), C_242) | ~m1_subset_1(C_242, k2_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_1986, c_2132])).
% 4.77/1.87  tff(c_2140, plain, (r1_waybel_7('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1166, c_2134])).
% 4.77/1.87  tff(c_2144, plain, (r1_waybel_7('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1449, c_2140])).
% 4.77/1.87  tff(c_2146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1167, c_2144])).
% 4.77/1.87  tff(c_2147, plain, (v1_xboole_0('#skF_2'('#skF_3'))), inference(splitRight, [status(thm)], [c_1537])).
% 4.77/1.87  tff(c_2151, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2147, c_20])).
% 4.77/1.87  tff(c_2154, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_2151])).
% 4.77/1.87  tff(c_2156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_2154])).
% 4.77/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.87  
% 4.77/1.87  Inference rules
% 4.77/1.87  ----------------------
% 4.77/1.87  #Ref     : 0
% 4.77/1.87  #Sup     : 399
% 4.77/1.87  #Fact    : 0
% 4.77/1.87  #Define  : 0
% 4.77/1.87  #Split   : 18
% 4.77/1.87  #Chain   : 0
% 4.77/1.87  #Close   : 0
% 4.77/1.87  
% 4.77/1.87  Ordering : KBO
% 4.77/1.87  
% 4.77/1.87  Simplification rules
% 4.77/1.87  ----------------------
% 4.77/1.87  #Subsume      : 68
% 4.77/1.87  #Demod        : 435
% 4.77/1.87  #Tautology    : 139
% 4.77/1.87  #SimpNegUnit  : 82
% 4.77/1.87  #BackRed      : 2
% 4.77/1.87  
% 4.77/1.87  #Partial instantiations: 0
% 4.77/1.87  #Strategies tried      : 1
% 4.77/1.87  
% 4.77/1.87  Timing (in seconds)
% 4.77/1.87  ----------------------
% 4.77/1.87  Preprocessing        : 0.39
% 4.77/1.87  Parsing              : 0.21
% 4.77/1.87  CNF conversion       : 0.03
% 4.77/1.87  Main loop            : 0.68
% 4.77/1.87  Inferencing          : 0.25
% 4.77/1.87  Reduction            : 0.23
% 4.77/1.87  Demodulation         : 0.16
% 4.77/1.87  BG Simplification    : 0.04
% 4.77/1.87  Subsumption          : 0.11
% 4.77/1.87  Abstraction          : 0.03
% 4.77/1.87  MUC search           : 0.00
% 4.77/1.87  Cooper               : 0.00
% 4.77/1.87  Total                : 1.14
% 4.77/1.87  Index Insertion      : 0.00
% 4.77/1.87  Index Deletion       : 0.00
% 4.77/1.87  Index Matching       : 0.00
% 4.77/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
