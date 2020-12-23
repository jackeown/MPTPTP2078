%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2074+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:51 EST 2020

% Result     : Theorem 7.53s
% Output     : CNFRefutation 8.27s
% Verified   : 
% Statistics : Number of formulae       :  234 (6114 expanded)
%              Number of leaves         :   50 (1993 expanded)
%              Depth                    :   34
%              Number of atoms          :  890 (27493 expanded)
%              Number of equality atoms :    7 (1032 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_compts_1 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > #nlpp > u1_struct_0 > k6_yellow_6 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_waybel_0,type,(
    v6_waybel_0: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k6_yellow_6,type,(
    k6_yellow_6: $i > $i )).

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

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_323,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ( v1_compts_1(A)
        <=> ! [B] :
              ( ( ~ v1_xboole_0(B)
                & v1_subset_1(B,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
                & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
                & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
                & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
             => ? [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                  & r1_waybel_7(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_yellow19)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_28,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_92,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_233,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & l1_waybel_0(B,A) )
           => ~ ( r2_hidden(B,k6_yellow_6(A))
                & ! [C] :
                    ( m1_subset_1(C,u1_struct_0(A))
                   => ~ r3_waybel_9(A,B,C) ) ) )
       => v1_compts_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_yellow19)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A) )
     => ( ~ v1_xboole_0(k2_yellow19(A,B))
        & v13_waybel_0(k2_yellow19(A,B),k3_yellow_1(k2_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_yellow19)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => ( v1_subset_1(k2_yellow19(A,B),u1_struct_0(k3_yellow_1(k2_struct_0(A))))
        & v2_waybel_0(k2_yellow19(A,B),k3_yellow_1(k2_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_yellow19)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A) )
     => m1_subset_1(k2_yellow19(A,B),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow19)).

tff(f_257,axiom,(
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

tff(f_32,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_153,axiom,(
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

tff(f_181,axiom,(
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

tff(f_70,axiom,(
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

tff(f_205,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_compts_1(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & l1_waybel_0(B,A) )
           => ? [C] :
                ( m1_subset_1(C,u1_struct_0(A))
                & r3_waybel_9(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l37_yellow19)).

tff(f_283,axiom,(
    ! [A] :
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

tff(c_78,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_74,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_14,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_631,plain,(
    ! [A_169] :
      ( u1_struct_0(A_169) = k2_struct_0(A_169)
      | ~ l1_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_636,plain,(
    ! [A_170] :
      ( u1_struct_0(A_170) = k2_struct_0(A_170)
      | ~ l1_pre_topc(A_170) ) ),
    inference(resolution,[status(thm)],[c_14,c_631])).

tff(c_644,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_636])).

tff(c_660,plain,(
    ! [A_172] :
      ( ~ v1_xboole_0(u1_struct_0(A_172))
      | ~ l1_struct_0(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_663,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_660])).

tff(c_667,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_663])).

tff(c_668,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_667])).

tff(c_671,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_668])).

tff(c_675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_671])).

tff(c_676,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_667])).

tff(c_90,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_compts_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_121,plain,(
    ~ v1_compts_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_76,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_56,plain,(
    ! [A_29] :
      ( v7_waybel_0('#skF_4'(A_29))
      | v1_compts_1(A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_58,plain,(
    ! [A_29] :
      ( v4_orders_2('#skF_4'(A_29))
      | v1_compts_1(A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_54,plain,(
    ! [A_29] :
      ( l1_waybel_0('#skF_4'(A_29),A_29)
      | v1_compts_1(A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_124,plain,(
    ! [A_66] :
      ( u1_struct_0(A_66) = k2_struct_0(A_66)
      | ~ l1_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_129,plain,(
    ! [A_67] :
      ( u1_struct_0(A_67) = k2_struct_0(A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_14,c_124])).

tff(c_137,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_129])).

tff(c_153,plain,(
    ! [A_69] :
      ( ~ v1_xboole_0(u1_struct_0(A_69))
      | ~ l1_struct_0(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_156,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_153])).

tff(c_160,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_156])).

tff(c_161,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_164,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_161])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_164])).

tff(c_170,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( v13_waybel_0(k2_yellow19(A_13,B_14),k3_yellow_1(k2_struct_0(A_13)))
      | ~ l1_waybel_0(B_14,A_13)
      | v2_struct_0(B_14)
      | ~ l1_struct_0(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_28,plain,(
    ! [A_15,B_16] :
      ( v2_waybel_0(k2_yellow19(A_15,B_16),k3_yellow_1(k2_struct_0(A_15)))
      | ~ l1_waybel_0(B_16,A_15)
      | ~ v7_waybel_0(B_16)
      | ~ v4_orders_2(B_16)
      | v2_struct_0(B_16)
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( v1_subset_1(k2_yellow19(A_15,B_16),u1_struct_0(k3_yellow_1(k2_struct_0(A_15))))
      | ~ l1_waybel_0(B_16,A_15)
      | ~ v7_waybel_0(B_16)
      | ~ v4_orders_2(B_16)
      | v2_struct_0(B_16)
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k2_yellow19(A_3,B_4),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_3)))))
      | ~ l1_waybel_0(B_4,A_3)
      | v2_struct_0(B_4)
      | ~ l1_struct_0(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_120,plain,(
    ! [B_62] :
      ( v1_compts_1('#skF_5')
      | m1_subset_1('#skF_7'(B_62),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v13_waybel_0(B_62,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(B_62,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1(B_62,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_318,plain,(
    ! [B_62] :
      ( v1_compts_1('#skF_5')
      | m1_subset_1('#skF_7'(B_62),k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v13_waybel_0(B_62,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(B_62,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1(B_62,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0(B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_120])).

tff(c_320,plain,(
    ! [B_117] :
      ( m1_subset_1('#skF_7'(B_117),k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v13_waybel_0(B_117,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(B_117,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1(B_117,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0(B_117) ) ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_318])).

tff(c_324,plain,(
    ! [B_4] :
      ( m1_subset_1('#skF_7'(k2_yellow19('#skF_5',B_4)),k2_struct_0('#skF_5'))
      | ~ v13_waybel_0(k2_yellow19('#skF_5',B_4),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(k2_yellow19('#skF_5',B_4),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1(k2_yellow19('#skF_5',B_4),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0(k2_yellow19('#skF_5',B_4))
      | ~ l1_waybel_0(B_4,'#skF_5')
      | v2_struct_0(B_4)
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6,c_320])).

tff(c_335,plain,(
    ! [B_4] :
      ( m1_subset_1('#skF_7'(k2_yellow19('#skF_5',B_4)),k2_struct_0('#skF_5'))
      | ~ v13_waybel_0(k2_yellow19('#skF_5',B_4),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(k2_yellow19('#skF_5',B_4),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1(k2_yellow19('#skF_5',B_4),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0(k2_yellow19('#skF_5',B_4))
      | ~ l1_waybel_0(B_4,'#skF_5')
      | v2_struct_0(B_4)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_324])).

tff(c_410,plain,(
    ! [B_144] :
      ( m1_subset_1('#skF_7'(k2_yellow19('#skF_5',B_144)),k2_struct_0('#skF_5'))
      | ~ v13_waybel_0(k2_yellow19('#skF_5',B_144),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(k2_yellow19('#skF_5',B_144),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1(k2_yellow19('#skF_5',B_144),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0(k2_yellow19('#skF_5',B_144))
      | ~ l1_waybel_0(B_144,'#skF_5')
      | v2_struct_0(B_144) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_335])).

tff(c_414,plain,(
    ! [B_16] :
      ( m1_subset_1('#skF_7'(k2_yellow19('#skF_5',B_16)),k2_struct_0('#skF_5'))
      | ~ v13_waybel_0(k2_yellow19('#skF_5',B_16),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(k2_yellow19('#skF_5',B_16),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0(k2_yellow19('#skF_5',B_16))
      | ~ l1_waybel_0(B_16,'#skF_5')
      | ~ v7_waybel_0(B_16)
      | ~ v4_orders_2(B_16)
      | v2_struct_0(B_16)
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_410])).

tff(c_417,plain,(
    ! [B_16] :
      ( m1_subset_1('#skF_7'(k2_yellow19('#skF_5',B_16)),k2_struct_0('#skF_5'))
      | ~ v13_waybel_0(k2_yellow19('#skF_5',B_16),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(k2_yellow19('#skF_5',B_16),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0(k2_yellow19('#skF_5',B_16))
      | ~ l1_waybel_0(B_16,'#skF_5')
      | ~ v7_waybel_0(B_16)
      | ~ v4_orders_2(B_16)
      | v2_struct_0(B_16)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_414])).

tff(c_431,plain,(
    ! [B_148] :
      ( m1_subset_1('#skF_7'(k2_yellow19('#skF_5',B_148)),k2_struct_0('#skF_5'))
      | ~ v13_waybel_0(k2_yellow19('#skF_5',B_148),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(k2_yellow19('#skF_5',B_148),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0(k2_yellow19('#skF_5',B_148))
      | ~ l1_waybel_0(B_148,'#skF_5')
      | ~ v7_waybel_0(B_148)
      | ~ v4_orders_2(B_148)
      | v2_struct_0(B_148) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_417])).

tff(c_435,plain,(
    ! [B_16] :
      ( m1_subset_1('#skF_7'(k2_yellow19('#skF_5',B_16)),k2_struct_0('#skF_5'))
      | ~ v13_waybel_0(k2_yellow19('#skF_5',B_16),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0(k2_yellow19('#skF_5',B_16))
      | ~ l1_waybel_0(B_16,'#skF_5')
      | ~ v7_waybel_0(B_16)
      | ~ v4_orders_2(B_16)
      | v2_struct_0(B_16)
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_431])).

tff(c_438,plain,(
    ! [B_16] :
      ( m1_subset_1('#skF_7'(k2_yellow19('#skF_5',B_16)),k2_struct_0('#skF_5'))
      | ~ v13_waybel_0(k2_yellow19('#skF_5',B_16),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0(k2_yellow19('#skF_5',B_16))
      | ~ l1_waybel_0(B_16,'#skF_5')
      | ~ v7_waybel_0(B_16)
      | ~ v4_orders_2(B_16)
      | v2_struct_0(B_16)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_435])).

tff(c_440,plain,(
    ! [B_149] :
      ( m1_subset_1('#skF_7'(k2_yellow19('#skF_5',B_149)),k2_struct_0('#skF_5'))
      | ~ v13_waybel_0(k2_yellow19('#skF_5',B_149),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0(k2_yellow19('#skF_5',B_149))
      | ~ l1_waybel_0(B_149,'#skF_5')
      | ~ v7_waybel_0(B_149)
      | ~ v4_orders_2(B_149)
      | v2_struct_0(B_149) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_438])).

tff(c_444,plain,(
    ! [B_14] :
      ( m1_subset_1('#skF_7'(k2_yellow19('#skF_5',B_14)),k2_struct_0('#skF_5'))
      | v1_xboole_0(k2_yellow19('#skF_5',B_14))
      | ~ v7_waybel_0(B_14)
      | ~ v4_orders_2(B_14)
      | ~ l1_waybel_0(B_14,'#skF_5')
      | v2_struct_0(B_14)
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_440])).

tff(c_447,plain,(
    ! [B_14] :
      ( m1_subset_1('#skF_7'(k2_yellow19('#skF_5',B_14)),k2_struct_0('#skF_5'))
      | v1_xboole_0(k2_yellow19('#skF_5',B_14))
      | ~ v7_waybel_0(B_14)
      | ~ v4_orders_2(B_14)
      | ~ l1_waybel_0(B_14,'#skF_5')
      | v2_struct_0(B_14)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_444])).

tff(c_448,plain,(
    ! [B_14] :
      ( m1_subset_1('#skF_7'(k2_yellow19('#skF_5',B_14)),k2_struct_0('#skF_5'))
      | v1_xboole_0(k2_yellow19('#skF_5',B_14))
      | ~ v7_waybel_0(B_14)
      | ~ v4_orders_2(B_14)
      | ~ l1_waybel_0(B_14,'#skF_5')
      | v2_struct_0(B_14) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_447])).

tff(c_106,plain,(
    ! [B_62] :
      ( v1_compts_1('#skF_5')
      | r1_waybel_7('#skF_5',B_62,'#skF_7'(B_62))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v13_waybel_0(B_62,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(B_62,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1(B_62,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_290,plain,(
    ! [B_108] :
      ( r1_waybel_7('#skF_5',B_108,'#skF_7'(B_108))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v13_waybel_0(B_108,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(B_108,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1(B_108,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0(B_108) ) ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_106])).

tff(c_293,plain,(
    ! [B_4] :
      ( r1_waybel_7('#skF_5',k2_yellow19('#skF_5',B_4),'#skF_7'(k2_yellow19('#skF_5',B_4)))
      | ~ v13_waybel_0(k2_yellow19('#skF_5',B_4),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(k2_yellow19('#skF_5',B_4),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1(k2_yellow19('#skF_5',B_4),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0(k2_yellow19('#skF_5',B_4))
      | ~ l1_waybel_0(B_4,'#skF_5')
      | v2_struct_0(B_4)
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6,c_290])).

tff(c_302,plain,(
    ! [B_4] :
      ( r1_waybel_7('#skF_5',k2_yellow19('#skF_5',B_4),'#skF_7'(k2_yellow19('#skF_5',B_4)))
      | ~ v13_waybel_0(k2_yellow19('#skF_5',B_4),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(k2_yellow19('#skF_5',B_4),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1(k2_yellow19('#skF_5',B_4),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0(k2_yellow19('#skF_5',B_4))
      | ~ l1_waybel_0(B_4,'#skF_5')
      | v2_struct_0(B_4)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_293])).

tff(c_450,plain,(
    ! [B_151] :
      ( r1_waybel_7('#skF_5',k2_yellow19('#skF_5',B_151),'#skF_7'(k2_yellow19('#skF_5',B_151)))
      | ~ v13_waybel_0(k2_yellow19('#skF_5',B_151),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(k2_yellow19('#skF_5',B_151),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1(k2_yellow19('#skF_5',B_151),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0(k2_yellow19('#skF_5',B_151))
      | ~ l1_waybel_0(B_151,'#skF_5')
      | v2_struct_0(B_151) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_302])).

tff(c_453,plain,(
    ! [B_16] :
      ( r1_waybel_7('#skF_5',k2_yellow19('#skF_5',B_16),'#skF_7'(k2_yellow19('#skF_5',B_16)))
      | ~ v13_waybel_0(k2_yellow19('#skF_5',B_16),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(k2_yellow19('#skF_5',B_16),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0(k2_yellow19('#skF_5',B_16))
      | ~ l1_waybel_0(B_16,'#skF_5')
      | ~ v7_waybel_0(B_16)
      | ~ v4_orders_2(B_16)
      | v2_struct_0(B_16)
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_450])).

tff(c_456,plain,(
    ! [B_16] :
      ( r1_waybel_7('#skF_5',k2_yellow19('#skF_5',B_16),'#skF_7'(k2_yellow19('#skF_5',B_16)))
      | ~ v13_waybel_0(k2_yellow19('#skF_5',B_16),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(k2_yellow19('#skF_5',B_16),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0(k2_yellow19('#skF_5',B_16))
      | ~ l1_waybel_0(B_16,'#skF_5')
      | ~ v7_waybel_0(B_16)
      | ~ v4_orders_2(B_16)
      | v2_struct_0(B_16)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_453])).

tff(c_458,plain,(
    ! [B_152] :
      ( r1_waybel_7('#skF_5',k2_yellow19('#skF_5',B_152),'#skF_7'(k2_yellow19('#skF_5',B_152)))
      | ~ v13_waybel_0(k2_yellow19('#skF_5',B_152),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(k2_yellow19('#skF_5',B_152),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0(k2_yellow19('#skF_5',B_152))
      | ~ l1_waybel_0(B_152,'#skF_5')
      | ~ v7_waybel_0(B_152)
      | ~ v4_orders_2(B_152)
      | v2_struct_0(B_152) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_456])).

tff(c_62,plain,(
    ! [A_35,B_39,C_41] :
      ( r3_waybel_9(A_35,B_39,C_41)
      | ~ r1_waybel_7(A_35,k2_yellow19(A_35,B_39),C_41)
      | ~ m1_subset_1(C_41,u1_struct_0(A_35))
      | ~ l1_waybel_0(B_39,A_35)
      | ~ v7_waybel_0(B_39)
      | ~ v4_orders_2(B_39)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_461,plain,(
    ! [B_152] :
      ( r3_waybel_9('#skF_5',B_152,'#skF_7'(k2_yellow19('#skF_5',B_152)))
      | ~ m1_subset_1('#skF_7'(k2_yellow19('#skF_5',B_152)),u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ v13_waybel_0(k2_yellow19('#skF_5',B_152),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(k2_yellow19('#skF_5',B_152),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0(k2_yellow19('#skF_5',B_152))
      | ~ l1_waybel_0(B_152,'#skF_5')
      | ~ v7_waybel_0(B_152)
      | ~ v4_orders_2(B_152)
      | v2_struct_0(B_152) ) ),
    inference(resolution,[status(thm)],[c_458,c_62])).

tff(c_464,plain,(
    ! [B_152] :
      ( r3_waybel_9('#skF_5',B_152,'#skF_7'(k2_yellow19('#skF_5',B_152)))
      | ~ m1_subset_1('#skF_7'(k2_yellow19('#skF_5',B_152)),k2_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ v13_waybel_0(k2_yellow19('#skF_5',B_152),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(k2_yellow19('#skF_5',B_152),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0(k2_yellow19('#skF_5',B_152))
      | ~ l1_waybel_0(B_152,'#skF_5')
      | ~ v7_waybel_0(B_152)
      | ~ v4_orders_2(B_152)
      | v2_struct_0(B_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_137,c_461])).

tff(c_466,plain,(
    ! [B_153] :
      ( r3_waybel_9('#skF_5',B_153,'#skF_7'(k2_yellow19('#skF_5',B_153)))
      | ~ m1_subset_1('#skF_7'(k2_yellow19('#skF_5',B_153)),k2_struct_0('#skF_5'))
      | ~ v13_waybel_0(k2_yellow19('#skF_5',B_153),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(k2_yellow19('#skF_5',B_153),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0(k2_yellow19('#skF_5',B_153))
      | ~ l1_waybel_0(B_153,'#skF_5')
      | ~ v7_waybel_0(B_153)
      | ~ v4_orders_2(B_153)
      | v2_struct_0(B_153) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_464])).

tff(c_469,plain,(
    ! [B_16] :
      ( r3_waybel_9('#skF_5',B_16,'#skF_7'(k2_yellow19('#skF_5',B_16)))
      | ~ m1_subset_1('#skF_7'(k2_yellow19('#skF_5',B_16)),k2_struct_0('#skF_5'))
      | ~ v13_waybel_0(k2_yellow19('#skF_5',B_16),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0(k2_yellow19('#skF_5',B_16))
      | ~ l1_waybel_0(B_16,'#skF_5')
      | ~ v7_waybel_0(B_16)
      | ~ v4_orders_2(B_16)
      | v2_struct_0(B_16)
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_466])).

tff(c_472,plain,(
    ! [B_16] :
      ( r3_waybel_9('#skF_5',B_16,'#skF_7'(k2_yellow19('#skF_5',B_16)))
      | ~ m1_subset_1('#skF_7'(k2_yellow19('#skF_5',B_16)),k2_struct_0('#skF_5'))
      | ~ v13_waybel_0(k2_yellow19('#skF_5',B_16),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0(k2_yellow19('#skF_5',B_16))
      | ~ l1_waybel_0(B_16,'#skF_5')
      | ~ v7_waybel_0(B_16)
      | ~ v4_orders_2(B_16)
      | v2_struct_0(B_16)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_469])).

tff(c_474,plain,(
    ! [B_154] :
      ( r3_waybel_9('#skF_5',B_154,'#skF_7'(k2_yellow19('#skF_5',B_154)))
      | ~ m1_subset_1('#skF_7'(k2_yellow19('#skF_5',B_154)),k2_struct_0('#skF_5'))
      | ~ v13_waybel_0(k2_yellow19('#skF_5',B_154),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0(k2_yellow19('#skF_5',B_154))
      | ~ l1_waybel_0(B_154,'#skF_5')
      | ~ v7_waybel_0(B_154)
      | ~ v4_orders_2(B_154)
      | v2_struct_0(B_154) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_472])).

tff(c_477,plain,(
    ! [B_14] :
      ( r3_waybel_9('#skF_5',B_14,'#skF_7'(k2_yellow19('#skF_5',B_14)))
      | ~ m1_subset_1('#skF_7'(k2_yellow19('#skF_5',B_14)),k2_struct_0('#skF_5'))
      | v1_xboole_0(k2_yellow19('#skF_5',B_14))
      | ~ v7_waybel_0(B_14)
      | ~ v4_orders_2(B_14)
      | ~ l1_waybel_0(B_14,'#skF_5')
      | v2_struct_0(B_14)
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_474])).

tff(c_480,plain,(
    ! [B_14] :
      ( r3_waybel_9('#skF_5',B_14,'#skF_7'(k2_yellow19('#skF_5',B_14)))
      | ~ m1_subset_1('#skF_7'(k2_yellow19('#skF_5',B_14)),k2_struct_0('#skF_5'))
      | v1_xboole_0(k2_yellow19('#skF_5',B_14))
      | ~ v7_waybel_0(B_14)
      | ~ v4_orders_2(B_14)
      | ~ l1_waybel_0(B_14,'#skF_5')
      | v2_struct_0(B_14)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_477])).

tff(c_482,plain,(
    ! [B_155] :
      ( r3_waybel_9('#skF_5',B_155,'#skF_7'(k2_yellow19('#skF_5',B_155)))
      | ~ m1_subset_1('#skF_7'(k2_yellow19('#skF_5',B_155)),k2_struct_0('#skF_5'))
      | v1_xboole_0(k2_yellow19('#skF_5',B_155))
      | ~ v7_waybel_0(B_155)
      | ~ v4_orders_2(B_155)
      | ~ l1_waybel_0(B_155,'#skF_5')
      | v2_struct_0(B_155) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_480])).

tff(c_486,plain,(
    ! [B_156] :
      ( r3_waybel_9('#skF_5',B_156,'#skF_7'(k2_yellow19('#skF_5',B_156)))
      | v1_xboole_0(k2_yellow19('#skF_5',B_156))
      | ~ v7_waybel_0(B_156)
      | ~ v4_orders_2(B_156)
      | ~ l1_waybel_0(B_156,'#skF_5')
      | v2_struct_0(B_156) ) ),
    inference(resolution,[status(thm)],[c_448,c_482])).

tff(c_50,plain,(
    ! [A_29,C_34] :
      ( ~ r3_waybel_9(A_29,'#skF_4'(A_29),C_34)
      | ~ m1_subset_1(C_34,u1_struct_0(A_29))
      | v1_compts_1(A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_490,plain,
    ( ~ m1_subset_1('#skF_7'(k2_yellow19('#skF_5','#skF_4'('#skF_5'))),u1_struct_0('#skF_5'))
    | v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(k2_yellow19('#skF_5','#skF_4'('#skF_5')))
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | ~ v4_orders_2('#skF_4'('#skF_5'))
    | ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_486,c_50])).

tff(c_493,plain,
    ( ~ m1_subset_1('#skF_7'(k2_yellow19('#skF_5','#skF_4'('#skF_5'))),k2_struct_0('#skF_5'))
    | v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(k2_yellow19('#skF_5','#skF_4'('#skF_5')))
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | ~ v4_orders_2('#skF_4'('#skF_5'))
    | ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_137,c_490])).

tff(c_494,plain,
    ( ~ m1_subset_1('#skF_7'(k2_yellow19('#skF_5','#skF_4'('#skF_5'))),k2_struct_0('#skF_5'))
    | v1_xboole_0(k2_yellow19('#skF_5','#skF_4'('#skF_5')))
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | ~ v4_orders_2('#skF_4'('#skF_5'))
    | ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_121,c_493])).

tff(c_507,plain,(
    ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_494])).

tff(c_510,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_507])).

tff(c_513,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_510])).

tff(c_515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_121,c_513])).

tff(c_517,plain,(
    l1_waybel_0('#skF_4'('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_494])).

tff(c_516,plain,
    ( ~ v4_orders_2('#skF_4'('#skF_5'))
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | ~ m1_subset_1('#skF_7'(k2_yellow19('#skF_5','#skF_4'('#skF_5'))),k2_struct_0('#skF_5'))
    | v2_struct_0('#skF_4'('#skF_5'))
    | v1_xboole_0(k2_yellow19('#skF_5','#skF_4'('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_494])).

tff(c_523,plain,(
    ~ m1_subset_1('#skF_7'(k2_yellow19('#skF_5','#skF_4'('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_516])).

tff(c_526,plain,
    ( v1_xboole_0(k2_yellow19('#skF_5','#skF_4'('#skF_5')))
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | ~ v4_orders_2('#skF_4'('#skF_5'))
    | ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_448,c_523])).

tff(c_529,plain,
    ( v1_xboole_0(k2_yellow19('#skF_5','#skF_4'('#skF_5')))
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | ~ v4_orders_2('#skF_4'('#skF_5'))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_526])).

tff(c_530,plain,(
    ~ v4_orders_2('#skF_4'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_529])).

tff(c_533,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_530])).

tff(c_536,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_533])).

tff(c_538,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_121,c_536])).

tff(c_539,plain,
    ( ~ v7_waybel_0('#skF_4'('#skF_5'))
    | v2_struct_0('#skF_4'('#skF_5'))
    | v1_xboole_0(k2_yellow19('#skF_5','#skF_4'('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_529])).

tff(c_542,plain,(
    ~ v7_waybel_0('#skF_4'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_539])).

tff(c_545,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_542])).

tff(c_548,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_545])).

tff(c_550,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_121,c_548])).

tff(c_551,plain,
    ( v1_xboole_0(k2_yellow19('#skF_5','#skF_4'('#skF_5')))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_539])).

tff(c_554,plain,(
    v2_struct_0('#skF_4'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_551])).

tff(c_60,plain,(
    ! [A_29] :
      ( ~ v2_struct_0('#skF_4'(A_29))
      | v1_compts_1(A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_557,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_554,c_60])).

tff(c_560,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_557])).

tff(c_562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_121,c_560])).

tff(c_564,plain,(
    ~ v2_struct_0('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_551])).

tff(c_563,plain,(
    v1_xboole_0(k2_yellow19('#skF_5','#skF_4'('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_551])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( ~ v1_xboole_0(k2_yellow19(A_13,B_14))
      | ~ l1_waybel_0(B_14,A_13)
      | v2_struct_0(B_14)
      | ~ l1_struct_0(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_567,plain,
    ( ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | v2_struct_0('#skF_4'('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_563,c_26])).

tff(c_570,plain,
    ( v2_struct_0('#skF_4'('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_517,c_567])).

tff(c_572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_564,c_570])).

tff(c_573,plain,
    ( ~ v7_waybel_0('#skF_4'('#skF_5'))
    | ~ v4_orders_2('#skF_4'('#skF_5'))
    | v1_xboole_0(k2_yellow19('#skF_5','#skF_4'('#skF_5')))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_516])).

tff(c_576,plain,(
    ~ v4_orders_2('#skF_4'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_573])).

tff(c_579,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_576])).

tff(c_582,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_579])).

tff(c_584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_121,c_582])).

tff(c_585,plain,
    ( ~ v7_waybel_0('#skF_4'('#skF_5'))
    | v2_struct_0('#skF_4'('#skF_5'))
    | v1_xboole_0(k2_yellow19('#skF_5','#skF_4'('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_573])).

tff(c_588,plain,(
    ~ v7_waybel_0('#skF_4'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_585])).

tff(c_591,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_588])).

tff(c_594,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_591])).

tff(c_596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_121,c_594])).

tff(c_597,plain,
    ( v1_xboole_0(k2_yellow19('#skF_5','#skF_4'('#skF_5')))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_585])).

tff(c_599,plain,(
    v2_struct_0('#skF_4'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_597])).

tff(c_603,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_599,c_60])).

tff(c_606,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_603])).

tff(c_608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_121,c_606])).

tff(c_610,plain,(
    ~ v2_struct_0('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_597])).

tff(c_609,plain,(
    v1_xboole_0(k2_yellow19('#skF_5','#skF_4'('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_597])).

tff(c_613,plain,
    ( ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | v2_struct_0('#skF_4'('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_609,c_26])).

tff(c_616,plain,
    ( v2_struct_0('#skF_4'('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_517,c_613])).

tff(c_618,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_610,c_616])).

tff(c_619,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_677,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_667])).

tff(c_708,plain,(
    ! [A_175] :
      ( m1_subset_1(k2_struct_0(A_175),k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_711,plain,
    ( m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_708])).

tff(c_716,plain,(
    m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_711])).

tff(c_620,plain,(
    v1_compts_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_86,plain,
    ( v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v1_compts_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_630,plain,(
    v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_86])).

tff(c_84,plain,
    ( v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v1_compts_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_621,plain,(
    ~ v1_compts_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_621])).

tff(c_624,plain,(
    v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_82,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
    | ~ v1_compts_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_707,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_82])).

tff(c_4,plain,(
    ! [A_2] :
      ( m1_subset_1(k2_struct_0(A_2),k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_871,plain,(
    ! [A_229,B_230,C_231] :
      ( v4_orders_2(k3_yellow19(A_229,B_230,C_231))
      | ~ m1_subset_1(C_231,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_230))))
      | ~ v13_waybel_0(C_231,k3_yellow_1(B_230))
      | ~ v2_waybel_0(C_231,k3_yellow_1(B_230))
      | v1_xboole_0(C_231)
      | ~ m1_subset_1(B_230,k1_zfmisc_1(u1_struct_0(A_229)))
      | v1_xboole_0(B_230)
      | ~ l1_struct_0(A_229)
      | v2_struct_0(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_878,plain,(
    ! [A_229] :
      ( v4_orders_2(k3_yellow19(A_229,k2_struct_0('#skF_5'),'#skF_6'))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_229)))
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | ~ l1_struct_0(A_229)
      | v2_struct_0(A_229) ) ),
    inference(resolution,[status(thm)],[c_707,c_871])).

tff(c_886,plain,(
    ! [A_229] :
      ( v4_orders_2(k3_yellow19(A_229,k2_struct_0('#skF_5'),'#skF_6'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_229)))
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | ~ l1_struct_0(A_229)
      | v2_struct_0(A_229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_624,c_878])).

tff(c_889,plain,(
    ! [A_232] :
      ( v4_orders_2(k3_yellow19(A_232,k2_struct_0('#skF_5'),'#skF_6'))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ l1_struct_0(A_232)
      | v2_struct_0(A_232) ) ),
    inference(negUnitSimplification,[status(thm)],[c_676,c_619,c_886])).

tff(c_893,plain,
    ( v4_orders_2(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_889])).

tff(c_902,plain,
    ( v4_orders_2(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_893])).

tff(c_903,plain,(
    v4_orders_2(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_902])).

tff(c_88,plain,
    ( v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
    | ~ v1_compts_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_684,plain,(
    v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_88])).

tff(c_990,plain,(
    ! [A_241,B_242,C_243] :
      ( v7_waybel_0(k3_yellow19(A_241,B_242,C_243))
      | ~ m1_subset_1(C_243,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_242))))
      | ~ v13_waybel_0(C_243,k3_yellow_1(B_242))
      | ~ v2_waybel_0(C_243,k3_yellow_1(B_242))
      | ~ v1_subset_1(C_243,u1_struct_0(k3_yellow_1(B_242)))
      | v1_xboole_0(C_243)
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_241)))
      | v1_xboole_0(B_242)
      | ~ l1_struct_0(A_241)
      | v2_struct_0(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_997,plain,(
    ! [A_241] :
      ( v7_waybel_0(k3_yellow19(A_241,k2_struct_0('#skF_5'),'#skF_6'))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_241)))
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | ~ l1_struct_0(A_241)
      | v2_struct_0(A_241) ) ),
    inference(resolution,[status(thm)],[c_707,c_990])).

tff(c_1005,plain,(
    ! [A_241] :
      ( v7_waybel_0(k3_yellow19(A_241,k2_struct_0('#skF_5'),'#skF_6'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_241)))
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | ~ l1_struct_0(A_241)
      | v2_struct_0(A_241) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_684,c_630,c_624,c_997])).

tff(c_1008,plain,(
    ! [A_244] :
      ( v7_waybel_0(k3_yellow19(A_244,k2_struct_0('#skF_5'),'#skF_6'))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_244)))
      | ~ l1_struct_0(A_244)
      | v2_struct_0(A_244) ) ),
    inference(negUnitSimplification,[status(thm)],[c_676,c_619,c_1005])).

tff(c_1012,plain,
    ( v7_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_1008])).

tff(c_1021,plain,
    ( v7_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_1012])).

tff(c_1022,plain,(
    v7_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1021])).

tff(c_911,plain,(
    ! [A_233,B_234,C_235] :
      ( l1_waybel_0(k3_yellow19(A_233,B_234,C_235),A_233)
      | ~ m1_subset_1(C_235,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_234))))
      | ~ v13_waybel_0(C_235,k3_yellow_1(B_234))
      | ~ v2_waybel_0(C_235,k3_yellow_1(B_234))
      | v1_xboole_0(C_235)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0(A_233)))
      | v1_xboole_0(B_234)
      | ~ l1_struct_0(A_233)
      | v2_struct_0(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_918,plain,(
    ! [A_233] :
      ( l1_waybel_0(k3_yellow19(A_233,k2_struct_0('#skF_5'),'#skF_6'),A_233)
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_233)))
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | ~ l1_struct_0(A_233)
      | v2_struct_0(A_233) ) ),
    inference(resolution,[status(thm)],[c_707,c_911])).

tff(c_926,plain,(
    ! [A_233] :
      ( l1_waybel_0(k3_yellow19(A_233,k2_struct_0('#skF_5'),'#skF_6'),A_233)
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_233)))
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | ~ l1_struct_0(A_233)
      | v2_struct_0(A_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_624,c_918])).

tff(c_929,plain,(
    ! [A_236] :
      ( l1_waybel_0(k3_yellow19(A_236,k2_struct_0('#skF_5'),'#skF_6'),A_236)
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ l1_struct_0(A_236)
      | v2_struct_0(A_236) ) ),
    inference(negUnitSimplification,[status(thm)],[c_676,c_619,c_926])).

tff(c_932,plain,
    ( l1_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),'#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_929])).

tff(c_939,plain,
    ( l1_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_932])).

tff(c_940,plain,(
    l1_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_939])).

tff(c_48,plain,(
    ! [A_23,B_27] :
      ( m1_subset_1('#skF_3'(A_23,B_27),u1_struct_0(A_23))
      | ~ l1_waybel_0(B_27,A_23)
      | ~ v7_waybel_0(B_27)
      | ~ v4_orders_2(B_27)
      | v2_struct_0(B_27)
      | ~ v1_compts_1(A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_46,plain,(
    ! [A_23,B_27] :
      ( r3_waybel_9(A_23,B_27,'#skF_3'(A_23,B_27))
      | ~ l1_waybel_0(B_27,A_23)
      | ~ v7_waybel_0(B_27)
      | ~ v4_orders_2(B_27)
      | v2_struct_0(B_27)
      | ~ v1_compts_1(A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_1056,plain,(
    ! [A_262,B_263,C_264] :
      ( r1_waybel_7(A_262,B_263,C_264)
      | ~ r3_waybel_9(A_262,k3_yellow19(A_262,k2_struct_0(A_262),B_263),C_264)
      | ~ m1_subset_1(C_264,u1_struct_0(A_262))
      | ~ m1_subset_1(B_263,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_262)))))
      | ~ v13_waybel_0(B_263,k3_yellow_1(k2_struct_0(A_262)))
      | ~ v2_waybel_0(B_263,k3_yellow_1(k2_struct_0(A_262)))
      | ~ v1_subset_1(B_263,u1_struct_0(k3_yellow_1(k2_struct_0(A_262))))
      | v1_xboole_0(B_263)
      | ~ l1_pre_topc(A_262)
      | ~ v2_pre_topc(A_262)
      | v2_struct_0(A_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_1198,plain,(
    ! [A_339,B_340] :
      ( r1_waybel_7(A_339,B_340,'#skF_3'(A_339,k3_yellow19(A_339,k2_struct_0(A_339),B_340)))
      | ~ m1_subset_1('#skF_3'(A_339,k3_yellow19(A_339,k2_struct_0(A_339),B_340)),u1_struct_0(A_339))
      | ~ m1_subset_1(B_340,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_339)))))
      | ~ v13_waybel_0(B_340,k3_yellow_1(k2_struct_0(A_339)))
      | ~ v2_waybel_0(B_340,k3_yellow_1(k2_struct_0(A_339)))
      | ~ v1_subset_1(B_340,u1_struct_0(k3_yellow_1(k2_struct_0(A_339))))
      | v1_xboole_0(B_340)
      | ~ l1_waybel_0(k3_yellow19(A_339,k2_struct_0(A_339),B_340),A_339)
      | ~ v7_waybel_0(k3_yellow19(A_339,k2_struct_0(A_339),B_340))
      | ~ v4_orders_2(k3_yellow19(A_339,k2_struct_0(A_339),B_340))
      | v2_struct_0(k3_yellow19(A_339,k2_struct_0(A_339),B_340))
      | ~ v1_compts_1(A_339)
      | ~ l1_pre_topc(A_339)
      | ~ v2_pre_topc(A_339)
      | v2_struct_0(A_339) ) ),
    inference(resolution,[status(thm)],[c_46,c_1056])).

tff(c_1212,plain,(
    ! [A_341,B_342] :
      ( r1_waybel_7(A_341,B_342,'#skF_3'(A_341,k3_yellow19(A_341,k2_struct_0(A_341),B_342)))
      | ~ m1_subset_1(B_342,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_341)))))
      | ~ v13_waybel_0(B_342,k3_yellow_1(k2_struct_0(A_341)))
      | ~ v2_waybel_0(B_342,k3_yellow_1(k2_struct_0(A_341)))
      | ~ v1_subset_1(B_342,u1_struct_0(k3_yellow_1(k2_struct_0(A_341))))
      | v1_xboole_0(B_342)
      | ~ l1_waybel_0(k3_yellow19(A_341,k2_struct_0(A_341),B_342),A_341)
      | ~ v7_waybel_0(k3_yellow19(A_341,k2_struct_0(A_341),B_342))
      | ~ v4_orders_2(k3_yellow19(A_341,k2_struct_0(A_341),B_342))
      | v2_struct_0(k3_yellow19(A_341,k2_struct_0(A_341),B_342))
      | ~ v1_compts_1(A_341)
      | ~ l1_pre_topc(A_341)
      | ~ v2_pre_topc(A_341)
      | v2_struct_0(A_341) ) ),
    inference(resolution,[status(thm)],[c_48,c_1198])).

tff(c_1219,plain,
    ( r1_waybel_7('#skF_5','#skF_6','#skF_3'('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')))
    | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
    | v1_xboole_0('#skF_6')
    | ~ l1_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),'#skF_5')
    | ~ v7_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | ~ v4_orders_2(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | v2_struct_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | ~ v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_707,c_1212])).

tff(c_1227,plain,
    ( r1_waybel_7('#skF_5','#skF_6','#skF_3'('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')))
    | v1_xboole_0('#skF_6')
    | v2_struct_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_620,c_903,c_1022,c_940,c_684,c_630,c_624,c_1219])).

tff(c_1228,plain,
    ( r1_waybel_7('#skF_5','#skF_6','#skF_3'('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')))
    | v2_struct_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_619,c_1227])).

tff(c_1230,plain,(
    v2_struct_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1228])).

tff(c_38,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1232,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
    | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1230,c_38])).

tff(c_1235,plain,
    ( v1_xboole_0('#skF_6')
    | v1_xboole_0(k2_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_716,c_644,c_630,c_624,c_707,c_1232])).

tff(c_1237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_676,c_619,c_1235])).

tff(c_1239,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1228])).

tff(c_1238,plain,(
    r1_waybel_7('#skF_5','#skF_6','#skF_3'('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_1228])).

tff(c_798,plain,(
    ! [A_210,B_211] :
      ( m1_subset_1('#skF_3'(A_210,B_211),u1_struct_0(A_210))
      | ~ l1_waybel_0(B_211,A_210)
      | ~ v7_waybel_0(B_211)
      | ~ v4_orders_2(B_211)
      | v2_struct_0(B_211)
      | ~ v1_compts_1(A_210)
      | ~ l1_pre_topc(A_210)
      | ~ v2_pre_topc(A_210)
      | v2_struct_0(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_801,plain,(
    ! [B_211] :
      ( m1_subset_1('#skF_3'('#skF_5',B_211),k2_struct_0('#skF_5'))
      | ~ l1_waybel_0(B_211,'#skF_5')
      | ~ v7_waybel_0(B_211)
      | ~ v4_orders_2(B_211)
      | v2_struct_0(B_211)
      | ~ v1_compts_1('#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_798])).

tff(c_806,plain,(
    ! [B_211] :
      ( m1_subset_1('#skF_3'('#skF_5',B_211),k2_struct_0('#skF_5'))
      | ~ l1_waybel_0(B_211,'#skF_5')
      | ~ v7_waybel_0(B_211)
      | ~ v4_orders_2(B_211)
      | v2_struct_0(B_211)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_620,c_801])).

tff(c_810,plain,(
    ! [B_212] :
      ( m1_subset_1('#skF_3'('#skF_5',B_212),k2_struct_0('#skF_5'))
      | ~ l1_waybel_0(B_212,'#skF_5')
      | ~ v7_waybel_0(B_212)
      | ~ v4_orders_2(B_212)
      | v2_struct_0(B_212) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_806])).

tff(c_80,plain,(
    ! [C_61] :
      ( ~ r1_waybel_7('#skF_5','#skF_6',C_61)
      | ~ m1_subset_1(C_61,u1_struct_0('#skF_5'))
      | ~ v1_compts_1('#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_743,plain,(
    ! [C_61] :
      ( ~ r1_waybel_7('#skF_5','#skF_6',C_61)
      | ~ m1_subset_1(C_61,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_644,c_80])).

tff(c_814,plain,(
    ! [B_212] :
      ( ~ r1_waybel_7('#skF_5','#skF_6','#skF_3'('#skF_5',B_212))
      | ~ l1_waybel_0(B_212,'#skF_5')
      | ~ v7_waybel_0(B_212)
      | ~ v4_orders_2(B_212)
      | v2_struct_0(B_212) ) ),
    inference(resolution,[status(thm)],[c_810,c_743])).

tff(c_1242,plain,
    ( ~ l1_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),'#skF_5')
    | ~ v7_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | ~ v4_orders_2(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | v2_struct_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_1238,c_814])).

tff(c_1245,plain,(
    v2_struct_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_903,c_1022,c_940,c_1242])).

tff(c_1247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1239,c_1245])).

%------------------------------------------------------------------------------
