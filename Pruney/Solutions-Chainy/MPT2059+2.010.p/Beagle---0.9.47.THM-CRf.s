%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:37 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :  152 (1275 expanded)
%              Number of leaves         :   39 ( 460 expanded)
%              Depth                    :   17
%              Number of atoms          :  497 (5145 expanded)
%              Number of equality atoms :   13 ( 237 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k10_yellow_6 > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_197,negated_conjecture,(
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

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_45,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_127,axiom,(
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

tff(f_99,axiom,(
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

tff(f_71,axiom,(
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

tff(f_170,axiom,(
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

tff(f_151,axiom,(
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

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_6,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_62,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_71,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_67])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_36])).

tff(c_54,plain,
    ( ~ r2_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_101,plain,(
    ~ r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,
    ( r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
    | r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_104,plain,(
    r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_60])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_77,plain,(
    ! [A_31] :
      ( ~ v1_xboole_0(u1_struct_0(A_31))
      | ~ l1_struct_0(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_80,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_77])).

tff(c_81,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_80])).

tff(c_86,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_89,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_86])).

tff(c_93,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_89])).

tff(c_94,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_95,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_82,plain,(
    ! [A_32] :
      ( m1_subset_1(k2_struct_0(A_32),k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_85,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_82])).

tff(c_103,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_85])).

tff(c_42,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_40,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_4,plain,(
    ! [A_2] :
      ( m1_subset_1(k2_struct_0(A_2),k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_243,plain,(
    ! [A_60,B_61,C_62] :
      ( v7_waybel_0(k3_yellow19(A_60,B_61,C_62))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_61))))
      | ~ v13_waybel_0(C_62,k3_yellow_1(B_61))
      | ~ v2_waybel_0(C_62,k3_yellow_1(B_61))
      | ~ v1_subset_1(C_62,u1_struct_0(k3_yellow_1(B_61)))
      | v1_xboole_0(C_62)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | v1_xboole_0(B_61)
      | ~ l1_struct_0(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_248,plain,(
    ! [A_60] :
      ( v7_waybel_0(k3_yellow19(A_60,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_60)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_38,c_243])).

tff(c_252,plain,(
    ! [A_60] :
      ( v7_waybel_0(k3_yellow19(A_60,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_60)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_60)
      | v2_struct_0(A_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_248])).

tff(c_254,plain,(
    ! [A_63] :
      ( v7_waybel_0(k3_yellow19(A_63,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_struct_0(A_63)
      | v2_struct_0(A_63) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_46,c_252])).

tff(c_258,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_254])).

tff(c_264,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_258])).

tff(c_265,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_264])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_111,plain,(
    ! [A_39,B_40,C_41] :
      ( v4_orders_2(k3_yellow19(A_39,B_40,C_41))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_40))))
      | ~ v13_waybel_0(C_41,k3_yellow_1(B_40))
      | ~ v2_waybel_0(C_41,k3_yellow_1(B_40))
      | v1_xboole_0(C_41)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | v1_xboole_0(B_40)
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_116,plain,(
    ! [A_39] :
      ( v4_orders_2(k3_yellow19(A_39,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_39)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_38,c_111])).

tff(c_120,plain,(
    ! [A_39] :
      ( v4_orders_2(k3_yellow19(A_39,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_39)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_116])).

tff(c_122,plain,(
    ! [A_42] :
      ( v4_orders_2(k3_yellow19(A_42,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_struct_0(A_42)
      | v2_struct_0(A_42) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_46,c_120])).

tff(c_126,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_122])).

tff(c_132,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_126])).

tff(c_133,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_132])).

tff(c_166,plain,(
    ! [A_50,B_51,C_52] :
      ( l1_waybel_0(k3_yellow19(A_50,B_51,C_52),A_50)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_51))))
      | ~ v13_waybel_0(C_52,k3_yellow_1(B_51))
      | ~ v2_waybel_0(C_52,k3_yellow_1(B_51))
      | v1_xboole_0(C_52)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | v1_xboole_0(B_51)
      | ~ l1_struct_0(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_171,plain,(
    ! [A_50] :
      ( l1_waybel_0(k3_yellow19(A_50,k2_struct_0('#skF_1'),'#skF_2'),A_50)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_50)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_50)
      | v2_struct_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_38,c_166])).

tff(c_175,plain,(
    ! [A_50] :
      ( l1_waybel_0(k3_yellow19(A_50,k2_struct_0('#skF_1'),'#skF_2'),A_50)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_50)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_50)
      | v2_struct_0(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_171])).

tff(c_177,plain,(
    ! [A_53] :
      ( l1_waybel_0(k3_yellow19(A_53,k2_struct_0('#skF_1'),'#skF_2'),A_53)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_struct_0(A_53)
      | v2_struct_0(A_53) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_46,c_175])).

tff(c_180,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_177])).

tff(c_185,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_180])).

tff(c_186,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_185])).

tff(c_216,plain,(
    ! [A_58,B_59] :
      ( k2_yellow19(A_58,k3_yellow19(A_58,k2_struct_0(A_58),B_59)) = B_59
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_58)))))
      | ~ v13_waybel_0(B_59,k3_yellow_1(k2_struct_0(A_58)))
      | ~ v2_waybel_0(B_59,k3_yellow_1(k2_struct_0(A_58)))
      | ~ v1_subset_1(B_59,u1_struct_0(k3_yellow_1(k2_struct_0(A_58))))
      | v1_xboole_0(B_59)
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_221,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_216])).

tff(c_225,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_44,c_42,c_40,c_221])).

tff(c_226,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_225])).

tff(c_32,plain,(
    ! [A_14,B_18,C_20] :
      ( r2_waybel_7(A_14,k2_yellow19(A_14,B_18),C_20)
      | ~ r2_hidden(C_20,k10_yellow_6(A_14,B_18))
      | ~ m1_subset_1(C_20,u1_struct_0(A_14))
      | ~ l1_waybel_0(B_18,A_14)
      | ~ v7_waybel_0(B_18)
      | ~ v4_orders_2(B_18)
      | v2_struct_0(B_18)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_230,plain,(
    ! [C_20] :
      ( r2_waybel_7('#skF_1','#skF_2',C_20)
      | ~ r2_hidden(C_20,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_20,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_32])).

tff(c_237,plain,(
    ! [C_20] :
      ( r2_waybel_7('#skF_1','#skF_2',C_20)
      | ~ r2_hidden(C_20,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_20,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_133,c_186,c_71,c_230])).

tff(c_238,plain,(
    ! [C_20] :
      ( r2_waybel_7('#skF_1','#skF_2',C_20)
      | ~ r2_hidden(C_20,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_20,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_237])).

tff(c_271,plain,(
    ! [C_20] :
      ( r2_waybel_7('#skF_1','#skF_2',C_20)
      | ~ r2_hidden(C_20,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_20,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_238])).

tff(c_272,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_22,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ v2_struct_0(k3_yellow19(A_8,B_9,C_10))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_9))))
      | ~ v13_waybel_0(C_10,k3_yellow_1(B_9))
      | ~ v2_waybel_0(C_10,k3_yellow_1(B_9))
      | v1_xboole_0(C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_8)))
      | v1_xboole_0(B_9)
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_274,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_272,c_22])).

tff(c_277,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_103,c_71,c_42,c_40,c_38,c_274])).

tff(c_279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_94,c_46,c_277])).

tff(c_281,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_30,plain,(
    ! [C_20,A_14,B_18] :
      ( r2_hidden(C_20,k10_yellow_6(A_14,B_18))
      | ~ r2_waybel_7(A_14,k2_yellow19(A_14,B_18),C_20)
      | ~ m1_subset_1(C_20,u1_struct_0(A_14))
      | ~ l1_waybel_0(B_18,A_14)
      | ~ v7_waybel_0(B_18)
      | ~ v4_orders_2(B_18)
      | v2_struct_0(B_18)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_233,plain,(
    ! [C_20] :
      ( r2_hidden(C_20,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_20)
      | ~ m1_subset_1(C_20,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_30])).

tff(c_240,plain,(
    ! [C_20] :
      ( r2_hidden(C_20,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_20)
      | ~ m1_subset_1(C_20,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_133,c_186,c_71,c_233])).

tff(c_241,plain,(
    ! [C_20] :
      ( r2_hidden(C_20,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_20)
      | ~ m1_subset_1(C_20,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_240])).

tff(c_284,plain,(
    ! [C_20] :
      ( r2_hidden(C_20,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_20)
      | ~ m1_subset_1(C_20,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_241])).

tff(c_286,plain,(
    ! [C_65] :
      ( r2_hidden(C_65,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_65)
      | ~ m1_subset_1(C_65,k2_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_281,c_284])).

tff(c_292,plain,
    ( ~ r2_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_286,c_101])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_104,c_292])).

tff(c_298,plain,(
    ~ r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_299,plain,(
    r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_301,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_85])).

tff(c_310,plain,(
    ! [A_72,B_73,C_74] :
      ( v4_orders_2(k3_yellow19(A_72,B_73,C_74))
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_73))))
      | ~ v13_waybel_0(C_74,k3_yellow_1(B_73))
      | ~ v2_waybel_0(C_74,k3_yellow_1(B_73))
      | v1_xboole_0(C_74)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | v1_xboole_0(B_73)
      | ~ l1_struct_0(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_315,plain,(
    ! [A_72] :
      ( v4_orders_2(k3_yellow19(A_72,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_72)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_72)
      | v2_struct_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_38,c_310])).

tff(c_319,plain,(
    ! [A_72] :
      ( v4_orders_2(k3_yellow19(A_72,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_72)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_72)
      | v2_struct_0(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_315])).

tff(c_321,plain,(
    ! [A_75] :
      ( v4_orders_2(k3_yellow19(A_75,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_struct_0(A_75)
      | v2_struct_0(A_75) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_46,c_319])).

tff(c_325,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_321])).

tff(c_331,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_325])).

tff(c_332,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_331])).

tff(c_401,plain,(
    ! [A_90,B_91,C_92] :
      ( v7_waybel_0(k3_yellow19(A_90,B_91,C_92))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_91))))
      | ~ v13_waybel_0(C_92,k3_yellow_1(B_91))
      | ~ v2_waybel_0(C_92,k3_yellow_1(B_91))
      | ~ v1_subset_1(C_92,u1_struct_0(k3_yellow_1(B_91)))
      | v1_xboole_0(C_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | v1_xboole_0(B_91)
      | ~ l1_struct_0(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_406,plain,(
    ! [A_90] :
      ( v7_waybel_0(k3_yellow19(A_90,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_90)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_90)
      | v2_struct_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_38,c_401])).

tff(c_410,plain,(
    ! [A_90] :
      ( v7_waybel_0(k3_yellow19(A_90,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_90)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_90)
      | v2_struct_0(A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_406])).

tff(c_412,plain,(
    ! [A_93] :
      ( v7_waybel_0(k3_yellow19(A_93,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_46,c_410])).

tff(c_416,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_412])).

tff(c_422,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_416])).

tff(c_423,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_422])).

tff(c_390,plain,(
    ! [A_87,B_88,C_89] :
      ( l1_waybel_0(k3_yellow19(A_87,B_88,C_89),A_87)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_88))))
      | ~ v13_waybel_0(C_89,k3_yellow_1(B_88))
      | ~ v2_waybel_0(C_89,k3_yellow_1(B_88))
      | v1_xboole_0(C_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | v1_xboole_0(B_88)
      | ~ l1_struct_0(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_395,plain,(
    ! [A_87] :
      ( l1_waybel_0(k3_yellow19(A_87,k2_struct_0('#skF_1'),'#skF_2'),A_87)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_87)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_87)
      | v2_struct_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_38,c_390])).

tff(c_399,plain,(
    ! [A_87] :
      ( l1_waybel_0(k3_yellow19(A_87,k2_struct_0('#skF_1'),'#skF_2'),A_87)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_87)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_87)
      | v2_struct_0(A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_395])).

tff(c_428,plain,(
    ! [A_94] :
      ( l1_waybel_0(k3_yellow19(A_94,k2_struct_0('#skF_1'),'#skF_2'),A_94)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_struct_0(A_94)
      | v2_struct_0(A_94) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_46,c_399])).

tff(c_431,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_428])).

tff(c_436,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_431])).

tff(c_437,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_436])).

tff(c_442,plain,(
    ! [A_95,B_96] :
      ( k2_yellow19(A_95,k3_yellow19(A_95,k2_struct_0(A_95),B_96)) = B_96
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_95)))))
      | ~ v13_waybel_0(B_96,k3_yellow_1(k2_struct_0(A_95)))
      | ~ v2_waybel_0(B_96,k3_yellow_1(k2_struct_0(A_95)))
      | ~ v1_subset_1(B_96,u1_struct_0(k3_yellow_1(k2_struct_0(A_95))))
      | v1_xboole_0(B_96)
      | ~ l1_struct_0(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_447,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_442])).

tff(c_451,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_44,c_42,c_40,c_447])).

tff(c_452,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_451])).

tff(c_456,plain,(
    ! [C_20] :
      ( r2_waybel_7('#skF_1','#skF_2',C_20)
      | ~ r2_hidden(C_20,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_20,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_32])).

tff(c_463,plain,(
    ! [C_20] :
      ( r2_waybel_7('#skF_1','#skF_2',C_20)
      | ~ r2_hidden(C_20,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_20,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_332,c_423,c_437,c_71,c_456])).

tff(c_464,plain,(
    ! [C_20] :
      ( r2_waybel_7('#skF_1','#skF_2',C_20)
      | ~ r2_hidden(C_20,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_20,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_463])).

tff(c_469,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_464])).

tff(c_472,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_469,c_22])).

tff(c_475,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_301,c_71,c_42,c_40,c_38,c_472])).

tff(c_477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_94,c_46,c_475])).

tff(c_480,plain,(
    ! [C_99] :
      ( r2_waybel_7('#skF_1','#skF_2',C_99)
      | ~ r2_hidden(C_99,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_99,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_464])).

tff(c_483,plain,
    ( r2_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_299,c_480])).

tff(c_486,plain,(
    r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_483])).

tff(c_488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_298,c_486])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:33:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.42  
% 2.89/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.42  %$ r2_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k10_yellow_6 > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.89/1.42  
% 2.89/1.42  %Foreground sorts:
% 2.89/1.42  
% 2.89/1.42  
% 2.89/1.42  %Background operators:
% 2.89/1.42  
% 2.89/1.42  
% 2.89/1.42  %Foreground operators:
% 2.89/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.89/1.42  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.89/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.42  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 2.89/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.42  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.89/1.42  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.89/1.42  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.89/1.42  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 2.89/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.89/1.42  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.89/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.89/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.89/1.42  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.89/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.89/1.42  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.89/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.42  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.89/1.42  tff(r2_waybel_7, type, r2_waybel_7: ($i * $i * $i) > $o).
% 2.89/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.42  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.89/1.42  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.89/1.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.89/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.89/1.42  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.89/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.89/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.42  
% 2.89/1.45  tff(f_197, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, k3_yellow19(A, k2_struct_0(A), B))) <=> r2_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_yellow19)).
% 2.89/1.45  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.89/1.45  tff(f_29, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.89/1.45  tff(f_45, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.89/1.45  tff(f_33, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.89/1.45  tff(f_127, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow19)).
% 2.89/1.45  tff(f_99, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_yellow19)).
% 2.89/1.45  tff(f_71, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 2.89/1.45  tff(f_170, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 2.89/1.45  tff(f_151, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, B)) <=> r2_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow19)).
% 2.89/1.45  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.89/1.45  tff(c_6, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.89/1.45  tff(c_62, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.89/1.45  tff(c_67, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_6, c_62])).
% 2.89/1.45  tff(c_71, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_67])).
% 2.89/1.45  tff(c_36, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.89/1.45  tff(c_72, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_36])).
% 2.89/1.45  tff(c_54, plain, (~r2_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.89/1.45  tff(c_101, plain, (~r2_hidden('#skF_3', k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(splitLeft, [status(thm)], [c_54])).
% 2.89/1.45  tff(c_60, plain, (r2_hidden('#skF_3', k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | r2_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.89/1.45  tff(c_104, plain, (r2_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_101, c_60])).
% 2.89/1.45  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.89/1.45  tff(c_77, plain, (![A_31]: (~v1_xboole_0(u1_struct_0(A_31)) | ~l1_struct_0(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.89/1.45  tff(c_80, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_71, c_77])).
% 2.89/1.45  tff(c_81, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_80])).
% 2.89/1.45  tff(c_86, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_81])).
% 2.89/1.45  tff(c_89, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_86])).
% 2.89/1.45  tff(c_93, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_89])).
% 2.89/1.45  tff(c_94, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_81])).
% 2.89/1.45  tff(c_46, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.89/1.45  tff(c_95, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_81])).
% 2.89/1.45  tff(c_82, plain, (![A_32]: (m1_subset_1(k2_struct_0(A_32), k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.89/1.45  tff(c_85, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_71, c_82])).
% 2.89/1.45  tff(c_103, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_85])).
% 2.89/1.45  tff(c_42, plain, (v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.89/1.45  tff(c_40, plain, (v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.89/1.45  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.89/1.45  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_struct_0(A_2), k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.89/1.45  tff(c_44, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.89/1.45  tff(c_243, plain, (![A_60, B_61, C_62]: (v7_waybel_0(k3_yellow19(A_60, B_61, C_62)) | ~m1_subset_1(C_62, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_61)))) | ~v13_waybel_0(C_62, k3_yellow_1(B_61)) | ~v2_waybel_0(C_62, k3_yellow_1(B_61)) | ~v1_subset_1(C_62, u1_struct_0(k3_yellow_1(B_61))) | v1_xboole_0(C_62) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | v1_xboole_0(B_61) | ~l1_struct_0(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.89/1.45  tff(c_248, plain, (![A_60]: (v7_waybel_0(k3_yellow19(A_60, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_60))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_38, c_243])).
% 2.89/1.45  tff(c_252, plain, (![A_60]: (v7_waybel_0(k3_yellow19(A_60, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_60))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_60) | v2_struct_0(A_60))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_248])).
% 2.89/1.45  tff(c_254, plain, (![A_63]: (v7_waybel_0(k3_yellow19(A_63, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_struct_0(A_63) | v2_struct_0(A_63))), inference(negUnitSimplification, [status(thm)], [c_94, c_46, c_252])).
% 2.89/1.45  tff(c_258, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_4, c_254])).
% 2.89/1.45  tff(c_264, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_258])).
% 2.89/1.45  tff(c_265, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_264])).
% 2.89/1.45  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.89/1.45  tff(c_111, plain, (![A_39, B_40, C_41]: (v4_orders_2(k3_yellow19(A_39, B_40, C_41)) | ~m1_subset_1(C_41, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_40)))) | ~v13_waybel_0(C_41, k3_yellow_1(B_40)) | ~v2_waybel_0(C_41, k3_yellow_1(B_40)) | v1_xboole_0(C_41) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | v1_xboole_0(B_40) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.89/1.45  tff(c_116, plain, (![A_39]: (v4_orders_2(k3_yellow19(A_39, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_39))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(resolution, [status(thm)], [c_38, c_111])).
% 2.89/1.45  tff(c_120, plain, (![A_39]: (v4_orders_2(k3_yellow19(A_39, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_39))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_116])).
% 2.89/1.45  tff(c_122, plain, (![A_42]: (v4_orders_2(k3_yellow19(A_42, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_struct_0(A_42) | v2_struct_0(A_42))), inference(negUnitSimplification, [status(thm)], [c_94, c_46, c_120])).
% 2.89/1.45  tff(c_126, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_4, c_122])).
% 2.89/1.45  tff(c_132, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_126])).
% 2.89/1.45  tff(c_133, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_132])).
% 2.89/1.45  tff(c_166, plain, (![A_50, B_51, C_52]: (l1_waybel_0(k3_yellow19(A_50, B_51, C_52), A_50) | ~m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_51)))) | ~v13_waybel_0(C_52, k3_yellow_1(B_51)) | ~v2_waybel_0(C_52, k3_yellow_1(B_51)) | v1_xboole_0(C_52) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | v1_xboole_0(B_51) | ~l1_struct_0(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.89/1.45  tff(c_171, plain, (![A_50]: (l1_waybel_0(k3_yellow19(A_50, k2_struct_0('#skF_1'), '#skF_2'), A_50) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_50))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_50) | v2_struct_0(A_50))), inference(resolution, [status(thm)], [c_38, c_166])).
% 2.89/1.45  tff(c_175, plain, (![A_50]: (l1_waybel_0(k3_yellow19(A_50, k2_struct_0('#skF_1'), '#skF_2'), A_50) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_50))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_50) | v2_struct_0(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_171])).
% 2.89/1.45  tff(c_177, plain, (![A_53]: (l1_waybel_0(k3_yellow19(A_53, k2_struct_0('#skF_1'), '#skF_2'), A_53) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_struct_0(A_53) | v2_struct_0(A_53))), inference(negUnitSimplification, [status(thm)], [c_94, c_46, c_175])).
% 2.89/1.45  tff(c_180, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_4, c_177])).
% 2.89/1.45  tff(c_185, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_180])).
% 2.89/1.45  tff(c_186, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_185])).
% 2.89/1.45  tff(c_216, plain, (![A_58, B_59]: (k2_yellow19(A_58, k3_yellow19(A_58, k2_struct_0(A_58), B_59))=B_59 | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_58))))) | ~v13_waybel_0(B_59, k3_yellow_1(k2_struct_0(A_58))) | ~v2_waybel_0(B_59, k3_yellow_1(k2_struct_0(A_58))) | ~v1_subset_1(B_59, u1_struct_0(k3_yellow_1(k2_struct_0(A_58)))) | v1_xboole_0(B_59) | ~l1_struct_0(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_170])).
% 2.89/1.45  tff(c_221, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_216])).
% 2.89/1.45  tff(c_225, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_44, c_42, c_40, c_221])).
% 2.89/1.45  tff(c_226, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_225])).
% 2.89/1.45  tff(c_32, plain, (![A_14, B_18, C_20]: (r2_waybel_7(A_14, k2_yellow19(A_14, B_18), C_20) | ~r2_hidden(C_20, k10_yellow_6(A_14, B_18)) | ~m1_subset_1(C_20, u1_struct_0(A_14)) | ~l1_waybel_0(B_18, A_14) | ~v7_waybel_0(B_18) | ~v4_orders_2(B_18) | v2_struct_0(B_18) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.89/1.45  tff(c_230, plain, (![C_20]: (r2_waybel_7('#skF_1', '#skF_2', C_20) | ~r2_hidden(C_20, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_20, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_226, c_32])).
% 2.89/1.45  tff(c_237, plain, (![C_20]: (r2_waybel_7('#skF_1', '#skF_2', C_20) | ~r2_hidden(C_20, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_20, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_133, c_186, c_71, c_230])).
% 2.89/1.45  tff(c_238, plain, (![C_20]: (r2_waybel_7('#skF_1', '#skF_2', C_20) | ~r2_hidden(C_20, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_20, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_237])).
% 2.89/1.45  tff(c_271, plain, (![C_20]: (r2_waybel_7('#skF_1', '#skF_2', C_20) | ~r2_hidden(C_20, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_20, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_238])).
% 2.89/1.45  tff(c_272, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_271])).
% 2.89/1.45  tff(c_22, plain, (![A_8, B_9, C_10]: (~v2_struct_0(k3_yellow19(A_8, B_9, C_10)) | ~m1_subset_1(C_10, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_9)))) | ~v13_waybel_0(C_10, k3_yellow_1(B_9)) | ~v2_waybel_0(C_10, k3_yellow_1(B_9)) | v1_xboole_0(C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_8))) | v1_xboole_0(B_9) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.89/1.45  tff(c_274, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_272, c_22])).
% 2.89/1.45  tff(c_277, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_103, c_71, c_42, c_40, c_38, c_274])).
% 2.89/1.45  tff(c_279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_94, c_46, c_277])).
% 2.89/1.45  tff(c_281, plain, (~v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_271])).
% 2.89/1.45  tff(c_30, plain, (![C_20, A_14, B_18]: (r2_hidden(C_20, k10_yellow_6(A_14, B_18)) | ~r2_waybel_7(A_14, k2_yellow19(A_14, B_18), C_20) | ~m1_subset_1(C_20, u1_struct_0(A_14)) | ~l1_waybel_0(B_18, A_14) | ~v7_waybel_0(B_18) | ~v4_orders_2(B_18) | v2_struct_0(B_18) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.89/1.45  tff(c_233, plain, (![C_20]: (r2_hidden(C_20, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_20) | ~m1_subset_1(C_20, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_226, c_30])).
% 2.89/1.45  tff(c_240, plain, (![C_20]: (r2_hidden(C_20, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_20) | ~m1_subset_1(C_20, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_133, c_186, c_71, c_233])).
% 2.89/1.45  tff(c_241, plain, (![C_20]: (r2_hidden(C_20, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_20) | ~m1_subset_1(C_20, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_240])).
% 2.89/1.45  tff(c_284, plain, (![C_20]: (r2_hidden(C_20, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_20) | ~m1_subset_1(C_20, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_241])).
% 2.89/1.45  tff(c_286, plain, (![C_65]: (r2_hidden(C_65, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_65) | ~m1_subset_1(C_65, k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_281, c_284])).
% 2.89/1.45  tff(c_292, plain, (~r2_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_286, c_101])).
% 2.89/1.45  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_104, c_292])).
% 2.89/1.45  tff(c_298, plain, (~r2_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_54])).
% 2.89/1.45  tff(c_299, plain, (r2_hidden('#skF_3', k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(splitRight, [status(thm)], [c_54])).
% 2.89/1.45  tff(c_301, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_85])).
% 2.89/1.45  tff(c_310, plain, (![A_72, B_73, C_74]: (v4_orders_2(k3_yellow19(A_72, B_73, C_74)) | ~m1_subset_1(C_74, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_73)))) | ~v13_waybel_0(C_74, k3_yellow_1(B_73)) | ~v2_waybel_0(C_74, k3_yellow_1(B_73)) | v1_xboole_0(C_74) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | v1_xboole_0(B_73) | ~l1_struct_0(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.89/1.45  tff(c_315, plain, (![A_72]: (v4_orders_2(k3_yellow19(A_72, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_72))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_72) | v2_struct_0(A_72))), inference(resolution, [status(thm)], [c_38, c_310])).
% 2.89/1.45  tff(c_319, plain, (![A_72]: (v4_orders_2(k3_yellow19(A_72, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_72))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_72) | v2_struct_0(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_315])).
% 2.89/1.45  tff(c_321, plain, (![A_75]: (v4_orders_2(k3_yellow19(A_75, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_struct_0(A_75) | v2_struct_0(A_75))), inference(negUnitSimplification, [status(thm)], [c_94, c_46, c_319])).
% 2.89/1.45  tff(c_325, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_4, c_321])).
% 2.89/1.45  tff(c_331, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_325])).
% 2.89/1.45  tff(c_332, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_331])).
% 2.89/1.45  tff(c_401, plain, (![A_90, B_91, C_92]: (v7_waybel_0(k3_yellow19(A_90, B_91, C_92)) | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_91)))) | ~v13_waybel_0(C_92, k3_yellow_1(B_91)) | ~v2_waybel_0(C_92, k3_yellow_1(B_91)) | ~v1_subset_1(C_92, u1_struct_0(k3_yellow_1(B_91))) | v1_xboole_0(C_92) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | v1_xboole_0(B_91) | ~l1_struct_0(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.89/1.45  tff(c_406, plain, (![A_90]: (v7_waybel_0(k3_yellow19(A_90, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_90))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_90) | v2_struct_0(A_90))), inference(resolution, [status(thm)], [c_38, c_401])).
% 2.89/1.45  tff(c_410, plain, (![A_90]: (v7_waybel_0(k3_yellow19(A_90, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_90))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_90) | v2_struct_0(A_90))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_406])).
% 2.89/1.45  tff(c_412, plain, (![A_93]: (v7_waybel_0(k3_yellow19(A_93, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_struct_0(A_93) | v2_struct_0(A_93))), inference(negUnitSimplification, [status(thm)], [c_94, c_46, c_410])).
% 2.89/1.45  tff(c_416, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_4, c_412])).
% 2.89/1.45  tff(c_422, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_416])).
% 2.89/1.45  tff(c_423, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_422])).
% 2.89/1.45  tff(c_390, plain, (![A_87, B_88, C_89]: (l1_waybel_0(k3_yellow19(A_87, B_88, C_89), A_87) | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_88)))) | ~v13_waybel_0(C_89, k3_yellow_1(B_88)) | ~v2_waybel_0(C_89, k3_yellow_1(B_88)) | v1_xboole_0(C_89) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | v1_xboole_0(B_88) | ~l1_struct_0(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.89/1.45  tff(c_395, plain, (![A_87]: (l1_waybel_0(k3_yellow19(A_87, k2_struct_0('#skF_1'), '#skF_2'), A_87) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_87))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_87) | v2_struct_0(A_87))), inference(resolution, [status(thm)], [c_38, c_390])).
% 2.89/1.45  tff(c_399, plain, (![A_87]: (l1_waybel_0(k3_yellow19(A_87, k2_struct_0('#skF_1'), '#skF_2'), A_87) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_87))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_87) | v2_struct_0(A_87))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_395])).
% 2.89/1.45  tff(c_428, plain, (![A_94]: (l1_waybel_0(k3_yellow19(A_94, k2_struct_0('#skF_1'), '#skF_2'), A_94) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_struct_0(A_94) | v2_struct_0(A_94))), inference(negUnitSimplification, [status(thm)], [c_94, c_46, c_399])).
% 2.89/1.45  tff(c_431, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_4, c_428])).
% 2.89/1.45  tff(c_436, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_431])).
% 2.89/1.45  tff(c_437, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_436])).
% 2.89/1.45  tff(c_442, plain, (![A_95, B_96]: (k2_yellow19(A_95, k3_yellow19(A_95, k2_struct_0(A_95), B_96))=B_96 | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_95))))) | ~v13_waybel_0(B_96, k3_yellow_1(k2_struct_0(A_95))) | ~v2_waybel_0(B_96, k3_yellow_1(k2_struct_0(A_95))) | ~v1_subset_1(B_96, u1_struct_0(k3_yellow_1(k2_struct_0(A_95)))) | v1_xboole_0(B_96) | ~l1_struct_0(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_170])).
% 2.89/1.45  tff(c_447, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_442])).
% 2.89/1.45  tff(c_451, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_44, c_42, c_40, c_447])).
% 2.89/1.45  tff(c_452, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_451])).
% 2.89/1.45  tff(c_456, plain, (![C_20]: (r2_waybel_7('#skF_1', '#skF_2', C_20) | ~r2_hidden(C_20, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_20, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_452, c_32])).
% 2.89/1.45  tff(c_463, plain, (![C_20]: (r2_waybel_7('#skF_1', '#skF_2', C_20) | ~r2_hidden(C_20, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_20, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_332, c_423, c_437, c_71, c_456])).
% 2.89/1.45  tff(c_464, plain, (![C_20]: (r2_waybel_7('#skF_1', '#skF_2', C_20) | ~r2_hidden(C_20, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_20, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_463])).
% 2.89/1.45  tff(c_469, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_464])).
% 2.89/1.45  tff(c_472, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_469, c_22])).
% 2.89/1.45  tff(c_475, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_301, c_71, c_42, c_40, c_38, c_472])).
% 2.89/1.45  tff(c_477, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_94, c_46, c_475])).
% 2.89/1.45  tff(c_480, plain, (![C_99]: (r2_waybel_7('#skF_1', '#skF_2', C_99) | ~r2_hidden(C_99, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_99, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_464])).
% 2.89/1.45  tff(c_483, plain, (r2_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_299, c_480])).
% 2.89/1.45  tff(c_486, plain, (r2_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_483])).
% 2.89/1.45  tff(c_488, plain, $false, inference(negUnitSimplification, [status(thm)], [c_298, c_486])).
% 2.89/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.45  
% 2.89/1.45  Inference rules
% 2.89/1.45  ----------------------
% 2.89/1.45  #Ref     : 0
% 2.89/1.45  #Sup     : 67
% 2.89/1.45  #Fact    : 0
% 2.89/1.45  #Define  : 0
% 2.89/1.45  #Split   : 4
% 2.89/1.45  #Chain   : 0
% 2.89/1.45  #Close   : 0
% 2.89/1.45  
% 2.89/1.45  Ordering : KBO
% 2.89/1.45  
% 2.89/1.45  Simplification rules
% 2.89/1.45  ----------------------
% 2.89/1.45  #Subsume      : 4
% 2.89/1.45  #Demod        : 115
% 2.89/1.45  #Tautology    : 23
% 2.89/1.45  #SimpNegUnit  : 43
% 2.89/1.45  #BackRed      : 1
% 2.89/1.45  
% 2.89/1.45  #Partial instantiations: 0
% 2.89/1.45  #Strategies tried      : 1
% 2.89/1.45  
% 2.89/1.45  Timing (in seconds)
% 2.89/1.45  ----------------------
% 2.89/1.46  Preprocessing        : 0.36
% 2.89/1.46  Parsing              : 0.19
% 2.89/1.46  CNF conversion       : 0.02
% 2.89/1.46  Main loop            : 0.31
% 2.89/1.46  Inferencing          : 0.11
% 2.89/1.46  Reduction            : 0.10
% 2.89/1.46  Demodulation         : 0.07
% 2.89/1.46  BG Simplification    : 0.02
% 2.89/1.46  Subsumption          : 0.05
% 2.89/1.46  Abstraction          : 0.02
% 2.89/1.46  MUC search           : 0.00
% 2.89/1.46  Cooper               : 0.00
% 2.89/1.46  Total                : 0.72
% 2.89/1.46  Index Insertion      : 0.00
% 2.89/1.46  Index Deletion       : 0.00
% 2.89/1.46  Index Matching       : 0.00
% 2.89/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
