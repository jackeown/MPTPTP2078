%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:37 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  168 (1548 expanded)
%              Number of leaves         :   38 ( 556 expanded)
%              Depth                    :   20
%              Number of atoms          :  533 (8497 expanded)
%              Number of equality atoms :    9 (  40 expanded)
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

tff(f_193,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow19)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

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
        & v3_orders_2(k3_yellow19(A,B,C))
        & v4_orders_2(k3_yellow19(A,B,C))
        & v6_waybel_0(k3_yellow19(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_yellow19)).

tff(f_41,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_67,axiom,(
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

tff(f_166,axiom,(
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

tff(f_147,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow19)).

tff(f_123,axiom,(
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

tff(c_34,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_52,plain,
    ( ~ r2_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_62,plain,(
    ~ r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,
    ( r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
    | r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_63,plain,(
    r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_4,plain,(
    ! [A_2] :
      ( l1_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_2,plain,(
    ! [A_1] :
      ( m1_subset_1(k2_struct_0(A_1),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_40,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_38,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_71,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_76,plain,(
    ! [A_39] :
      ( v4_orders_2(k3_yellow19(A_39,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_39)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_36,c_71])).

tff(c_80,plain,(
    ! [A_39] :
      ( v4_orders_2(k3_yellow19(A_39,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_39)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_76])).

tff(c_81,plain,(
    ! [A_39] :
      ( v4_orders_2(k3_yellow19(A_39,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_39)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_80])).

tff(c_82,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_6,plain,(
    ! [A_3] :
      ( ~ v1_xboole_0(k2_struct_0(A_3))
      | ~ l1_struct_0(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_85,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_82,c_6])).

tff(c_88,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_85])).

tff(c_91,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_88])).

tff(c_95,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_91])).

tff(c_98,plain,(
    ! [A_42] :
      ( v4_orders_2(k3_yellow19(A_42,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_struct_0(A_42)
      | v2_struct_0(A_42) ) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_102,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_98])).

tff(c_105,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_102])).

tff(c_106,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_120,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_106])).

tff(c_124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_120])).

tff(c_126,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_97,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_125,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_166,plain,(
    ! [A_54,B_55,C_56] :
      ( l1_waybel_0(k3_yellow19(A_54,B_55,C_56),A_54)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_55))))
      | ~ v13_waybel_0(C_56,k3_yellow_1(B_55))
      | ~ v2_waybel_0(C_56,k3_yellow_1(B_55))
      | v1_xboole_0(C_56)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | v1_xboole_0(B_55)
      | ~ l1_struct_0(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_171,plain,(
    ! [A_54] :
      ( l1_waybel_0(k3_yellow19(A_54,k2_struct_0('#skF_1'),'#skF_2'),A_54)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_54)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_54)
      | v2_struct_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_36,c_166])).

tff(c_175,plain,(
    ! [A_54] :
      ( l1_waybel_0(k3_yellow19(A_54,k2_struct_0('#skF_1'),'#skF_2'),A_54)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_54)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_54)
      | v2_struct_0(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_171])).

tff(c_177,plain,(
    ! [A_57] :
      ( l1_waybel_0(k3_yellow19(A_57,k2_struct_0('#skF_1'),'#skF_2'),A_57)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_struct_0(A_57)
      | v2_struct_0(A_57) ) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_44,c_175])).

tff(c_180,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_177])).

tff(c_183,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_180])).

tff(c_184,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_183])).

tff(c_42,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_185,plain,(
    ! [A_58,B_59] :
      ( k2_yellow19(A_58,k3_yellow19(A_58,k2_struct_0(A_58),B_59)) = B_59
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_58)))))
      | ~ v13_waybel_0(B_59,k3_yellow_1(k2_struct_0(A_58)))
      | ~ v2_waybel_0(B_59,k3_yellow_1(k2_struct_0(A_58)))
      | ~ v1_subset_1(B_59,u1_struct_0(k3_yellow_1(k2_struct_0(A_58))))
      | v1_xboole_0(B_59)
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_190,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_185])).

tff(c_194,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_42,c_40,c_38,c_190])).

tff(c_195,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_194])).

tff(c_30,plain,(
    ! [A_13,B_17,C_19] :
      ( r2_waybel_7(A_13,k2_yellow19(A_13,B_17),C_19)
      | ~ r2_hidden(C_19,k10_yellow_6(A_13,B_17))
      | ~ m1_subset_1(C_19,u1_struct_0(A_13))
      | ~ l1_waybel_0(B_17,A_13)
      | ~ v7_waybel_0(B_17)
      | ~ v4_orders_2(B_17)
      | v2_struct_0(B_17)
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_199,plain,(
    ! [C_19] :
      ( r2_waybel_7('#skF_1','#skF_2',C_19)
      | ~ r2_hidden(C_19,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_19,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_30])).

tff(c_206,plain,(
    ! [C_19] :
      ( r2_waybel_7('#skF_1','#skF_2',C_19)
      | ~ r2_hidden(C_19,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_19,u1_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_125,c_184,c_199])).

tff(c_207,plain,(
    ! [C_19] :
      ( r2_waybel_7('#skF_1','#skF_2',C_19)
      | ~ r2_hidden(C_19,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_19,u1_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_206])).

tff(c_212,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_213,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_218,plain,(
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
    inference(resolution,[status(thm)],[c_36,c_213])).

tff(c_222,plain,(
    ! [A_60] :
      ( v7_waybel_0(k3_yellow19(A_60,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_60)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_60)
      | v2_struct_0(A_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_218])).

tff(c_224,plain,(
    ! [A_63] :
      ( v7_waybel_0(k3_yellow19(A_63,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_struct_0(A_63)
      | v2_struct_0(A_63) ) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_44,c_222])).

tff(c_228,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_224])).

tff(c_231,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_228])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_212,c_231])).

tff(c_234,plain,(
    ! [C_19] :
      ( v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | r2_waybel_7('#skF_1','#skF_2',C_19)
      | ~ r2_hidden(C_19,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_19,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_256,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_20,plain,(
    ! [A_7,B_8,C_9] :
      ( ~ v2_struct_0(k3_yellow19(A_7,B_8,C_9))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_8))))
      | ~ v13_waybel_0(C_9,k3_yellow_1(B_8))
      | ~ v2_waybel_0(C_9,k3_yellow_1(B_8))
      | v1_xboole_0(C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_7)))
      | v1_xboole_0(B_8)
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_261,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_256,c_20])).

tff(c_264,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_40,c_38,c_36,c_261])).

tff(c_265,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_97,c_44,c_264])).

tff(c_269,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_265])).

tff(c_273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_269])).

tff(c_275,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_235,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_28,plain,(
    ! [C_19,A_13,B_17] :
      ( r2_hidden(C_19,k10_yellow_6(A_13,B_17))
      | ~ r2_waybel_7(A_13,k2_yellow19(A_13,B_17),C_19)
      | ~ m1_subset_1(C_19,u1_struct_0(A_13))
      | ~ l1_waybel_0(B_17,A_13)
      | ~ v7_waybel_0(B_17)
      | ~ v4_orders_2(B_17)
      | v2_struct_0(B_17)
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_202,plain,(
    ! [C_19] :
      ( r2_hidden(C_19,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_19)
      | ~ m1_subset_1(C_19,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_28])).

tff(c_209,plain,(
    ! [C_19] :
      ( r2_hidden(C_19,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_19)
      | ~ m1_subset_1(C_19,u1_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_125,c_184,c_202])).

tff(c_210,plain,(
    ! [C_19] :
      ( r2_hidden(C_19,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_19)
      | ~ m1_subset_1(C_19,u1_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_209])).

tff(c_279,plain,(
    ! [C_19] :
      ( r2_hidden(C_19,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_19)
      | ~ m1_subset_1(C_19,u1_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_210])).

tff(c_281,plain,(
    ! [C_71] :
      ( r2_hidden(C_71,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_71)
      | ~ m1_subset_1(C_71,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_279])).

tff(c_287,plain,
    ( ~ r2_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_281,c_62])).

tff(c_292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_63,c_287])).

tff(c_293,plain,(
    ~ r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_294,plain,(
    r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_304,plain,(
    ! [A_81,B_82,C_83] :
      ( v4_orders_2(k3_yellow19(A_81,B_82,C_83))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_82))))
      | ~ v13_waybel_0(C_83,k3_yellow_1(B_82))
      | ~ v2_waybel_0(C_83,k3_yellow_1(B_82))
      | v1_xboole_0(C_83)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | v1_xboole_0(B_82)
      | ~ l1_struct_0(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_309,plain,(
    ! [A_81] :
      ( v4_orders_2(k3_yellow19(A_81,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_81)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_81)
      | v2_struct_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_36,c_304])).

tff(c_313,plain,(
    ! [A_81] :
      ( v4_orders_2(k3_yellow19(A_81,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_81)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_81)
      | v2_struct_0(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_309])).

tff(c_314,plain,(
    ! [A_81] :
      ( v4_orders_2(k3_yellow19(A_81,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_81)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_81)
      | v2_struct_0(A_81) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_313])).

tff(c_315,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_314])).

tff(c_329,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_315,c_6])).

tff(c_332,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_329])).

tff(c_335,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_332])).

tff(c_339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_335])).

tff(c_342,plain,(
    ! [A_87] :
      ( v4_orders_2(k3_yellow19(A_87,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_struct_0(A_87)
      | v2_struct_0(A_87) ) ),
    inference(splitRight,[status(thm)],[c_314])).

tff(c_346,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_342])).

tff(c_349,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_346])).

tff(c_350,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_349])).

tff(c_353,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_350])).

tff(c_357,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_353])).

tff(c_359,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_341,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_314])).

tff(c_358,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_418,plain,(
    ! [A_100,B_101,C_102] :
      ( v7_waybel_0(k3_yellow19(A_100,B_101,C_102))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_101))))
      | ~ v13_waybel_0(C_102,k3_yellow_1(B_101))
      | ~ v2_waybel_0(C_102,k3_yellow_1(B_101))
      | ~ v1_subset_1(C_102,u1_struct_0(k3_yellow_1(B_101)))
      | v1_xboole_0(C_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | v1_xboole_0(B_101)
      | ~ l1_struct_0(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_423,plain,(
    ! [A_100] :
      ( v7_waybel_0(k3_yellow19(A_100,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_100)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_100)
      | v2_struct_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_36,c_418])).

tff(c_427,plain,(
    ! [A_100] :
      ( v7_waybel_0(k3_yellow19(A_100,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_100)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_100)
      | v2_struct_0(A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_423])).

tff(c_429,plain,(
    ! [A_103] :
      ( v7_waybel_0(k3_yellow19(A_103,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_struct_0(A_103)
      | v2_struct_0(A_103) ) ),
    inference(negUnitSimplification,[status(thm)],[c_341,c_44,c_427])).

tff(c_433,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_429])).

tff(c_436,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_433])).

tff(c_437,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_436])).

tff(c_399,plain,(
    ! [A_96,B_97,C_98] :
      ( l1_waybel_0(k3_yellow19(A_96,B_97,C_98),A_96)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_97))))
      | ~ v13_waybel_0(C_98,k3_yellow_1(B_97))
      | ~ v2_waybel_0(C_98,k3_yellow_1(B_97))
      | v1_xboole_0(C_98)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | v1_xboole_0(B_97)
      | ~ l1_struct_0(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_404,plain,(
    ! [A_96] :
      ( l1_waybel_0(k3_yellow19(A_96,k2_struct_0('#skF_1'),'#skF_2'),A_96)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_96)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_96)
      | v2_struct_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_36,c_399])).

tff(c_408,plain,(
    ! [A_96] :
      ( l1_waybel_0(k3_yellow19(A_96,k2_struct_0('#skF_1'),'#skF_2'),A_96)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_96)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_96)
      | v2_struct_0(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_404])).

tff(c_410,plain,(
    ! [A_99] :
      ( l1_waybel_0(k3_yellow19(A_99,k2_struct_0('#skF_1'),'#skF_2'),A_99)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_struct_0(A_99)
      | v2_struct_0(A_99) ) ),
    inference(negUnitSimplification,[status(thm)],[c_341,c_44,c_408])).

tff(c_413,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_410])).

tff(c_416,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_413])).

tff(c_417,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_416])).

tff(c_438,plain,(
    ! [A_104,B_105] :
      ( k2_yellow19(A_104,k3_yellow19(A_104,k2_struct_0(A_104),B_105)) = B_105
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_104)))))
      | ~ v13_waybel_0(B_105,k3_yellow_1(k2_struct_0(A_104)))
      | ~ v2_waybel_0(B_105,k3_yellow_1(k2_struct_0(A_104)))
      | ~ v1_subset_1(B_105,u1_struct_0(k3_yellow_1(k2_struct_0(A_104))))
      | v1_xboole_0(B_105)
      | ~ l1_struct_0(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_443,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_438])).

tff(c_447,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_42,c_40,c_38,c_443])).

tff(c_448,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_447])).

tff(c_452,plain,(
    ! [C_19] :
      ( r2_hidden(C_19,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_19)
      | ~ m1_subset_1(C_19,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_28])).

tff(c_459,plain,(
    ! [C_19] :
      ( r2_hidden(C_19,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_19)
      | ~ m1_subset_1(C_19,u1_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_358,c_437,c_417,c_452])).

tff(c_460,plain,(
    ! [C_19] :
      ( r2_hidden(C_19,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_19)
      | ~ m1_subset_1(C_19,u1_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_459])).

tff(c_465,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_460])).

tff(c_468,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_465,c_20])).

tff(c_471,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_40,c_38,c_36,c_468])).

tff(c_472,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_341,c_44,c_471])).

tff(c_476,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_472])).

tff(c_480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_476])).

tff(c_482,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_460])).

tff(c_455,plain,(
    ! [C_19] :
      ( r2_waybel_7('#skF_1','#skF_2',C_19)
      | ~ r2_hidden(C_19,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_19,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_30])).

tff(c_462,plain,(
    ! [C_19] :
      ( r2_waybel_7('#skF_1','#skF_2',C_19)
      | ~ r2_hidden(C_19,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_19,u1_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_358,c_437,c_417,c_455])).

tff(c_463,plain,(
    ! [C_19] :
      ( r2_waybel_7('#skF_1','#skF_2',C_19)
      | ~ r2_hidden(C_19,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_19,u1_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_462])).

tff(c_486,plain,(
    ! [C_109] :
      ( r2_waybel_7('#skF_1','#skF_2',C_109)
      | ~ r2_hidden(C_109,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_109,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_482,c_463])).

tff(c_492,plain,
    ( r2_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_294,c_486])).

tff(c_496,plain,(
    r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_492])).

tff(c_498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_293,c_496])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.42  
% 2.85/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.42  %$ r2_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k10_yellow_6 > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.85/1.42  
% 2.85/1.42  %Foreground sorts:
% 2.85/1.42  
% 2.85/1.42  
% 2.85/1.42  %Background operators:
% 2.85/1.42  
% 2.85/1.42  
% 2.85/1.42  %Foreground operators:
% 2.85/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.85/1.42  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.85/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.42  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 2.85/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.42  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.85/1.42  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.85/1.42  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.85/1.42  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 2.85/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.85/1.42  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.85/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.85/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.85/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.85/1.42  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.85/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.85/1.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.85/1.42  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.85/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.42  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.85/1.42  tff(r2_waybel_7, type, r2_waybel_7: ($i * $i * $i) > $o).
% 2.85/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.42  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.85/1.42  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.85/1.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.85/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.85/1.42  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.85/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.85/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.85/1.42  
% 3.26/1.46  tff(f_193, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, k3_yellow19(A, k2_struct_0(A), B))) <=> r2_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow19)).
% 3.26/1.46  tff(f_33, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.26/1.46  tff(f_29, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 3.26/1.46  tff(f_95, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_yellow19)).
% 3.26/1.46  tff(f_41, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.26/1.46  tff(f_67, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 3.26/1.46  tff(f_166, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 3.26/1.46  tff(f_147, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, B)) <=> r2_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow19)).
% 3.26/1.46  tff(f_123, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow19)).
% 3.26/1.46  tff(c_34, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.26/1.46  tff(c_52, plain, (~r2_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.26/1.46  tff(c_62, plain, (~r2_hidden('#skF_3', k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(splitLeft, [status(thm)], [c_52])).
% 3.26/1.46  tff(c_58, plain, (r2_hidden('#skF_3', k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | r2_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.26/1.46  tff(c_63, plain, (r2_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_58])).
% 3.26/1.46  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.26/1.46  tff(c_4, plain, (![A_2]: (l1_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.26/1.46  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.26/1.46  tff(c_2, plain, (![A_1]: (m1_subset_1(k2_struct_0(A_1), k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.26/1.46  tff(c_44, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.26/1.46  tff(c_40, plain, (v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.26/1.46  tff(c_38, plain, (v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.26/1.46  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.26/1.46  tff(c_71, plain, (![A_39, B_40, C_41]: (v4_orders_2(k3_yellow19(A_39, B_40, C_41)) | ~m1_subset_1(C_41, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_40)))) | ~v13_waybel_0(C_41, k3_yellow_1(B_40)) | ~v2_waybel_0(C_41, k3_yellow_1(B_40)) | v1_xboole_0(C_41) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | v1_xboole_0(B_40) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.26/1.46  tff(c_76, plain, (![A_39]: (v4_orders_2(k3_yellow19(A_39, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_39))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(resolution, [status(thm)], [c_36, c_71])).
% 3.26/1.46  tff(c_80, plain, (![A_39]: (v4_orders_2(k3_yellow19(A_39, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_39))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_76])).
% 3.26/1.46  tff(c_81, plain, (![A_39]: (v4_orders_2(k3_yellow19(A_39, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_39))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(negUnitSimplification, [status(thm)], [c_44, c_80])).
% 3.26/1.46  tff(c_82, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_81])).
% 3.26/1.46  tff(c_6, plain, (![A_3]: (~v1_xboole_0(k2_struct_0(A_3)) | ~l1_struct_0(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.26/1.46  tff(c_85, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_82, c_6])).
% 3.26/1.46  tff(c_88, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_85])).
% 3.26/1.46  tff(c_91, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_88])).
% 3.26/1.46  tff(c_95, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_91])).
% 3.26/1.46  tff(c_98, plain, (![A_42]: (v4_orders_2(k3_yellow19(A_42, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_struct_0(A_42) | v2_struct_0(A_42))), inference(splitRight, [status(thm)], [c_81])).
% 3.26/1.46  tff(c_102, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_98])).
% 3.26/1.46  tff(c_105, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_102])).
% 3.26/1.46  tff(c_106, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_105])).
% 3.26/1.46  tff(c_120, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_106])).
% 3.26/1.46  tff(c_124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_120])).
% 3.26/1.46  tff(c_126, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_105])).
% 3.26/1.46  tff(c_97, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_81])).
% 3.26/1.46  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.26/1.46  tff(c_125, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_105])).
% 3.26/1.46  tff(c_166, plain, (![A_54, B_55, C_56]: (l1_waybel_0(k3_yellow19(A_54, B_55, C_56), A_54) | ~m1_subset_1(C_56, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_55)))) | ~v13_waybel_0(C_56, k3_yellow_1(B_55)) | ~v2_waybel_0(C_56, k3_yellow_1(B_55)) | v1_xboole_0(C_56) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | v1_xboole_0(B_55) | ~l1_struct_0(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.26/1.46  tff(c_171, plain, (![A_54]: (l1_waybel_0(k3_yellow19(A_54, k2_struct_0('#skF_1'), '#skF_2'), A_54) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_54))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_54) | v2_struct_0(A_54))), inference(resolution, [status(thm)], [c_36, c_166])).
% 3.26/1.46  tff(c_175, plain, (![A_54]: (l1_waybel_0(k3_yellow19(A_54, k2_struct_0('#skF_1'), '#skF_2'), A_54) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_54))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_54) | v2_struct_0(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_171])).
% 3.26/1.46  tff(c_177, plain, (![A_57]: (l1_waybel_0(k3_yellow19(A_57, k2_struct_0('#skF_1'), '#skF_2'), A_57) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_struct_0(A_57) | v2_struct_0(A_57))), inference(negUnitSimplification, [status(thm)], [c_97, c_44, c_175])).
% 3.26/1.46  tff(c_180, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_177])).
% 3.26/1.46  tff(c_183, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_180])).
% 3.26/1.46  tff(c_184, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_183])).
% 3.26/1.46  tff(c_42, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.26/1.46  tff(c_185, plain, (![A_58, B_59]: (k2_yellow19(A_58, k3_yellow19(A_58, k2_struct_0(A_58), B_59))=B_59 | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_58))))) | ~v13_waybel_0(B_59, k3_yellow_1(k2_struct_0(A_58))) | ~v2_waybel_0(B_59, k3_yellow_1(k2_struct_0(A_58))) | ~v1_subset_1(B_59, u1_struct_0(k3_yellow_1(k2_struct_0(A_58)))) | v1_xboole_0(B_59) | ~l1_struct_0(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.26/1.46  tff(c_190, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_185])).
% 3.26/1.46  tff(c_194, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_42, c_40, c_38, c_190])).
% 3.26/1.46  tff(c_195, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_194])).
% 3.26/1.46  tff(c_30, plain, (![A_13, B_17, C_19]: (r2_waybel_7(A_13, k2_yellow19(A_13, B_17), C_19) | ~r2_hidden(C_19, k10_yellow_6(A_13, B_17)) | ~m1_subset_1(C_19, u1_struct_0(A_13)) | ~l1_waybel_0(B_17, A_13) | ~v7_waybel_0(B_17) | ~v4_orders_2(B_17) | v2_struct_0(B_17) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.26/1.46  tff(c_199, plain, (![C_19]: (r2_waybel_7('#skF_1', '#skF_2', C_19) | ~r2_hidden(C_19, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_19, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_195, c_30])).
% 3.26/1.46  tff(c_206, plain, (![C_19]: (r2_waybel_7('#skF_1', '#skF_2', C_19) | ~r2_hidden(C_19, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_19, u1_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_125, c_184, c_199])).
% 3.26/1.46  tff(c_207, plain, (![C_19]: (r2_waybel_7('#skF_1', '#skF_2', C_19) | ~r2_hidden(C_19, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_19, u1_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_206])).
% 3.26/1.46  tff(c_212, plain, (~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_207])).
% 3.26/1.46  tff(c_213, plain, (![A_60, B_61, C_62]: (v7_waybel_0(k3_yellow19(A_60, B_61, C_62)) | ~m1_subset_1(C_62, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_61)))) | ~v13_waybel_0(C_62, k3_yellow_1(B_61)) | ~v2_waybel_0(C_62, k3_yellow_1(B_61)) | ~v1_subset_1(C_62, u1_struct_0(k3_yellow_1(B_61))) | v1_xboole_0(C_62) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | v1_xboole_0(B_61) | ~l1_struct_0(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.26/1.46  tff(c_218, plain, (![A_60]: (v7_waybel_0(k3_yellow19(A_60, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_60))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_36, c_213])).
% 3.26/1.46  tff(c_222, plain, (![A_60]: (v7_waybel_0(k3_yellow19(A_60, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_60))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_60) | v2_struct_0(A_60))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_218])).
% 3.26/1.46  tff(c_224, plain, (![A_63]: (v7_waybel_0(k3_yellow19(A_63, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_struct_0(A_63) | v2_struct_0(A_63))), inference(negUnitSimplification, [status(thm)], [c_97, c_44, c_222])).
% 3.26/1.46  tff(c_228, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_224])).
% 3.26/1.46  tff(c_231, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_228])).
% 3.26/1.46  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_212, c_231])).
% 3.26/1.46  tff(c_234, plain, (![C_19]: (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | r2_waybel_7('#skF_1', '#skF_2', C_19) | ~r2_hidden(C_19, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_19, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_207])).
% 3.26/1.46  tff(c_256, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_234])).
% 3.26/1.46  tff(c_20, plain, (![A_7, B_8, C_9]: (~v2_struct_0(k3_yellow19(A_7, B_8, C_9)) | ~m1_subset_1(C_9, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_8)))) | ~v13_waybel_0(C_9, k3_yellow_1(B_8)) | ~v2_waybel_0(C_9, k3_yellow_1(B_8)) | v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_7))) | v1_xboole_0(B_8) | ~l1_struct_0(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.26/1.46  tff(c_261, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_256, c_20])).
% 3.26/1.46  tff(c_264, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_40, c_38, c_36, c_261])).
% 3.26/1.46  tff(c_265, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_97, c_44, c_264])).
% 3.26/1.46  tff(c_269, plain, (~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_265])).
% 3.26/1.46  tff(c_273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_269])).
% 3.26/1.46  tff(c_275, plain, (~v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_234])).
% 3.26/1.46  tff(c_235, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_207])).
% 3.26/1.46  tff(c_28, plain, (![C_19, A_13, B_17]: (r2_hidden(C_19, k10_yellow_6(A_13, B_17)) | ~r2_waybel_7(A_13, k2_yellow19(A_13, B_17), C_19) | ~m1_subset_1(C_19, u1_struct_0(A_13)) | ~l1_waybel_0(B_17, A_13) | ~v7_waybel_0(B_17) | ~v4_orders_2(B_17) | v2_struct_0(B_17) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.26/1.46  tff(c_202, plain, (![C_19]: (r2_hidden(C_19, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_19) | ~m1_subset_1(C_19, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_195, c_28])).
% 3.26/1.46  tff(c_209, plain, (![C_19]: (r2_hidden(C_19, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_19) | ~m1_subset_1(C_19, u1_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_125, c_184, c_202])).
% 3.26/1.46  tff(c_210, plain, (![C_19]: (r2_hidden(C_19, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_19) | ~m1_subset_1(C_19, u1_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_209])).
% 3.26/1.46  tff(c_279, plain, (![C_19]: (r2_hidden(C_19, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_19) | ~m1_subset_1(C_19, u1_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_210])).
% 3.26/1.46  tff(c_281, plain, (![C_71]: (r2_hidden(C_71, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_71) | ~m1_subset_1(C_71, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_275, c_279])).
% 3.26/1.46  tff(c_287, plain, (~r2_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_281, c_62])).
% 3.26/1.46  tff(c_292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_63, c_287])).
% 3.26/1.46  tff(c_293, plain, (~r2_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 3.26/1.46  tff(c_294, plain, (r2_hidden('#skF_3', k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(splitRight, [status(thm)], [c_52])).
% 3.26/1.46  tff(c_304, plain, (![A_81, B_82, C_83]: (v4_orders_2(k3_yellow19(A_81, B_82, C_83)) | ~m1_subset_1(C_83, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_82)))) | ~v13_waybel_0(C_83, k3_yellow_1(B_82)) | ~v2_waybel_0(C_83, k3_yellow_1(B_82)) | v1_xboole_0(C_83) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | v1_xboole_0(B_82) | ~l1_struct_0(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.26/1.46  tff(c_309, plain, (![A_81]: (v4_orders_2(k3_yellow19(A_81, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_81))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_81) | v2_struct_0(A_81))), inference(resolution, [status(thm)], [c_36, c_304])).
% 3.26/1.46  tff(c_313, plain, (![A_81]: (v4_orders_2(k3_yellow19(A_81, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_81))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_81) | v2_struct_0(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_309])).
% 3.26/1.46  tff(c_314, plain, (![A_81]: (v4_orders_2(k3_yellow19(A_81, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_81))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_81) | v2_struct_0(A_81))), inference(negUnitSimplification, [status(thm)], [c_44, c_313])).
% 3.26/1.46  tff(c_315, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_314])).
% 3.26/1.46  tff(c_329, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_315, c_6])).
% 3.26/1.46  tff(c_332, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_329])).
% 3.26/1.46  tff(c_335, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_332])).
% 3.26/1.46  tff(c_339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_335])).
% 3.26/1.46  tff(c_342, plain, (![A_87]: (v4_orders_2(k3_yellow19(A_87, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_struct_0(A_87) | v2_struct_0(A_87))), inference(splitRight, [status(thm)], [c_314])).
% 3.26/1.46  tff(c_346, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_342])).
% 3.26/1.46  tff(c_349, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_346])).
% 3.26/1.46  tff(c_350, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_349])).
% 3.26/1.46  tff(c_353, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_350])).
% 3.26/1.46  tff(c_357, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_353])).
% 3.26/1.46  tff(c_359, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_349])).
% 3.26/1.46  tff(c_341, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_314])).
% 3.26/1.46  tff(c_358, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_349])).
% 3.26/1.46  tff(c_418, plain, (![A_100, B_101, C_102]: (v7_waybel_0(k3_yellow19(A_100, B_101, C_102)) | ~m1_subset_1(C_102, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_101)))) | ~v13_waybel_0(C_102, k3_yellow_1(B_101)) | ~v2_waybel_0(C_102, k3_yellow_1(B_101)) | ~v1_subset_1(C_102, u1_struct_0(k3_yellow_1(B_101))) | v1_xboole_0(C_102) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | v1_xboole_0(B_101) | ~l1_struct_0(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.26/1.46  tff(c_423, plain, (![A_100]: (v7_waybel_0(k3_yellow19(A_100, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_100))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_100) | v2_struct_0(A_100))), inference(resolution, [status(thm)], [c_36, c_418])).
% 3.26/1.46  tff(c_427, plain, (![A_100]: (v7_waybel_0(k3_yellow19(A_100, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_100))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_100) | v2_struct_0(A_100))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_423])).
% 3.26/1.46  tff(c_429, plain, (![A_103]: (v7_waybel_0(k3_yellow19(A_103, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_struct_0(A_103) | v2_struct_0(A_103))), inference(negUnitSimplification, [status(thm)], [c_341, c_44, c_427])).
% 3.26/1.46  tff(c_433, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_429])).
% 3.26/1.46  tff(c_436, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_359, c_433])).
% 3.26/1.46  tff(c_437, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_436])).
% 3.26/1.46  tff(c_399, plain, (![A_96, B_97, C_98]: (l1_waybel_0(k3_yellow19(A_96, B_97, C_98), A_96) | ~m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_97)))) | ~v13_waybel_0(C_98, k3_yellow_1(B_97)) | ~v2_waybel_0(C_98, k3_yellow_1(B_97)) | v1_xboole_0(C_98) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | v1_xboole_0(B_97) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.26/1.46  tff(c_404, plain, (![A_96]: (l1_waybel_0(k3_yellow19(A_96, k2_struct_0('#skF_1'), '#skF_2'), A_96) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_96))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(resolution, [status(thm)], [c_36, c_399])).
% 3.26/1.46  tff(c_408, plain, (![A_96]: (l1_waybel_0(k3_yellow19(A_96, k2_struct_0('#skF_1'), '#skF_2'), A_96) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_96))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_404])).
% 3.26/1.46  tff(c_410, plain, (![A_99]: (l1_waybel_0(k3_yellow19(A_99, k2_struct_0('#skF_1'), '#skF_2'), A_99) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_struct_0(A_99) | v2_struct_0(A_99))), inference(negUnitSimplification, [status(thm)], [c_341, c_44, c_408])).
% 3.26/1.46  tff(c_413, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_410])).
% 3.26/1.46  tff(c_416, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_359, c_413])).
% 3.26/1.46  tff(c_417, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_416])).
% 3.26/1.46  tff(c_438, plain, (![A_104, B_105]: (k2_yellow19(A_104, k3_yellow19(A_104, k2_struct_0(A_104), B_105))=B_105 | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_104))))) | ~v13_waybel_0(B_105, k3_yellow_1(k2_struct_0(A_104))) | ~v2_waybel_0(B_105, k3_yellow_1(k2_struct_0(A_104))) | ~v1_subset_1(B_105, u1_struct_0(k3_yellow_1(k2_struct_0(A_104)))) | v1_xboole_0(B_105) | ~l1_struct_0(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.26/1.46  tff(c_443, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_438])).
% 3.26/1.46  tff(c_447, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_359, c_42, c_40, c_38, c_443])).
% 3.26/1.46  tff(c_448, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_447])).
% 3.26/1.46  tff(c_452, plain, (![C_19]: (r2_hidden(C_19, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_19) | ~m1_subset_1(C_19, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_448, c_28])).
% 3.26/1.46  tff(c_459, plain, (![C_19]: (r2_hidden(C_19, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_19) | ~m1_subset_1(C_19, u1_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_358, c_437, c_417, c_452])).
% 3.26/1.46  tff(c_460, plain, (![C_19]: (r2_hidden(C_19, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_19) | ~m1_subset_1(C_19, u1_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_459])).
% 3.26/1.46  tff(c_465, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_460])).
% 3.26/1.46  tff(c_468, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_465, c_20])).
% 3.26/1.46  tff(c_471, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_359, c_40, c_38, c_36, c_468])).
% 3.26/1.46  tff(c_472, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_341, c_44, c_471])).
% 3.26/1.46  tff(c_476, plain, (~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_472])).
% 3.26/1.46  tff(c_480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_359, c_476])).
% 3.26/1.46  tff(c_482, plain, (~v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_460])).
% 3.26/1.46  tff(c_455, plain, (![C_19]: (r2_waybel_7('#skF_1', '#skF_2', C_19) | ~r2_hidden(C_19, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_19, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_448, c_30])).
% 3.26/1.46  tff(c_462, plain, (![C_19]: (r2_waybel_7('#skF_1', '#skF_2', C_19) | ~r2_hidden(C_19, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_19, u1_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_358, c_437, c_417, c_455])).
% 3.26/1.46  tff(c_463, plain, (![C_19]: (r2_waybel_7('#skF_1', '#skF_2', C_19) | ~r2_hidden(C_19, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_19, u1_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_462])).
% 3.26/1.46  tff(c_486, plain, (![C_109]: (r2_waybel_7('#skF_1', '#skF_2', C_109) | ~r2_hidden(C_109, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_109, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_482, c_463])).
% 3.26/1.46  tff(c_492, plain, (r2_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_294, c_486])).
% 3.26/1.46  tff(c_496, plain, (r2_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_492])).
% 3.26/1.46  tff(c_498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_293, c_496])).
% 3.26/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.46  
% 3.26/1.46  Inference rules
% 3.26/1.46  ----------------------
% 3.26/1.46  #Ref     : 0
% 3.26/1.46  #Sup     : 65
% 3.26/1.46  #Fact    : 0
% 3.26/1.46  #Define  : 0
% 3.26/1.46  #Split   : 10
% 3.26/1.46  #Chain   : 0
% 3.26/1.46  #Close   : 0
% 3.26/1.46  
% 3.26/1.46  Ordering : KBO
% 3.26/1.46  
% 3.26/1.46  Simplification rules
% 3.26/1.46  ----------------------
% 3.26/1.46  #Subsume      : 5
% 3.26/1.46  #Demod        : 87
% 3.26/1.46  #Tautology    : 14
% 3.26/1.46  #SimpNegUnit  : 39
% 3.26/1.46  #BackRed      : 0
% 3.26/1.46  
% 3.26/1.46  #Partial instantiations: 0
% 3.26/1.46  #Strategies tried      : 1
% 3.26/1.46  
% 3.26/1.46  Timing (in seconds)
% 3.26/1.46  ----------------------
% 3.26/1.46  Preprocessing        : 0.33
% 3.26/1.46  Parsing              : 0.18
% 3.26/1.46  CNF conversion       : 0.02
% 3.26/1.46  Main loop            : 0.33
% 3.26/1.46  Inferencing          : 0.12
% 3.26/1.46  Reduction            : 0.10
% 3.26/1.46  Demodulation         : 0.07
% 3.26/1.46  BG Simplification    : 0.02
% 3.26/1.46  Subsumption          : 0.06
% 3.26/1.46  Abstraction          : 0.01
% 3.26/1.46  MUC search           : 0.00
% 3.26/1.46  Cooper               : 0.00
% 3.26/1.46  Total                : 0.73
% 3.26/1.46  Index Insertion      : 0.00
% 3.26/1.46  Index Deletion       : 0.00
% 3.26/1.46  Index Matching       : 0.00
% 3.26/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
