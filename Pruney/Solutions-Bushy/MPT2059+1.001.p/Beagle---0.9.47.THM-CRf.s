%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2059+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:49 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :  168 (1397 expanded)
%              Number of leaves         :   38 ( 504 expanded)
%              Depth                    :   20
%              Number of atoms          :  538 (7655 expanded)
%              Number of equality atoms :    9 (  30 expanded)
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

tff(f_192,negated_conjecture,(
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

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_28,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_86,axiom,(
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

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_122,axiom,(
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

tff(f_54,axiom,(
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

tff(f_165,axiom,(
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

tff(f_146,axiom,(
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

tff(c_34,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_52,plain,
    ( ~ r2_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_62,plain,(
    ~ r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,
    ( r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
    | r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_63,plain,(
    r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_10,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_2,plain,(
    ! [A_1] :
      ( m1_subset_1(k2_struct_0(A_1),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_40,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_38,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_70,plain,(
    ! [A_36,B_37,C_38] :
      ( v3_orders_2(k3_yellow19(A_36,B_37,C_38))
      | ~ m1_subset_1(C_38,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_37))))
      | ~ v13_waybel_0(C_38,k3_yellow_1(B_37))
      | ~ v2_waybel_0(C_38,k3_yellow_1(B_37))
      | v1_xboole_0(C_38)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | v1_xboole_0(B_37)
      | ~ l1_struct_0(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_75,plain,(
    ! [A_36] :
      ( v3_orders_2(k3_yellow19(A_36,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_36)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_36)
      | v2_struct_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_36,c_70])).

tff(c_79,plain,(
    ! [A_36] :
      ( v3_orders_2(k3_yellow19(A_36,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_36)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_36)
      | v2_struct_0(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_75])).

tff(c_80,plain,(
    ! [A_36] :
      ( v3_orders_2(k3_yellow19(A_36,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_36)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_36)
      | v2_struct_0(A_36) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_79])).

tff(c_81,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_20,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k2_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_84,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_81,c_20])).

tff(c_87,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_84])).

tff(c_90,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_87])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_90])).

tff(c_97,plain,(
    ! [A_39] :
      ( v3_orders_2(k3_yellow19(A_39,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_101,plain,
    ( v3_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_97])).

tff(c_104,plain,
    ( v3_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_101])).

tff(c_105,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_108,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_105])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_108])).

tff(c_114,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_96,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_116,plain,(
    ! [A_43,B_44,C_45] :
      ( v4_orders_2(k3_yellow19(A_43,B_44,C_45))
      | ~ m1_subset_1(C_45,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_44))))
      | ~ v13_waybel_0(C_45,k3_yellow_1(B_44))
      | ~ v2_waybel_0(C_45,k3_yellow_1(B_44))
      | v1_xboole_0(C_45)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | v1_xboole_0(B_44)
      | ~ l1_struct_0(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_121,plain,(
    ! [A_43] :
      ( v4_orders_2(k3_yellow19(A_43,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_43)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_43)
      | v2_struct_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_36,c_116])).

tff(c_125,plain,(
    ! [A_43] :
      ( v4_orders_2(k3_yellow19(A_43,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_43)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_43)
      | v2_struct_0(A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_121])).

tff(c_127,plain,(
    ! [A_46] :
      ( v4_orders_2(k3_yellow19(A_46,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_struct_0(A_46)
      | v2_struct_0(A_46) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_44,c_125])).

tff(c_131,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_127])).

tff(c_134,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_131])).

tff(c_135,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_134])).

tff(c_42,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_166,plain,(
    ! [A_54,B_55,C_56] :
      ( v7_waybel_0(k3_yellow19(A_54,B_55,C_56))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_55))))
      | ~ v13_waybel_0(C_56,k3_yellow_1(B_55))
      | ~ v2_waybel_0(C_56,k3_yellow_1(B_55))
      | ~ v1_subset_1(C_56,u1_struct_0(k3_yellow_1(B_55)))
      | v1_xboole_0(C_56)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | v1_xboole_0(B_55)
      | ~ l1_struct_0(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_171,plain,(
    ! [A_54] :
      ( v7_waybel_0(k3_yellow19(A_54,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_54)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_54)
      | v2_struct_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_36,c_166])).

tff(c_175,plain,(
    ! [A_54] :
      ( v7_waybel_0(k3_yellow19(A_54,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_54)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_54)
      | v2_struct_0(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_171])).

tff(c_177,plain,(
    ! [A_57] :
      ( v7_waybel_0(k3_yellow19(A_57,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_struct_0(A_57)
      | v2_struct_0(A_57) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_44,c_175])).

tff(c_181,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_177])).

tff(c_184,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_181])).

tff(c_185,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_184])).

tff(c_155,plain,(
    ! [A_51,B_52,C_53] :
      ( l1_waybel_0(k3_yellow19(A_51,B_52,C_53),A_51)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_52))))
      | ~ v13_waybel_0(C_53,k3_yellow_1(B_52))
      | ~ v2_waybel_0(C_53,k3_yellow_1(B_52))
      | v1_xboole_0(C_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | v1_xboole_0(B_52)
      | ~ l1_struct_0(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_160,plain,(
    ! [A_51] :
      ( l1_waybel_0(k3_yellow19(A_51,k2_struct_0('#skF_1'),'#skF_2'),A_51)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_51)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_51)
      | v2_struct_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_36,c_155])).

tff(c_164,plain,(
    ! [A_51] :
      ( l1_waybel_0(k3_yellow19(A_51,k2_struct_0('#skF_1'),'#skF_2'),A_51)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_51)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_51)
      | v2_struct_0(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_160])).

tff(c_186,plain,(
    ! [A_58] :
      ( l1_waybel_0(k3_yellow19(A_58,k2_struct_0('#skF_1'),'#skF_2'),A_58)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_44,c_164])).

tff(c_189,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_186])).

tff(c_192,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_189])).

tff(c_193,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_192])).

tff(c_194,plain,(
    ! [A_59,B_60] :
      ( k2_yellow19(A_59,k3_yellow19(A_59,k2_struct_0(A_59),B_60)) = B_60
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_59)))))
      | ~ v13_waybel_0(B_60,k3_yellow_1(k2_struct_0(A_59)))
      | ~ v2_waybel_0(B_60,k3_yellow_1(k2_struct_0(A_59)))
      | ~ v1_subset_1(B_60,u1_struct_0(k3_yellow_1(k2_struct_0(A_59))))
      | v1_xboole_0(B_60)
      | ~ l1_struct_0(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_199,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_194])).

tff(c_203,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_42,c_40,c_38,c_199])).

tff(c_204,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_203])).

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
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_208,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_204,c_30])).

tff(c_215,plain,(
    ! [C_19] :
      ( r2_waybel_7('#skF_1','#skF_2',C_19)
      | ~ r2_hidden(C_19,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_19,u1_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_135,c_185,c_193,c_208])).

tff(c_216,plain,(
    ! [C_19] :
      ( r2_waybel_7('#skF_1','#skF_2',C_19)
      | ~ r2_hidden(C_19,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_19,u1_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_215])).

tff(c_221,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_18,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ v2_struct_0(k3_yellow19(A_6,B_7,C_8))
      | ~ m1_subset_1(C_8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_7))))
      | ~ v13_waybel_0(C_8,k3_yellow_1(B_7))
      | ~ v2_waybel_0(C_8,k3_yellow_1(B_7))
      | v1_xboole_0(C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | v1_xboole_0(B_7)
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_223,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_221,c_18])).

tff(c_226,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_40,c_38,c_36,c_223])).

tff(c_227,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_96,c_44,c_226])).

tff(c_230,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_227])).

tff(c_234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_230])).

tff(c_236,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_216])).

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
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_211,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_204,c_28])).

tff(c_218,plain,(
    ! [C_19] :
      ( r2_hidden(C_19,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_19)
      | ~ m1_subset_1(C_19,u1_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_135,c_185,c_193,c_211])).

tff(c_219,plain,(
    ! [C_19] :
      ( r2_hidden(C_19,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_19)
      | ~ m1_subset_1(C_19,u1_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_218])).

tff(c_240,plain,(
    ! [C_64] :
      ( r2_hidden(C_64,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_64)
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_219])).

tff(c_246,plain,
    ( ~ r2_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_240,c_62])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_63,c_246])).

tff(c_252,plain,(
    ~ r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_253,plain,(
    r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_265,plain,(
    ! [A_71,B_72,C_73] :
      ( v4_orders_2(k3_yellow19(A_71,B_72,C_73))
      | ~ m1_subset_1(C_73,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_72))))
      | ~ v13_waybel_0(C_73,k3_yellow_1(B_72))
      | ~ v2_waybel_0(C_73,k3_yellow_1(B_72))
      | v1_xboole_0(C_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | v1_xboole_0(B_72)
      | ~ l1_struct_0(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_270,plain,(
    ! [A_71] :
      ( v4_orders_2(k3_yellow19(A_71,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_71)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_71)
      | v2_struct_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_36,c_265])).

tff(c_274,plain,(
    ! [A_71] :
      ( v4_orders_2(k3_yellow19(A_71,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_71)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_71)
      | v2_struct_0(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_270])).

tff(c_275,plain,(
    ! [A_71] :
      ( v4_orders_2(k3_yellow19(A_71,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_71)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_71)
      | v2_struct_0(A_71) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_274])).

tff(c_276,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_275])).

tff(c_279,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_276,c_20])).

tff(c_282,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_279])).

tff(c_285,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_282])).

tff(c_289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_285])).

tff(c_292,plain,(
    ! [A_74] :
      ( v4_orders_2(k3_yellow19(A_74,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_struct_0(A_74)
      | v2_struct_0(A_74) ) ),
    inference(splitRight,[status(thm)],[c_275])).

tff(c_296,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_292])).

tff(c_299,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_296])).

tff(c_300,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_304,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_300])).

tff(c_308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_304])).

tff(c_310,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_291,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_275])).

tff(c_309,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_332,plain,(
    ! [A_85,B_86,C_87] :
      ( l1_waybel_0(k3_yellow19(A_85,B_86,C_87),A_85)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_86))))
      | ~ v13_waybel_0(C_87,k3_yellow_1(B_86))
      | ~ v2_waybel_0(C_87,k3_yellow_1(B_86))
      | v1_xboole_0(C_87)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | v1_xboole_0(B_86)
      | ~ l1_struct_0(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_337,plain,(
    ! [A_85] :
      ( l1_waybel_0(k3_yellow19(A_85,k2_struct_0('#skF_1'),'#skF_2'),A_85)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_85)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_85)
      | v2_struct_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_36,c_332])).

tff(c_341,plain,(
    ! [A_85] :
      ( l1_waybel_0(k3_yellow19(A_85,k2_struct_0('#skF_1'),'#skF_2'),A_85)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_85)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_85)
      | v2_struct_0(A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_337])).

tff(c_343,plain,(
    ! [A_88] :
      ( l1_waybel_0(k3_yellow19(A_88,k2_struct_0('#skF_1'),'#skF_2'),A_88)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_struct_0(A_88)
      | v2_struct_0(A_88) ) ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_44,c_341])).

tff(c_346,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_343])).

tff(c_349,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_346])).

tff(c_350,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_349])).

tff(c_370,plain,(
    ! [A_93,B_94] :
      ( k2_yellow19(A_93,k3_yellow19(A_93,k2_struct_0(A_93),B_94)) = B_94
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_93)))))
      | ~ v13_waybel_0(B_94,k3_yellow_1(k2_struct_0(A_93)))
      | ~ v2_waybel_0(B_94,k3_yellow_1(k2_struct_0(A_93)))
      | ~ v1_subset_1(B_94,u1_struct_0(k3_yellow_1(k2_struct_0(A_93))))
      | v1_xboole_0(B_94)
      | ~ l1_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_375,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_370])).

tff(c_379,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_42,c_40,c_38,c_375])).

tff(c_380,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_379])).

tff(c_384,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_380,c_30])).

tff(c_391,plain,(
    ! [C_19] :
      ( r2_waybel_7('#skF_1','#skF_2',C_19)
      | ~ r2_hidden(C_19,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_19,u1_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_309,c_350,c_384])).

tff(c_392,plain,(
    ! [C_19] :
      ( r2_waybel_7('#skF_1','#skF_2',C_19)
      | ~ r2_hidden(C_19,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_19,u1_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_391])).

tff(c_397,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_392])).

tff(c_398,plain,(
    ! [A_95,B_96,C_97] :
      ( v7_waybel_0(k3_yellow19(A_95,B_96,C_97))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_96))))
      | ~ v13_waybel_0(C_97,k3_yellow_1(B_96))
      | ~ v2_waybel_0(C_97,k3_yellow_1(B_96))
      | ~ v1_subset_1(C_97,u1_struct_0(k3_yellow_1(B_96)))
      | v1_xboole_0(C_97)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | v1_xboole_0(B_96)
      | ~ l1_struct_0(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_403,plain,(
    ! [A_95] :
      ( v7_waybel_0(k3_yellow19(A_95,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_95)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_95)
      | v2_struct_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_36,c_398])).

tff(c_407,plain,(
    ! [A_95] :
      ( v7_waybel_0(k3_yellow19(A_95,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_95)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_95)
      | v2_struct_0(A_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_403])).

tff(c_409,plain,(
    ! [A_98] :
      ( v7_waybel_0(k3_yellow19(A_98,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_struct_0(A_98)
      | v2_struct_0(A_98) ) ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_44,c_407])).

tff(c_413,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_409])).

tff(c_416,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_413])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_397,c_416])).

tff(c_419,plain,(
    ! [C_19] :
      ( v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | r2_waybel_7('#skF_1','#skF_2',C_19)
      | ~ r2_hidden(C_19,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_19,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_392])).

tff(c_421,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_419])).

tff(c_423,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_421,c_18])).

tff(c_426,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_40,c_38,c_36,c_423])).

tff(c_427,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_291,c_44,c_426])).

tff(c_430,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_427])).

tff(c_434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_430])).

tff(c_437,plain,(
    ! [C_99] :
      ( r2_waybel_7('#skF_1','#skF_2',C_99)
      | ~ r2_hidden(C_99,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_99,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_419])).

tff(c_440,plain,
    ( r2_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_253,c_437])).

tff(c_443,plain,(
    r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_440])).

tff(c_445,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_252,c_443])).

%------------------------------------------------------------------------------
