%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:37 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  162 (2096 expanded)
%              Number of leaves         :   43 ( 753 expanded)
%              Depth                    :   17
%              Number of atoms          :  522 (8181 expanded)
%              Number of equality atoms :   15 ( 479 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k10_yellow_6 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1

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
               => ( r2_hidden(C,k10_yellow_6(A,k3_yellow19(A,k2_struct_0(A),B)))
                <=> r2_waybel_7(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow19)).

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
             => ( r2_hidden(C,k10_yellow_6(A,B))
              <=> r2_waybel_7(A,k2_yellow19(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow19)).

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

tff(c_58,plain,
    ( ~ r2_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_122,plain,(
    ~ r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,
    ( r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
    | r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_123,plain,(
    r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_64])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_101,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(u1_struct_0(A_36))
      | ~ l1_struct_0(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_104,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_101])).

tff(c_105,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_104])).

tff(c_106,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_110,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_106])).

tff(c_114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_110])).

tff(c_115,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_116,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_65,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_46,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_44,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_149,plain,(
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

tff(c_151,plain,(
    ! [A_50] :
      ( v4_orders_2(k3_yellow19(A_50,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_50)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_50)
      | v2_struct_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_42,c_149])).

tff(c_157,plain,(
    ! [A_50] :
      ( v4_orders_2(k3_yellow19(A_50,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_50)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_50)
      | v2_struct_0(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_151])).

tff(c_160,plain,(
    ! [A_53] :
      ( v4_orders_2(k3_yellow19(A_53,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_struct_0(A_53)
      | v2_struct_0(A_53) ) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_50,c_157])).

tff(c_163,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_160])).

tff(c_165,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_65,c_163])).

tff(c_166,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_165])).

tff(c_167,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_169,plain,(
    ! [A_54] :
      ( l1_waybel_0(k3_yellow19(A_54,k2_struct_0('#skF_1'),'#skF_2'),A_54)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_54)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_54)
      | v2_struct_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_42,c_167])).

tff(c_175,plain,(
    ! [A_54] :
      ( l1_waybel_0(k3_yellow19(A_54,k2_struct_0('#skF_1'),'#skF_2'),A_54)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_54)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_54)
      | v2_struct_0(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_169])).

tff(c_178,plain,(
    ! [A_57] :
      ( l1_waybel_0(k3_yellow19(A_57,k2_struct_0('#skF_1'),'#skF_2'),A_57)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_struct_0(A_57)
      | v2_struct_0(A_57) ) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_50,c_175])).

tff(c_180,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_178])).

tff(c_182,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_65,c_180])).

tff(c_183,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_182])).

tff(c_48,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_205,plain,(
    ! [A_70,B_71] :
      ( k2_yellow19(A_70,k3_yellow19(A_70,k2_struct_0(A_70),B_71)) = B_71
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_70)))))
      | ~ v13_waybel_0(B_71,k3_yellow_1(k2_struct_0(A_70)))
      | ~ v2_waybel_0(B_71,k3_yellow_1(k2_struct_0(A_70)))
      | ~ v1_subset_1(B_71,u1_struct_0(k3_yellow_1(k2_struct_0(A_70))))
      | v1_xboole_0(B_71)
      | ~ l1_struct_0(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_207,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_205])).

tff(c_213,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_48,c_46,c_44,c_207])).

tff(c_214,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_213])).

tff(c_36,plain,(
    ! [A_16,B_20,C_22] :
      ( r2_waybel_7(A_16,k2_yellow19(A_16,B_20),C_22)
      | ~ r2_hidden(C_22,k10_yellow_6(A_16,B_20))
      | ~ m1_subset_1(C_22,u1_struct_0(A_16))
      | ~ l1_waybel_0(B_20,A_16)
      | ~ v7_waybel_0(B_20)
      | ~ v4_orders_2(B_20)
      | v2_struct_0(B_20)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_219,plain,(
    ! [C_22] :
      ( r2_waybel_7('#skF_1','#skF_2',C_22)
      | ~ r2_hidden(C_22,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_22,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_36])).

tff(c_226,plain,(
    ! [C_22] :
      ( r2_waybel_7('#skF_1','#skF_2',C_22)
      | ~ r2_hidden(C_22,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_22,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_166,c_183,c_95,c_219])).

tff(c_227,plain,(
    ! [C_22] :
      ( r2_waybel_7('#skF_1','#skF_2',C_22)
      | ~ r2_hidden(C_22,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_22,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_226])).

tff(c_232,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_233,plain,(
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

tff(c_235,plain,(
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
    inference(resolution,[status(thm)],[c_42,c_233])).

tff(c_241,plain,(
    ! [A_72] :
      ( v7_waybel_0(k3_yellow19(A_72,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_72)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_72)
      | v2_struct_0(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_235])).

tff(c_244,plain,(
    ! [A_75] :
      ( v7_waybel_0(k3_yellow19(A_75,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_struct_0(A_75)
      | v2_struct_0(A_75) ) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_50,c_241])).

tff(c_247,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_244])).

tff(c_249,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_65,c_247])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_232,c_249])).

tff(c_252,plain,(
    ! [C_22] :
      ( v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | r2_waybel_7('#skF_1','#skF_2',C_22)
      | ~ r2_hidden(C_22,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_22,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_254,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_252])).

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

tff(c_256,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_254,c_26])).

tff(c_259,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_65,c_95,c_46,c_44,c_42,c_256])).

tff(c_261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_115,c_50,c_259])).

tff(c_263,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_253,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_34,plain,(
    ! [C_22,A_16,B_20] :
      ( r2_hidden(C_22,k10_yellow_6(A_16,B_20))
      | ~ r2_waybel_7(A_16,k2_yellow19(A_16,B_20),C_22)
      | ~ m1_subset_1(C_22,u1_struct_0(A_16))
      | ~ l1_waybel_0(B_20,A_16)
      | ~ v7_waybel_0(B_20)
      | ~ v4_orders_2(B_20)
      | v2_struct_0(B_20)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_222,plain,(
    ! [C_22] :
      ( r2_hidden(C_22,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_22)
      | ~ m1_subset_1(C_22,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_34])).

tff(c_229,plain,(
    ! [C_22] :
      ( r2_hidden(C_22,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_22)
      | ~ m1_subset_1(C_22,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_166,c_183,c_95,c_222])).

tff(c_230,plain,(
    ! [C_22] :
      ( r2_hidden(C_22,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_22)
      | ~ m1_subset_1(C_22,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_229])).

tff(c_284,plain,(
    ! [C_22] :
      ( r2_hidden(C_22,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_22)
      | ~ m1_subset_1(C_22,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_230])).

tff(c_286,plain,(
    ! [C_81] :
      ( r2_hidden(C_81,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_81)
      | ~ m1_subset_1(C_81,k2_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_263,c_284])).

tff(c_292,plain,
    ( ~ r2_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_286,c_122])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_123,c_292])).

tff(c_298,plain,(
    ~ r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_299,plain,(
    r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_327,plain,(
    ! [A_95,B_96,C_97] :
      ( v4_orders_2(k3_yellow19(A_95,B_96,C_97))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_96))))
      | ~ v13_waybel_0(C_97,k3_yellow_1(B_96))
      | ~ v2_waybel_0(C_97,k3_yellow_1(B_96))
      | v1_xboole_0(C_97)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | v1_xboole_0(B_96)
      | ~ l1_struct_0(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_329,plain,(
    ! [A_95] :
      ( v4_orders_2(k3_yellow19(A_95,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_95)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_95)
      | v2_struct_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_42,c_327])).

tff(c_335,plain,(
    ! [A_95] :
      ( v4_orders_2(k3_yellow19(A_95,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_95)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_95)
      | v2_struct_0(A_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_329])).

tff(c_338,plain,(
    ! [A_98] :
      ( v4_orders_2(k3_yellow19(A_98,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_struct_0(A_98)
      | v2_struct_0(A_98) ) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_50,c_335])).

tff(c_341,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_338])).

tff(c_343,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_65,c_341])).

tff(c_344,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_343])).

tff(c_380,plain,(
    ! [A_109,B_110,C_111] :
      ( v7_waybel_0(k3_yellow19(A_109,B_110,C_111))
      | ~ m1_subset_1(C_111,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_110))))
      | ~ v13_waybel_0(C_111,k3_yellow_1(B_110))
      | ~ v2_waybel_0(C_111,k3_yellow_1(B_110))
      | ~ v1_subset_1(C_111,u1_struct_0(k3_yellow_1(B_110)))
      | v1_xboole_0(C_111)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | v1_xboole_0(B_110)
      | ~ l1_struct_0(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_382,plain,(
    ! [A_109] :
      ( v7_waybel_0(k3_yellow19(A_109,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_109)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_109)
      | v2_struct_0(A_109) ) ),
    inference(resolution,[status(thm)],[c_42,c_380])).

tff(c_388,plain,(
    ! [A_109] :
      ( v7_waybel_0(k3_yellow19(A_109,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_109)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_109)
      | v2_struct_0(A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_382])).

tff(c_391,plain,(
    ! [A_112] :
      ( v7_waybel_0(k3_yellow19(A_112,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_struct_0(A_112)
      | v2_struct_0(A_112) ) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_50,c_388])).

tff(c_394,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_391])).

tff(c_396,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_65,c_394])).

tff(c_397,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_396])).

tff(c_362,plain,(
    ! [A_103,B_104,C_105] :
      ( l1_waybel_0(k3_yellow19(A_103,B_104,C_105),A_103)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_104))))
      | ~ v13_waybel_0(C_105,k3_yellow_1(B_104))
      | ~ v2_waybel_0(C_105,k3_yellow_1(B_104))
      | v1_xboole_0(C_105)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | v1_xboole_0(B_104)
      | ~ l1_struct_0(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_364,plain,(
    ! [A_103] :
      ( l1_waybel_0(k3_yellow19(A_103,k2_struct_0('#skF_1'),'#skF_2'),A_103)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_103)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_103)
      | v2_struct_0(A_103) ) ),
    inference(resolution,[status(thm)],[c_42,c_362])).

tff(c_370,plain,(
    ! [A_103] :
      ( l1_waybel_0(k3_yellow19(A_103,k2_struct_0('#skF_1'),'#skF_2'),A_103)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_103)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_103)
      | v2_struct_0(A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_364])).

tff(c_373,plain,(
    ! [A_106] :
      ( l1_waybel_0(k3_yellow19(A_106,k2_struct_0('#skF_1'),'#skF_2'),A_106)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_struct_0(A_106)
      | v2_struct_0(A_106) ) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_50,c_370])).

tff(c_375,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_373])).

tff(c_377,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_65,c_375])).

tff(c_378,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_377])).

tff(c_401,plain,(
    ! [A_119,B_120] :
      ( k2_yellow19(A_119,k3_yellow19(A_119,k2_struct_0(A_119),B_120)) = B_120
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_119)))))
      | ~ v13_waybel_0(B_120,k3_yellow_1(k2_struct_0(A_119)))
      | ~ v2_waybel_0(B_120,k3_yellow_1(k2_struct_0(A_119)))
      | ~ v1_subset_1(B_120,u1_struct_0(k3_yellow_1(k2_struct_0(A_119))))
      | v1_xboole_0(B_120)
      | ~ l1_struct_0(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_403,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_401])).

tff(c_409,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_48,c_46,c_44,c_403])).

tff(c_410,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_409])).

tff(c_415,plain,(
    ! [C_22] :
      ( r2_hidden(C_22,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_22)
      | ~ m1_subset_1(C_22,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_34])).

tff(c_422,plain,(
    ! [C_22] :
      ( r2_hidden(C_22,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_22)
      | ~ m1_subset_1(C_22,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_344,c_397,c_378,c_95,c_415])).

tff(c_423,plain,(
    ! [C_22] :
      ( r2_hidden(C_22,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_22)
      | ~ m1_subset_1(C_22,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_422])).

tff(c_428,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_423])).

tff(c_430,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_428,c_26])).

tff(c_433,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_65,c_95,c_46,c_44,c_42,c_430])).

tff(c_435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_115,c_50,c_433])).

tff(c_437,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_423])).

tff(c_418,plain,(
    ! [C_22] :
      ( r2_waybel_7('#skF_1','#skF_2',C_22)
      | ~ r2_hidden(C_22,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_22,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_36])).

tff(c_425,plain,(
    ! [C_22] :
      ( r2_waybel_7('#skF_1','#skF_2',C_22)
      | ~ r2_hidden(C_22,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_22,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_344,c_397,c_378,c_95,c_418])).

tff(c_426,plain,(
    ! [C_22] :
      ( r2_waybel_7('#skF_1','#skF_2',C_22)
      | ~ r2_hidden(C_22,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_22,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_425])).

tff(c_438,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_426])).

tff(c_439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_437,c_438])).

tff(c_442,plain,(
    ! [C_121] :
      ( r2_waybel_7('#skF_1','#skF_2',C_121)
      | ~ r2_hidden(C_121,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_121,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_426])).

tff(c_445,plain,
    ( r2_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_299,c_442])).

tff(c_448,plain,(
    r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_445])).

tff(c_450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_298,c_448])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:30:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.44  
% 2.87/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.45  %$ r2_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k10_yellow_6 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1
% 2.87/1.45  
% 2.87/1.45  %Foreground sorts:
% 2.87/1.45  
% 2.87/1.45  
% 2.87/1.45  %Background operators:
% 2.87/1.45  
% 2.87/1.45  
% 2.87/1.45  %Foreground operators:
% 2.87/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.87/1.45  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.87/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.45  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.87/1.45  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 2.87/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.45  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.87/1.45  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.87/1.45  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.87/1.45  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 2.87/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.87/1.45  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.87/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.87/1.45  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.87/1.45  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.87/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.87/1.45  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.87/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.45  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.87/1.45  tff(r2_waybel_7, type, r2_waybel_7: ($i * $i * $i) > $o).
% 2.87/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.45  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.87/1.45  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.87/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.87/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.87/1.45  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.87/1.45  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.87/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.87/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.45  
% 3.29/1.47  tff(f_199, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, k3_yellow19(A, k2_struct_0(A), B))) <=> r2_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_yellow19)).
% 3.29/1.47  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.29/1.47  tff(f_33, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.29/1.47  tff(f_45, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.29/1.47  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.29/1.47  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.29/1.47  tff(f_101, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_yellow19)).
% 3.29/1.47  tff(f_73, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 3.29/1.47  tff(f_172, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 3.29/1.47  tff(f_153, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, B)) <=> r2_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow19)).
% 3.29/1.47  tff(f_129, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow19)).
% 3.29/1.47  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.29/1.47  tff(c_8, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.29/1.47  tff(c_86, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.29/1.47  tff(c_91, plain, (![A_35]: (u1_struct_0(A_35)=k2_struct_0(A_35) | ~l1_pre_topc(A_35))), inference(resolution, [status(thm)], [c_8, c_86])).
% 3.29/1.47  tff(c_95, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_91])).
% 3.29/1.47  tff(c_40, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.29/1.47  tff(c_96, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_40])).
% 3.29/1.47  tff(c_58, plain, (~r2_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.29/1.47  tff(c_122, plain, (~r2_hidden('#skF_3', k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(splitLeft, [status(thm)], [c_58])).
% 3.29/1.47  tff(c_64, plain, (r2_hidden('#skF_3', k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | r2_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.29/1.47  tff(c_123, plain, (r2_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_122, c_64])).
% 3.29/1.47  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.29/1.47  tff(c_101, plain, (![A_36]: (~v1_xboole_0(u1_struct_0(A_36)) | ~l1_struct_0(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.29/1.47  tff(c_104, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_95, c_101])).
% 3.29/1.47  tff(c_105, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_104])).
% 3.29/1.47  tff(c_106, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_105])).
% 3.29/1.47  tff(c_110, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_106])).
% 3.29/1.47  tff(c_114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_110])).
% 3.29/1.47  tff(c_115, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_105])).
% 3.29/1.47  tff(c_50, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.29/1.47  tff(c_116, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_105])).
% 3.29/1.47  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.29/1.47  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.29/1.47  tff(c_65, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.29/1.47  tff(c_46, plain, (v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.29/1.47  tff(c_44, plain, (v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.29/1.47  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.29/1.47  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.29/1.47  tff(c_149, plain, (![A_50, B_51, C_52]: (v4_orders_2(k3_yellow19(A_50, B_51, C_52)) | ~m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_51)))) | ~v13_waybel_0(C_52, k3_yellow_1(B_51)) | ~v2_waybel_0(C_52, k3_yellow_1(B_51)) | v1_xboole_0(C_52) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | v1_xboole_0(B_51) | ~l1_struct_0(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.29/1.47  tff(c_151, plain, (![A_50]: (v4_orders_2(k3_yellow19(A_50, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_50))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_50) | v2_struct_0(A_50))), inference(resolution, [status(thm)], [c_42, c_149])).
% 3.29/1.47  tff(c_157, plain, (![A_50]: (v4_orders_2(k3_yellow19(A_50, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_50))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_50) | v2_struct_0(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_151])).
% 3.29/1.47  tff(c_160, plain, (![A_53]: (v4_orders_2(k3_yellow19(A_53, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_struct_0(A_53) | v2_struct_0(A_53))), inference(negUnitSimplification, [status(thm)], [c_115, c_50, c_157])).
% 3.29/1.47  tff(c_163, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_95, c_160])).
% 3.29/1.47  tff(c_165, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_65, c_163])).
% 3.29/1.47  tff(c_166, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_165])).
% 3.29/1.47  tff(c_167, plain, (![A_54, B_55, C_56]: (l1_waybel_0(k3_yellow19(A_54, B_55, C_56), A_54) | ~m1_subset_1(C_56, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_55)))) | ~v13_waybel_0(C_56, k3_yellow_1(B_55)) | ~v2_waybel_0(C_56, k3_yellow_1(B_55)) | v1_xboole_0(C_56) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | v1_xboole_0(B_55) | ~l1_struct_0(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.29/1.47  tff(c_169, plain, (![A_54]: (l1_waybel_0(k3_yellow19(A_54, k2_struct_0('#skF_1'), '#skF_2'), A_54) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_54))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_54) | v2_struct_0(A_54))), inference(resolution, [status(thm)], [c_42, c_167])).
% 3.29/1.47  tff(c_175, plain, (![A_54]: (l1_waybel_0(k3_yellow19(A_54, k2_struct_0('#skF_1'), '#skF_2'), A_54) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_54))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_54) | v2_struct_0(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_169])).
% 3.29/1.47  tff(c_178, plain, (![A_57]: (l1_waybel_0(k3_yellow19(A_57, k2_struct_0('#skF_1'), '#skF_2'), A_57) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_struct_0(A_57) | v2_struct_0(A_57))), inference(negUnitSimplification, [status(thm)], [c_115, c_50, c_175])).
% 3.29/1.47  tff(c_180, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_95, c_178])).
% 3.29/1.47  tff(c_182, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_65, c_180])).
% 3.29/1.47  tff(c_183, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_182])).
% 3.29/1.47  tff(c_48, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.29/1.47  tff(c_205, plain, (![A_70, B_71]: (k2_yellow19(A_70, k3_yellow19(A_70, k2_struct_0(A_70), B_71))=B_71 | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_70))))) | ~v13_waybel_0(B_71, k3_yellow_1(k2_struct_0(A_70))) | ~v2_waybel_0(B_71, k3_yellow_1(k2_struct_0(A_70))) | ~v1_subset_1(B_71, u1_struct_0(k3_yellow_1(k2_struct_0(A_70)))) | v1_xboole_0(B_71) | ~l1_struct_0(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.29/1.47  tff(c_207, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_205])).
% 3.29/1.47  tff(c_213, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_48, c_46, c_44, c_207])).
% 3.29/1.47  tff(c_214, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_56, c_50, c_213])).
% 3.29/1.47  tff(c_36, plain, (![A_16, B_20, C_22]: (r2_waybel_7(A_16, k2_yellow19(A_16, B_20), C_22) | ~r2_hidden(C_22, k10_yellow_6(A_16, B_20)) | ~m1_subset_1(C_22, u1_struct_0(A_16)) | ~l1_waybel_0(B_20, A_16) | ~v7_waybel_0(B_20) | ~v4_orders_2(B_20) | v2_struct_0(B_20) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.29/1.47  tff(c_219, plain, (![C_22]: (r2_waybel_7('#skF_1', '#skF_2', C_22) | ~r2_hidden(C_22, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_22, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_214, c_36])).
% 3.29/1.47  tff(c_226, plain, (![C_22]: (r2_waybel_7('#skF_1', '#skF_2', C_22) | ~r2_hidden(C_22, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_22, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_166, c_183, c_95, c_219])).
% 3.29/1.47  tff(c_227, plain, (![C_22]: (r2_waybel_7('#skF_1', '#skF_2', C_22) | ~r2_hidden(C_22, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_22, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_226])).
% 3.29/1.47  tff(c_232, plain, (~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_227])).
% 3.29/1.47  tff(c_233, plain, (![A_72, B_73, C_74]: (v7_waybel_0(k3_yellow19(A_72, B_73, C_74)) | ~m1_subset_1(C_74, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_73)))) | ~v13_waybel_0(C_74, k3_yellow_1(B_73)) | ~v2_waybel_0(C_74, k3_yellow_1(B_73)) | ~v1_subset_1(C_74, u1_struct_0(k3_yellow_1(B_73))) | v1_xboole_0(C_74) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | v1_xboole_0(B_73) | ~l1_struct_0(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.29/1.47  tff(c_235, plain, (![A_72]: (v7_waybel_0(k3_yellow19(A_72, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_72))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_72) | v2_struct_0(A_72))), inference(resolution, [status(thm)], [c_42, c_233])).
% 3.29/1.47  tff(c_241, plain, (![A_72]: (v7_waybel_0(k3_yellow19(A_72, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_72))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_72) | v2_struct_0(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_235])).
% 3.29/1.47  tff(c_244, plain, (![A_75]: (v7_waybel_0(k3_yellow19(A_75, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_struct_0(A_75) | v2_struct_0(A_75))), inference(negUnitSimplification, [status(thm)], [c_115, c_50, c_241])).
% 3.29/1.47  tff(c_247, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_95, c_244])).
% 3.29/1.47  tff(c_249, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_65, c_247])).
% 3.29/1.47  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_232, c_249])).
% 3.29/1.47  tff(c_252, plain, (![C_22]: (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | r2_waybel_7('#skF_1', '#skF_2', C_22) | ~r2_hidden(C_22, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_22, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_227])).
% 3.29/1.47  tff(c_254, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_252])).
% 3.29/1.47  tff(c_26, plain, (![A_10, B_11, C_12]: (~v2_struct_0(k3_yellow19(A_10, B_11, C_12)) | ~m1_subset_1(C_12, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_11)))) | ~v13_waybel_0(C_12, k3_yellow_1(B_11)) | ~v2_waybel_0(C_12, k3_yellow_1(B_11)) | v1_xboole_0(C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0(A_10))) | v1_xboole_0(B_11) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.29/1.47  tff(c_256, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_254, c_26])).
% 3.29/1.47  tff(c_259, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_65, c_95, c_46, c_44, c_42, c_256])).
% 3.29/1.47  tff(c_261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_115, c_50, c_259])).
% 3.29/1.47  tff(c_263, plain, (~v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_252])).
% 3.29/1.47  tff(c_253, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_227])).
% 3.29/1.47  tff(c_34, plain, (![C_22, A_16, B_20]: (r2_hidden(C_22, k10_yellow_6(A_16, B_20)) | ~r2_waybel_7(A_16, k2_yellow19(A_16, B_20), C_22) | ~m1_subset_1(C_22, u1_struct_0(A_16)) | ~l1_waybel_0(B_20, A_16) | ~v7_waybel_0(B_20) | ~v4_orders_2(B_20) | v2_struct_0(B_20) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.29/1.47  tff(c_222, plain, (![C_22]: (r2_hidden(C_22, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_22) | ~m1_subset_1(C_22, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_214, c_34])).
% 3.29/1.47  tff(c_229, plain, (![C_22]: (r2_hidden(C_22, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_22) | ~m1_subset_1(C_22, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_166, c_183, c_95, c_222])).
% 3.29/1.47  tff(c_230, plain, (![C_22]: (r2_hidden(C_22, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_22) | ~m1_subset_1(C_22, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_229])).
% 3.29/1.47  tff(c_284, plain, (![C_22]: (r2_hidden(C_22, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_22) | ~m1_subset_1(C_22, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_230])).
% 3.29/1.47  tff(c_286, plain, (![C_81]: (r2_hidden(C_81, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_81) | ~m1_subset_1(C_81, k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_263, c_284])).
% 3.29/1.47  tff(c_292, plain, (~r2_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_286, c_122])).
% 3.29/1.47  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_123, c_292])).
% 3.29/1.47  tff(c_298, plain, (~r2_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 3.29/1.47  tff(c_299, plain, (r2_hidden('#skF_3', k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(splitRight, [status(thm)], [c_58])).
% 3.29/1.47  tff(c_327, plain, (![A_95, B_96, C_97]: (v4_orders_2(k3_yellow19(A_95, B_96, C_97)) | ~m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_96)))) | ~v13_waybel_0(C_97, k3_yellow_1(B_96)) | ~v2_waybel_0(C_97, k3_yellow_1(B_96)) | v1_xboole_0(C_97) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | v1_xboole_0(B_96) | ~l1_struct_0(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.29/1.47  tff(c_329, plain, (![A_95]: (v4_orders_2(k3_yellow19(A_95, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_95))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_95) | v2_struct_0(A_95))), inference(resolution, [status(thm)], [c_42, c_327])).
% 3.29/1.47  tff(c_335, plain, (![A_95]: (v4_orders_2(k3_yellow19(A_95, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_95))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_95) | v2_struct_0(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_329])).
% 3.29/1.47  tff(c_338, plain, (![A_98]: (v4_orders_2(k3_yellow19(A_98, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_struct_0(A_98) | v2_struct_0(A_98))), inference(negUnitSimplification, [status(thm)], [c_115, c_50, c_335])).
% 3.29/1.47  tff(c_341, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_95, c_338])).
% 3.29/1.47  tff(c_343, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_65, c_341])).
% 3.29/1.47  tff(c_344, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_343])).
% 3.29/1.47  tff(c_380, plain, (![A_109, B_110, C_111]: (v7_waybel_0(k3_yellow19(A_109, B_110, C_111)) | ~m1_subset_1(C_111, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_110)))) | ~v13_waybel_0(C_111, k3_yellow_1(B_110)) | ~v2_waybel_0(C_111, k3_yellow_1(B_110)) | ~v1_subset_1(C_111, u1_struct_0(k3_yellow_1(B_110))) | v1_xboole_0(C_111) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | v1_xboole_0(B_110) | ~l1_struct_0(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.29/1.47  tff(c_382, plain, (![A_109]: (v7_waybel_0(k3_yellow19(A_109, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_109))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_109) | v2_struct_0(A_109))), inference(resolution, [status(thm)], [c_42, c_380])).
% 3.29/1.47  tff(c_388, plain, (![A_109]: (v7_waybel_0(k3_yellow19(A_109, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_109))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_109) | v2_struct_0(A_109))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_382])).
% 3.29/1.47  tff(c_391, plain, (![A_112]: (v7_waybel_0(k3_yellow19(A_112, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_struct_0(A_112) | v2_struct_0(A_112))), inference(negUnitSimplification, [status(thm)], [c_115, c_50, c_388])).
% 3.29/1.47  tff(c_394, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_95, c_391])).
% 3.29/1.47  tff(c_396, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_65, c_394])).
% 3.29/1.47  tff(c_397, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_396])).
% 3.29/1.47  tff(c_362, plain, (![A_103, B_104, C_105]: (l1_waybel_0(k3_yellow19(A_103, B_104, C_105), A_103) | ~m1_subset_1(C_105, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_104)))) | ~v13_waybel_0(C_105, k3_yellow_1(B_104)) | ~v2_waybel_0(C_105, k3_yellow_1(B_104)) | v1_xboole_0(C_105) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | v1_xboole_0(B_104) | ~l1_struct_0(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.29/1.47  tff(c_364, plain, (![A_103]: (l1_waybel_0(k3_yellow19(A_103, k2_struct_0('#skF_1'), '#skF_2'), A_103) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_103))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_103) | v2_struct_0(A_103))), inference(resolution, [status(thm)], [c_42, c_362])).
% 3.29/1.47  tff(c_370, plain, (![A_103]: (l1_waybel_0(k3_yellow19(A_103, k2_struct_0('#skF_1'), '#skF_2'), A_103) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_103))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_103) | v2_struct_0(A_103))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_364])).
% 3.29/1.47  tff(c_373, plain, (![A_106]: (l1_waybel_0(k3_yellow19(A_106, k2_struct_0('#skF_1'), '#skF_2'), A_106) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_struct_0(A_106) | v2_struct_0(A_106))), inference(negUnitSimplification, [status(thm)], [c_115, c_50, c_370])).
% 3.29/1.47  tff(c_375, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_95, c_373])).
% 3.29/1.47  tff(c_377, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_65, c_375])).
% 3.29/1.47  tff(c_378, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_377])).
% 3.29/1.47  tff(c_401, plain, (![A_119, B_120]: (k2_yellow19(A_119, k3_yellow19(A_119, k2_struct_0(A_119), B_120))=B_120 | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_119))))) | ~v13_waybel_0(B_120, k3_yellow_1(k2_struct_0(A_119))) | ~v2_waybel_0(B_120, k3_yellow_1(k2_struct_0(A_119))) | ~v1_subset_1(B_120, u1_struct_0(k3_yellow_1(k2_struct_0(A_119)))) | v1_xboole_0(B_120) | ~l1_struct_0(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.29/1.47  tff(c_403, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_401])).
% 3.29/1.47  tff(c_409, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_48, c_46, c_44, c_403])).
% 3.29/1.47  tff(c_410, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_56, c_50, c_409])).
% 3.29/1.47  tff(c_415, plain, (![C_22]: (r2_hidden(C_22, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_22) | ~m1_subset_1(C_22, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_410, c_34])).
% 3.29/1.47  tff(c_422, plain, (![C_22]: (r2_hidden(C_22, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_22) | ~m1_subset_1(C_22, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_344, c_397, c_378, c_95, c_415])).
% 3.29/1.47  tff(c_423, plain, (![C_22]: (r2_hidden(C_22, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_22) | ~m1_subset_1(C_22, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_422])).
% 3.29/1.47  tff(c_428, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_423])).
% 3.29/1.47  tff(c_430, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_428, c_26])).
% 3.29/1.47  tff(c_433, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_65, c_95, c_46, c_44, c_42, c_430])).
% 3.29/1.47  tff(c_435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_115, c_50, c_433])).
% 3.29/1.47  tff(c_437, plain, (~v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_423])).
% 3.29/1.47  tff(c_418, plain, (![C_22]: (r2_waybel_7('#skF_1', '#skF_2', C_22) | ~r2_hidden(C_22, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_22, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_410, c_36])).
% 3.29/1.47  tff(c_425, plain, (![C_22]: (r2_waybel_7('#skF_1', '#skF_2', C_22) | ~r2_hidden(C_22, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_22, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_344, c_397, c_378, c_95, c_418])).
% 3.29/1.47  tff(c_426, plain, (![C_22]: (r2_waybel_7('#skF_1', '#skF_2', C_22) | ~r2_hidden(C_22, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_22, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_425])).
% 3.29/1.47  tff(c_438, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_426])).
% 3.29/1.47  tff(c_439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_437, c_438])).
% 3.29/1.47  tff(c_442, plain, (![C_121]: (r2_waybel_7('#skF_1', '#skF_2', C_121) | ~r2_hidden(C_121, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_121, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_426])).
% 3.29/1.47  tff(c_445, plain, (r2_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_299, c_442])).
% 3.29/1.47  tff(c_448, plain, (r2_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_445])).
% 3.29/1.47  tff(c_450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_298, c_448])).
% 3.29/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.47  
% 3.29/1.47  Inference rules
% 3.29/1.47  ----------------------
% 3.29/1.47  #Ref     : 0
% 3.29/1.47  #Sup     : 63
% 3.29/1.47  #Fact    : 0
% 3.29/1.47  #Define  : 0
% 3.29/1.47  #Split   : 7
% 3.29/1.47  #Chain   : 0
% 3.29/1.47  #Close   : 0
% 3.29/1.47  
% 3.29/1.47  Ordering : KBO
% 3.29/1.48  
% 3.29/1.48  Simplification rules
% 3.29/1.48  ----------------------
% 3.29/1.48  #Subsume      : 6
% 3.29/1.48  #Demod        : 99
% 3.29/1.48  #Tautology    : 18
% 3.29/1.48  #SimpNegUnit  : 36
% 3.29/1.48  #BackRed      : 1
% 3.29/1.48  
% 3.29/1.48  #Partial instantiations: 0
% 3.29/1.48  #Strategies tried      : 1
% 3.29/1.48  
% 3.29/1.48  Timing (in seconds)
% 3.29/1.48  ----------------------
% 3.29/1.48  Preprocessing        : 0.36
% 3.29/1.48  Parsing              : 0.19
% 3.29/1.48  CNF conversion       : 0.02
% 3.29/1.48  Main loop            : 0.32
% 3.29/1.48  Inferencing          : 0.12
% 3.29/1.48  Reduction            : 0.10
% 3.29/1.48  Demodulation         : 0.07
% 3.29/1.48  BG Simplification    : 0.02
% 3.29/1.48  Subsumption          : 0.06
% 3.29/1.48  Abstraction          : 0.02
% 3.29/1.48  MUC search           : 0.00
% 3.29/1.48  Cooper               : 0.00
% 3.29/1.48  Total                : 0.74
% 3.29/1.48  Index Insertion      : 0.00
% 3.29/1.48  Index Deletion       : 0.00
% 3.29/1.48  Index Matching       : 0.00
% 3.29/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
