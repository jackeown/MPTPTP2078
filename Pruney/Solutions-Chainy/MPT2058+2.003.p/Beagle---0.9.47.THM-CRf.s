%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:32 EST 2020

% Result     : Theorem 12.00s
% Output     : CNFRefutation 12.29s
% Verified   : 
% Statistics : Number of formulae       :  273 (3857 expanded)
%              Number of leaves         :   58 (1313 expanded)
%              Depth                    :   28
%              Number of atoms          :  784 (13159 expanded)
%              Number of equality atoms :   38 (1215 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_7 > m2_connsp_2 > m1_connsp_2 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v7_struct_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k6_domain_1 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_302,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_150,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ( v7_struct_0(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => B = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_struct_0)).

tff(f_54,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_56,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_204,axiom,(
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

tff(f_232,axiom,(
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

tff(f_176,axiom,(
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

tff(f_275,axiom,(
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

tff(f_256,axiom,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_138,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ( v7_struct_0(A)
      <=> ? [B] :
            ( m1_subset_1(B,u1_struct_0(A))
            & u1_struct_0(A) = k6_domain_1(u1_struct_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,k6_domain_1(u1_struct_0(A),B))
              <=> m1_connsp_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_connsp_2)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( m1_connsp_2(B,A,C)
               => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_88,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_22,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_129,plain,(
    ! [A_82] :
      ( u1_struct_0(A_82) = k2_struct_0(A_82)
      | ~ l1_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_134,plain,(
    ! [A_83] :
      ( u1_struct_0(A_83) = k2_struct_0(A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_22,c_129])).

tff(c_138,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_134])).

tff(c_76,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_139,plain,(
    m1_subset_1('#skF_7',k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_76])).

tff(c_94,plain,
    ( ~ r1_waybel_7('#skF_5','#skF_6','#skF_7')
    | ~ r3_waybel_9('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_185,plain,(
    ~ r3_waybel_9('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_100,plain,
    ( r3_waybel_9('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),'#skF_7')
    | r1_waybel_7('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_228,plain,(
    r1_waybel_7('#skF_5','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_100])).

tff(c_92,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_145,plain,(
    ! [B_86,A_87] :
      ( v1_xboole_0(B_86)
      | ~ m1_subset_1(B_86,A_87)
      | ~ v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_162,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_139,c_145])).

tff(c_165,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_86,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_187,plain,(
    ! [A_95] :
      ( m1_subset_1('#skF_3'(A_95),u1_struct_0(A_95))
      | v7_struct_0(A_95)
      | ~ l1_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_193,plain,
    ( m1_subset_1('#skF_3'('#skF_5'),k2_struct_0('#skF_5'))
    | v7_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_187])).

tff(c_203,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_215,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_203])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_215])).

tff(c_221,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_16,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_101,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_82,plain,(
    v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_80,plain,(
    v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_78,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_90,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_2005,plain,(
    ! [A_176,B_177,C_178] :
      ( v4_orders_2(k3_yellow19(A_176,B_177,C_178))
      | ~ m1_subset_1(C_178,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_177))))
      | ~ v13_waybel_0(C_178,k3_yellow_1(B_177))
      | ~ v2_waybel_0(C_178,k3_yellow_1(B_177))
      | v1_xboole_0(C_178)
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_176)))
      | v1_xboole_0(B_177)
      | ~ l1_struct_0(A_176)
      | v2_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_2025,plain,(
    ! [A_176] :
      ( v4_orders_2(k3_yellow19(A_176,k2_struct_0('#skF_5'),'#skF_6'))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_176)))
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | ~ l1_struct_0(A_176)
      | v2_struct_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_78,c_2005])).

tff(c_2033,plain,(
    ! [A_176] :
      ( v4_orders_2(k3_yellow19(A_176,k2_struct_0('#skF_5'),'#skF_6'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_176)))
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | ~ l1_struct_0(A_176)
      | v2_struct_0(A_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_2025])).

tff(c_2036,plain,(
    ! [A_179] :
      ( v4_orders_2(k3_yellow19(A_179,k2_struct_0('#skF_5'),'#skF_6'))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_struct_0(A_179)
      | v2_struct_0(A_179) ) ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_86,c_2033])).

tff(c_2054,plain,
    ( v4_orders_2(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_2036])).

tff(c_2057,plain,
    ( v4_orders_2(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_101,c_2054])).

tff(c_2058,plain,(
    v4_orders_2(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_2057])).

tff(c_84,plain,(
    v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_6000,plain,(
    ! [A_226,B_227,C_228] :
      ( v7_waybel_0(k3_yellow19(A_226,B_227,C_228))
      | ~ m1_subset_1(C_228,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_227))))
      | ~ v13_waybel_0(C_228,k3_yellow_1(B_227))
      | ~ v2_waybel_0(C_228,k3_yellow_1(B_227))
      | ~ v1_subset_1(C_228,u1_struct_0(k3_yellow_1(B_227)))
      | v1_xboole_0(C_228)
      | ~ m1_subset_1(B_227,k1_zfmisc_1(u1_struct_0(A_226)))
      | v1_xboole_0(B_227)
      | ~ l1_struct_0(A_226)
      | v2_struct_0(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_6041,plain,(
    ! [A_226] :
      ( v7_waybel_0(k3_yellow19(A_226,k2_struct_0('#skF_5'),'#skF_6'))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_226)))
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | ~ l1_struct_0(A_226)
      | v2_struct_0(A_226) ) ),
    inference(resolution,[status(thm)],[c_78,c_6000])).

tff(c_6049,plain,(
    ! [A_226] :
      ( v7_waybel_0(k3_yellow19(A_226,k2_struct_0('#skF_5'),'#skF_6'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_226)))
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | ~ l1_struct_0(A_226)
      | v2_struct_0(A_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_6041])).

tff(c_6052,plain,(
    ! [A_229] :
      ( v7_waybel_0(k3_yellow19(A_229,k2_struct_0('#skF_5'),'#skF_6'))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ l1_struct_0(A_229)
      | v2_struct_0(A_229) ) ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_86,c_6049])).

tff(c_6091,plain,
    ( v7_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_6052])).

tff(c_6094,plain,
    ( v7_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_101,c_6091])).

tff(c_6095,plain,(
    v7_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_6094])).

tff(c_5614,plain,(
    ! [A_216,B_217,C_218] :
      ( l1_waybel_0(k3_yellow19(A_216,B_217,C_218),A_216)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_217))))
      | ~ v13_waybel_0(C_218,k3_yellow_1(B_217))
      | ~ v2_waybel_0(C_218,k3_yellow_1(B_217))
      | v1_xboole_0(C_218)
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0(A_216)))
      | v1_xboole_0(B_217)
      | ~ l1_struct_0(A_216)
      | v2_struct_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_5655,plain,(
    ! [A_216] :
      ( l1_waybel_0(k3_yellow19(A_216,k2_struct_0('#skF_5'),'#skF_6'),A_216)
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_216)))
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | ~ l1_struct_0(A_216)
      | v2_struct_0(A_216) ) ),
    inference(resolution,[status(thm)],[c_78,c_5614])).

tff(c_5663,plain,(
    ! [A_216] :
      ( l1_waybel_0(k3_yellow19(A_216,k2_struct_0('#skF_5'),'#skF_6'),A_216)
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_216)))
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | ~ l1_struct_0(A_216)
      | v2_struct_0(A_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_5655])).

tff(c_5666,plain,(
    ! [A_219] :
      ( l1_waybel_0(k3_yellow19(A_219,k2_struct_0('#skF_5'),'#skF_6'),A_219)
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ l1_struct_0(A_219)
      | v2_struct_0(A_219) ) ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_86,c_5663])).

tff(c_5693,plain,
    ( l1_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),'#skF_5')
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_5666])).

tff(c_5696,plain,
    ( l1_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_101,c_5693])).

tff(c_5697,plain,(
    l1_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_5696])).

tff(c_6507,plain,(
    ! [A_242,B_243] :
      ( k2_yellow19(A_242,k3_yellow19(A_242,k2_struct_0(A_242),B_243)) = B_243
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_242)))))
      | ~ v13_waybel_0(B_243,k3_yellow_1(k2_struct_0(A_242)))
      | ~ v2_waybel_0(B_243,k3_yellow_1(k2_struct_0(A_242)))
      | ~ v1_subset_1(B_243,u1_struct_0(k3_yellow_1(k2_struct_0(A_242))))
      | v1_xboole_0(B_243)
      | ~ l1_struct_0(A_242)
      | v2_struct_0(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_6548,plain,
    ( k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = '#skF_6'
    | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
    | v1_xboole_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_6507])).

tff(c_6556,plain,
    ( k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_84,c_82,c_80,c_6548])).

tff(c_6557,plain,(
    k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_6556])).

tff(c_72,plain,(
    ! [A_59,B_63,C_65] :
      ( r1_waybel_7(A_59,k2_yellow19(A_59,B_63),C_65)
      | ~ r3_waybel_9(A_59,B_63,C_65)
      | ~ m1_subset_1(C_65,u1_struct_0(A_59))
      | ~ l1_waybel_0(B_63,A_59)
      | ~ v7_waybel_0(B_63)
      | ~ v4_orders_2(B_63)
      | v2_struct_0(B_63)
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_6562,plain,(
    ! [C_65] :
      ( r1_waybel_7('#skF_5','#skF_6',C_65)
      | ~ r3_waybel_9('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),C_65)
      | ~ m1_subset_1(C_65,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),'#skF_5')
      | ~ v7_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
      | ~ v4_orders_2(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
      | v2_struct_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6557,c_72])).

tff(c_6569,plain,(
    ! [C_65] :
      ( r1_waybel_7('#skF_5','#skF_6',C_65)
      | ~ r3_waybel_9('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),C_65)
      | ~ m1_subset_1(C_65,k2_struct_0('#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_2058,c_6095,c_5697,c_138,c_6562])).

tff(c_6570,plain,(
    ! [C_65] :
      ( r1_waybel_7('#skF_5','#skF_6',C_65)
      | ~ r3_waybel_9('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),C_65)
      | ~ m1_subset_1(C_65,k2_struct_0('#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_6569])).

tff(c_6575,plain,(
    v2_struct_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_6570])).

tff(c_62,plain,(
    ! [A_53,B_54,C_55] :
      ( ~ v2_struct_0(k3_yellow19(A_53,B_54,C_55))
      | ~ m1_subset_1(C_55,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_54))))
      | ~ v13_waybel_0(C_55,k3_yellow_1(B_54))
      | ~ v2_waybel_0(C_55,k3_yellow_1(B_54))
      | v1_xboole_0(C_55)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | v1_xboole_0(B_54)
      | ~ l1_struct_0(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_6577,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
    | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_6575,c_62])).

tff(c_6580,plain,
    ( v1_xboole_0('#skF_6')
    | v1_xboole_0(k2_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_101,c_138,c_82,c_80,c_78,c_6577])).

tff(c_6582,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_165,c_86,c_6580])).

tff(c_6584,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) ),
    inference(splitRight,[status(thm)],[c_6570])).

tff(c_70,plain,(
    ! [A_59,B_63,C_65] :
      ( r3_waybel_9(A_59,B_63,C_65)
      | ~ r1_waybel_7(A_59,k2_yellow19(A_59,B_63),C_65)
      | ~ m1_subset_1(C_65,u1_struct_0(A_59))
      | ~ l1_waybel_0(B_63,A_59)
      | ~ v7_waybel_0(B_63)
      | ~ v4_orders_2(B_63)
      | v2_struct_0(B_63)
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_6565,plain,(
    ! [C_65] :
      ( r3_waybel_9('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),C_65)
      | ~ r1_waybel_7('#skF_5','#skF_6',C_65)
      | ~ m1_subset_1(C_65,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),'#skF_5')
      | ~ v7_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
      | ~ v4_orders_2(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
      | v2_struct_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6557,c_70])).

tff(c_6572,plain,(
    ! [C_65] :
      ( r3_waybel_9('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),C_65)
      | ~ r1_waybel_7('#skF_5','#skF_6',C_65)
      | ~ m1_subset_1(C_65,k2_struct_0('#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_2058,c_6095,c_5697,c_138,c_6565])).

tff(c_6573,plain,(
    ! [C_65] :
      ( r3_waybel_9('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),C_65)
      | ~ r1_waybel_7('#skF_5','#skF_6',C_65)
      | ~ m1_subset_1(C_65,k2_struct_0('#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_6572])).

tff(c_6585,plain,(
    v2_struct_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_6573])).

tff(c_6586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6584,c_6585])).

tff(c_6624,plain,(
    ! [C_247] :
      ( r3_waybel_9('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),C_247)
      | ~ r1_waybel_7('#skF_5','#skF_6',C_247)
      | ~ m1_subset_1(C_247,k2_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_6573])).

tff(c_6630,plain,
    ( ~ r1_waybel_7('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6624,c_185])).

tff(c_6635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_228,c_6630])).

tff(c_6636,plain,(
    ~ r1_waybel_7('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_6639,plain,(
    r3_waybel_9('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_6636,c_100])).

tff(c_6641,plain,(
    ! [A_249] :
      ( m1_subset_1('#skF_4'(A_249),u1_struct_0(A_249))
      | v7_struct_0(A_249)
      | ~ l1_struct_0(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_6647,plain,
    ( m1_subset_1('#skF_4'('#skF_5'),k2_struct_0('#skF_5'))
    | v7_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_6641])).

tff(c_6657,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6647])).

tff(c_6660,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_6657])).

tff(c_6664,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_6660])).

tff(c_6666,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_6647])).

tff(c_9490,plain,(
    ! [A_335,B_336,C_337] :
      ( v4_orders_2(k3_yellow19(A_335,B_336,C_337))
      | ~ m1_subset_1(C_337,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_336))))
      | ~ v13_waybel_0(C_337,k3_yellow_1(B_336))
      | ~ v2_waybel_0(C_337,k3_yellow_1(B_336))
      | v1_xboole_0(C_337)
      | ~ m1_subset_1(B_336,k1_zfmisc_1(u1_struct_0(A_335)))
      | v1_xboole_0(B_336)
      | ~ l1_struct_0(A_335)
      | v2_struct_0(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_9519,plain,(
    ! [A_335] :
      ( v4_orders_2(k3_yellow19(A_335,k2_struct_0('#skF_5'),'#skF_6'))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_335)))
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | ~ l1_struct_0(A_335)
      | v2_struct_0(A_335) ) ),
    inference(resolution,[status(thm)],[c_78,c_9490])).

tff(c_9527,plain,(
    ! [A_335] :
      ( v4_orders_2(k3_yellow19(A_335,k2_struct_0('#skF_5'),'#skF_6'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_335)))
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | ~ l1_struct_0(A_335)
      | v2_struct_0(A_335) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_9519])).

tff(c_9530,plain,(
    ! [A_338] :
      ( v4_orders_2(k3_yellow19(A_338,k2_struct_0('#skF_5'),'#skF_6'))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_338)))
      | ~ l1_struct_0(A_338)
      | v2_struct_0(A_338) ) ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_86,c_9527])).

tff(c_9557,plain,
    ( v4_orders_2(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_9530])).

tff(c_9560,plain,
    ( v4_orders_2(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6666,c_101,c_9557])).

tff(c_9561,plain,(
    v4_orders_2(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_9560])).

tff(c_9586,plain,(
    ! [A_344,B_345,C_346] :
      ( l1_waybel_0(k3_yellow19(A_344,B_345,C_346),A_344)
      | ~ m1_subset_1(C_346,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_345))))
      | ~ v13_waybel_0(C_346,k3_yellow_1(B_345))
      | ~ v2_waybel_0(C_346,k3_yellow_1(B_345))
      | v1_xboole_0(C_346)
      | ~ m1_subset_1(B_345,k1_zfmisc_1(u1_struct_0(A_344)))
      | v1_xboole_0(B_345)
      | ~ l1_struct_0(A_344)
      | v2_struct_0(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_9615,plain,(
    ! [A_344] :
      ( l1_waybel_0(k3_yellow19(A_344,k2_struct_0('#skF_5'),'#skF_6'),A_344)
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_344)))
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | ~ l1_struct_0(A_344)
      | v2_struct_0(A_344) ) ),
    inference(resolution,[status(thm)],[c_78,c_9586])).

tff(c_9623,plain,(
    ! [A_344] :
      ( l1_waybel_0(k3_yellow19(A_344,k2_struct_0('#skF_5'),'#skF_6'),A_344)
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_344)))
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | ~ l1_struct_0(A_344)
      | v2_struct_0(A_344) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_9615])).

tff(c_9626,plain,(
    ! [A_347] :
      ( l1_waybel_0(k3_yellow19(A_347,k2_struct_0('#skF_5'),'#skF_6'),A_347)
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_347)))
      | ~ l1_struct_0(A_347)
      | v2_struct_0(A_347) ) ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_86,c_9623])).

tff(c_9645,plain,
    ( l1_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),'#skF_5')
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_9626])).

tff(c_9648,plain,
    ( l1_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6666,c_101,c_9645])).

tff(c_9649,plain,(
    l1_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_9648])).

tff(c_11514,plain,(
    ! [A_369,B_370] :
      ( k2_yellow19(A_369,k3_yellow19(A_369,k2_struct_0(A_369),B_370)) = B_370
      | ~ m1_subset_1(B_370,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_369)))))
      | ~ v13_waybel_0(B_370,k3_yellow_1(k2_struct_0(A_369)))
      | ~ v2_waybel_0(B_370,k3_yellow_1(k2_struct_0(A_369)))
      | ~ v1_subset_1(B_370,u1_struct_0(k3_yellow_1(k2_struct_0(A_369))))
      | v1_xboole_0(B_370)
      | ~ l1_struct_0(A_369)
      | v2_struct_0(A_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_11555,plain,
    ( k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = '#skF_6'
    | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
    | v1_xboole_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_11514])).

tff(c_11563,plain,
    ( k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6666,c_84,c_82,c_80,c_11555])).

tff(c_11564,plain,(
    k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_11563])).

tff(c_11569,plain,(
    ! [C_65] :
      ( r1_waybel_7('#skF_5','#skF_6',C_65)
      | ~ r3_waybel_9('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),C_65)
      | ~ m1_subset_1(C_65,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),'#skF_5')
      | ~ v7_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
      | ~ v4_orders_2(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
      | v2_struct_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11564,c_72])).

tff(c_11576,plain,(
    ! [C_65] :
      ( r1_waybel_7('#skF_5','#skF_6',C_65)
      | ~ r3_waybel_9('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),C_65)
      | ~ m1_subset_1(C_65,k2_struct_0('#skF_5'))
      | ~ v7_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
      | v2_struct_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_9561,c_9649,c_138,c_11569])).

tff(c_11577,plain,(
    ! [C_65] :
      ( r1_waybel_7('#skF_5','#skF_6',C_65)
      | ~ r3_waybel_9('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),C_65)
      | ~ m1_subset_1(C_65,k2_struct_0('#skF_5'))
      | ~ v7_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
      | v2_struct_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_11576])).

tff(c_11582,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_11577])).

tff(c_12207,plain,(
    ! [A_377,B_378,C_379] :
      ( v7_waybel_0(k3_yellow19(A_377,B_378,C_379))
      | ~ m1_subset_1(C_379,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_378))))
      | ~ v13_waybel_0(C_379,k3_yellow_1(B_378))
      | ~ v2_waybel_0(C_379,k3_yellow_1(B_378))
      | ~ v1_subset_1(C_379,u1_struct_0(k3_yellow_1(B_378)))
      | v1_xboole_0(C_379)
      | ~ m1_subset_1(B_378,k1_zfmisc_1(u1_struct_0(A_377)))
      | v1_xboole_0(B_378)
      | ~ l1_struct_0(A_377)
      | v2_struct_0(A_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_12248,plain,(
    ! [A_377] :
      ( v7_waybel_0(k3_yellow19(A_377,k2_struct_0('#skF_5'),'#skF_6'))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_377)))
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | ~ l1_struct_0(A_377)
      | v2_struct_0(A_377) ) ),
    inference(resolution,[status(thm)],[c_78,c_12207])).

tff(c_12256,plain,(
    ! [A_377] :
      ( v7_waybel_0(k3_yellow19(A_377,k2_struct_0('#skF_5'),'#skF_6'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_377)))
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | ~ l1_struct_0(A_377)
      | v2_struct_0(A_377) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_12248])).

tff(c_12259,plain,(
    ! [A_380] :
      ( v7_waybel_0(k3_yellow19(A_380,k2_struct_0('#skF_5'),'#skF_6'))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(A_380)))
      | ~ l1_struct_0(A_380)
      | v2_struct_0(A_380) ) ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_86,c_12256])).

tff(c_12298,plain,
    ( v7_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_12259])).

tff(c_12301,plain,
    ( v7_waybel_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6666,c_101,c_12298])).

tff(c_12303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_11582,c_12301])).

tff(c_12304,plain,(
    ! [C_65] :
      ( v2_struct_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
      | r1_waybel_7('#skF_5','#skF_6',C_65)
      | ~ r3_waybel_9('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),C_65)
      | ~ m1_subset_1(C_65,k2_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_11577])).

tff(c_12306,plain,(
    v2_struct_0(k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_12304])).

tff(c_12311,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
    | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_12306,c_62])).

tff(c_12314,plain,
    ( v1_xboole_0('#skF_6')
    | v1_xboole_0(k2_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6666,c_101,c_138,c_82,c_80,c_78,c_12311])).

tff(c_12316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_165,c_86,c_12314])).

tff(c_12319,plain,(
    ! [C_381] :
      ( r1_waybel_7('#skF_5','#skF_6',C_381)
      | ~ r3_waybel_9('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'),C_381)
      | ~ m1_subset_1(C_381,k2_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_12304])).

tff(c_12322,plain,
    ( r1_waybel_7('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6639,c_12319])).

tff(c_12325,plain,(
    r1_waybel_7('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_12322])).

tff(c_12327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6636,c_12325])).

tff(c_12328,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_12329,plain,(
    v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( ~ v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12341,plain,(
    ! [A_384] :
      ( A_384 = '#skF_7'
      | ~ v1_xboole_0(A_384) ) ),
    inference(resolution,[status(thm)],[c_12328,c_6])).

tff(c_12348,plain,(
    k2_struct_0('#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_12329,c_12341])).

tff(c_12354,plain,(
    u1_struct_0('#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12348,c_138])).

tff(c_12353,plain,(
    m1_subset_1('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12348,c_139])).

tff(c_13938,plain,(
    ! [A_527,B_528] :
      ( m2_connsp_2(k2_struct_0(A_527),A_527,B_528)
      | ~ m1_subset_1(B_528,k1_zfmisc_1(u1_struct_0(A_527)))
      | ~ l1_pre_topc(A_527)
      | ~ v2_pre_topc(A_527)
      | v2_struct_0(A_527) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_13945,plain,(
    ! [B_528] :
      ( m2_connsp_2(k2_struct_0('#skF_5'),'#skF_5',B_528)
      | ~ m1_subset_1(B_528,k1_zfmisc_1('#skF_7'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12354,c_13938])).

tff(c_13955,plain,(
    ! [B_528] :
      ( m2_connsp_2('#skF_7','#skF_5',B_528)
      | ~ m1_subset_1(B_528,k1_zfmisc_1('#skF_7'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_12348,c_13945])).

tff(c_13959,plain,(
    ! [B_529] :
      ( m2_connsp_2('#skF_7','#skF_5',B_529)
      | ~ m1_subset_1(B_529,k1_zfmisc_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_13955])).

tff(c_13974,plain,(
    m2_connsp_2('#skF_7','#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_101,c_13959])).

tff(c_12399,plain,(
    ! [A_389] :
      ( m1_subset_1('#skF_4'(A_389),u1_struct_0(A_389))
      | v7_struct_0(A_389)
      | ~ l1_struct_0(A_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_12405,plain,
    ( m1_subset_1('#skF_4'('#skF_5'),'#skF_7')
    | v7_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_12354,c_12399])).

tff(c_12407,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_12405])).

tff(c_12418,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_12407])).

tff(c_12422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_12418])).

tff(c_12424,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_12405])).

tff(c_12423,plain,
    ( v7_struct_0('#skF_5')
    | m1_subset_1('#skF_4'('#skF_5'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_12405])).

tff(c_12430,plain,(
    m1_subset_1('#skF_4'('#skF_5'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_12423])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( v1_xboole_0(B_8)
      | ~ m1_subset_1(B_8,A_7)
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12433,plain,
    ( v1_xboole_0('#skF_4'('#skF_5'))
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_12430,c_14])).

tff(c_12436,plain,(
    v1_xboole_0('#skF_4'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12328,c_12433])).

tff(c_12332,plain,(
    ! [A_5] :
      ( A_5 = '#skF_7'
      | ~ v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_12328,c_6])).

tff(c_12442,plain,(
    '#skF_4'('#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_12436,c_12332])).

tff(c_44,plain,(
    ! [A_39] :
      ( '#skF_4'(A_39) != '#skF_3'(A_39)
      | v7_struct_0(A_39)
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_12700,plain,(
    ! [A_411,B_412] :
      ( m2_connsp_2(k2_struct_0(A_411),A_411,B_412)
      | ~ m1_subset_1(B_412,k1_zfmisc_1(u1_struct_0(A_411)))
      | ~ l1_pre_topc(A_411)
      | ~ v2_pre_topc(A_411)
      | v2_struct_0(A_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_12707,plain,(
    ! [B_412] :
      ( m2_connsp_2(k2_struct_0('#skF_5'),'#skF_5',B_412)
      | ~ m1_subset_1(B_412,k1_zfmisc_1('#skF_7'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12354,c_12700])).

tff(c_12717,plain,(
    ! [B_412] :
      ( m2_connsp_2('#skF_7','#skF_5',B_412)
      | ~ m1_subset_1(B_412,k1_zfmisc_1('#skF_7'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_12348,c_12707])).

tff(c_12721,plain,(
    ! [B_413] :
      ( m2_connsp_2('#skF_7','#skF_5',B_413)
      | ~ m1_subset_1(B_413,k1_zfmisc_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_12717])).

tff(c_12736,plain,(
    m2_connsp_2('#skF_7','#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_101,c_12721])).

tff(c_12458,plain,(
    ! [A_391] :
      ( m1_subset_1('#skF_3'(A_391),u1_struct_0(A_391))
      | v7_struct_0(A_391)
      | ~ l1_struct_0(A_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_12464,plain,
    ( m1_subset_1('#skF_3'('#skF_5'),'#skF_7')
    | v7_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_12354,c_12458])).

tff(c_12467,plain,
    ( m1_subset_1('#skF_3'('#skF_5'),'#skF_7')
    | v7_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12424,c_12464])).

tff(c_12468,plain,(
    v7_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_12467])).

tff(c_12469,plain,(
    ! [A_392] :
      ( m1_subset_1('#skF_2'(A_392),u1_struct_0(A_392))
      | ~ v7_struct_0(A_392)
      | ~ l1_struct_0(A_392)
      | v2_struct_0(A_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_12475,plain,
    ( m1_subset_1('#skF_2'('#skF_5'),'#skF_7')
    | ~ v7_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_12354,c_12469])).

tff(c_12478,plain,
    ( m1_subset_1('#skF_2'('#skF_5'),'#skF_7')
    | ~ v7_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12424,c_12475])).

tff(c_12479,plain,
    ( m1_subset_1('#skF_2'('#skF_5'),'#skF_7')
    | ~ v7_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_12478])).

tff(c_12481,plain,(
    m1_subset_1('#skF_2'('#skF_5'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12468,c_12479])).

tff(c_12484,plain,
    ( v1_xboole_0('#skF_2'('#skF_5'))
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_12481,c_14])).

tff(c_12487,plain,(
    v1_xboole_0('#skF_2'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12328,c_12484])).

tff(c_12493,plain,(
    '#skF_2'('#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_12487,c_12332])).

tff(c_12529,plain,(
    ! [A_396] :
      ( k6_domain_1(u1_struct_0(A_396),'#skF_2'(A_396)) = u1_struct_0(A_396)
      | ~ v7_struct_0(A_396)
      | ~ l1_struct_0(A_396)
      | v2_struct_0(A_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_12541,plain,
    ( k6_domain_1('#skF_7','#skF_2'('#skF_5')) = u1_struct_0('#skF_5')
    | ~ v7_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_12354,c_12529])).

tff(c_12548,plain,
    ( k6_domain_1('#skF_7','#skF_7') = '#skF_7'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12424,c_12468,c_12493,c_12354,c_12541])).

tff(c_12549,plain,(
    k6_domain_1('#skF_7','#skF_7') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_12548])).

tff(c_13475,plain,(
    ! [C_491,A_492,B_493] :
      ( m1_connsp_2(C_491,A_492,B_493)
      | ~ m2_connsp_2(C_491,A_492,k6_domain_1(u1_struct_0(A_492),B_493))
      | ~ m1_subset_1(C_491,k1_zfmisc_1(u1_struct_0(A_492)))
      | ~ m1_subset_1(B_493,u1_struct_0(A_492))
      | ~ l1_pre_topc(A_492)
      | ~ v2_pre_topc(A_492)
      | v2_struct_0(A_492) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_13481,plain,(
    ! [C_491,B_493] :
      ( m1_connsp_2(C_491,'#skF_5',B_493)
      | ~ m2_connsp_2(C_491,'#skF_5',k6_domain_1('#skF_7',B_493))
      | ~ m1_subset_1(C_491,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_493,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12354,c_13475])).

tff(c_13483,plain,(
    ! [C_491,B_493] :
      ( m1_connsp_2(C_491,'#skF_5',B_493)
      | ~ m2_connsp_2(C_491,'#skF_5',k6_domain_1('#skF_7',B_493))
      | ~ m1_subset_1(C_491,k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1(B_493,'#skF_7')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_12354,c_12354,c_13481])).

tff(c_13485,plain,(
    ! [C_494,B_495] :
      ( m1_connsp_2(C_494,'#skF_5',B_495)
      | ~ m2_connsp_2(C_494,'#skF_5',k6_domain_1('#skF_7',B_495))
      | ~ m1_subset_1(C_494,k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1(B_495,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_13483])).

tff(c_13488,plain,(
    ! [C_494] :
      ( m1_connsp_2(C_494,'#skF_5','#skF_7')
      | ~ m2_connsp_2(C_494,'#skF_5','#skF_7')
      | ~ m1_subset_1(C_494,k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1('#skF_7','#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12549,c_13485])).

tff(c_13491,plain,(
    ! [C_496] :
      ( m1_connsp_2(C_496,'#skF_5','#skF_7')
      | ~ m2_connsp_2(C_496,'#skF_5','#skF_7')
      | ~ m1_subset_1(C_496,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12353,c_13488])).

tff(c_13503,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_7')
    | ~ m2_connsp_2('#skF_7','#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_101,c_13491])).

tff(c_13510,plain,(
    m1_connsp_2('#skF_7','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12736,c_13503])).

tff(c_32,plain,(
    ! [C_33,B_31,A_27] :
      ( r2_hidden(C_33,B_31)
      | ~ m1_connsp_2(B_31,A_27,C_33)
      | ~ m1_subset_1(C_33,u1_struct_0(A_27))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_13512,plain,
    ( r2_hidden('#skF_7','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_13510,c_32])).

tff(c_13517,plain,
    ( r2_hidden('#skF_7','#skF_7')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_101,c_12354,c_12353,c_12354,c_13512])).

tff(c_13518,plain,(
    r2_hidden('#skF_7','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_13517])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_13528,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_13518,c_2])).

tff(c_13534,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12328,c_13528])).

tff(c_13536,plain,(
    ~ v7_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_12467])).

tff(c_13539,plain,
    ( '#skF_4'('#skF_5') != '#skF_3'('#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_13536])).

tff(c_13542,plain,(
    '#skF_3'('#skF_5') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12424,c_12442,c_13539])).

tff(c_13535,plain,(
    m1_subset_1('#skF_3'('#skF_5'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_12467])).

tff(c_13545,plain,
    ( v1_xboole_0('#skF_3'('#skF_5'))
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_13535,c_14])).

tff(c_13548,plain,(
    v1_xboole_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12328,c_13545])).

tff(c_13551,plain,(
    '#skF_3'('#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_13548,c_12332])).

tff(c_13557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13542,c_13551])).

tff(c_13558,plain,(
    v7_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_12423])).

tff(c_13583,plain,(
    ! [A_499] :
      ( m1_subset_1('#skF_2'(A_499),u1_struct_0(A_499))
      | ~ v7_struct_0(A_499)
      | ~ l1_struct_0(A_499)
      | v2_struct_0(A_499) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_13589,plain,
    ( m1_subset_1('#skF_2'('#skF_5'),'#skF_7')
    | ~ v7_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_12354,c_13583])).

tff(c_13592,plain,
    ( m1_subset_1('#skF_2'('#skF_5'),'#skF_7')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12424,c_13558,c_13589])).

tff(c_13593,plain,(
    m1_subset_1('#skF_2'('#skF_5'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_13592])).

tff(c_13596,plain,
    ( v1_xboole_0('#skF_2'('#skF_5'))
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_13593,c_14])).

tff(c_13599,plain,(
    v1_xboole_0('#skF_2'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12328,c_13596])).

tff(c_13605,plain,(
    '#skF_2'('#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_13599,c_12332])).

tff(c_13628,plain,(
    ! [A_501] :
      ( k6_domain_1(u1_struct_0(A_501),'#skF_2'(A_501)) = u1_struct_0(A_501)
      | ~ v7_struct_0(A_501)
      | ~ l1_struct_0(A_501)
      | v2_struct_0(A_501) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_13640,plain,
    ( k6_domain_1('#skF_7','#skF_2'('#skF_5')) = u1_struct_0('#skF_5')
    | ~ v7_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_12354,c_13628])).

tff(c_13647,plain,
    ( k6_domain_1('#skF_7','#skF_7') = '#skF_7'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12424,c_13558,c_13605,c_12354,c_13640])).

tff(c_13648,plain,(
    k6_domain_1('#skF_7','#skF_7') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_13647])).

tff(c_14482,plain,(
    ! [C_596,A_597,B_598] :
      ( m1_connsp_2(C_596,A_597,B_598)
      | ~ m2_connsp_2(C_596,A_597,k6_domain_1(u1_struct_0(A_597),B_598))
      | ~ m1_subset_1(C_596,k1_zfmisc_1(u1_struct_0(A_597)))
      | ~ m1_subset_1(B_598,u1_struct_0(A_597))
      | ~ l1_pre_topc(A_597)
      | ~ v2_pre_topc(A_597)
      | v2_struct_0(A_597) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_14491,plain,(
    ! [C_596,B_598] :
      ( m1_connsp_2(C_596,'#skF_5',B_598)
      | ~ m2_connsp_2(C_596,'#skF_5',k6_domain_1('#skF_7',B_598))
      | ~ m1_subset_1(C_596,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_598,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12354,c_14482])).

tff(c_14494,plain,(
    ! [C_596,B_598] :
      ( m1_connsp_2(C_596,'#skF_5',B_598)
      | ~ m2_connsp_2(C_596,'#skF_5',k6_domain_1('#skF_7',B_598))
      | ~ m1_subset_1(C_596,k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1(B_598,'#skF_7')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_12354,c_12354,c_14491])).

tff(c_14496,plain,(
    ! [C_599,B_600] :
      ( m1_connsp_2(C_599,'#skF_5',B_600)
      | ~ m2_connsp_2(C_599,'#skF_5',k6_domain_1('#skF_7',B_600))
      | ~ m1_subset_1(C_599,k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1(B_600,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_14494])).

tff(c_14502,plain,(
    ! [C_599] :
      ( m1_connsp_2(C_599,'#skF_5','#skF_7')
      | ~ m2_connsp_2(C_599,'#skF_5','#skF_7')
      | ~ m1_subset_1(C_599,k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1('#skF_7','#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13648,c_14496])).

tff(c_14506,plain,(
    ! [C_601] :
      ( m1_connsp_2(C_601,'#skF_5','#skF_7')
      | ~ m2_connsp_2(C_601,'#skF_5','#skF_7')
      | ~ m1_subset_1(C_601,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12353,c_14502])).

tff(c_14518,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_7')
    | ~ m2_connsp_2('#skF_7','#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_101,c_14506])).

tff(c_14525,plain,(
    m1_connsp_2('#skF_7','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13974,c_14518])).

tff(c_14527,plain,
    ( r2_hidden('#skF_7','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_14525,c_32])).

tff(c_14532,plain,
    ( r2_hidden('#skF_7','#skF_7')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_101,c_12354,c_12353,c_12354,c_14527])).

tff(c_14533,plain,(
    r2_hidden('#skF_7','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_14532])).

tff(c_14543,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_14533,c_2])).

tff(c_14549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12328,c_14543])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:53:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.00/5.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.00/5.04  
% 12.00/5.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.00/5.04  %$ r3_waybel_9 > r1_waybel_7 > m2_connsp_2 > m1_connsp_2 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v7_struct_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k6_domain_1 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3
% 12.00/5.04  
% 12.00/5.04  %Foreground sorts:
% 12.00/5.04  
% 12.00/5.04  
% 12.00/5.04  %Background operators:
% 12.00/5.04  
% 12.00/5.04  
% 12.00/5.04  %Foreground operators:
% 12.00/5.04  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.00/5.04  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 12.00/5.04  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 12.00/5.04  tff('#skF_2', type, '#skF_2': $i > $i).
% 12.00/5.04  tff('#skF_4', type, '#skF_4': $i > $i).
% 12.00/5.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.00/5.04  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 12.00/5.04  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 12.00/5.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.00/5.04  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 12.00/5.04  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 12.00/5.04  tff('#skF_1', type, '#skF_1': $i > $i).
% 12.00/5.04  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 12.00/5.04  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 12.00/5.04  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.00/5.04  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 12.00/5.04  tff('#skF_7', type, '#skF_7': $i).
% 12.00/5.04  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 12.00/5.04  tff('#skF_5', type, '#skF_5': $i).
% 12.00/5.04  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 12.00/5.04  tff('#skF_6', type, '#skF_6': $i).
% 12.00/5.04  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 12.00/5.04  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 12.00/5.04  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 12.00/5.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.00/5.04  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 12.00/5.04  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 12.00/5.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.00/5.04  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 12.00/5.04  tff('#skF_3', type, '#skF_3': $i > $i).
% 12.00/5.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.00/5.04  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 12.00/5.04  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 12.00/5.04  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.00/5.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.00/5.04  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 12.00/5.04  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 12.00/5.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.00/5.04  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 12.00/5.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.00/5.04  
% 12.29/5.08  tff(f_302, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, k3_yellow19(A, k2_struct_0(A), B), C) <=> r1_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_yellow19)).
% 12.29/5.08  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 12.29/5.08  tff(f_60, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 12.29/5.08  tff(f_52, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 12.29/5.08  tff(f_150, axiom, (![A]: (l1_struct_0(A) => (v7_struct_0(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (B = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_struct_0)).
% 12.29/5.08  tff(f_54, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 12.29/5.08  tff(f_56, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 12.29/5.08  tff(f_204, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_yellow19)).
% 12.29/5.08  tff(f_232, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow19)).
% 12.29/5.08  tff(f_176, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 12.29/5.08  tff(f_275, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 12.29/5.08  tff(f_256, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> r1_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_yellow19)).
% 12.29/5.08  tff(f_39, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 12.29/5.08  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_connsp_2)).
% 12.29/5.08  tff(f_138, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (v7_struct_0(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & (u1_struct_0(A) = k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_1)).
% 12.29/5.08  tff(f_95, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_connsp_2)).
% 12.29/5.08  tff(f_124, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 12.29/5.08  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 12.29/5.08  tff(c_88, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_302])).
% 12.29/5.08  tff(c_22, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.29/5.08  tff(c_129, plain, (![A_82]: (u1_struct_0(A_82)=k2_struct_0(A_82) | ~l1_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.29/5.08  tff(c_134, plain, (![A_83]: (u1_struct_0(A_83)=k2_struct_0(A_83) | ~l1_pre_topc(A_83))), inference(resolution, [status(thm)], [c_22, c_129])).
% 12.29/5.08  tff(c_138, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_88, c_134])).
% 12.29/5.08  tff(c_76, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_302])).
% 12.29/5.08  tff(c_139, plain, (m1_subset_1('#skF_7', k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_76])).
% 12.29/5.08  tff(c_94, plain, (~r1_waybel_7('#skF_5', '#skF_6', '#skF_7') | ~r3_waybel_9('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_302])).
% 12.29/5.08  tff(c_185, plain, (~r3_waybel_9('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), '#skF_7')), inference(splitLeft, [status(thm)], [c_94])).
% 12.29/5.08  tff(c_100, plain, (r3_waybel_9('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), '#skF_7') | r1_waybel_7('#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_302])).
% 12.29/5.08  tff(c_228, plain, (r1_waybel_7('#skF_5', '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_185, c_100])).
% 12.29/5.08  tff(c_92, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_302])).
% 12.29/5.08  tff(c_145, plain, (![B_86, A_87]: (v1_xboole_0(B_86) | ~m1_subset_1(B_86, A_87) | ~v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.29/5.08  tff(c_162, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_139, c_145])).
% 12.29/5.08  tff(c_165, plain, (~v1_xboole_0(k2_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_162])).
% 12.29/5.08  tff(c_86, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_302])).
% 12.29/5.08  tff(c_187, plain, (![A_95]: (m1_subset_1('#skF_3'(A_95), u1_struct_0(A_95)) | v7_struct_0(A_95) | ~l1_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.29/5.08  tff(c_193, plain, (m1_subset_1('#skF_3'('#skF_5'), k2_struct_0('#skF_5')) | v7_struct_0('#skF_5') | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_138, c_187])).
% 12.29/5.08  tff(c_203, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_193])).
% 12.29/5.08  tff(c_215, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_22, c_203])).
% 12.29/5.08  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_215])).
% 12.29/5.08  tff(c_221, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_193])).
% 12.29/5.08  tff(c_16, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.29/5.08  tff(c_18, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.29/5.08  tff(c_101, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 12.29/5.08  tff(c_82, plain, (v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_302])).
% 12.29/5.08  tff(c_80, plain, (v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_302])).
% 12.29/5.08  tff(c_78, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))), inference(cnfTransformation, [status(thm)], [f_302])).
% 12.29/5.08  tff(c_90, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_302])).
% 12.29/5.08  tff(c_2005, plain, (![A_176, B_177, C_178]: (v4_orders_2(k3_yellow19(A_176, B_177, C_178)) | ~m1_subset_1(C_178, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_177)))) | ~v13_waybel_0(C_178, k3_yellow_1(B_177)) | ~v2_waybel_0(C_178, k3_yellow_1(B_177)) | v1_xboole_0(C_178) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_176))) | v1_xboole_0(B_177) | ~l1_struct_0(A_176) | v2_struct_0(A_176))), inference(cnfTransformation, [status(thm)], [f_204])).
% 12.29/5.08  tff(c_2025, plain, (![A_176]: (v4_orders_2(k3_yellow19(A_176, k2_struct_0('#skF_5'), '#skF_6')) | ~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_6') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(A_176))) | v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0(A_176) | v2_struct_0(A_176))), inference(resolution, [status(thm)], [c_78, c_2005])).
% 12.29/5.08  tff(c_2033, plain, (![A_176]: (v4_orders_2(k3_yellow19(A_176, k2_struct_0('#skF_5'), '#skF_6')) | v1_xboole_0('#skF_6') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(A_176))) | v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0(A_176) | v2_struct_0(A_176))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_2025])).
% 12.29/5.08  tff(c_2036, plain, (![A_179]: (v4_orders_2(k3_yellow19(A_179, k2_struct_0('#skF_5'), '#skF_6')) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_struct_0(A_179) | v2_struct_0(A_179))), inference(negUnitSimplification, [status(thm)], [c_165, c_86, c_2033])).
% 12.29/5.08  tff(c_2054, plain, (v4_orders_2(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_138, c_2036])).
% 12.29/5.08  tff(c_2057, plain, (v4_orders_2(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_101, c_2054])).
% 12.29/5.08  tff(c_2058, plain, (v4_orders_2(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_92, c_2057])).
% 12.29/5.08  tff(c_84, plain, (v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_302])).
% 12.29/5.08  tff(c_6000, plain, (![A_226, B_227, C_228]: (v7_waybel_0(k3_yellow19(A_226, B_227, C_228)) | ~m1_subset_1(C_228, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_227)))) | ~v13_waybel_0(C_228, k3_yellow_1(B_227)) | ~v2_waybel_0(C_228, k3_yellow_1(B_227)) | ~v1_subset_1(C_228, u1_struct_0(k3_yellow_1(B_227))) | v1_xboole_0(C_228) | ~m1_subset_1(B_227, k1_zfmisc_1(u1_struct_0(A_226))) | v1_xboole_0(B_227) | ~l1_struct_0(A_226) | v2_struct_0(A_226))), inference(cnfTransformation, [status(thm)], [f_232])).
% 12.29/5.08  tff(c_6041, plain, (![A_226]: (v7_waybel_0(k3_yellow19(A_226, k2_struct_0('#skF_5'), '#skF_6')) | ~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0('#skF_6') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(A_226))) | v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0(A_226) | v2_struct_0(A_226))), inference(resolution, [status(thm)], [c_78, c_6000])).
% 12.29/5.08  tff(c_6049, plain, (![A_226]: (v7_waybel_0(k3_yellow19(A_226, k2_struct_0('#skF_5'), '#skF_6')) | v1_xboole_0('#skF_6') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(A_226))) | v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0(A_226) | v2_struct_0(A_226))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_6041])).
% 12.29/5.08  tff(c_6052, plain, (![A_229]: (v7_waybel_0(k3_yellow19(A_229, k2_struct_0('#skF_5'), '#skF_6')) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(A_229))) | ~l1_struct_0(A_229) | v2_struct_0(A_229))), inference(negUnitSimplification, [status(thm)], [c_165, c_86, c_6049])).
% 12.29/5.08  tff(c_6091, plain, (v7_waybel_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_138, c_6052])).
% 12.29/5.08  tff(c_6094, plain, (v7_waybel_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_101, c_6091])).
% 12.29/5.08  tff(c_6095, plain, (v7_waybel_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_92, c_6094])).
% 12.29/5.08  tff(c_5614, plain, (![A_216, B_217, C_218]: (l1_waybel_0(k3_yellow19(A_216, B_217, C_218), A_216) | ~m1_subset_1(C_218, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_217)))) | ~v13_waybel_0(C_218, k3_yellow_1(B_217)) | ~v2_waybel_0(C_218, k3_yellow_1(B_217)) | v1_xboole_0(C_218) | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0(A_216))) | v1_xboole_0(B_217) | ~l1_struct_0(A_216) | v2_struct_0(A_216))), inference(cnfTransformation, [status(thm)], [f_176])).
% 12.29/5.08  tff(c_5655, plain, (![A_216]: (l1_waybel_0(k3_yellow19(A_216, k2_struct_0('#skF_5'), '#skF_6'), A_216) | ~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_6') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(A_216))) | v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0(A_216) | v2_struct_0(A_216))), inference(resolution, [status(thm)], [c_78, c_5614])).
% 12.29/5.08  tff(c_5663, plain, (![A_216]: (l1_waybel_0(k3_yellow19(A_216, k2_struct_0('#skF_5'), '#skF_6'), A_216) | v1_xboole_0('#skF_6') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(A_216))) | v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0(A_216) | v2_struct_0(A_216))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_5655])).
% 12.29/5.08  tff(c_5666, plain, (![A_219]: (l1_waybel_0(k3_yellow19(A_219, k2_struct_0('#skF_5'), '#skF_6'), A_219) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(A_219))) | ~l1_struct_0(A_219) | v2_struct_0(A_219))), inference(negUnitSimplification, [status(thm)], [c_165, c_86, c_5663])).
% 12.29/5.08  tff(c_5693, plain, (l1_waybel_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), '#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_138, c_5666])).
% 12.29/5.08  tff(c_5696, plain, (l1_waybel_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_101, c_5693])).
% 12.29/5.08  tff(c_5697, plain, (l1_waybel_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_92, c_5696])).
% 12.29/5.08  tff(c_6507, plain, (![A_242, B_243]: (k2_yellow19(A_242, k3_yellow19(A_242, k2_struct_0(A_242), B_243))=B_243 | ~m1_subset_1(B_243, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_242))))) | ~v13_waybel_0(B_243, k3_yellow_1(k2_struct_0(A_242))) | ~v2_waybel_0(B_243, k3_yellow_1(k2_struct_0(A_242))) | ~v1_subset_1(B_243, u1_struct_0(k3_yellow_1(k2_struct_0(A_242)))) | v1_xboole_0(B_243) | ~l1_struct_0(A_242) | v2_struct_0(A_242))), inference(cnfTransformation, [status(thm)], [f_275])).
% 12.29/5.08  tff(c_6548, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))='#skF_6' | ~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_78, c_6507])).
% 12.29/5.08  tff(c_6556, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))='#skF_6' | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_84, c_82, c_80, c_6548])).
% 12.29/5.08  tff(c_6557, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_6556])).
% 12.29/5.08  tff(c_72, plain, (![A_59, B_63, C_65]: (r1_waybel_7(A_59, k2_yellow19(A_59, B_63), C_65) | ~r3_waybel_9(A_59, B_63, C_65) | ~m1_subset_1(C_65, u1_struct_0(A_59)) | ~l1_waybel_0(B_63, A_59) | ~v7_waybel_0(B_63) | ~v4_orders_2(B_63) | v2_struct_0(B_63) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_256])).
% 12.29/5.08  tff(c_6562, plain, (![C_65]: (r1_waybel_7('#skF_5', '#skF_6', C_65) | ~r3_waybel_9('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), C_65) | ~m1_subset_1(C_65, u1_struct_0('#skF_5')) | ~l1_waybel_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), '#skF_5') | ~v7_waybel_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | ~v4_orders_2(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | v2_struct_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6557, c_72])).
% 12.29/5.08  tff(c_6569, plain, (![C_65]: (r1_waybel_7('#skF_5', '#skF_6', C_65) | ~r3_waybel_9('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), C_65) | ~m1_subset_1(C_65, k2_struct_0('#skF_5')) | v2_struct_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_2058, c_6095, c_5697, c_138, c_6562])).
% 12.29/5.08  tff(c_6570, plain, (![C_65]: (r1_waybel_7('#skF_5', '#skF_6', C_65) | ~r3_waybel_9('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), C_65) | ~m1_subset_1(C_65, k2_struct_0('#skF_5')) | v2_struct_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_92, c_6569])).
% 12.29/5.08  tff(c_6575, plain, (v2_struct_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_6570])).
% 12.29/5.08  tff(c_62, plain, (![A_53, B_54, C_55]: (~v2_struct_0(k3_yellow19(A_53, B_54, C_55)) | ~m1_subset_1(C_55, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_54)))) | ~v13_waybel_0(C_55, k3_yellow_1(B_54)) | ~v2_waybel_0(C_55, k3_yellow_1(B_54)) | v1_xboole_0(C_55) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | v1_xboole_0(B_54) | ~l1_struct_0(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_204])).
% 12.29/5.08  tff(c_6577, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_6') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_6575, c_62])).
% 12.29/5.08  tff(c_6580, plain, (v1_xboole_0('#skF_6') | v1_xboole_0(k2_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_101, c_138, c_82, c_80, c_78, c_6577])).
% 12.29/5.08  tff(c_6582, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_165, c_86, c_6580])).
% 12.29/5.08  tff(c_6584, plain, (~v2_struct_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))), inference(splitRight, [status(thm)], [c_6570])).
% 12.29/5.08  tff(c_70, plain, (![A_59, B_63, C_65]: (r3_waybel_9(A_59, B_63, C_65) | ~r1_waybel_7(A_59, k2_yellow19(A_59, B_63), C_65) | ~m1_subset_1(C_65, u1_struct_0(A_59)) | ~l1_waybel_0(B_63, A_59) | ~v7_waybel_0(B_63) | ~v4_orders_2(B_63) | v2_struct_0(B_63) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_256])).
% 12.29/5.08  tff(c_6565, plain, (![C_65]: (r3_waybel_9('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), C_65) | ~r1_waybel_7('#skF_5', '#skF_6', C_65) | ~m1_subset_1(C_65, u1_struct_0('#skF_5')) | ~l1_waybel_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), '#skF_5') | ~v7_waybel_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | ~v4_orders_2(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | v2_struct_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6557, c_70])).
% 12.29/5.08  tff(c_6572, plain, (![C_65]: (r3_waybel_9('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), C_65) | ~r1_waybel_7('#skF_5', '#skF_6', C_65) | ~m1_subset_1(C_65, k2_struct_0('#skF_5')) | v2_struct_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_2058, c_6095, c_5697, c_138, c_6565])).
% 12.29/5.08  tff(c_6573, plain, (![C_65]: (r3_waybel_9('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), C_65) | ~r1_waybel_7('#skF_5', '#skF_6', C_65) | ~m1_subset_1(C_65, k2_struct_0('#skF_5')) | v2_struct_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_92, c_6572])).
% 12.29/5.08  tff(c_6585, plain, (v2_struct_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_6573])).
% 12.29/5.08  tff(c_6586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6584, c_6585])).
% 12.29/5.08  tff(c_6624, plain, (![C_247]: (r3_waybel_9('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), C_247) | ~r1_waybel_7('#skF_5', '#skF_6', C_247) | ~m1_subset_1(C_247, k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_6573])).
% 12.29/5.08  tff(c_6630, plain, (~r1_waybel_7('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_6624, c_185])).
% 12.29/5.08  tff(c_6635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_228, c_6630])).
% 12.29/5.08  tff(c_6636, plain, (~r1_waybel_7('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_94])).
% 12.29/5.08  tff(c_6639, plain, (r3_waybel_9('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_6636, c_100])).
% 12.29/5.08  tff(c_6641, plain, (![A_249]: (m1_subset_1('#skF_4'(A_249), u1_struct_0(A_249)) | v7_struct_0(A_249) | ~l1_struct_0(A_249))), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.29/5.08  tff(c_6647, plain, (m1_subset_1('#skF_4'('#skF_5'), k2_struct_0('#skF_5')) | v7_struct_0('#skF_5') | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_138, c_6641])).
% 12.29/5.08  tff(c_6657, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_6647])).
% 12.29/5.08  tff(c_6660, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_22, c_6657])).
% 12.29/5.08  tff(c_6664, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_6660])).
% 12.29/5.08  tff(c_6666, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_6647])).
% 12.29/5.08  tff(c_9490, plain, (![A_335, B_336, C_337]: (v4_orders_2(k3_yellow19(A_335, B_336, C_337)) | ~m1_subset_1(C_337, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_336)))) | ~v13_waybel_0(C_337, k3_yellow_1(B_336)) | ~v2_waybel_0(C_337, k3_yellow_1(B_336)) | v1_xboole_0(C_337) | ~m1_subset_1(B_336, k1_zfmisc_1(u1_struct_0(A_335))) | v1_xboole_0(B_336) | ~l1_struct_0(A_335) | v2_struct_0(A_335))), inference(cnfTransformation, [status(thm)], [f_204])).
% 12.29/5.08  tff(c_9519, plain, (![A_335]: (v4_orders_2(k3_yellow19(A_335, k2_struct_0('#skF_5'), '#skF_6')) | ~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_6') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(A_335))) | v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0(A_335) | v2_struct_0(A_335))), inference(resolution, [status(thm)], [c_78, c_9490])).
% 12.29/5.08  tff(c_9527, plain, (![A_335]: (v4_orders_2(k3_yellow19(A_335, k2_struct_0('#skF_5'), '#skF_6')) | v1_xboole_0('#skF_6') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(A_335))) | v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0(A_335) | v2_struct_0(A_335))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_9519])).
% 12.29/5.08  tff(c_9530, plain, (![A_338]: (v4_orders_2(k3_yellow19(A_338, k2_struct_0('#skF_5'), '#skF_6')) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(A_338))) | ~l1_struct_0(A_338) | v2_struct_0(A_338))), inference(negUnitSimplification, [status(thm)], [c_165, c_86, c_9527])).
% 12.29/5.08  tff(c_9557, plain, (v4_orders_2(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_138, c_9530])).
% 12.29/5.08  tff(c_9560, plain, (v4_orders_2(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6666, c_101, c_9557])).
% 12.29/5.08  tff(c_9561, plain, (v4_orders_2(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_92, c_9560])).
% 12.29/5.08  tff(c_9586, plain, (![A_344, B_345, C_346]: (l1_waybel_0(k3_yellow19(A_344, B_345, C_346), A_344) | ~m1_subset_1(C_346, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_345)))) | ~v13_waybel_0(C_346, k3_yellow_1(B_345)) | ~v2_waybel_0(C_346, k3_yellow_1(B_345)) | v1_xboole_0(C_346) | ~m1_subset_1(B_345, k1_zfmisc_1(u1_struct_0(A_344))) | v1_xboole_0(B_345) | ~l1_struct_0(A_344) | v2_struct_0(A_344))), inference(cnfTransformation, [status(thm)], [f_176])).
% 12.29/5.08  tff(c_9615, plain, (![A_344]: (l1_waybel_0(k3_yellow19(A_344, k2_struct_0('#skF_5'), '#skF_6'), A_344) | ~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_6') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(A_344))) | v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0(A_344) | v2_struct_0(A_344))), inference(resolution, [status(thm)], [c_78, c_9586])).
% 12.29/5.08  tff(c_9623, plain, (![A_344]: (l1_waybel_0(k3_yellow19(A_344, k2_struct_0('#skF_5'), '#skF_6'), A_344) | v1_xboole_0('#skF_6') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(A_344))) | v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0(A_344) | v2_struct_0(A_344))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_9615])).
% 12.29/5.08  tff(c_9626, plain, (![A_347]: (l1_waybel_0(k3_yellow19(A_347, k2_struct_0('#skF_5'), '#skF_6'), A_347) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(A_347))) | ~l1_struct_0(A_347) | v2_struct_0(A_347))), inference(negUnitSimplification, [status(thm)], [c_165, c_86, c_9623])).
% 12.29/5.08  tff(c_9645, plain, (l1_waybel_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), '#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_138, c_9626])).
% 12.29/5.08  tff(c_9648, plain, (l1_waybel_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6666, c_101, c_9645])).
% 12.29/5.08  tff(c_9649, plain, (l1_waybel_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_92, c_9648])).
% 12.29/5.08  tff(c_11514, plain, (![A_369, B_370]: (k2_yellow19(A_369, k3_yellow19(A_369, k2_struct_0(A_369), B_370))=B_370 | ~m1_subset_1(B_370, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_369))))) | ~v13_waybel_0(B_370, k3_yellow_1(k2_struct_0(A_369))) | ~v2_waybel_0(B_370, k3_yellow_1(k2_struct_0(A_369))) | ~v1_subset_1(B_370, u1_struct_0(k3_yellow_1(k2_struct_0(A_369)))) | v1_xboole_0(B_370) | ~l1_struct_0(A_369) | v2_struct_0(A_369))), inference(cnfTransformation, [status(thm)], [f_275])).
% 12.29/5.08  tff(c_11555, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))='#skF_6' | ~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_78, c_11514])).
% 12.29/5.08  tff(c_11563, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))='#skF_6' | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6666, c_84, c_82, c_80, c_11555])).
% 12.29/5.08  tff(c_11564, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_11563])).
% 12.29/5.08  tff(c_11569, plain, (![C_65]: (r1_waybel_7('#skF_5', '#skF_6', C_65) | ~r3_waybel_9('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), C_65) | ~m1_subset_1(C_65, u1_struct_0('#skF_5')) | ~l1_waybel_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), '#skF_5') | ~v7_waybel_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | ~v4_orders_2(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | v2_struct_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_11564, c_72])).
% 12.29/5.08  tff(c_11576, plain, (![C_65]: (r1_waybel_7('#skF_5', '#skF_6', C_65) | ~r3_waybel_9('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), C_65) | ~m1_subset_1(C_65, k2_struct_0('#skF_5')) | ~v7_waybel_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | v2_struct_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_9561, c_9649, c_138, c_11569])).
% 12.29/5.08  tff(c_11577, plain, (![C_65]: (r1_waybel_7('#skF_5', '#skF_6', C_65) | ~r3_waybel_9('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), C_65) | ~m1_subset_1(C_65, k2_struct_0('#skF_5')) | ~v7_waybel_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | v2_struct_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_92, c_11576])).
% 12.29/5.08  tff(c_11582, plain, (~v7_waybel_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_11577])).
% 12.29/5.08  tff(c_12207, plain, (![A_377, B_378, C_379]: (v7_waybel_0(k3_yellow19(A_377, B_378, C_379)) | ~m1_subset_1(C_379, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_378)))) | ~v13_waybel_0(C_379, k3_yellow_1(B_378)) | ~v2_waybel_0(C_379, k3_yellow_1(B_378)) | ~v1_subset_1(C_379, u1_struct_0(k3_yellow_1(B_378))) | v1_xboole_0(C_379) | ~m1_subset_1(B_378, k1_zfmisc_1(u1_struct_0(A_377))) | v1_xboole_0(B_378) | ~l1_struct_0(A_377) | v2_struct_0(A_377))), inference(cnfTransformation, [status(thm)], [f_232])).
% 12.29/5.08  tff(c_12248, plain, (![A_377]: (v7_waybel_0(k3_yellow19(A_377, k2_struct_0('#skF_5'), '#skF_6')) | ~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0('#skF_6') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(A_377))) | v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0(A_377) | v2_struct_0(A_377))), inference(resolution, [status(thm)], [c_78, c_12207])).
% 12.29/5.08  tff(c_12256, plain, (![A_377]: (v7_waybel_0(k3_yellow19(A_377, k2_struct_0('#skF_5'), '#skF_6')) | v1_xboole_0('#skF_6') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(A_377))) | v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0(A_377) | v2_struct_0(A_377))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_12248])).
% 12.29/5.08  tff(c_12259, plain, (![A_380]: (v7_waybel_0(k3_yellow19(A_380, k2_struct_0('#skF_5'), '#skF_6')) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(A_380))) | ~l1_struct_0(A_380) | v2_struct_0(A_380))), inference(negUnitSimplification, [status(thm)], [c_165, c_86, c_12256])).
% 12.29/5.08  tff(c_12298, plain, (v7_waybel_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_138, c_12259])).
% 12.29/5.08  tff(c_12301, plain, (v7_waybel_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6666, c_101, c_12298])).
% 12.29/5.08  tff(c_12303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_11582, c_12301])).
% 12.29/5.08  tff(c_12304, plain, (![C_65]: (v2_struct_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | r1_waybel_7('#skF_5', '#skF_6', C_65) | ~r3_waybel_9('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), C_65) | ~m1_subset_1(C_65, k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_11577])).
% 12.29/5.08  tff(c_12306, plain, (v2_struct_0(k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_12304])).
% 12.29/5.08  tff(c_12311, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_6') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_12306, c_62])).
% 12.29/5.08  tff(c_12314, plain, (v1_xboole_0('#skF_6') | v1_xboole_0(k2_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6666, c_101, c_138, c_82, c_80, c_78, c_12311])).
% 12.29/5.08  tff(c_12316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_165, c_86, c_12314])).
% 12.29/5.08  tff(c_12319, plain, (![C_381]: (r1_waybel_7('#skF_5', '#skF_6', C_381) | ~r3_waybel_9('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'), C_381) | ~m1_subset_1(C_381, k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_12304])).
% 12.29/5.08  tff(c_12322, plain, (r1_waybel_7('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_6639, c_12319])).
% 12.29/5.08  tff(c_12325, plain, (r1_waybel_7('#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_12322])).
% 12.29/5.08  tff(c_12327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6636, c_12325])).
% 12.29/5.08  tff(c_12328, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_162])).
% 12.29/5.08  tff(c_12329, plain, (v1_xboole_0(k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_162])).
% 12.29/5.08  tff(c_6, plain, (![B_6, A_5]: (~v1_xboole_0(B_6) | B_6=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.29/5.08  tff(c_12341, plain, (![A_384]: (A_384='#skF_7' | ~v1_xboole_0(A_384))), inference(resolution, [status(thm)], [c_12328, c_6])).
% 12.29/5.08  tff(c_12348, plain, (k2_struct_0('#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_12329, c_12341])).
% 12.29/5.08  tff(c_12354, plain, (u1_struct_0('#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_12348, c_138])).
% 12.29/5.08  tff(c_12353, plain, (m1_subset_1('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_12348, c_139])).
% 12.29/5.08  tff(c_13938, plain, (![A_527, B_528]: (m2_connsp_2(k2_struct_0(A_527), A_527, B_528) | ~m1_subset_1(B_528, k1_zfmisc_1(u1_struct_0(A_527))) | ~l1_pre_topc(A_527) | ~v2_pre_topc(A_527) | v2_struct_0(A_527))), inference(cnfTransformation, [status(thm)], [f_107])).
% 12.29/5.08  tff(c_13945, plain, (![B_528]: (m2_connsp_2(k2_struct_0('#skF_5'), '#skF_5', B_528) | ~m1_subset_1(B_528, k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_12354, c_13938])).
% 12.29/5.08  tff(c_13955, plain, (![B_528]: (m2_connsp_2('#skF_7', '#skF_5', B_528) | ~m1_subset_1(B_528, k1_zfmisc_1('#skF_7')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_12348, c_13945])).
% 12.29/5.08  tff(c_13959, plain, (![B_529]: (m2_connsp_2('#skF_7', '#skF_5', B_529) | ~m1_subset_1(B_529, k1_zfmisc_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_92, c_13955])).
% 12.29/5.08  tff(c_13974, plain, (m2_connsp_2('#skF_7', '#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_101, c_13959])).
% 12.29/5.08  tff(c_12399, plain, (![A_389]: (m1_subset_1('#skF_4'(A_389), u1_struct_0(A_389)) | v7_struct_0(A_389) | ~l1_struct_0(A_389))), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.29/5.08  tff(c_12405, plain, (m1_subset_1('#skF_4'('#skF_5'), '#skF_7') | v7_struct_0('#skF_5') | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_12354, c_12399])).
% 12.29/5.08  tff(c_12407, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_12405])).
% 12.29/5.08  tff(c_12418, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_22, c_12407])).
% 12.29/5.08  tff(c_12422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_12418])).
% 12.29/5.08  tff(c_12424, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_12405])).
% 12.29/5.08  tff(c_12423, plain, (v7_struct_0('#skF_5') | m1_subset_1('#skF_4'('#skF_5'), '#skF_7')), inference(splitRight, [status(thm)], [c_12405])).
% 12.29/5.08  tff(c_12430, plain, (m1_subset_1('#skF_4'('#skF_5'), '#skF_7')), inference(splitLeft, [status(thm)], [c_12423])).
% 12.29/5.08  tff(c_14, plain, (![B_8, A_7]: (v1_xboole_0(B_8) | ~m1_subset_1(B_8, A_7) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.29/5.08  tff(c_12433, plain, (v1_xboole_0('#skF_4'('#skF_5')) | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_12430, c_14])).
% 12.29/5.08  tff(c_12436, plain, (v1_xboole_0('#skF_4'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_12328, c_12433])).
% 12.29/5.08  tff(c_12332, plain, (![A_5]: (A_5='#skF_7' | ~v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_12328, c_6])).
% 12.29/5.08  tff(c_12442, plain, ('#skF_4'('#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_12436, c_12332])).
% 12.29/5.08  tff(c_44, plain, (![A_39]: ('#skF_4'(A_39)!='#skF_3'(A_39) | v7_struct_0(A_39) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.29/5.08  tff(c_12700, plain, (![A_411, B_412]: (m2_connsp_2(k2_struct_0(A_411), A_411, B_412) | ~m1_subset_1(B_412, k1_zfmisc_1(u1_struct_0(A_411))) | ~l1_pre_topc(A_411) | ~v2_pre_topc(A_411) | v2_struct_0(A_411))), inference(cnfTransformation, [status(thm)], [f_107])).
% 12.29/5.08  tff(c_12707, plain, (![B_412]: (m2_connsp_2(k2_struct_0('#skF_5'), '#skF_5', B_412) | ~m1_subset_1(B_412, k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_12354, c_12700])).
% 12.29/5.08  tff(c_12717, plain, (![B_412]: (m2_connsp_2('#skF_7', '#skF_5', B_412) | ~m1_subset_1(B_412, k1_zfmisc_1('#skF_7')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_12348, c_12707])).
% 12.29/5.08  tff(c_12721, plain, (![B_413]: (m2_connsp_2('#skF_7', '#skF_5', B_413) | ~m1_subset_1(B_413, k1_zfmisc_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_92, c_12717])).
% 12.29/5.08  tff(c_12736, plain, (m2_connsp_2('#skF_7', '#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_101, c_12721])).
% 12.29/5.08  tff(c_12458, plain, (![A_391]: (m1_subset_1('#skF_3'(A_391), u1_struct_0(A_391)) | v7_struct_0(A_391) | ~l1_struct_0(A_391))), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.29/5.08  tff(c_12464, plain, (m1_subset_1('#skF_3'('#skF_5'), '#skF_7') | v7_struct_0('#skF_5') | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_12354, c_12458])).
% 12.29/5.08  tff(c_12467, plain, (m1_subset_1('#skF_3'('#skF_5'), '#skF_7') | v7_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12424, c_12464])).
% 12.29/5.08  tff(c_12468, plain, (v7_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_12467])).
% 12.29/5.08  tff(c_12469, plain, (![A_392]: (m1_subset_1('#skF_2'(A_392), u1_struct_0(A_392)) | ~v7_struct_0(A_392) | ~l1_struct_0(A_392) | v2_struct_0(A_392))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.29/5.08  tff(c_12475, plain, (m1_subset_1('#skF_2'('#skF_5'), '#skF_7') | ~v7_struct_0('#skF_5') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_12354, c_12469])).
% 12.29/5.08  tff(c_12478, plain, (m1_subset_1('#skF_2'('#skF_5'), '#skF_7') | ~v7_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12424, c_12475])).
% 12.29/5.08  tff(c_12479, plain, (m1_subset_1('#skF_2'('#skF_5'), '#skF_7') | ~v7_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_92, c_12478])).
% 12.29/5.08  tff(c_12481, plain, (m1_subset_1('#skF_2'('#skF_5'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_12468, c_12479])).
% 12.29/5.08  tff(c_12484, plain, (v1_xboole_0('#skF_2'('#skF_5')) | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_12481, c_14])).
% 12.29/5.08  tff(c_12487, plain, (v1_xboole_0('#skF_2'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_12328, c_12484])).
% 12.29/5.08  tff(c_12493, plain, ('#skF_2'('#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_12487, c_12332])).
% 12.29/5.08  tff(c_12529, plain, (![A_396]: (k6_domain_1(u1_struct_0(A_396), '#skF_2'(A_396))=u1_struct_0(A_396) | ~v7_struct_0(A_396) | ~l1_struct_0(A_396) | v2_struct_0(A_396))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.29/5.08  tff(c_12541, plain, (k6_domain_1('#skF_7', '#skF_2'('#skF_5'))=u1_struct_0('#skF_5') | ~v7_struct_0('#skF_5') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_12354, c_12529])).
% 12.29/5.08  tff(c_12548, plain, (k6_domain_1('#skF_7', '#skF_7')='#skF_7' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12424, c_12468, c_12493, c_12354, c_12541])).
% 12.29/5.08  tff(c_12549, plain, (k6_domain_1('#skF_7', '#skF_7')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_92, c_12548])).
% 12.29/5.08  tff(c_13475, plain, (![C_491, A_492, B_493]: (m1_connsp_2(C_491, A_492, B_493) | ~m2_connsp_2(C_491, A_492, k6_domain_1(u1_struct_0(A_492), B_493)) | ~m1_subset_1(C_491, k1_zfmisc_1(u1_struct_0(A_492))) | ~m1_subset_1(B_493, u1_struct_0(A_492)) | ~l1_pre_topc(A_492) | ~v2_pre_topc(A_492) | v2_struct_0(A_492))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.29/5.08  tff(c_13481, plain, (![C_491, B_493]: (m1_connsp_2(C_491, '#skF_5', B_493) | ~m2_connsp_2(C_491, '#skF_5', k6_domain_1('#skF_7', B_493)) | ~m1_subset_1(C_491, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_493, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_12354, c_13475])).
% 12.29/5.08  tff(c_13483, plain, (![C_491, B_493]: (m1_connsp_2(C_491, '#skF_5', B_493) | ~m2_connsp_2(C_491, '#skF_5', k6_domain_1('#skF_7', B_493)) | ~m1_subset_1(C_491, k1_zfmisc_1('#skF_7')) | ~m1_subset_1(B_493, '#skF_7') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_12354, c_12354, c_13481])).
% 12.29/5.08  tff(c_13485, plain, (![C_494, B_495]: (m1_connsp_2(C_494, '#skF_5', B_495) | ~m2_connsp_2(C_494, '#skF_5', k6_domain_1('#skF_7', B_495)) | ~m1_subset_1(C_494, k1_zfmisc_1('#skF_7')) | ~m1_subset_1(B_495, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_92, c_13483])).
% 12.29/5.08  tff(c_13488, plain, (![C_494]: (m1_connsp_2(C_494, '#skF_5', '#skF_7') | ~m2_connsp_2(C_494, '#skF_5', '#skF_7') | ~m1_subset_1(C_494, k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_7', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_12549, c_13485])).
% 12.29/5.08  tff(c_13491, plain, (![C_496]: (m1_connsp_2(C_496, '#skF_5', '#skF_7') | ~m2_connsp_2(C_496, '#skF_5', '#skF_7') | ~m1_subset_1(C_496, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_12353, c_13488])).
% 12.29/5.08  tff(c_13503, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_7') | ~m2_connsp_2('#skF_7', '#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_101, c_13491])).
% 12.29/5.08  tff(c_13510, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_12736, c_13503])).
% 12.29/5.08  tff(c_32, plain, (![C_33, B_31, A_27]: (r2_hidden(C_33, B_31) | ~m1_connsp_2(B_31, A_27, C_33) | ~m1_subset_1(C_33, u1_struct_0(A_27)) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_124])).
% 12.29/5.08  tff(c_13512, plain, (r2_hidden('#skF_7', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_13510, c_32])).
% 12.29/5.08  tff(c_13517, plain, (r2_hidden('#skF_7', '#skF_7') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_101, c_12354, c_12353, c_12354, c_13512])).
% 12.29/5.08  tff(c_13518, plain, (r2_hidden('#skF_7', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_92, c_13517])).
% 12.29/5.08  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.29/5.08  tff(c_13528, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_13518, c_2])).
% 12.29/5.08  tff(c_13534, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12328, c_13528])).
% 12.29/5.08  tff(c_13536, plain, (~v7_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_12467])).
% 12.29/5.08  tff(c_13539, plain, ('#skF_4'('#skF_5')!='#skF_3'('#skF_5') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_44, c_13536])).
% 12.29/5.08  tff(c_13542, plain, ('#skF_3'('#skF_5')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_12424, c_12442, c_13539])).
% 12.29/5.08  tff(c_13535, plain, (m1_subset_1('#skF_3'('#skF_5'), '#skF_7')), inference(splitRight, [status(thm)], [c_12467])).
% 12.29/5.08  tff(c_13545, plain, (v1_xboole_0('#skF_3'('#skF_5')) | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_13535, c_14])).
% 12.29/5.08  tff(c_13548, plain, (v1_xboole_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_12328, c_13545])).
% 12.29/5.08  tff(c_13551, plain, ('#skF_3'('#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_13548, c_12332])).
% 12.29/5.08  tff(c_13557, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13542, c_13551])).
% 12.29/5.08  tff(c_13558, plain, (v7_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_12423])).
% 12.29/5.08  tff(c_13583, plain, (![A_499]: (m1_subset_1('#skF_2'(A_499), u1_struct_0(A_499)) | ~v7_struct_0(A_499) | ~l1_struct_0(A_499) | v2_struct_0(A_499))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.29/5.08  tff(c_13589, plain, (m1_subset_1('#skF_2'('#skF_5'), '#skF_7') | ~v7_struct_0('#skF_5') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_12354, c_13583])).
% 12.29/5.08  tff(c_13592, plain, (m1_subset_1('#skF_2'('#skF_5'), '#skF_7') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12424, c_13558, c_13589])).
% 12.29/5.08  tff(c_13593, plain, (m1_subset_1('#skF_2'('#skF_5'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_92, c_13592])).
% 12.29/5.08  tff(c_13596, plain, (v1_xboole_0('#skF_2'('#skF_5')) | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_13593, c_14])).
% 12.29/5.08  tff(c_13599, plain, (v1_xboole_0('#skF_2'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_12328, c_13596])).
% 12.29/5.08  tff(c_13605, plain, ('#skF_2'('#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_13599, c_12332])).
% 12.29/5.08  tff(c_13628, plain, (![A_501]: (k6_domain_1(u1_struct_0(A_501), '#skF_2'(A_501))=u1_struct_0(A_501) | ~v7_struct_0(A_501) | ~l1_struct_0(A_501) | v2_struct_0(A_501))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.29/5.08  tff(c_13640, plain, (k6_domain_1('#skF_7', '#skF_2'('#skF_5'))=u1_struct_0('#skF_5') | ~v7_struct_0('#skF_5') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_12354, c_13628])).
% 12.29/5.08  tff(c_13647, plain, (k6_domain_1('#skF_7', '#skF_7')='#skF_7' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12424, c_13558, c_13605, c_12354, c_13640])).
% 12.29/5.08  tff(c_13648, plain, (k6_domain_1('#skF_7', '#skF_7')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_92, c_13647])).
% 12.29/5.08  tff(c_14482, plain, (![C_596, A_597, B_598]: (m1_connsp_2(C_596, A_597, B_598) | ~m2_connsp_2(C_596, A_597, k6_domain_1(u1_struct_0(A_597), B_598)) | ~m1_subset_1(C_596, k1_zfmisc_1(u1_struct_0(A_597))) | ~m1_subset_1(B_598, u1_struct_0(A_597)) | ~l1_pre_topc(A_597) | ~v2_pre_topc(A_597) | v2_struct_0(A_597))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.29/5.08  tff(c_14491, plain, (![C_596, B_598]: (m1_connsp_2(C_596, '#skF_5', B_598) | ~m2_connsp_2(C_596, '#skF_5', k6_domain_1('#skF_7', B_598)) | ~m1_subset_1(C_596, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_598, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_12354, c_14482])).
% 12.29/5.08  tff(c_14494, plain, (![C_596, B_598]: (m1_connsp_2(C_596, '#skF_5', B_598) | ~m2_connsp_2(C_596, '#skF_5', k6_domain_1('#skF_7', B_598)) | ~m1_subset_1(C_596, k1_zfmisc_1('#skF_7')) | ~m1_subset_1(B_598, '#skF_7') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_12354, c_12354, c_14491])).
% 12.29/5.08  tff(c_14496, plain, (![C_599, B_600]: (m1_connsp_2(C_599, '#skF_5', B_600) | ~m2_connsp_2(C_599, '#skF_5', k6_domain_1('#skF_7', B_600)) | ~m1_subset_1(C_599, k1_zfmisc_1('#skF_7')) | ~m1_subset_1(B_600, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_92, c_14494])).
% 12.29/5.08  tff(c_14502, plain, (![C_599]: (m1_connsp_2(C_599, '#skF_5', '#skF_7') | ~m2_connsp_2(C_599, '#skF_5', '#skF_7') | ~m1_subset_1(C_599, k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_7', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_13648, c_14496])).
% 12.29/5.08  tff(c_14506, plain, (![C_601]: (m1_connsp_2(C_601, '#skF_5', '#skF_7') | ~m2_connsp_2(C_601, '#skF_5', '#skF_7') | ~m1_subset_1(C_601, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_12353, c_14502])).
% 12.29/5.08  tff(c_14518, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_7') | ~m2_connsp_2('#skF_7', '#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_101, c_14506])).
% 12.29/5.08  tff(c_14525, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13974, c_14518])).
% 12.29/5.08  tff(c_14527, plain, (r2_hidden('#skF_7', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_14525, c_32])).
% 12.29/5.08  tff(c_14532, plain, (r2_hidden('#skF_7', '#skF_7') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_101, c_12354, c_12353, c_12354, c_14527])).
% 12.29/5.08  tff(c_14533, plain, (r2_hidden('#skF_7', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_92, c_14532])).
% 12.29/5.08  tff(c_14543, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_14533, c_2])).
% 12.29/5.08  tff(c_14549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12328, c_14543])).
% 12.29/5.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.29/5.08  
% 12.29/5.08  Inference rules
% 12.29/5.08  ----------------------
% 12.29/5.08  #Ref     : 0
% 12.29/5.08  #Sup     : 4087
% 12.29/5.08  #Fact    : 28
% 12.29/5.08  #Define  : 0
% 12.29/5.08  #Split   : 37
% 12.29/5.08  #Chain   : 0
% 12.29/5.08  #Close   : 0
% 12.29/5.08  
% 12.29/5.08  Ordering : KBO
% 12.29/5.08  
% 12.29/5.08  Simplification rules
% 12.29/5.08  ----------------------
% 12.29/5.08  #Subsume      : 1997
% 12.29/5.08  #Demod        : 1454
% 12.29/5.08  #Tautology    : 937
% 12.29/5.08  #SimpNegUnit  : 296
% 12.29/5.08  #BackRed      : 21
% 12.29/5.08  
% 12.29/5.08  #Partial instantiations: 0
% 12.29/5.08  #Strategies tried      : 1
% 12.29/5.08  
% 12.29/5.08  Timing (in seconds)
% 12.29/5.08  ----------------------
% 12.29/5.08  Preprocessing        : 0.41
% 12.29/5.08  Parsing              : 0.21
% 12.29/5.08  CNF conversion       : 0.03
% 12.29/5.08  Main loop            : 3.88
% 12.29/5.08  Inferencing          : 0.75
% 12.29/5.08  Reduction            : 0.86
% 12.29/5.08  Demodulation         : 0.62
% 12.29/5.08  BG Simplification    : 0.09
% 12.29/5.08  Subsumption          : 2.05
% 12.29/5.08  Abstraction          : 0.14
% 12.29/5.08  MUC search           : 0.00
% 12.29/5.08  Cooper               : 0.00
% 12.29/5.08  Total                : 4.36
% 12.29/5.08  Index Insertion      : 0.00
% 12.29/5.08  Index Deletion       : 0.00
% 12.29/5.09  Index Matching       : 0.00
% 12.29/5.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
