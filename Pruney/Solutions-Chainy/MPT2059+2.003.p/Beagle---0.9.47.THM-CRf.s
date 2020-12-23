%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:36 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  181 (1811 expanded)
%              Number of leaves         :   43 ( 637 expanded)
%              Depth                    :   18
%              Number of atoms          :  548 (9010 expanded)
%              Number of equality atoms :   14 ( 247 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k10_yellow_6 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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
               => ( r2_hidden(C,k10_yellow_6(A,k3_yellow19(A,k2_struct_0(A),B)))
                <=> r2_waybel_7(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow19)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_yellow19)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow19)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow19)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

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
             => ( r2_hidden(C,k10_yellow_6(A,B))
              <=> r2_waybel_7(A,k2_yellow19(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow19)).

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
    ( ~ r2_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_104,plain,(
    ~ r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,
    ( r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
    | r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_121,plain,(
    r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_70])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_52,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_50,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_129,plain,(
    ! [A_53,B_54,C_55] :
      ( v3_orders_2(k3_yellow19(A_53,B_54,C_55))
      | ~ m1_subset_1(C_55,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_54))))
      | ~ v13_waybel_0(C_55,k3_yellow_1(B_54))
      | ~ v2_waybel_0(C_55,k3_yellow_1(B_54))
      | v1_xboole_0(C_55)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | v1_xboole_0(B_54)
      | ~ l1_struct_0(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_134,plain,(
    ! [A_53] :
      ( v3_orders_2(k3_yellow19(A_53,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_53)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_53)
      | v2_struct_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_48,c_129])).

tff(c_138,plain,(
    ! [A_53] :
      ( v3_orders_2(k3_yellow19(A_53,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_53)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_53)
      | v2_struct_0(A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_134])).

tff(c_139,plain,(
    ! [A_53] :
      ( v3_orders_2(k3_yellow19(A_53,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_53)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_53)
      | v2_struct_0(A_53) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_138])).

tff(c_140,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_16,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(k2_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_143,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_140,c_16])).

tff(c_146,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_143])).

tff(c_149,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_146])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_149])).

tff(c_155,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_156,plain,(
    ! [A_56] :
      ( v3_orders_2(k3_yellow19(A_56,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_struct_0(A_56)
      | v2_struct_0(A_56) ) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_162,plain,
    ( v3_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_156])).

tff(c_164,plain,
    ( v3_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_162])).

tff(c_176,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_179,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_176])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_179])).

tff(c_185,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_184,plain,
    ( ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | v3_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_202,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_205,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_202])).

tff(c_209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_205])).

tff(c_211,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_165,plain,(
    ! [A_57,B_58,C_59] :
      ( v4_orders_2(k3_yellow19(A_57,B_58,C_59))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_58))))
      | ~ v13_waybel_0(C_59,k3_yellow_1(B_58))
      | ~ v2_waybel_0(C_59,k3_yellow_1(B_58))
      | v1_xboole_0(C_59)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | v1_xboole_0(B_58)
      | ~ l1_struct_0(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_170,plain,(
    ! [A_57] :
      ( v4_orders_2(k3_yellow19(A_57,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_57)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_57)
      | v2_struct_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_48,c_165])).

tff(c_174,plain,(
    ! [A_57] :
      ( v4_orders_2(k3_yellow19(A_57,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_57)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_57)
      | v2_struct_0(A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_170])).

tff(c_191,plain,(
    ! [A_60] :
      ( v4_orders_2(k3_yellow19(A_60,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_struct_0(A_60)
      | v2_struct_0(A_60) ) ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_56,c_174])).

tff(c_197,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_191])).

tff(c_200,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_197])).

tff(c_201,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_200])).

tff(c_218,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_201])).

tff(c_54,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_365,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_370,plain,(
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
    inference(resolution,[status(thm)],[c_48,c_365])).

tff(c_374,plain,(
    ! [A_90] :
      ( v7_waybel_0(k3_yellow19(A_90,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_90)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_90)
      | v2_struct_0(A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_370])).

tff(c_376,plain,(
    ! [A_93] :
      ( v7_waybel_0(k3_yellow19(A_93,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_56,c_374])).

tff(c_382,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_376])).

tff(c_385,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_211,c_382])).

tff(c_386,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_385])).

tff(c_295,plain,(
    ! [A_76,B_77,C_78] :
      ( l1_waybel_0(k3_yellow19(A_76,B_77,C_78),A_76)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_77))))
      | ~ v13_waybel_0(C_78,k3_yellow_1(B_77))
      | ~ v2_waybel_0(C_78,k3_yellow_1(B_77))
      | v1_xboole_0(C_78)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | v1_xboole_0(B_77)
      | ~ l1_struct_0(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_300,plain,(
    ! [A_76] :
      ( l1_waybel_0(k3_yellow19(A_76,k2_struct_0('#skF_1'),'#skF_2'),A_76)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_76)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_76)
      | v2_struct_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_48,c_295])).

tff(c_304,plain,(
    ! [A_76] :
      ( l1_waybel_0(k3_yellow19(A_76,k2_struct_0('#skF_1'),'#skF_2'),A_76)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_76)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_76)
      | v2_struct_0(A_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_300])).

tff(c_310,plain,(
    ! [A_79] :
      ( l1_waybel_0(k3_yellow19(A_79,k2_struct_0('#skF_1'),'#skF_2'),A_79)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_struct_0(A_79)
      | v2_struct_0(A_79) ) ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_56,c_304])).

tff(c_315,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_310])).

tff(c_318,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_211,c_315])).

tff(c_319,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_318])).

tff(c_448,plain,(
    ! [A_108,B_109] :
      ( k2_yellow19(A_108,k3_yellow19(A_108,k2_struct_0(A_108),B_109)) = B_109
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_108)))))
      | ~ v13_waybel_0(B_109,k3_yellow_1(k2_struct_0(A_108)))
      | ~ v2_waybel_0(B_109,k3_yellow_1(k2_struct_0(A_108)))
      | ~ v1_subset_1(B_109,u1_struct_0(k3_yellow_1(k2_struct_0(A_108))))
      | v1_xboole_0(B_109)
      | ~ l1_struct_0(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_453,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_448])).

tff(c_457,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_54,c_52,c_50,c_453])).

tff(c_458,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_457])).

tff(c_40,plain,(
    ! [C_24,A_18,B_22] :
      ( r2_hidden(C_24,k10_yellow_6(A_18,B_22))
      | ~ r2_waybel_7(A_18,k2_yellow19(A_18,B_22),C_24)
      | ~ m1_subset_1(C_24,u1_struct_0(A_18))
      | ~ l1_waybel_0(B_22,A_18)
      | ~ v7_waybel_0(B_22)
      | ~ v4_orders_2(B_22)
      | v2_struct_0(B_22)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_462,plain,(
    ! [C_24] :
      ( r2_hidden(C_24,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_24)
      | ~ m1_subset_1(C_24,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_40])).

tff(c_469,plain,(
    ! [C_24] :
      ( r2_hidden(C_24,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_24)
      | ~ m1_subset_1(C_24,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_218,c_386,c_319,c_92,c_462])).

tff(c_470,plain,(
    ! [C_24] :
      ( r2_hidden(C_24,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_24)
      | ~ m1_subset_1(C_24,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_469])).

tff(c_475,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_470])).

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

tff(c_477,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_475,c_32])).

tff(c_480,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_211,c_92,c_52,c_50,c_48,c_477])).

tff(c_482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_155,c_56,c_480])).

tff(c_497,plain,(
    ! [C_113] :
      ( r2_hidden(C_113,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ r2_waybel_7('#skF_1','#skF_2',C_113)
      | ~ m1_subset_1(C_113,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_470])).

tff(c_503,plain,
    ( ~ r2_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_497,c_104])).

tff(c_508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_121,c_503])).

tff(c_509,plain,(
    ~ r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_516,plain,(
    r2_hidden('#skF_3',k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_509,c_70])).

tff(c_536,plain,(
    ! [A_127,B_128,C_129] :
      ( v4_orders_2(k3_yellow19(A_127,B_128,C_129))
      | ~ m1_subset_1(C_129,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_128))))
      | ~ v13_waybel_0(C_129,k3_yellow_1(B_128))
      | ~ v2_waybel_0(C_129,k3_yellow_1(B_128))
      | v1_xboole_0(C_129)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | v1_xboole_0(B_128)
      | ~ l1_struct_0(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_541,plain,(
    ! [A_127] :
      ( v4_orders_2(k3_yellow19(A_127,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_127)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_127)
      | v2_struct_0(A_127) ) ),
    inference(resolution,[status(thm)],[c_48,c_536])).

tff(c_545,plain,(
    ! [A_127] :
      ( v4_orders_2(k3_yellow19(A_127,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_127)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_127)
      | v2_struct_0(A_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_541])).

tff(c_546,plain,(
    ! [A_127] :
      ( v4_orders_2(k3_yellow19(A_127,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_127)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_127)
      | v2_struct_0(A_127) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_545])).

tff(c_547,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_546])).

tff(c_550,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_547,c_16])).

tff(c_553,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_550])).

tff(c_556,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_553])).

tff(c_560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_556])).

tff(c_562,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_546])).

tff(c_563,plain,(
    ! [A_130] :
      ( v4_orders_2(k3_yellow19(A_130,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_struct_0(A_130)
      | v2_struct_0(A_130) ) ),
    inference(splitRight,[status(thm)],[c_546])).

tff(c_569,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_563])).

tff(c_571,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_569])).

tff(c_572,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_571])).

tff(c_575,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_572])).

tff(c_579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_575])).

tff(c_581,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_571])).

tff(c_580,plain,
    ( ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_571])).

tff(c_598,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_580])).

tff(c_601,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_598])).

tff(c_605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_601])).

tff(c_607,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_580])).

tff(c_606,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_580])).

tff(c_662,plain,(
    ! [A_142,B_143,C_144] :
      ( l1_waybel_0(k3_yellow19(A_142,B_143,C_144),A_142)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_143))))
      | ~ v13_waybel_0(C_144,k3_yellow_1(B_143))
      | ~ v2_waybel_0(C_144,k3_yellow_1(B_143))
      | v1_xboole_0(C_144)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | v1_xboole_0(B_143)
      | ~ l1_struct_0(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_667,plain,(
    ! [A_142] :
      ( l1_waybel_0(k3_yellow19(A_142,k2_struct_0('#skF_1'),'#skF_2'),A_142)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_142)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_142)
      | v2_struct_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_48,c_662])).

tff(c_671,plain,(
    ! [A_142] :
      ( l1_waybel_0(k3_yellow19(A_142,k2_struct_0('#skF_1'),'#skF_2'),A_142)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_142)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_142)
      | v2_struct_0(A_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_667])).

tff(c_673,plain,(
    ! [A_145] :
      ( l1_waybel_0(k3_yellow19(A_145,k2_struct_0('#skF_1'),'#skF_2'),A_145)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_struct_0(A_145)
      | v2_struct_0(A_145) ) ),
    inference(negUnitSimplification,[status(thm)],[c_562,c_56,c_671])).

tff(c_678,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_673])).

tff(c_681,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_607,c_678])).

tff(c_682,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_681])).

tff(c_717,plain,(
    ! [A_152,B_153] :
      ( k2_yellow19(A_152,k3_yellow19(A_152,k2_struct_0(A_152),B_153)) = B_153
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_152)))))
      | ~ v13_waybel_0(B_153,k3_yellow_1(k2_struct_0(A_152)))
      | ~ v2_waybel_0(B_153,k3_yellow_1(k2_struct_0(A_152)))
      | ~ v1_subset_1(B_153,u1_struct_0(k3_yellow_1(k2_struct_0(A_152))))
      | v1_xboole_0(B_153)
      | ~ l1_struct_0(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_722,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_717])).

tff(c_726,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_54,c_52,c_50,c_722])).

tff(c_727,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_726])).

tff(c_42,plain,(
    ! [A_18,B_22,C_24] :
      ( r2_waybel_7(A_18,k2_yellow19(A_18,B_22),C_24)
      | ~ r2_hidden(C_24,k10_yellow_6(A_18,B_22))
      | ~ m1_subset_1(C_24,u1_struct_0(A_18))
      | ~ l1_waybel_0(B_22,A_18)
      | ~ v7_waybel_0(B_22)
      | ~ v4_orders_2(B_22)
      | v2_struct_0(B_22)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_731,plain,(
    ! [C_24] :
      ( r2_waybel_7('#skF_1','#skF_2',C_24)
      | ~ r2_hidden(C_24,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_24,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_727,c_42])).

tff(c_738,plain,(
    ! [C_24] :
      ( r2_waybel_7('#skF_1','#skF_2',C_24)
      | ~ r2_hidden(C_24,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_24,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_606,c_682,c_92,c_731])).

tff(c_739,plain,(
    ! [C_24] :
      ( r2_waybel_7('#skF_1','#skF_2',C_24)
      | ~ r2_hidden(C_24,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_24,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_738])).

tff(c_744,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_739])).

tff(c_762,plain,(
    ! [A_158,B_159,C_160] :
      ( v7_waybel_0(k3_yellow19(A_158,B_159,C_160))
      | ~ m1_subset_1(C_160,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_159))))
      | ~ v13_waybel_0(C_160,k3_yellow_1(B_159))
      | ~ v2_waybel_0(C_160,k3_yellow_1(B_159))
      | ~ v1_subset_1(C_160,u1_struct_0(k3_yellow_1(B_159)))
      | v1_xboole_0(C_160)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_158)))
      | v1_xboole_0(B_159)
      | ~ l1_struct_0(A_158)
      | v2_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_767,plain,(
    ! [A_158] :
      ( v7_waybel_0(k3_yellow19(A_158,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_158)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_158)
      | v2_struct_0(A_158) ) ),
    inference(resolution,[status(thm)],[c_48,c_762])).

tff(c_771,plain,(
    ! [A_158] :
      ( v7_waybel_0(k3_yellow19(A_158,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_158)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_158)
      | v2_struct_0(A_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_767])).

tff(c_773,plain,(
    ! [A_161] :
      ( v7_waybel_0(k3_yellow19(A_161,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_struct_0(A_161)
      | v2_struct_0(A_161) ) ),
    inference(negUnitSimplification,[status(thm)],[c_562,c_56,c_771])).

tff(c_779,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_773])).

tff(c_782,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_607,c_779])).

tff(c_784,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_744,c_782])).

tff(c_785,plain,(
    ! [C_24] :
      ( v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | r2_waybel_7('#skF_1','#skF_2',C_24)
      | ~ r2_hidden(C_24,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_24,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_739])).

tff(c_787,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_785])).

tff(c_792,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_787,c_32])).

tff(c_795,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_607,c_92,c_52,c_50,c_48,c_792])).

tff(c_797,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_562,c_56,c_795])).

tff(c_800,plain,(
    ! [C_162] :
      ( r2_waybel_7('#skF_1','#skF_2',C_162)
      | ~ r2_hidden(C_162,k10_yellow_6('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(C_162,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_785])).

tff(c_803,plain,
    ( r2_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_516,c_800])).

tff(c_806,plain,(
    r2_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_803])).

tff(c_808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_509,c_806])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:38:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.72  
% 3.31/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.72  %$ r2_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k10_yellow_6 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1
% 3.31/1.72  
% 3.31/1.72  %Foreground sorts:
% 3.31/1.72  
% 3.31/1.72  
% 3.31/1.72  %Background operators:
% 3.31/1.72  
% 3.31/1.72  
% 3.31/1.72  %Foreground operators:
% 3.31/1.72  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.31/1.72  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.31/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.72  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.31/1.72  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 3.31/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.31/1.72  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.31/1.72  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.31/1.72  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.31/1.72  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 3.31/1.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.31/1.72  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.31/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.72  tff('#skF_1', type, '#skF_1': $i).
% 3.31/1.72  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.31/1.72  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.31/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.72  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.31/1.72  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.31/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.72  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.31/1.72  tff(r2_waybel_7, type, r2_waybel_7: ($i * $i * $i) > $o).
% 3.31/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.72  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.31/1.72  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.31/1.72  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.31/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.31/1.72  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.31/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.31/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.72  
% 3.65/1.75  tff(f_205, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, k3_yellow19(A, k2_struct_0(A), B))) <=> r2_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow19)).
% 3.65/1.75  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.65/1.75  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.65/1.75  tff(f_107, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_yellow19)).
% 3.65/1.75  tff(f_51, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.65/1.75  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.65/1.75  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.65/1.75  tff(f_135, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow19)).
% 3.65/1.75  tff(f_79, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 3.65/1.75  tff(f_178, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 3.65/1.75  tff(f_159, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, B)) <=> r2_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow19)).
% 3.65/1.75  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.65/1.75  tff(c_14, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.65/1.75  tff(c_83, plain, (![A_35]: (u1_struct_0(A_35)=k2_struct_0(A_35) | ~l1_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.65/1.75  tff(c_88, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_pre_topc(A_36))), inference(resolution, [status(thm)], [c_14, c_83])).
% 3.65/1.75  tff(c_92, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_88])).
% 3.65/1.75  tff(c_46, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.65/1.75  tff(c_93, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_46])).
% 3.65/1.75  tff(c_64, plain, (~r2_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.65/1.75  tff(c_104, plain, (~r2_hidden('#skF_3', k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(splitLeft, [status(thm)], [c_64])).
% 3.65/1.75  tff(c_70, plain, (r2_hidden('#skF_3', k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | r2_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.65/1.75  tff(c_121, plain, (r2_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_104, c_70])).
% 3.65/1.75  tff(c_62, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.65/1.75  tff(c_56, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.65/1.75  tff(c_52, plain, (v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.65/1.75  tff(c_50, plain, (v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.65/1.75  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.65/1.75  tff(c_129, plain, (![A_53, B_54, C_55]: (v3_orders_2(k3_yellow19(A_53, B_54, C_55)) | ~m1_subset_1(C_55, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_54)))) | ~v13_waybel_0(C_55, k3_yellow_1(B_54)) | ~v2_waybel_0(C_55, k3_yellow_1(B_54)) | v1_xboole_0(C_55) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | v1_xboole_0(B_54) | ~l1_struct_0(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.65/1.75  tff(c_134, plain, (![A_53]: (v3_orders_2(k3_yellow19(A_53, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_53))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_53) | v2_struct_0(A_53))), inference(resolution, [status(thm)], [c_48, c_129])).
% 3.65/1.75  tff(c_138, plain, (![A_53]: (v3_orders_2(k3_yellow19(A_53, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_53))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_53) | v2_struct_0(A_53))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_134])).
% 3.65/1.75  tff(c_139, plain, (![A_53]: (v3_orders_2(k3_yellow19(A_53, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_53))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_53) | v2_struct_0(A_53))), inference(negUnitSimplification, [status(thm)], [c_56, c_138])).
% 3.65/1.75  tff(c_140, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_139])).
% 3.65/1.75  tff(c_16, plain, (![A_7]: (~v1_xboole_0(k2_struct_0(A_7)) | ~l1_struct_0(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.65/1.75  tff(c_143, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_140, c_16])).
% 3.65/1.75  tff(c_146, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_143])).
% 3.65/1.75  tff(c_149, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_146])).
% 3.65/1.75  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_149])).
% 3.65/1.75  tff(c_155, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_139])).
% 3.65/1.75  tff(c_156, plain, (![A_56]: (v3_orders_2(k3_yellow19(A_56, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_struct_0(A_56) | v2_struct_0(A_56))), inference(splitRight, [status(thm)], [c_139])).
% 3.65/1.75  tff(c_162, plain, (v3_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_92, c_156])).
% 3.65/1.75  tff(c_164, plain, (v3_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_162])).
% 3.65/1.75  tff(c_176, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_164])).
% 3.65/1.75  tff(c_179, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_176])).
% 3.65/1.75  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_179])).
% 3.65/1.75  tff(c_185, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_164])).
% 3.65/1.75  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.65/1.75  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.65/1.75  tff(c_184, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | v3_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_164])).
% 3.65/1.75  tff(c_202, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_184])).
% 3.65/1.75  tff(c_205, plain, (~r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_202])).
% 3.65/1.75  tff(c_209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_205])).
% 3.65/1.75  tff(c_211, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_184])).
% 3.65/1.75  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.65/1.75  tff(c_165, plain, (![A_57, B_58, C_59]: (v4_orders_2(k3_yellow19(A_57, B_58, C_59)) | ~m1_subset_1(C_59, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_58)))) | ~v13_waybel_0(C_59, k3_yellow_1(B_58)) | ~v2_waybel_0(C_59, k3_yellow_1(B_58)) | v1_xboole_0(C_59) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | v1_xboole_0(B_58) | ~l1_struct_0(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.65/1.75  tff(c_170, plain, (![A_57]: (v4_orders_2(k3_yellow19(A_57, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_57))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_57) | v2_struct_0(A_57))), inference(resolution, [status(thm)], [c_48, c_165])).
% 3.65/1.75  tff(c_174, plain, (![A_57]: (v4_orders_2(k3_yellow19(A_57, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_57))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_57) | v2_struct_0(A_57))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_170])).
% 3.65/1.75  tff(c_191, plain, (![A_60]: (v4_orders_2(k3_yellow19(A_60, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_struct_0(A_60) | v2_struct_0(A_60))), inference(negUnitSimplification, [status(thm)], [c_155, c_56, c_174])).
% 3.65/1.75  tff(c_197, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_92, c_191])).
% 3.65/1.75  tff(c_200, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_197])).
% 3.65/1.75  tff(c_201, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_62, c_200])).
% 3.65/1.75  tff(c_218, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_201])).
% 3.65/1.75  tff(c_54, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.65/1.75  tff(c_365, plain, (![A_90, B_91, C_92]: (v7_waybel_0(k3_yellow19(A_90, B_91, C_92)) | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_91)))) | ~v13_waybel_0(C_92, k3_yellow_1(B_91)) | ~v2_waybel_0(C_92, k3_yellow_1(B_91)) | ~v1_subset_1(C_92, u1_struct_0(k3_yellow_1(B_91))) | v1_xboole_0(C_92) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | v1_xboole_0(B_91) | ~l1_struct_0(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.65/1.75  tff(c_370, plain, (![A_90]: (v7_waybel_0(k3_yellow19(A_90, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_90))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_90) | v2_struct_0(A_90))), inference(resolution, [status(thm)], [c_48, c_365])).
% 3.65/1.75  tff(c_374, plain, (![A_90]: (v7_waybel_0(k3_yellow19(A_90, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_90))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_90) | v2_struct_0(A_90))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_370])).
% 3.65/1.75  tff(c_376, plain, (![A_93]: (v7_waybel_0(k3_yellow19(A_93, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_struct_0(A_93) | v2_struct_0(A_93))), inference(negUnitSimplification, [status(thm)], [c_155, c_56, c_374])).
% 3.65/1.75  tff(c_382, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_92, c_376])).
% 3.65/1.75  tff(c_385, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_211, c_382])).
% 3.65/1.75  tff(c_386, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_385])).
% 3.65/1.75  tff(c_295, plain, (![A_76, B_77, C_78]: (l1_waybel_0(k3_yellow19(A_76, B_77, C_78), A_76) | ~m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_77)))) | ~v13_waybel_0(C_78, k3_yellow_1(B_77)) | ~v2_waybel_0(C_78, k3_yellow_1(B_77)) | v1_xboole_0(C_78) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | v1_xboole_0(B_77) | ~l1_struct_0(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.65/1.75  tff(c_300, plain, (![A_76]: (l1_waybel_0(k3_yellow19(A_76, k2_struct_0('#skF_1'), '#skF_2'), A_76) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_76))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_76) | v2_struct_0(A_76))), inference(resolution, [status(thm)], [c_48, c_295])).
% 3.65/1.75  tff(c_304, plain, (![A_76]: (l1_waybel_0(k3_yellow19(A_76, k2_struct_0('#skF_1'), '#skF_2'), A_76) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_76))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_76) | v2_struct_0(A_76))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_300])).
% 3.65/1.75  tff(c_310, plain, (![A_79]: (l1_waybel_0(k3_yellow19(A_79, k2_struct_0('#skF_1'), '#skF_2'), A_79) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_struct_0(A_79) | v2_struct_0(A_79))), inference(negUnitSimplification, [status(thm)], [c_155, c_56, c_304])).
% 3.65/1.75  tff(c_315, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_92, c_310])).
% 3.65/1.75  tff(c_318, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_211, c_315])).
% 3.65/1.75  tff(c_319, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_318])).
% 3.65/1.75  tff(c_448, plain, (![A_108, B_109]: (k2_yellow19(A_108, k3_yellow19(A_108, k2_struct_0(A_108), B_109))=B_109 | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_108))))) | ~v13_waybel_0(B_109, k3_yellow_1(k2_struct_0(A_108))) | ~v2_waybel_0(B_109, k3_yellow_1(k2_struct_0(A_108))) | ~v1_subset_1(B_109, u1_struct_0(k3_yellow_1(k2_struct_0(A_108)))) | v1_xboole_0(B_109) | ~l1_struct_0(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.65/1.75  tff(c_453, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_448])).
% 3.65/1.75  tff(c_457, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_54, c_52, c_50, c_453])).
% 3.65/1.75  tff(c_458, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_457])).
% 3.65/1.75  tff(c_40, plain, (![C_24, A_18, B_22]: (r2_hidden(C_24, k10_yellow_6(A_18, B_22)) | ~r2_waybel_7(A_18, k2_yellow19(A_18, B_22), C_24) | ~m1_subset_1(C_24, u1_struct_0(A_18)) | ~l1_waybel_0(B_22, A_18) | ~v7_waybel_0(B_22) | ~v4_orders_2(B_22) | v2_struct_0(B_22) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.65/1.75  tff(c_462, plain, (![C_24]: (r2_hidden(C_24, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_24) | ~m1_subset_1(C_24, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_458, c_40])).
% 3.65/1.75  tff(c_469, plain, (![C_24]: (r2_hidden(C_24, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_24) | ~m1_subset_1(C_24, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_218, c_386, c_319, c_92, c_462])).
% 3.65/1.75  tff(c_470, plain, (![C_24]: (r2_hidden(C_24, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_24) | ~m1_subset_1(C_24, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_62, c_469])).
% 3.65/1.75  tff(c_475, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_470])).
% 3.65/1.75  tff(c_32, plain, (![A_12, B_13, C_14]: (~v2_struct_0(k3_yellow19(A_12, B_13, C_14)) | ~m1_subset_1(C_14, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_13)))) | ~v13_waybel_0(C_14, k3_yellow_1(B_13)) | ~v2_waybel_0(C_14, k3_yellow_1(B_13)) | v1_xboole_0(C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_12))) | v1_xboole_0(B_13) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.65/1.75  tff(c_477, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_475, c_32])).
% 3.65/1.75  tff(c_480, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_211, c_92, c_52, c_50, c_48, c_477])).
% 3.65/1.75  tff(c_482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_155, c_56, c_480])).
% 3.65/1.75  tff(c_497, plain, (![C_113]: (r2_hidden(C_113, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~r2_waybel_7('#skF_1', '#skF_2', C_113) | ~m1_subset_1(C_113, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_470])).
% 3.65/1.75  tff(c_503, plain, (~r2_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_497, c_104])).
% 3.65/1.75  tff(c_508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_121, c_503])).
% 3.65/1.75  tff(c_509, plain, (~r2_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_64])).
% 3.65/1.75  tff(c_516, plain, (r2_hidden('#skF_3', k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_509, c_70])).
% 3.65/1.75  tff(c_536, plain, (![A_127, B_128, C_129]: (v4_orders_2(k3_yellow19(A_127, B_128, C_129)) | ~m1_subset_1(C_129, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_128)))) | ~v13_waybel_0(C_129, k3_yellow_1(B_128)) | ~v2_waybel_0(C_129, k3_yellow_1(B_128)) | v1_xboole_0(C_129) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | v1_xboole_0(B_128) | ~l1_struct_0(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.65/1.75  tff(c_541, plain, (![A_127]: (v4_orders_2(k3_yellow19(A_127, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_127))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_127) | v2_struct_0(A_127))), inference(resolution, [status(thm)], [c_48, c_536])).
% 3.65/1.75  tff(c_545, plain, (![A_127]: (v4_orders_2(k3_yellow19(A_127, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_127))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_127) | v2_struct_0(A_127))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_541])).
% 3.65/1.75  tff(c_546, plain, (![A_127]: (v4_orders_2(k3_yellow19(A_127, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_127))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_127) | v2_struct_0(A_127))), inference(negUnitSimplification, [status(thm)], [c_56, c_545])).
% 3.65/1.75  tff(c_547, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_546])).
% 3.65/1.75  tff(c_550, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_547, c_16])).
% 3.65/1.75  tff(c_553, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_550])).
% 3.65/1.75  tff(c_556, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_553])).
% 3.65/1.75  tff(c_560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_556])).
% 3.65/1.75  tff(c_562, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_546])).
% 3.65/1.75  tff(c_563, plain, (![A_130]: (v4_orders_2(k3_yellow19(A_130, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_struct_0(A_130) | v2_struct_0(A_130))), inference(splitRight, [status(thm)], [c_546])).
% 3.65/1.75  tff(c_569, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_92, c_563])).
% 3.65/1.75  tff(c_571, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_569])).
% 3.65/1.75  tff(c_572, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_571])).
% 3.65/1.75  tff(c_575, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_572])).
% 3.65/1.75  tff(c_579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_575])).
% 3.65/1.75  tff(c_581, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_571])).
% 3.65/1.75  tff(c_580, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_571])).
% 3.65/1.75  tff(c_598, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_580])).
% 3.65/1.75  tff(c_601, plain, (~r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_598])).
% 3.65/1.75  tff(c_605, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_601])).
% 3.65/1.75  tff(c_607, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_580])).
% 3.65/1.75  tff(c_606, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_580])).
% 3.65/1.75  tff(c_662, plain, (![A_142, B_143, C_144]: (l1_waybel_0(k3_yellow19(A_142, B_143, C_144), A_142) | ~m1_subset_1(C_144, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_143)))) | ~v13_waybel_0(C_144, k3_yellow_1(B_143)) | ~v2_waybel_0(C_144, k3_yellow_1(B_143)) | v1_xboole_0(C_144) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_142))) | v1_xboole_0(B_143) | ~l1_struct_0(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.65/1.75  tff(c_667, plain, (![A_142]: (l1_waybel_0(k3_yellow19(A_142, k2_struct_0('#skF_1'), '#skF_2'), A_142) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_142))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_142) | v2_struct_0(A_142))), inference(resolution, [status(thm)], [c_48, c_662])).
% 3.65/1.75  tff(c_671, plain, (![A_142]: (l1_waybel_0(k3_yellow19(A_142, k2_struct_0('#skF_1'), '#skF_2'), A_142) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_142))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_142) | v2_struct_0(A_142))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_667])).
% 3.65/1.75  tff(c_673, plain, (![A_145]: (l1_waybel_0(k3_yellow19(A_145, k2_struct_0('#skF_1'), '#skF_2'), A_145) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_struct_0(A_145) | v2_struct_0(A_145))), inference(negUnitSimplification, [status(thm)], [c_562, c_56, c_671])).
% 3.65/1.75  tff(c_678, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_92, c_673])).
% 3.65/1.75  tff(c_681, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_581, c_607, c_678])).
% 3.65/1.75  tff(c_682, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_681])).
% 3.65/1.75  tff(c_717, plain, (![A_152, B_153]: (k2_yellow19(A_152, k3_yellow19(A_152, k2_struct_0(A_152), B_153))=B_153 | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_152))))) | ~v13_waybel_0(B_153, k3_yellow_1(k2_struct_0(A_152))) | ~v2_waybel_0(B_153, k3_yellow_1(k2_struct_0(A_152))) | ~v1_subset_1(B_153, u1_struct_0(k3_yellow_1(k2_struct_0(A_152)))) | v1_xboole_0(B_153) | ~l1_struct_0(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.65/1.75  tff(c_722, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_717])).
% 3.65/1.75  tff(c_726, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_581, c_54, c_52, c_50, c_722])).
% 3.65/1.75  tff(c_727, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_726])).
% 3.65/1.75  tff(c_42, plain, (![A_18, B_22, C_24]: (r2_waybel_7(A_18, k2_yellow19(A_18, B_22), C_24) | ~r2_hidden(C_24, k10_yellow_6(A_18, B_22)) | ~m1_subset_1(C_24, u1_struct_0(A_18)) | ~l1_waybel_0(B_22, A_18) | ~v7_waybel_0(B_22) | ~v4_orders_2(B_22) | v2_struct_0(B_22) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.65/1.75  tff(c_731, plain, (![C_24]: (r2_waybel_7('#skF_1', '#skF_2', C_24) | ~r2_hidden(C_24, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_24, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_727, c_42])).
% 3.65/1.75  tff(c_738, plain, (![C_24]: (r2_waybel_7('#skF_1', '#skF_2', C_24) | ~r2_hidden(C_24, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_24, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_606, c_682, c_92, c_731])).
% 3.65/1.75  tff(c_739, plain, (![C_24]: (r2_waybel_7('#skF_1', '#skF_2', C_24) | ~r2_hidden(C_24, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_24, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_62, c_738])).
% 3.65/1.75  tff(c_744, plain, (~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_739])).
% 3.65/1.75  tff(c_762, plain, (![A_158, B_159, C_160]: (v7_waybel_0(k3_yellow19(A_158, B_159, C_160)) | ~m1_subset_1(C_160, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_159)))) | ~v13_waybel_0(C_160, k3_yellow_1(B_159)) | ~v2_waybel_0(C_160, k3_yellow_1(B_159)) | ~v1_subset_1(C_160, u1_struct_0(k3_yellow_1(B_159))) | v1_xboole_0(C_160) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0(A_158))) | v1_xboole_0(B_159) | ~l1_struct_0(A_158) | v2_struct_0(A_158))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.65/1.75  tff(c_767, plain, (![A_158]: (v7_waybel_0(k3_yellow19(A_158, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_158))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_158) | v2_struct_0(A_158))), inference(resolution, [status(thm)], [c_48, c_762])).
% 3.65/1.75  tff(c_771, plain, (![A_158]: (v7_waybel_0(k3_yellow19(A_158, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_158))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_158) | v2_struct_0(A_158))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_767])).
% 3.65/1.75  tff(c_773, plain, (![A_161]: (v7_waybel_0(k3_yellow19(A_161, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_161))) | ~l1_struct_0(A_161) | v2_struct_0(A_161))), inference(negUnitSimplification, [status(thm)], [c_562, c_56, c_771])).
% 3.65/1.75  tff(c_779, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_92, c_773])).
% 3.65/1.75  tff(c_782, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_581, c_607, c_779])).
% 3.65/1.75  tff(c_784, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_744, c_782])).
% 3.65/1.75  tff(c_785, plain, (![C_24]: (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | r2_waybel_7('#skF_1', '#skF_2', C_24) | ~r2_hidden(C_24, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_24, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_739])).
% 3.65/1.75  tff(c_787, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_785])).
% 3.65/1.75  tff(c_792, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_787, c_32])).
% 3.65/1.75  tff(c_795, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_581, c_607, c_92, c_52, c_50, c_48, c_792])).
% 3.65/1.75  tff(c_797, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_562, c_56, c_795])).
% 3.65/1.75  tff(c_800, plain, (![C_162]: (r2_waybel_7('#skF_1', '#skF_2', C_162) | ~r2_hidden(C_162, k10_yellow_6('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(C_162, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_785])).
% 3.65/1.75  tff(c_803, plain, (r2_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_516, c_800])).
% 3.65/1.75  tff(c_806, plain, (r2_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_803])).
% 3.65/1.75  tff(c_808, plain, $false, inference(negUnitSimplification, [status(thm)], [c_509, c_806])).
% 3.65/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.75  
% 3.65/1.75  Inference rules
% 3.65/1.75  ----------------------
% 3.65/1.75  #Ref     : 0
% 3.65/1.75  #Sup     : 125
% 3.65/1.75  #Fact    : 0
% 3.65/1.75  #Define  : 0
% 3.65/1.75  #Split   : 16
% 3.65/1.75  #Chain   : 0
% 3.65/1.75  #Close   : 0
% 3.65/1.75  
% 3.65/1.75  Ordering : KBO
% 3.65/1.75  
% 3.65/1.75  Simplification rules
% 3.65/1.75  ----------------------
% 3.65/1.75  #Subsume      : 13
% 3.65/1.75  #Demod        : 154
% 3.65/1.75  #Tautology    : 35
% 3.65/1.75  #SimpNegUnit  : 60
% 3.65/1.75  #BackRed      : 1
% 3.65/1.75  
% 3.65/1.75  #Partial instantiations: 0
% 3.65/1.75  #Strategies tried      : 1
% 3.65/1.75  
% 3.65/1.75  Timing (in seconds)
% 3.65/1.75  ----------------------
% 3.65/1.75  Preprocessing        : 0.43
% 3.65/1.75  Parsing              : 0.25
% 3.65/1.75  CNF conversion       : 0.02
% 3.65/1.75  Main loop            : 0.41
% 3.65/1.75  Inferencing          : 0.15
% 3.65/1.75  Reduction            : 0.13
% 3.65/1.75  Demodulation         : 0.09
% 3.65/1.75  BG Simplification    : 0.02
% 3.65/1.75  Subsumption          : 0.08
% 3.65/1.75  Abstraction          : 0.02
% 3.65/1.76  MUC search           : 0.00
% 3.65/1.76  Cooper               : 0.00
% 3.65/1.76  Total                : 0.89
% 3.65/1.76  Index Insertion      : 0.00
% 3.65/1.76  Index Deletion       : 0.00
% 3.65/1.76  Index Matching       : 0.00
% 3.65/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
