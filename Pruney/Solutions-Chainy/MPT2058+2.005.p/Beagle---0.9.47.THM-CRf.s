%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:33 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.93s
% Verified   : 
% Statistics : Number of formulae       :  198 (4581 expanded)
%              Number of leaves         :   46 (1629 expanded)
%              Depth                    :   23
%              Number of atoms          :  612 (19481 expanded)
%              Number of equality atoms :   14 ( 963 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k1_connsp_2 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_connsp_2,type,(
    k1_connsp_2: ( $i * $i ) > $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_227,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_129,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_157,axiom,(
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
        & v6_waybel_0(k3_yellow19(A,B,C),A)
        & l1_waybel_0(k3_yellow19(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).

tff(f_200,axiom,(
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

tff(f_181,axiom,(
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
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_64,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_62,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_16,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_87,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_92,plain,(
    ! [A_43] :
      ( u1_struct_0(A_43) = k2_struct_0(A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_16,c_87])).

tff(c_96,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_92])).

tff(c_20,plain,(
    ! [B_14,A_12] :
      ( r2_hidden(B_14,k1_connsp_2(A_12,B_14))
      | ~ m1_subset_1(B_14,u1_struct_0(A_12))
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_97,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_50])).

tff(c_68,plain,
    ( ~ r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_112,plain,(
    ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_74,plain,
    ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3')
    | r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_131,plain,(
    r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_74])).

tff(c_138,plain,(
    ! [A_58,B_59] :
      ( m1_subset_1(k1_connsp_2(A_58,B_59),k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ m1_subset_1(B_59,u1_struct_0(A_58))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_146,plain,(
    ! [B_59] :
      ( m1_subset_1(k1_connsp_2('#skF_1',B_59),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_59,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_138])).

tff(c_150,plain,(
    ! [B_59] :
      ( m1_subset_1(k1_connsp_2('#skF_1',B_59),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_59,k2_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_96,c_146])).

tff(c_152,plain,(
    ! [B_60] :
      ( m1_subset_1(k1_connsp_2('#skF_1',B_60),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_60,k2_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_150])).

tff(c_12,plain,(
    ! [C_7,B_6,A_5] :
      ( ~ v1_xboole_0(C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_158,plain,(
    ! [A_5,B_60] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ r2_hidden(A_5,k1_connsp_2('#skF_1',B_60))
      | ~ m1_subset_1(B_60,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_152,c_12])).

tff(c_164,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_56,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_54,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_218,plain,(
    ! [A_79,B_80,C_81] :
      ( v4_orders_2(k3_yellow19(A_79,B_80,C_81))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_80))))
      | ~ v13_waybel_0(C_81,k3_yellow_1(B_80))
      | ~ v2_waybel_0(C_81,k3_yellow_1(B_80))
      | v1_xboole_0(C_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | v1_xboole_0(B_80)
      | ~ l1_struct_0(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_223,plain,(
    ! [A_79] :
      ( v4_orders_2(k3_yellow19(A_79,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_79)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_79)
      | v2_struct_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_52,c_218])).

tff(c_230,plain,(
    ! [A_79] :
      ( v4_orders_2(k3_yellow19(A_79,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_79)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_79)
      | v2_struct_0(A_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_223])).

tff(c_233,plain,(
    ! [A_82] :
      ( v4_orders_2(k3_yellow19(A_82,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_struct_0(A_82)
      | v2_struct_0(A_82) ) ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_60,c_230])).

tff(c_239,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_233])).

tff(c_241,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_239])).

tff(c_242,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_241])).

tff(c_245,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_242])).

tff(c_249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_245])).

tff(c_251,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_250,plain,
    ( ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_257,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_260,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_257])).

tff(c_264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_260])).

tff(c_266,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_265,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_58,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_556,plain,(
    ! [A_134,B_135,C_136] :
      ( v7_waybel_0(k3_yellow19(A_134,B_135,C_136))
      | ~ m1_subset_1(C_136,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_135))))
      | ~ v13_waybel_0(C_136,k3_yellow_1(B_135))
      | ~ v2_waybel_0(C_136,k3_yellow_1(B_135))
      | ~ v1_subset_1(C_136,u1_struct_0(k3_yellow_1(B_135)))
      | v1_xboole_0(C_136)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | v1_xboole_0(B_135)
      | ~ l1_struct_0(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_561,plain,(
    ! [A_134] :
      ( v7_waybel_0(k3_yellow19(A_134,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_134)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_134)
      | v2_struct_0(A_134) ) ),
    inference(resolution,[status(thm)],[c_52,c_556])).

tff(c_568,plain,(
    ! [A_134] :
      ( v7_waybel_0(k3_yellow19(A_134,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_134)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_134)
      | v2_struct_0(A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_561])).

tff(c_571,plain,(
    ! [A_137] :
      ( v7_waybel_0(k3_yellow19(A_137,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_struct_0(A_137)
      | v2_struct_0(A_137) ) ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_60,c_568])).

tff(c_577,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_571])).

tff(c_580,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_266,c_577])).

tff(c_581,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_580])).

tff(c_456,plain,(
    ! [A_116,B_117,C_118] :
      ( l1_waybel_0(k3_yellow19(A_116,B_117,C_118),A_116)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_117))))
      | ~ v13_waybel_0(C_118,k3_yellow_1(B_117))
      | ~ v2_waybel_0(C_118,k3_yellow_1(B_117))
      | v1_xboole_0(C_118)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | v1_xboole_0(B_117)
      | ~ l1_struct_0(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_461,plain,(
    ! [A_116] :
      ( l1_waybel_0(k3_yellow19(A_116,k2_struct_0('#skF_1'),'#skF_2'),A_116)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_116)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_116)
      | v2_struct_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_52,c_456])).

tff(c_468,plain,(
    ! [A_116] :
      ( l1_waybel_0(k3_yellow19(A_116,k2_struct_0('#skF_1'),'#skF_2'),A_116)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_116)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_116)
      | v2_struct_0(A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_461])).

tff(c_471,plain,(
    ! [A_119] :
      ( l1_waybel_0(k3_yellow19(A_119,k2_struct_0('#skF_1'),'#skF_2'),A_119)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_struct_0(A_119)
      | v2_struct_0(A_119) ) ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_60,c_468])).

tff(c_476,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_471])).

tff(c_479,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_266,c_476])).

tff(c_480,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_479])).

tff(c_626,plain,(
    ! [A_151,B_152] :
      ( k2_yellow19(A_151,k3_yellow19(A_151,k2_struct_0(A_151),B_152)) = B_152
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_151)))))
      | ~ v13_waybel_0(B_152,k3_yellow_1(k2_struct_0(A_151)))
      | ~ v2_waybel_0(B_152,k3_yellow_1(k2_struct_0(A_151)))
      | ~ v1_subset_1(B_152,u1_struct_0(k3_yellow_1(k2_struct_0(A_151))))
      | v1_xboole_0(B_152)
      | ~ l1_struct_0(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_631,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_626])).

tff(c_638,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_58,c_56,c_54,c_631])).

tff(c_639,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_638])).

tff(c_46,plain,(
    ! [A_25,B_29,C_31] :
      ( r1_waybel_7(A_25,k2_yellow19(A_25,B_29),C_31)
      | ~ r3_waybel_9(A_25,B_29,C_31)
      | ~ m1_subset_1(C_31,u1_struct_0(A_25))
      | ~ l1_waybel_0(B_29,A_25)
      | ~ v7_waybel_0(B_29)
      | ~ v4_orders_2(B_29)
      | v2_struct_0(B_29)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_644,plain,(
    ! [C_31] :
      ( r1_waybel_7('#skF_1','#skF_2',C_31)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_31)
      | ~ m1_subset_1(C_31,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_639,c_46])).

tff(c_651,plain,(
    ! [C_31] :
      ( r1_waybel_7('#skF_1','#skF_2',C_31)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_31)
      | ~ m1_subset_1(C_31,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_265,c_581,c_480,c_96,c_644])).

tff(c_652,plain,(
    ! [C_31] :
      ( r1_waybel_7('#skF_1','#skF_2',C_31)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_31)
      | ~ m1_subset_1(C_31,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_651])).

tff(c_657,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_652])).

tff(c_36,plain,(
    ! [A_19,B_20,C_21] :
      ( ~ v2_struct_0(k3_yellow19(A_19,B_20,C_21))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_20))))
      | ~ v13_waybel_0(C_21,k3_yellow_1(B_20))
      | ~ v2_waybel_0(C_21,k3_yellow_1(B_20))
      | v1_xboole_0(C_21)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | v1_xboole_0(B_20)
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_659,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_657,c_36])).

tff(c_662,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_266,c_96,c_56,c_54,c_52,c_659])).

tff(c_664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_164,c_60,c_662])).

tff(c_666,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_652])).

tff(c_44,plain,(
    ! [A_25,B_29,C_31] :
      ( r3_waybel_9(A_25,B_29,C_31)
      | ~ r1_waybel_7(A_25,k2_yellow19(A_25,B_29),C_31)
      | ~ m1_subset_1(C_31,u1_struct_0(A_25))
      | ~ l1_waybel_0(B_29,A_25)
      | ~ v7_waybel_0(B_29)
      | ~ v4_orders_2(B_29)
      | v2_struct_0(B_29)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_647,plain,(
    ! [C_31] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_31)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_31)
      | ~ m1_subset_1(C_31,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_639,c_44])).

tff(c_654,plain,(
    ! [C_31] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_31)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_31)
      | ~ m1_subset_1(C_31,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_265,c_581,c_480,c_96,c_647])).

tff(c_655,plain,(
    ! [C_31] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_31)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_31)
      | ~ m1_subset_1(C_31,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_654])).

tff(c_667,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_655])).

tff(c_668,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_666,c_667])).

tff(c_679,plain,(
    ! [C_156] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_156)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_156)
      | ~ m1_subset_1(C_156,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_655])).

tff(c_685,plain,
    ( ~ r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_679,c_112])).

tff(c_690,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_131,c_685])).

tff(c_693,plain,(
    ! [A_157,B_158] :
      ( ~ r2_hidden(A_157,k1_connsp_2('#skF_1',B_158))
      | ~ m1_subset_1(B_158,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_697,plain,(
    ! [B_14] :
      ( ~ m1_subset_1(B_14,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_14,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_693])).

tff(c_700,plain,(
    ! [B_14] :
      ( ~ m1_subset_1(B_14,k2_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_96,c_697])).

tff(c_701,plain,(
    ! [B_14] : ~ m1_subset_1(B_14,k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_700])).

tff(c_703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_701,c_97])).

tff(c_704,plain,(
    ~ r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_705,plain,(
    r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_732,plain,(
    ! [A_169,B_170] :
      ( m1_subset_1(k1_connsp_2(A_169,B_170),k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ m1_subset_1(B_170,u1_struct_0(A_169))
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_740,plain,(
    ! [B_170] :
      ( m1_subset_1(k1_connsp_2('#skF_1',B_170),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_170,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_732])).

tff(c_744,plain,(
    ! [B_170] :
      ( m1_subset_1(k1_connsp_2('#skF_1',B_170),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_170,k2_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_96,c_740])).

tff(c_746,plain,(
    ! [B_171] :
      ( m1_subset_1(k1_connsp_2('#skF_1',B_171),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_171,k2_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_744])).

tff(c_752,plain,(
    ! [A_5,B_171] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ r2_hidden(A_5,k1_connsp_2('#skF_1',B_171))
      | ~ m1_subset_1(B_171,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_746,c_12])).

tff(c_758,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_752])).

tff(c_812,plain,(
    ! [A_190,B_191,C_192] :
      ( v4_orders_2(k3_yellow19(A_190,B_191,C_192))
      | ~ m1_subset_1(C_192,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_191))))
      | ~ v13_waybel_0(C_192,k3_yellow_1(B_191))
      | ~ v2_waybel_0(C_192,k3_yellow_1(B_191))
      | v1_xboole_0(C_192)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(A_190)))
      | v1_xboole_0(B_191)
      | ~ l1_struct_0(A_190)
      | v2_struct_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_817,plain,(
    ! [A_190] :
      ( v4_orders_2(k3_yellow19(A_190,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_190)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_190)
      | v2_struct_0(A_190) ) ),
    inference(resolution,[status(thm)],[c_52,c_812])).

tff(c_824,plain,(
    ! [A_190] :
      ( v4_orders_2(k3_yellow19(A_190,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_190)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_190)
      | v2_struct_0(A_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_817])).

tff(c_827,plain,(
    ! [A_193] :
      ( v4_orders_2(k3_yellow19(A_193,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_struct_0(A_193)
      | v2_struct_0(A_193) ) ),
    inference(negUnitSimplification,[status(thm)],[c_758,c_60,c_824])).

tff(c_833,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_827])).

tff(c_835,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_833])).

tff(c_836,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_835])).

tff(c_839,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_836])).

tff(c_843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_839])).

tff(c_845,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_835])).

tff(c_844,plain,
    ( ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_835])).

tff(c_851,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_844])).

tff(c_854,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_851])).

tff(c_858,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_854])).

tff(c_860,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_844])).

tff(c_859,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_844])).

tff(c_1035,plain,(
    ! [A_224,B_225,C_226] :
      ( l1_waybel_0(k3_yellow19(A_224,B_225,C_226),A_224)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_225))))
      | ~ v13_waybel_0(C_226,k3_yellow_1(B_225))
      | ~ v2_waybel_0(C_226,k3_yellow_1(B_225))
      | v1_xboole_0(C_226)
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0(A_224)))
      | v1_xboole_0(B_225)
      | ~ l1_struct_0(A_224)
      | v2_struct_0(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1040,plain,(
    ! [A_224] :
      ( l1_waybel_0(k3_yellow19(A_224,k2_struct_0('#skF_1'),'#skF_2'),A_224)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_224)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_224)
      | v2_struct_0(A_224) ) ),
    inference(resolution,[status(thm)],[c_52,c_1035])).

tff(c_1047,plain,(
    ! [A_224] :
      ( l1_waybel_0(k3_yellow19(A_224,k2_struct_0('#skF_1'),'#skF_2'),A_224)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_224)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_224)
      | v2_struct_0(A_224) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1040])).

tff(c_1050,plain,(
    ! [A_227] :
      ( l1_waybel_0(k3_yellow19(A_227,k2_struct_0('#skF_1'),'#skF_2'),A_227)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ l1_struct_0(A_227)
      | v2_struct_0(A_227) ) ),
    inference(negUnitSimplification,[status(thm)],[c_758,c_60,c_1047])).

tff(c_1055,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_1050])).

tff(c_1058,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_845,c_860,c_1055])).

tff(c_1059,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1058])).

tff(c_1133,plain,(
    ! [A_242,B_243] :
      ( k2_yellow19(A_242,k3_yellow19(A_242,k2_struct_0(A_242),B_243)) = B_243
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_242)))))
      | ~ v13_waybel_0(B_243,k3_yellow_1(k2_struct_0(A_242)))
      | ~ v2_waybel_0(B_243,k3_yellow_1(k2_struct_0(A_242)))
      | ~ v1_subset_1(B_243,u1_struct_0(k3_yellow_1(k2_struct_0(A_242))))
      | v1_xboole_0(B_243)
      | ~ l1_struct_0(A_242)
      | v2_struct_0(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_1138,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1133])).

tff(c_1145,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_845,c_58,c_56,c_54,c_1138])).

tff(c_1146,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_1145])).

tff(c_1151,plain,(
    ! [C_31] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_31)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_31)
      | ~ m1_subset_1(C_31,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1146,c_44])).

tff(c_1158,plain,(
    ! [C_31] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_31)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_31)
      | ~ m1_subset_1(C_31,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_859,c_1059,c_96,c_1151])).

tff(c_1159,plain,(
    ! [C_31] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_31)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_31)
      | ~ m1_subset_1(C_31,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1158])).

tff(c_1164,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1159])).

tff(c_1217,plain,(
    ! [A_255,B_256,C_257] :
      ( v7_waybel_0(k3_yellow19(A_255,B_256,C_257))
      | ~ m1_subset_1(C_257,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_256))))
      | ~ v13_waybel_0(C_257,k3_yellow_1(B_256))
      | ~ v2_waybel_0(C_257,k3_yellow_1(B_256))
      | ~ v1_subset_1(C_257,u1_struct_0(k3_yellow_1(B_256)))
      | v1_xboole_0(C_257)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_255)))
      | v1_xboole_0(B_256)
      | ~ l1_struct_0(A_255)
      | v2_struct_0(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1222,plain,(
    ! [A_255] :
      ( v7_waybel_0(k3_yellow19(A_255,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_255)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_255)
      | v2_struct_0(A_255) ) ),
    inference(resolution,[status(thm)],[c_52,c_1217])).

tff(c_1229,plain,(
    ! [A_255] :
      ( v7_waybel_0(k3_yellow19(A_255,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_255)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_255)
      | v2_struct_0(A_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1222])).

tff(c_1232,plain,(
    ! [A_258] :
      ( v7_waybel_0(k3_yellow19(A_258,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ l1_struct_0(A_258)
      | v2_struct_0(A_258) ) ),
    inference(negUnitSimplification,[status(thm)],[c_758,c_60,c_1229])).

tff(c_1238,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_1232])).

tff(c_1241,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_845,c_860,c_1238])).

tff(c_1243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1164,c_1241])).

tff(c_1244,plain,(
    ! [C_31] :
      ( v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_31)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_31)
      | ~ m1_subset_1(C_31,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_1159])).

tff(c_1246,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1244])).

tff(c_1251,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1246,c_36])).

tff(c_1254,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_845,c_860,c_96,c_56,c_54,c_52,c_1251])).

tff(c_1256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_758,c_60,c_1254])).

tff(c_1258,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1244])).

tff(c_1245,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1159])).

tff(c_1154,plain,(
    ! [C_31] :
      ( r1_waybel_7('#skF_1','#skF_2',C_31)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_31)
      | ~ m1_subset_1(C_31,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1146,c_46])).

tff(c_1161,plain,(
    ! [C_31] :
      ( r1_waybel_7('#skF_1','#skF_2',C_31)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_31)
      | ~ m1_subset_1(C_31,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_859,c_1059,c_96,c_1154])).

tff(c_1162,plain,(
    ! [C_31] :
      ( r1_waybel_7('#skF_1','#skF_2',C_31)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_31)
      | ~ m1_subset_1(C_31,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1161])).

tff(c_1261,plain,(
    ! [C_31] :
      ( r1_waybel_7('#skF_1','#skF_2',C_31)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_31)
      | ~ m1_subset_1(C_31,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1245,c_1162])).

tff(c_1263,plain,(
    ! [C_260] :
      ( r1_waybel_7('#skF_1','#skF_2',C_260)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_260)
      | ~ m1_subset_1(C_260,k2_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1258,c_1261])).

tff(c_1269,plain,
    ( r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_705,c_1263])).

tff(c_1273,plain,(
    r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_1269])).

tff(c_1275,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_704,c_1273])).

tff(c_1279,plain,(
    ! [A_264,B_265] :
      ( ~ r2_hidden(A_264,k1_connsp_2('#skF_1',B_265))
      | ~ m1_subset_1(B_265,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_752])).

tff(c_1283,plain,(
    ! [B_14] :
      ( ~ m1_subset_1(B_14,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_14,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_1279])).

tff(c_1286,plain,(
    ! [B_14] :
      ( ~ m1_subset_1(B_14,k2_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_96,c_1283])).

tff(c_1287,plain,(
    ! [B_14] : ~ m1_subset_1(B_14,k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1286])).

tff(c_1289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1287,c_97])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.94  
% 4.61/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.94  %$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k1_connsp_2 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1
% 4.61/1.94  
% 4.61/1.94  %Foreground sorts:
% 4.61/1.94  
% 4.61/1.94  
% 4.61/1.94  %Background operators:
% 4.61/1.94  
% 4.61/1.94  
% 4.61/1.94  %Foreground operators:
% 4.61/1.94  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.61/1.94  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.61/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.61/1.94  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 4.61/1.94  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 4.61/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.61/1.94  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.61/1.94  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 4.61/1.94  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 4.61/1.94  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 4.61/1.94  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.61/1.94  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 4.61/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.61/1.94  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 4.61/1.94  tff('#skF_2', type, '#skF_2': $i).
% 4.61/1.94  tff('#skF_3', type, '#skF_3': $i).
% 4.61/1.94  tff('#skF_1', type, '#skF_1': $i).
% 4.61/1.94  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 4.61/1.94  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.61/1.94  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 4.61/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.61/1.94  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.61/1.94  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 4.61/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.61/1.94  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 4.61/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.61/1.94  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 4.61/1.94  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 4.61/1.94  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.61/1.94  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.61/1.94  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.61/1.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.61/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.61/1.94  
% 4.93/1.97  tff(f_227, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, k3_yellow19(A, k2_struct_0(A), B), C) <=> r1_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_yellow19)).
% 4.93/1.97  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.93/1.97  tff(f_46, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.93/1.97  tff(f_73, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_connsp_2)).
% 4.93/1.97  tff(f_61, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 4.93/1.97  tff(f_42, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.93/1.97  tff(f_129, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_yellow19)).
% 4.93/1.97  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.93/1.97  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.93/1.97  tff(f_157, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow19)).
% 4.93/1.97  tff(f_101, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 4.93/1.97  tff(f_200, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 4.93/1.97  tff(f_181, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> r1_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_yellow19)).
% 4.93/1.97  tff(c_66, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.93/1.97  tff(c_64, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.93/1.97  tff(c_62, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.93/1.97  tff(c_16, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.93/1.97  tff(c_87, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.93/1.97  tff(c_92, plain, (![A_43]: (u1_struct_0(A_43)=k2_struct_0(A_43) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_16, c_87])).
% 4.93/1.97  tff(c_96, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_92])).
% 4.93/1.97  tff(c_20, plain, (![B_14, A_12]: (r2_hidden(B_14, k1_connsp_2(A_12, B_14)) | ~m1_subset_1(B_14, u1_struct_0(A_12)) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.93/1.97  tff(c_50, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.93/1.97  tff(c_97, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_50])).
% 4.93/1.97  tff(c_68, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.93/1.97  tff(c_112, plain, (~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 4.93/1.97  tff(c_74, plain, (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3') | r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.93/1.97  tff(c_131, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_112, c_74])).
% 4.93/1.97  tff(c_138, plain, (![A_58, B_59]: (m1_subset_1(k1_connsp_2(A_58, B_59), k1_zfmisc_1(u1_struct_0(A_58))) | ~m1_subset_1(B_59, u1_struct_0(A_58)) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.93/1.97  tff(c_146, plain, (![B_59]: (m1_subset_1(k1_connsp_2('#skF_1', B_59), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_59, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_138])).
% 4.93/1.97  tff(c_150, plain, (![B_59]: (m1_subset_1(k1_connsp_2('#skF_1', B_59), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_59, k2_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_96, c_146])).
% 4.93/1.97  tff(c_152, plain, (![B_60]: (m1_subset_1(k1_connsp_2('#skF_1', B_60), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_60, k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_66, c_150])).
% 4.93/1.97  tff(c_12, plain, (![C_7, B_6, A_5]: (~v1_xboole_0(C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.93/1.97  tff(c_158, plain, (![A_5, B_60]: (~v1_xboole_0(k2_struct_0('#skF_1')) | ~r2_hidden(A_5, k1_connsp_2('#skF_1', B_60)) | ~m1_subset_1(B_60, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_152, c_12])).
% 4.93/1.97  tff(c_164, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_158])).
% 4.93/1.97  tff(c_60, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.93/1.97  tff(c_56, plain, (v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.93/1.97  tff(c_54, plain, (v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.93/1.97  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.93/1.97  tff(c_218, plain, (![A_79, B_80, C_81]: (v4_orders_2(k3_yellow19(A_79, B_80, C_81)) | ~m1_subset_1(C_81, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_80)))) | ~v13_waybel_0(C_81, k3_yellow_1(B_80)) | ~v2_waybel_0(C_81, k3_yellow_1(B_80)) | v1_xboole_0(C_81) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | v1_xboole_0(B_80) | ~l1_struct_0(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.93/1.97  tff(c_223, plain, (![A_79]: (v4_orders_2(k3_yellow19(A_79, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_79))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_79) | v2_struct_0(A_79))), inference(resolution, [status(thm)], [c_52, c_218])).
% 4.93/1.97  tff(c_230, plain, (![A_79]: (v4_orders_2(k3_yellow19(A_79, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_79))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_79) | v2_struct_0(A_79))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_223])).
% 4.93/1.97  tff(c_233, plain, (![A_82]: (v4_orders_2(k3_yellow19(A_82, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_struct_0(A_82) | v2_struct_0(A_82))), inference(negUnitSimplification, [status(thm)], [c_164, c_60, c_230])).
% 4.93/1.97  tff(c_239, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_96, c_233])).
% 4.93/1.97  tff(c_241, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_239])).
% 4.93/1.97  tff(c_242, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_241])).
% 4.93/1.97  tff(c_245, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_242])).
% 4.93/1.97  tff(c_249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_245])).
% 4.93/1.97  tff(c_251, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_241])).
% 4.93/1.97  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.93/1.97  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.93/1.97  tff(c_250, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_241])).
% 4.93/1.97  tff(c_257, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_250])).
% 4.93/1.97  tff(c_260, plain, (~r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_257])).
% 4.93/1.97  tff(c_264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_260])).
% 4.93/1.97  tff(c_266, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_250])).
% 4.93/1.97  tff(c_265, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_250])).
% 4.93/1.97  tff(c_58, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.93/1.97  tff(c_556, plain, (![A_134, B_135, C_136]: (v7_waybel_0(k3_yellow19(A_134, B_135, C_136)) | ~m1_subset_1(C_136, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_135)))) | ~v13_waybel_0(C_136, k3_yellow_1(B_135)) | ~v2_waybel_0(C_136, k3_yellow_1(B_135)) | ~v1_subset_1(C_136, u1_struct_0(k3_yellow_1(B_135))) | v1_xboole_0(C_136) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | v1_xboole_0(B_135) | ~l1_struct_0(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.93/1.97  tff(c_561, plain, (![A_134]: (v7_waybel_0(k3_yellow19(A_134, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_134))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_134) | v2_struct_0(A_134))), inference(resolution, [status(thm)], [c_52, c_556])).
% 4.93/1.97  tff(c_568, plain, (![A_134]: (v7_waybel_0(k3_yellow19(A_134, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_134))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_134) | v2_struct_0(A_134))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_561])).
% 4.93/1.97  tff(c_571, plain, (![A_137]: (v7_waybel_0(k3_yellow19(A_137, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_struct_0(A_137) | v2_struct_0(A_137))), inference(negUnitSimplification, [status(thm)], [c_164, c_60, c_568])).
% 4.93/1.97  tff(c_577, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_96, c_571])).
% 4.93/1.97  tff(c_580, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_251, c_266, c_577])).
% 4.93/1.97  tff(c_581, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_580])).
% 4.93/1.97  tff(c_456, plain, (![A_116, B_117, C_118]: (l1_waybel_0(k3_yellow19(A_116, B_117, C_118), A_116) | ~m1_subset_1(C_118, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_117)))) | ~v13_waybel_0(C_118, k3_yellow_1(B_117)) | ~v2_waybel_0(C_118, k3_yellow_1(B_117)) | v1_xboole_0(C_118) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | v1_xboole_0(B_117) | ~l1_struct_0(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.93/1.97  tff(c_461, plain, (![A_116]: (l1_waybel_0(k3_yellow19(A_116, k2_struct_0('#skF_1'), '#skF_2'), A_116) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_116))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_116) | v2_struct_0(A_116))), inference(resolution, [status(thm)], [c_52, c_456])).
% 4.93/1.97  tff(c_468, plain, (![A_116]: (l1_waybel_0(k3_yellow19(A_116, k2_struct_0('#skF_1'), '#skF_2'), A_116) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_116))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_116) | v2_struct_0(A_116))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_461])).
% 4.93/1.97  tff(c_471, plain, (![A_119]: (l1_waybel_0(k3_yellow19(A_119, k2_struct_0('#skF_1'), '#skF_2'), A_119) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_struct_0(A_119) | v2_struct_0(A_119))), inference(negUnitSimplification, [status(thm)], [c_164, c_60, c_468])).
% 4.93/1.97  tff(c_476, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_96, c_471])).
% 4.93/1.97  tff(c_479, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_251, c_266, c_476])).
% 4.93/1.97  tff(c_480, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_479])).
% 4.93/1.97  tff(c_626, plain, (![A_151, B_152]: (k2_yellow19(A_151, k3_yellow19(A_151, k2_struct_0(A_151), B_152))=B_152 | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_151))))) | ~v13_waybel_0(B_152, k3_yellow_1(k2_struct_0(A_151))) | ~v2_waybel_0(B_152, k3_yellow_1(k2_struct_0(A_151))) | ~v1_subset_1(B_152, u1_struct_0(k3_yellow_1(k2_struct_0(A_151)))) | v1_xboole_0(B_152) | ~l1_struct_0(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_200])).
% 4.93/1.97  tff(c_631, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_626])).
% 4.93/1.97  tff(c_638, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_251, c_58, c_56, c_54, c_631])).
% 4.93/1.97  tff(c_639, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_638])).
% 4.93/1.97  tff(c_46, plain, (![A_25, B_29, C_31]: (r1_waybel_7(A_25, k2_yellow19(A_25, B_29), C_31) | ~r3_waybel_9(A_25, B_29, C_31) | ~m1_subset_1(C_31, u1_struct_0(A_25)) | ~l1_waybel_0(B_29, A_25) | ~v7_waybel_0(B_29) | ~v4_orders_2(B_29) | v2_struct_0(B_29) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_181])).
% 4.93/1.97  tff(c_644, plain, (![C_31]: (r1_waybel_7('#skF_1', '#skF_2', C_31) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_31) | ~m1_subset_1(C_31, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_639, c_46])).
% 4.93/1.97  tff(c_651, plain, (![C_31]: (r1_waybel_7('#skF_1', '#skF_2', C_31) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_31) | ~m1_subset_1(C_31, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_265, c_581, c_480, c_96, c_644])).
% 4.93/1.97  tff(c_652, plain, (![C_31]: (r1_waybel_7('#skF_1', '#skF_2', C_31) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_31) | ~m1_subset_1(C_31, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_66, c_651])).
% 4.93/1.97  tff(c_657, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_652])).
% 4.93/1.97  tff(c_36, plain, (![A_19, B_20, C_21]: (~v2_struct_0(k3_yellow19(A_19, B_20, C_21)) | ~m1_subset_1(C_21, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_20)))) | ~v13_waybel_0(C_21, k3_yellow_1(B_20)) | ~v2_waybel_0(C_21, k3_yellow_1(B_20)) | v1_xboole_0(C_21) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | v1_xboole_0(B_20) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.93/1.97  tff(c_659, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_657, c_36])).
% 4.93/1.97  tff(c_662, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_251, c_266, c_96, c_56, c_54, c_52, c_659])).
% 4.93/1.97  tff(c_664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_164, c_60, c_662])).
% 4.93/1.97  tff(c_666, plain, (~v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_652])).
% 4.93/1.97  tff(c_44, plain, (![A_25, B_29, C_31]: (r3_waybel_9(A_25, B_29, C_31) | ~r1_waybel_7(A_25, k2_yellow19(A_25, B_29), C_31) | ~m1_subset_1(C_31, u1_struct_0(A_25)) | ~l1_waybel_0(B_29, A_25) | ~v7_waybel_0(B_29) | ~v4_orders_2(B_29) | v2_struct_0(B_29) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_181])).
% 4.93/1.97  tff(c_647, plain, (![C_31]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_31) | ~r1_waybel_7('#skF_1', '#skF_2', C_31) | ~m1_subset_1(C_31, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_639, c_44])).
% 4.93/1.97  tff(c_654, plain, (![C_31]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_31) | ~r1_waybel_7('#skF_1', '#skF_2', C_31) | ~m1_subset_1(C_31, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_265, c_581, c_480, c_96, c_647])).
% 4.93/1.97  tff(c_655, plain, (![C_31]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_31) | ~r1_waybel_7('#skF_1', '#skF_2', C_31) | ~m1_subset_1(C_31, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_66, c_654])).
% 4.93/1.97  tff(c_667, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_655])).
% 4.93/1.97  tff(c_668, plain, $false, inference(negUnitSimplification, [status(thm)], [c_666, c_667])).
% 4.93/1.97  tff(c_679, plain, (![C_156]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_156) | ~r1_waybel_7('#skF_1', '#skF_2', C_156) | ~m1_subset_1(C_156, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_655])).
% 4.93/1.97  tff(c_685, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_679, c_112])).
% 4.93/1.97  tff(c_690, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_131, c_685])).
% 4.93/1.97  tff(c_693, plain, (![A_157, B_158]: (~r2_hidden(A_157, k1_connsp_2('#skF_1', B_158)) | ~m1_subset_1(B_158, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_158])).
% 4.93/1.97  tff(c_697, plain, (![B_14]: (~m1_subset_1(B_14, k2_struct_0('#skF_1')) | ~m1_subset_1(B_14, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_693])).
% 4.93/1.97  tff(c_700, plain, (![B_14]: (~m1_subset_1(B_14, k2_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_96, c_697])).
% 4.93/1.97  tff(c_701, plain, (![B_14]: (~m1_subset_1(B_14, k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_66, c_700])).
% 4.93/1.97  tff(c_703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_701, c_97])).
% 4.93/1.97  tff(c_704, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_68])).
% 4.93/1.97  tff(c_705, plain, (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_68])).
% 4.93/1.97  tff(c_732, plain, (![A_169, B_170]: (m1_subset_1(k1_connsp_2(A_169, B_170), k1_zfmisc_1(u1_struct_0(A_169))) | ~m1_subset_1(B_170, u1_struct_0(A_169)) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.93/1.97  tff(c_740, plain, (![B_170]: (m1_subset_1(k1_connsp_2('#skF_1', B_170), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_170, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_732])).
% 4.93/1.97  tff(c_744, plain, (![B_170]: (m1_subset_1(k1_connsp_2('#skF_1', B_170), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_170, k2_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_96, c_740])).
% 4.93/1.97  tff(c_746, plain, (![B_171]: (m1_subset_1(k1_connsp_2('#skF_1', B_171), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_171, k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_66, c_744])).
% 4.93/1.97  tff(c_752, plain, (![A_5, B_171]: (~v1_xboole_0(k2_struct_0('#skF_1')) | ~r2_hidden(A_5, k1_connsp_2('#skF_1', B_171)) | ~m1_subset_1(B_171, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_746, c_12])).
% 4.93/1.97  tff(c_758, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_752])).
% 4.93/1.97  tff(c_812, plain, (![A_190, B_191, C_192]: (v4_orders_2(k3_yellow19(A_190, B_191, C_192)) | ~m1_subset_1(C_192, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_191)))) | ~v13_waybel_0(C_192, k3_yellow_1(B_191)) | ~v2_waybel_0(C_192, k3_yellow_1(B_191)) | v1_xboole_0(C_192) | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0(A_190))) | v1_xboole_0(B_191) | ~l1_struct_0(A_190) | v2_struct_0(A_190))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.93/1.97  tff(c_817, plain, (![A_190]: (v4_orders_2(k3_yellow19(A_190, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_190))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_190) | v2_struct_0(A_190))), inference(resolution, [status(thm)], [c_52, c_812])).
% 4.93/1.97  tff(c_824, plain, (![A_190]: (v4_orders_2(k3_yellow19(A_190, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_190))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_190) | v2_struct_0(A_190))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_817])).
% 4.93/1.97  tff(c_827, plain, (![A_193]: (v4_orders_2(k3_yellow19(A_193, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_struct_0(A_193) | v2_struct_0(A_193))), inference(negUnitSimplification, [status(thm)], [c_758, c_60, c_824])).
% 4.93/1.97  tff(c_833, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_96, c_827])).
% 4.93/1.97  tff(c_835, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_833])).
% 4.93/1.97  tff(c_836, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_835])).
% 4.93/1.97  tff(c_839, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_836])).
% 4.93/1.97  tff(c_843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_839])).
% 4.93/1.97  tff(c_845, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_835])).
% 4.93/1.97  tff(c_844, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_835])).
% 4.93/1.97  tff(c_851, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_844])).
% 4.93/1.97  tff(c_854, plain, (~r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_851])).
% 4.93/1.97  tff(c_858, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_854])).
% 4.93/1.97  tff(c_860, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_844])).
% 4.93/1.97  tff(c_859, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_844])).
% 4.93/1.97  tff(c_1035, plain, (![A_224, B_225, C_226]: (l1_waybel_0(k3_yellow19(A_224, B_225, C_226), A_224) | ~m1_subset_1(C_226, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_225)))) | ~v13_waybel_0(C_226, k3_yellow_1(B_225)) | ~v2_waybel_0(C_226, k3_yellow_1(B_225)) | v1_xboole_0(C_226) | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0(A_224))) | v1_xboole_0(B_225) | ~l1_struct_0(A_224) | v2_struct_0(A_224))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.93/1.97  tff(c_1040, plain, (![A_224]: (l1_waybel_0(k3_yellow19(A_224, k2_struct_0('#skF_1'), '#skF_2'), A_224) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_224))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_224) | v2_struct_0(A_224))), inference(resolution, [status(thm)], [c_52, c_1035])).
% 4.93/1.97  tff(c_1047, plain, (![A_224]: (l1_waybel_0(k3_yellow19(A_224, k2_struct_0('#skF_1'), '#skF_2'), A_224) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_224))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_224) | v2_struct_0(A_224))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1040])).
% 4.93/1.97  tff(c_1050, plain, (![A_227]: (l1_waybel_0(k3_yellow19(A_227, k2_struct_0('#skF_1'), '#skF_2'), A_227) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_227))) | ~l1_struct_0(A_227) | v2_struct_0(A_227))), inference(negUnitSimplification, [status(thm)], [c_758, c_60, c_1047])).
% 4.93/1.97  tff(c_1055, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_96, c_1050])).
% 4.93/1.97  tff(c_1058, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_845, c_860, c_1055])).
% 4.93/1.97  tff(c_1059, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_1058])).
% 4.93/1.97  tff(c_1133, plain, (![A_242, B_243]: (k2_yellow19(A_242, k3_yellow19(A_242, k2_struct_0(A_242), B_243))=B_243 | ~m1_subset_1(B_243, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_242))))) | ~v13_waybel_0(B_243, k3_yellow_1(k2_struct_0(A_242))) | ~v2_waybel_0(B_243, k3_yellow_1(k2_struct_0(A_242))) | ~v1_subset_1(B_243, u1_struct_0(k3_yellow_1(k2_struct_0(A_242)))) | v1_xboole_0(B_243) | ~l1_struct_0(A_242) | v2_struct_0(A_242))), inference(cnfTransformation, [status(thm)], [f_200])).
% 4.93/1.97  tff(c_1138, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_1133])).
% 4.93/1.97  tff(c_1145, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_845, c_58, c_56, c_54, c_1138])).
% 4.93/1.97  tff(c_1146, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_1145])).
% 4.93/1.97  tff(c_1151, plain, (![C_31]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_31) | ~r1_waybel_7('#skF_1', '#skF_2', C_31) | ~m1_subset_1(C_31, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1146, c_44])).
% 4.93/1.97  tff(c_1158, plain, (![C_31]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_31) | ~r1_waybel_7('#skF_1', '#skF_2', C_31) | ~m1_subset_1(C_31, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_859, c_1059, c_96, c_1151])).
% 4.93/1.97  tff(c_1159, plain, (![C_31]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_31) | ~r1_waybel_7('#skF_1', '#skF_2', C_31) | ~m1_subset_1(C_31, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_66, c_1158])).
% 4.93/1.97  tff(c_1164, plain, (~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_1159])).
% 4.93/1.97  tff(c_1217, plain, (![A_255, B_256, C_257]: (v7_waybel_0(k3_yellow19(A_255, B_256, C_257)) | ~m1_subset_1(C_257, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_256)))) | ~v13_waybel_0(C_257, k3_yellow_1(B_256)) | ~v2_waybel_0(C_257, k3_yellow_1(B_256)) | ~v1_subset_1(C_257, u1_struct_0(k3_yellow_1(B_256))) | v1_xboole_0(C_257) | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0(A_255))) | v1_xboole_0(B_256) | ~l1_struct_0(A_255) | v2_struct_0(A_255))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.93/1.97  tff(c_1222, plain, (![A_255]: (v7_waybel_0(k3_yellow19(A_255, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_255))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_255) | v2_struct_0(A_255))), inference(resolution, [status(thm)], [c_52, c_1217])).
% 4.93/1.97  tff(c_1229, plain, (![A_255]: (v7_waybel_0(k3_yellow19(A_255, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_255))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_255) | v2_struct_0(A_255))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1222])).
% 4.93/1.97  tff(c_1232, plain, (![A_258]: (v7_waybel_0(k3_yellow19(A_258, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_258))) | ~l1_struct_0(A_258) | v2_struct_0(A_258))), inference(negUnitSimplification, [status(thm)], [c_758, c_60, c_1229])).
% 4.93/1.97  tff(c_1238, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_96, c_1232])).
% 4.93/1.97  tff(c_1241, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_845, c_860, c_1238])).
% 4.93/1.97  tff(c_1243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1164, c_1241])).
% 4.93/1.97  tff(c_1244, plain, (![C_31]: (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_31) | ~r1_waybel_7('#skF_1', '#skF_2', C_31) | ~m1_subset_1(C_31, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1159])).
% 4.93/1.97  tff(c_1246, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_1244])).
% 4.93/1.97  tff(c_1251, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1246, c_36])).
% 4.93/1.97  tff(c_1254, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_845, c_860, c_96, c_56, c_54, c_52, c_1251])).
% 4.93/1.97  tff(c_1256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_758, c_60, c_1254])).
% 4.93/1.97  tff(c_1258, plain, (~v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_1244])).
% 4.93/1.97  tff(c_1245, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_1159])).
% 4.93/1.97  tff(c_1154, plain, (![C_31]: (r1_waybel_7('#skF_1', '#skF_2', C_31) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_31) | ~m1_subset_1(C_31, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1146, c_46])).
% 4.93/1.97  tff(c_1161, plain, (![C_31]: (r1_waybel_7('#skF_1', '#skF_2', C_31) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_31) | ~m1_subset_1(C_31, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_859, c_1059, c_96, c_1154])).
% 4.93/1.97  tff(c_1162, plain, (![C_31]: (r1_waybel_7('#skF_1', '#skF_2', C_31) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_31) | ~m1_subset_1(C_31, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_66, c_1161])).
% 4.93/1.97  tff(c_1261, plain, (![C_31]: (r1_waybel_7('#skF_1', '#skF_2', C_31) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_31) | ~m1_subset_1(C_31, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1245, c_1162])).
% 4.93/1.97  tff(c_1263, plain, (![C_260]: (r1_waybel_7('#skF_1', '#skF_2', C_260) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_260) | ~m1_subset_1(C_260, k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_1258, c_1261])).
% 4.93/1.97  tff(c_1269, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_705, c_1263])).
% 4.93/1.97  tff(c_1273, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_1269])).
% 4.93/1.97  tff(c_1275, plain, $false, inference(negUnitSimplification, [status(thm)], [c_704, c_1273])).
% 4.93/1.97  tff(c_1279, plain, (![A_264, B_265]: (~r2_hidden(A_264, k1_connsp_2('#skF_1', B_265)) | ~m1_subset_1(B_265, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_752])).
% 4.93/1.97  tff(c_1283, plain, (![B_14]: (~m1_subset_1(B_14, k2_struct_0('#skF_1')) | ~m1_subset_1(B_14, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_1279])).
% 4.93/1.97  tff(c_1286, plain, (![B_14]: (~m1_subset_1(B_14, k2_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_96, c_1283])).
% 4.93/1.97  tff(c_1287, plain, (![B_14]: (~m1_subset_1(B_14, k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_66, c_1286])).
% 4.93/1.97  tff(c_1289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1287, c_97])).
% 4.93/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.93/1.97  
% 4.93/1.97  Inference rules
% 4.93/1.97  ----------------------
% 4.93/1.97  #Ref     : 0
% 4.93/1.97  #Sup     : 222
% 4.93/1.97  #Fact    : 0
% 4.93/1.97  #Define  : 0
% 4.93/1.97  #Split   : 18
% 4.93/1.97  #Chain   : 0
% 4.93/1.97  #Close   : 0
% 4.93/1.97  
% 4.93/1.97  Ordering : KBO
% 4.93/1.97  
% 4.93/1.97  Simplification rules
% 4.93/1.97  ----------------------
% 4.93/1.97  #Subsume      : 38
% 4.93/1.97  #Demod        : 222
% 4.93/1.97  #Tautology    : 39
% 4.93/1.97  #SimpNegUnit  : 89
% 4.93/1.97  #BackRed      : 3
% 4.93/1.97  
% 4.93/1.97  #Partial instantiations: 0
% 4.93/1.97  #Strategies tried      : 1
% 4.93/1.97  
% 4.93/1.97  Timing (in seconds)
% 4.93/1.97  ----------------------
% 4.93/1.98  Preprocessing        : 0.43
% 4.93/1.98  Parsing              : 0.20
% 4.93/1.98  CNF conversion       : 0.04
% 4.93/1.98  Main loop            : 0.67
% 4.93/1.98  Inferencing          : 0.24
% 4.93/1.98  Reduction            : 0.22
% 4.93/1.98  Demodulation         : 0.15
% 4.93/1.98  BG Simplification    : 0.04
% 4.93/1.98  Subsumption          : 0.13
% 4.93/1.98  Abstraction          : 0.04
% 4.93/1.98  MUC search           : 0.00
% 4.93/1.98  Cooper               : 0.00
% 4.93/1.98  Total                : 1.19
% 4.93/1.98  Index Insertion      : 0.00
% 4.93/1.98  Index Deletion       : 0.00
% 4.93/1.98  Index Matching       : 0.00
% 4.93/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
