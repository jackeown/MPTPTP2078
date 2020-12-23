%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:36 EST 2020

% Result     : Theorem 5.60s
% Output     : CNFRefutation 5.89s
% Verified   : 
% Statistics : Number of formulae       :  227 (2530 expanded)
%              Number of leaves         :   50 ( 903 expanded)
%              Depth                    :   21
%              Number of atoms          :  663 (9136 expanded)
%              Number of equality atoms :   24 ( 515 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k1_connsp_2 > k10_yellow_6 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r2_waybel_7,type,(
    r2_waybel_7: ( $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_237,negated_conjecture,(
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

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_139,axiom,(
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

tff(f_167,axiom,(
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

tff(f_111,axiom,(
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

tff(f_210,axiom,(
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

tff(f_191,axiom,(
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

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

tff(c_78,plain,
    ( ~ r2_waybel_7('#skF_3','#skF_4','#skF_5')
    | ~ r2_hidden('#skF_5',k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_123,plain,(
    ~ r2_hidden('#skF_5',k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_72,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_26,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_103,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = k2_struct_0(A_52)
      | ~ l1_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_108,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_26,c_103])).

tff(c_112,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_108])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_113,plain,(
    m1_subset_1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_60])).

tff(c_84,plain,
    ( r2_hidden('#skF_5',k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
    | r2_waybel_7('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_189,plain,(
    r2_waybel_7('#skF_3','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_129,plain,(
    ! [A_58] :
      ( m1_subset_1(k2_struct_0(A_58),k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_135,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_129])).

tff(c_191,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_194,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_191])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_194])).

tff(c_200,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_74,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_376,plain,(
    ! [A_102,B_103] :
      ( m1_subset_1(k1_connsp_2(A_102,B_103),k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ m1_subset_1(B_103,u1_struct_0(A_102))
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_382,plain,(
    ! [B_103] :
      ( m1_subset_1(k1_connsp_2('#skF_3',B_103),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_376])).

tff(c_385,plain,(
    ! [B_103] :
      ( m1_subset_1(k1_connsp_2('#skF_3',B_103),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_103,k2_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_112,c_382])).

tff(c_387,plain,(
    ! [B_104] :
      ( m1_subset_1(k1_connsp_2('#skF_3',B_104),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_104,k2_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_385])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_392,plain,(
    ! [B_105] :
      ( r1_tarski(k1_connsp_2('#skF_3',B_105),k2_struct_0('#skF_3'))
      | ~ m1_subset_1(B_105,k2_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_387,c_18])).

tff(c_136,plain,(
    ! [A_58] :
      ( r1_tarski(k2_struct_0(A_58),u1_struct_0(A_58))
      | ~ l1_struct_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_129,c_18])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_206,plain,(
    ! [C_72,B_73,A_74] :
      ( r2_hidden(C_72,B_73)
      | ~ r2_hidden(C_72,A_74)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_218,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_1'(A_75),B_76)
      | ~ r1_tarski(A_75,B_76)
      | v1_xboole_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_4,c_206])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_306,plain,(
    ! [A_92,B_93,B_94] :
      ( r2_hidden('#skF_1'(A_92),B_93)
      | ~ r1_tarski(B_94,B_93)
      | ~ r1_tarski(A_92,B_94)
      | v1_xboole_0(A_92) ) ),
    inference(resolution,[status(thm)],[c_218,c_6])).

tff(c_347,plain,(
    ! [A_98,A_99] :
      ( r2_hidden('#skF_1'(A_98),u1_struct_0(A_99))
      | ~ r1_tarski(A_98,k2_struct_0(A_99))
      | v1_xboole_0(A_98)
      | ~ l1_struct_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_136,c_306])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_357,plain,(
    ! [A_99,A_98] :
      ( ~ v1_xboole_0(u1_struct_0(A_99))
      | ~ r1_tarski(A_98,k2_struct_0(A_99))
      | v1_xboole_0(A_98)
      | ~ l1_struct_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_347,c_2])).

tff(c_395,plain,(
    ! [B_105] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(k1_connsp_2('#skF_3',B_105))
      | ~ l1_struct_0('#skF_3')
      | ~ m1_subset_1(B_105,k2_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_392,c_357])).

tff(c_413,plain,(
    ! [B_105] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
      | v1_xboole_0(k1_connsp_2('#skF_3',B_105))
      | ~ m1_subset_1(B_105,k2_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_112,c_395])).

tff(c_422,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_413])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_199,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_66,plain,(
    v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_64,plain,(
    v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_24,plain,(
    ! [A_15] :
      ( m1_subset_1(k2_struct_0(A_15),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_860,plain,(
    ! [A_157,B_158,C_159] :
      ( v4_orders_2(k3_yellow19(A_157,B_158,C_159))
      | ~ m1_subset_1(C_159,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_158))))
      | ~ v13_waybel_0(C_159,k3_yellow_1(B_158))
      | ~ v2_waybel_0(C_159,k3_yellow_1(B_158))
      | v1_xboole_0(C_159)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | v1_xboole_0(B_158)
      | ~ l1_struct_0(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_871,plain,(
    ! [A_157] :
      ( v4_orders_2(k3_yellow19(A_157,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_157)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_157)
      | v2_struct_0(A_157) ) ),
    inference(resolution,[status(thm)],[c_62,c_860])).

tff(c_877,plain,(
    ! [A_157] :
      ( v4_orders_2(k3_yellow19(A_157,k2_struct_0('#skF_3'),'#skF_4'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_157)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_157)
      | v2_struct_0(A_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_871])).

tff(c_879,plain,(
    ! [A_160] :
      ( v4_orders_2(k3_yellow19(A_160,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_struct_0(A_160)
      | v2_struct_0(A_160) ) ),
    inference(negUnitSimplification,[status(thm)],[c_422,c_70,c_877])).

tff(c_883,plain,
    ( v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_879])).

tff(c_892,plain,
    ( v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_883])).

tff(c_893,plain,(
    v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_892])).

tff(c_68,plain,(
    v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_1349,plain,(
    ! [A_212,B_213,C_214] :
      ( v7_waybel_0(k3_yellow19(A_212,B_213,C_214))
      | ~ m1_subset_1(C_214,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_213))))
      | ~ v13_waybel_0(C_214,k3_yellow_1(B_213))
      | ~ v2_waybel_0(C_214,k3_yellow_1(B_213))
      | ~ v1_subset_1(C_214,u1_struct_0(k3_yellow_1(B_213)))
      | v1_xboole_0(C_214)
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0(A_212)))
      | v1_xboole_0(B_213)
      | ~ l1_struct_0(A_212)
      | v2_struct_0(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1360,plain,(
    ! [A_212] :
      ( v7_waybel_0(k3_yellow19(A_212,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_212)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_212)
      | v2_struct_0(A_212) ) ),
    inference(resolution,[status(thm)],[c_62,c_1349])).

tff(c_1366,plain,(
    ! [A_212] :
      ( v7_waybel_0(k3_yellow19(A_212,k2_struct_0('#skF_3'),'#skF_4'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_212)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_212)
      | v2_struct_0(A_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_1360])).

tff(c_1368,plain,(
    ! [A_215] :
      ( v7_waybel_0(k3_yellow19(A_215,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_struct_0(A_215)
      | v2_struct_0(A_215) ) ),
    inference(negUnitSimplification,[status(thm)],[c_422,c_70,c_1366])).

tff(c_1372,plain,
    ( v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_1368])).

tff(c_1381,plain,
    ( v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_1372])).

tff(c_1382,plain,(
    v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1381])).

tff(c_1136,plain,(
    ! [A_190,B_191,C_192] :
      ( l1_waybel_0(k3_yellow19(A_190,B_191,C_192),A_190)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_191))))
      | ~ v13_waybel_0(C_192,k3_yellow_1(B_191))
      | ~ v2_waybel_0(C_192,k3_yellow_1(B_191))
      | v1_xboole_0(C_192)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(A_190)))
      | v1_xboole_0(B_191)
      | ~ l1_struct_0(A_190)
      | v2_struct_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1147,plain,(
    ! [A_190] :
      ( l1_waybel_0(k3_yellow19(A_190,k2_struct_0('#skF_3'),'#skF_4'),A_190)
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_190)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_190)
      | v2_struct_0(A_190) ) ),
    inference(resolution,[status(thm)],[c_62,c_1136])).

tff(c_1153,plain,(
    ! [A_190] :
      ( l1_waybel_0(k3_yellow19(A_190,k2_struct_0('#skF_3'),'#skF_4'),A_190)
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_190)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_190)
      | v2_struct_0(A_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1147])).

tff(c_1182,plain,(
    ! [A_197] :
      ( l1_waybel_0(k3_yellow19(A_197,k2_struct_0('#skF_3'),'#skF_4'),A_197)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ l1_struct_0(A_197)
      | v2_struct_0(A_197) ) ),
    inference(negUnitSimplification,[status(thm)],[c_422,c_70,c_1153])).

tff(c_1185,plain,
    ( l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_1182])).

tff(c_1193,plain,
    ( l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_1185])).

tff(c_1194,plain,(
    l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1193])).

tff(c_1515,plain,(
    ! [A_230,B_231] :
      ( k2_yellow19(A_230,k3_yellow19(A_230,k2_struct_0(A_230),B_231)) = B_231
      | ~ m1_subset_1(B_231,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_230)))))
      | ~ v13_waybel_0(B_231,k3_yellow_1(k2_struct_0(A_230)))
      | ~ v2_waybel_0(B_231,k3_yellow_1(k2_struct_0(A_230)))
      | ~ v1_subset_1(B_231,u1_struct_0(k3_yellow_1(k2_struct_0(A_230))))
      | v1_xboole_0(B_231)
      | ~ l1_struct_0(A_230)
      | v2_struct_0(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_1526,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = '#skF_4'
    | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1515])).

tff(c_1532,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_68,c_66,c_64,c_1526])).

tff(c_1533,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_1532])).

tff(c_54,plain,(
    ! [C_38,A_32,B_36] :
      ( r2_hidden(C_38,k10_yellow_6(A_32,B_36))
      | ~ r2_waybel_7(A_32,k2_yellow19(A_32,B_36),C_38)
      | ~ m1_subset_1(C_38,u1_struct_0(A_32))
      | ~ l1_waybel_0(B_36,A_32)
      | ~ v7_waybel_0(B_36)
      | ~ v4_orders_2(B_36)
      | v2_struct_0(B_36)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1540,plain,(
    ! [C_38] :
      ( r2_hidden(C_38,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ r2_waybel_7('#skF_3','#skF_4',C_38)
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_54])).

tff(c_1547,plain,(
    ! [C_38] :
      ( r2_hidden(C_38,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ r2_waybel_7('#skF_3','#skF_4',C_38)
      | ~ m1_subset_1(C_38,k2_struct_0('#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_893,c_1382,c_1194,c_112,c_1540])).

tff(c_1548,plain,(
    ! [C_38] :
      ( r2_hidden(C_38,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ r2_waybel_7('#skF_3','#skF_4',C_38)
      | ~ m1_subset_1(C_38,k2_struct_0('#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1547])).

tff(c_1576,plain,(
    v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1548])).

tff(c_46,plain,(
    ! [A_26,B_27,C_28] :
      ( ~ v2_struct_0(k3_yellow19(A_26,B_27,C_28))
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_27))))
      | ~ v13_waybel_0(C_28,k3_yellow_1(B_27))
      | ~ v2_waybel_0(C_28,k3_yellow_1(B_27))
      | v1_xboole_0(C_28)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | v1_xboole_0(B_27)
      | ~ l1_struct_0(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1578,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1576,c_46])).

tff(c_1581,plain,
    ( v1_xboole_0('#skF_4')
    | v1_xboole_0(k2_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_199,c_112,c_66,c_64,c_62,c_1578])).

tff(c_1583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_422,c_70,c_1581])).

tff(c_1586,plain,(
    ! [C_234] :
      ( r2_hidden(C_234,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ r2_waybel_7('#skF_3','#skF_4',C_234)
      | ~ m1_subset_1(C_234,k2_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_1548])).

tff(c_1589,plain,
    ( ~ r2_waybel_7('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1586,c_123])).

tff(c_1602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_189,c_1589])).

tff(c_1604,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_413])).

tff(c_1618,plain,(
    ! [B_239] :
      ( v1_xboole_0(k1_connsp_2('#skF_3',B_239))
      | ~ m1_subset_1(B_239,k2_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_413])).

tff(c_1622,plain,(
    v1_xboole_0(k1_connsp_2('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_113,c_1618])).

tff(c_142,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_2'(A_60,B_61),A_60)
      | r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_146,plain,(
    ! [A_60,B_61] :
      ( ~ v1_xboole_0(A_60)
      | r1_tarski(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_142,c_2])).

tff(c_155,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r1_tarski(B_66,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_171,plain,(
    ! [B_68,A_69] :
      ( B_68 = A_69
      | ~ r1_tarski(B_68,A_69)
      | ~ v1_xboole_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_146,c_155])).

tff(c_184,plain,(
    ! [B_61,A_60] :
      ( B_61 = A_60
      | ~ v1_xboole_0(B_61)
      | ~ v1_xboole_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_146,c_171])).

tff(c_1610,plain,(
    ! [A_60] :
      ( k2_struct_0('#skF_3') = A_60
      | ~ v1_xboole_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_1604,c_184])).

tff(c_1630,plain,(
    k1_connsp_2('#skF_3','#skF_5') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1622,c_1610])).

tff(c_30,plain,(
    ! [B_21,A_19] :
      ( r2_hidden(B_21,k1_connsp_2(A_19,B_21))
      | ~ m1_subset_1(B_21,u1_struct_0(A_19))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1647,plain,
    ( r2_hidden('#skF_5',k2_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1630,c_30])).

tff(c_1658,plain,
    ( r2_hidden('#skF_5',k2_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_113,c_112,c_1647])).

tff(c_1659,plain,(
    r2_hidden('#skF_5',k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1658])).

tff(c_1665,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1659,c_2])).

tff(c_1670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1604,c_1665])).

tff(c_1671,plain,(
    r2_hidden('#skF_5',k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_1701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_1671])).

tff(c_1702,plain,(
    ~ r2_waybel_7('#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1703,plain,(
    r2_hidden('#skF_5',k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1909,plain,(
    ! [A_282,B_283] :
      ( m1_subset_1(k1_connsp_2(A_282,B_283),k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ m1_subset_1(B_283,u1_struct_0(A_282))
      | ~ l1_pre_topc(A_282)
      | ~ v2_pre_topc(A_282)
      | v2_struct_0(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1915,plain,(
    ! [B_283] :
      ( m1_subset_1(k1_connsp_2('#skF_3',B_283),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_283,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_1909])).

tff(c_1918,plain,(
    ! [B_283] :
      ( m1_subset_1(k1_connsp_2('#skF_3',B_283),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_283,k2_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_112,c_1915])).

tff(c_1920,plain,(
    ! [B_284] :
      ( m1_subset_1(k1_connsp_2('#skF_3',B_284),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_284,k2_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1918])).

tff(c_1925,plain,(
    ! [B_285] :
      ( r1_tarski(k1_connsp_2('#skF_3',B_285),k2_struct_0('#skF_3'))
      | ~ m1_subset_1(B_285,k2_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1920,c_18])).

tff(c_1800,plain,(
    ! [C_261,B_262,A_263] :
      ( r2_hidden(C_261,B_262)
      | ~ r2_hidden(C_261,A_263)
      | ~ r1_tarski(A_263,B_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1810,plain,(
    ! [A_264,B_265] :
      ( r2_hidden('#skF_1'(A_264),B_265)
      | ~ r1_tarski(A_264,B_265)
      | v1_xboole_0(A_264) ) ),
    inference(resolution,[status(thm)],[c_4,c_1800])).

tff(c_1817,plain,(
    ! [B_265,A_264] :
      ( ~ v1_xboole_0(B_265)
      | ~ r1_tarski(A_264,B_265)
      | v1_xboole_0(A_264) ) ),
    inference(resolution,[status(thm)],[c_1810,c_2])).

tff(c_1937,plain,(
    ! [B_285] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
      | v1_xboole_0(k1_connsp_2('#skF_3',B_285))
      | ~ m1_subset_1(B_285,k2_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1925,c_1817])).

tff(c_1940,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1937])).

tff(c_1723,plain,(
    ! [A_249] :
      ( m1_subset_1(k2_struct_0(A_249),k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ l1_struct_0(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1729,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_1723])).

tff(c_1779,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1729])).

tff(c_1782,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_1779])).

tff(c_1786,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1782])).

tff(c_1788,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1729])).

tff(c_1787,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1729])).

tff(c_2386,plain,(
    ! [A_344,B_345,C_346] :
      ( v4_orders_2(k3_yellow19(A_344,B_345,C_346))
      | ~ m1_subset_1(C_346,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_345))))
      | ~ v13_waybel_0(C_346,k3_yellow_1(B_345))
      | ~ v2_waybel_0(C_346,k3_yellow_1(B_345))
      | v1_xboole_0(C_346)
      | ~ m1_subset_1(B_345,k1_zfmisc_1(u1_struct_0(A_344)))
      | v1_xboole_0(B_345)
      | ~ l1_struct_0(A_344)
      | v2_struct_0(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2397,plain,(
    ! [A_344] :
      ( v4_orders_2(k3_yellow19(A_344,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_344)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_344)
      | v2_struct_0(A_344) ) ),
    inference(resolution,[status(thm)],[c_62,c_2386])).

tff(c_2403,plain,(
    ! [A_344] :
      ( v4_orders_2(k3_yellow19(A_344,k2_struct_0('#skF_3'),'#skF_4'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_344)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_344)
      | v2_struct_0(A_344) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_2397])).

tff(c_2410,plain,(
    ! [A_348] :
      ( v4_orders_2(k3_yellow19(A_348,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_348)))
      | ~ l1_struct_0(A_348)
      | v2_struct_0(A_348) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1940,c_70,c_2403])).

tff(c_2414,plain,
    ( v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_2410])).

tff(c_2423,plain,
    ( v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1788,c_2414])).

tff(c_2424,plain,(
    v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2423])).

tff(c_2790,plain,(
    ! [A_383,B_384,C_385] :
      ( l1_waybel_0(k3_yellow19(A_383,B_384,C_385),A_383)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_384))))
      | ~ v13_waybel_0(C_385,k3_yellow_1(B_384))
      | ~ v2_waybel_0(C_385,k3_yellow_1(B_384))
      | v1_xboole_0(C_385)
      | ~ m1_subset_1(B_384,k1_zfmisc_1(u1_struct_0(A_383)))
      | v1_xboole_0(B_384)
      | ~ l1_struct_0(A_383)
      | v2_struct_0(A_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2801,plain,(
    ! [A_383] :
      ( l1_waybel_0(k3_yellow19(A_383,k2_struct_0('#skF_3'),'#skF_4'),A_383)
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_383)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_383)
      | v2_struct_0(A_383) ) ),
    inference(resolution,[status(thm)],[c_62,c_2790])).

tff(c_2807,plain,(
    ! [A_383] :
      ( l1_waybel_0(k3_yellow19(A_383,k2_struct_0('#skF_3'),'#skF_4'),A_383)
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_383)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_383)
      | v2_struct_0(A_383) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_2801])).

tff(c_2827,plain,(
    ! [A_388] :
      ( l1_waybel_0(k3_yellow19(A_388,k2_struct_0('#skF_3'),'#skF_4'),A_388)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_388)))
      | ~ l1_struct_0(A_388)
      | v2_struct_0(A_388) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1940,c_70,c_2807])).

tff(c_2830,plain,
    ( l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_2827])).

tff(c_2838,plain,
    ( l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1788,c_2830])).

tff(c_2839,plain,(
    l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2838])).

tff(c_2911,plain,(
    ! [A_393,B_394] :
      ( k2_yellow19(A_393,k3_yellow19(A_393,k2_struct_0(A_393),B_394)) = B_394
      | ~ m1_subset_1(B_394,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_393)))))
      | ~ v13_waybel_0(B_394,k3_yellow_1(k2_struct_0(A_393)))
      | ~ v2_waybel_0(B_394,k3_yellow_1(k2_struct_0(A_393)))
      | ~ v1_subset_1(B_394,u1_struct_0(k3_yellow_1(k2_struct_0(A_393))))
      | v1_xboole_0(B_394)
      | ~ l1_struct_0(A_393)
      | v2_struct_0(A_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_2922,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = '#skF_4'
    | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2911])).

tff(c_2928,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1788,c_68,c_66,c_64,c_2922])).

tff(c_2929,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_2928])).

tff(c_2933,plain,(
    ! [C_38] :
      ( r2_hidden(C_38,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ r2_waybel_7('#skF_3','#skF_4',C_38)
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2929,c_54])).

tff(c_2940,plain,(
    ! [C_38] :
      ( r2_hidden(C_38,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ r2_waybel_7('#skF_3','#skF_4',C_38)
      | ~ m1_subset_1(C_38,k2_struct_0('#skF_3'))
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_2424,c_2839,c_112,c_2933])).

tff(c_2941,plain,(
    ! [C_38] :
      ( r2_hidden(C_38,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ r2_waybel_7('#skF_3','#skF_4',C_38)
      | ~ m1_subset_1(C_38,k2_struct_0('#skF_3'))
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2940])).

tff(c_2981,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2941])).

tff(c_3031,plain,(
    ! [A_408,B_409,C_410] :
      ( v7_waybel_0(k3_yellow19(A_408,B_409,C_410))
      | ~ m1_subset_1(C_410,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_409))))
      | ~ v13_waybel_0(C_410,k3_yellow_1(B_409))
      | ~ v2_waybel_0(C_410,k3_yellow_1(B_409))
      | ~ v1_subset_1(C_410,u1_struct_0(k3_yellow_1(B_409)))
      | v1_xboole_0(C_410)
      | ~ m1_subset_1(B_409,k1_zfmisc_1(u1_struct_0(A_408)))
      | v1_xboole_0(B_409)
      | ~ l1_struct_0(A_408)
      | v2_struct_0(A_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_3042,plain,(
    ! [A_408] :
      ( v7_waybel_0(k3_yellow19(A_408,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_408)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_408)
      | v2_struct_0(A_408) ) ),
    inference(resolution,[status(thm)],[c_62,c_3031])).

tff(c_3048,plain,(
    ! [A_408] :
      ( v7_waybel_0(k3_yellow19(A_408,k2_struct_0('#skF_3'),'#skF_4'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_408)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_408)
      | v2_struct_0(A_408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_3042])).

tff(c_3050,plain,(
    ! [A_411] :
      ( v7_waybel_0(k3_yellow19(A_411,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_411)))
      | ~ l1_struct_0(A_411)
      | v2_struct_0(A_411) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1940,c_70,c_3048])).

tff(c_3054,plain,
    ( v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_3050])).

tff(c_3063,plain,
    ( v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1788,c_3054])).

tff(c_3065,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2981,c_3063])).

tff(c_3067,plain,(
    v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2941])).

tff(c_56,plain,(
    ! [A_32,B_36,C_38] :
      ( r2_waybel_7(A_32,k2_yellow19(A_32,B_36),C_38)
      | ~ r2_hidden(C_38,k10_yellow_6(A_32,B_36))
      | ~ m1_subset_1(C_38,u1_struct_0(A_32))
      | ~ l1_waybel_0(B_36,A_32)
      | ~ v7_waybel_0(B_36)
      | ~ v4_orders_2(B_36)
      | v2_struct_0(B_36)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_2936,plain,(
    ! [C_38] :
      ( r2_waybel_7('#skF_3','#skF_4',C_38)
      | ~ r2_hidden(C_38,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2929,c_56])).

tff(c_2943,plain,(
    ! [C_38] :
      ( r2_waybel_7('#skF_3','#skF_4',C_38)
      | ~ r2_hidden(C_38,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ m1_subset_1(C_38,k2_struct_0('#skF_3'))
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_2424,c_2839,c_112,c_2936])).

tff(c_2944,plain,(
    ! [C_38] :
      ( r2_waybel_7('#skF_3','#skF_4',C_38)
      | ~ r2_hidden(C_38,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ m1_subset_1(C_38,k2_struct_0('#skF_3'))
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2943])).

tff(c_3069,plain,(
    ! [C_38] :
      ( r2_waybel_7('#skF_3','#skF_4',C_38)
      | ~ r2_hidden(C_38,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ m1_subset_1(C_38,k2_struct_0('#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3067,c_2944])).

tff(c_3070,plain,(
    v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3069])).

tff(c_3072,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3070,c_46])).

tff(c_3075,plain,
    ( v1_xboole_0('#skF_4')
    | v1_xboole_0(k2_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1788,c_1787,c_112,c_66,c_64,c_62,c_3072])).

tff(c_3077,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1940,c_70,c_3075])).

tff(c_3080,plain,(
    ! [C_412] :
      ( r2_waybel_7('#skF_3','#skF_4',C_412)
      | ~ r2_hidden(C_412,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ m1_subset_1(C_412,k2_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_3069])).

tff(c_3095,plain,
    ( r2_waybel_7('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1703,c_3080])).

tff(c_3105,plain,(
    r2_waybel_7('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_3095])).

tff(c_3107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1702,c_3105])).

tff(c_3109,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1937])).

tff(c_3123,plain,(
    ! [B_417] :
      ( v1_xboole_0(k1_connsp_2('#skF_3',B_417))
      | ~ m1_subset_1(B_417,k2_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_1937])).

tff(c_3127,plain,(
    v1_xboole_0(k1_connsp_2('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_113,c_3123])).

tff(c_1743,plain,(
    ! [A_251,B_252] :
      ( r2_hidden('#skF_2'(A_251,B_252),A_251)
      | r1_tarski(A_251,B_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1747,plain,(
    ! [A_251,B_252] :
      ( ~ v1_xboole_0(A_251)
      | r1_tarski(A_251,B_252) ) ),
    inference(resolution,[status(thm)],[c_1743,c_2])).

tff(c_1748,plain,(
    ! [A_253,B_254] :
      ( ~ v1_xboole_0(A_253)
      | r1_tarski(A_253,B_254) ) ),
    inference(resolution,[status(thm)],[c_1743,c_2])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1752,plain,(
    ! [B_255,A_256] :
      ( B_255 = A_256
      | ~ r1_tarski(B_255,A_256)
      | ~ v1_xboole_0(A_256) ) ),
    inference(resolution,[status(thm)],[c_1748,c_12])).

tff(c_1765,plain,(
    ! [B_252,A_251] :
      ( B_252 = A_251
      | ~ v1_xboole_0(B_252)
      | ~ v1_xboole_0(A_251) ) ),
    inference(resolution,[status(thm)],[c_1747,c_1752])).

tff(c_3115,plain,(
    ! [A_251] :
      ( k2_struct_0('#skF_3') = A_251
      | ~ v1_xboole_0(A_251) ) ),
    inference(resolution,[status(thm)],[c_3109,c_1765])).

tff(c_3135,plain,(
    k1_connsp_2('#skF_3','#skF_5') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3127,c_3115])).

tff(c_3152,plain,
    ( r2_hidden('#skF_5',k2_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3135,c_30])).

tff(c_3163,plain,
    ( r2_hidden('#skF_5',k2_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_113,c_112,c_3152])).

tff(c_3164,plain,(
    r2_hidden('#skF_5',k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3163])).

tff(c_3170,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3164,c_2])).

tff(c_3175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3109,c_3170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:05:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.60/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.68/2.08  
% 5.68/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.68/2.09  %$ r2_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k1_connsp_2 > k10_yellow_6 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 5.68/2.09  
% 5.68/2.09  %Foreground sorts:
% 5.68/2.09  
% 5.68/2.09  
% 5.68/2.09  %Background operators:
% 5.68/2.09  
% 5.68/2.09  
% 5.68/2.09  %Foreground operators:
% 5.68/2.09  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.68/2.09  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.68/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.68/2.09  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 5.68/2.09  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 5.68/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.68/2.09  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.68/2.09  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 5.68/2.09  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 5.68/2.09  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.68/2.09  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 5.68/2.09  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 5.68/2.09  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.68/2.09  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 5.68/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.68/2.09  tff('#skF_5', type, '#skF_5': $i).
% 5.68/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.68/2.09  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 5.68/2.09  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.68/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.68/2.09  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.68/2.09  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 5.68/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.68/2.09  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 5.68/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.68/2.09  tff(r2_waybel_7, type, r2_waybel_7: ($i * $i * $i) > $o).
% 5.68/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.68/2.09  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.68/2.09  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 5.68/2.09  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 5.68/2.09  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.68/2.09  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.68/2.09  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.68/2.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.68/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.68/2.09  
% 5.89/2.12  tff(f_237, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, k3_yellow19(A, k2_struct_0(A), B))) <=> r2_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_yellow19)).
% 5.89/2.12  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.89/2.12  tff(f_52, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.89/2.12  tff(f_56, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 5.89/2.12  tff(f_71, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 5.89/2.12  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.89/2.12  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.89/2.12  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.89/2.12  tff(f_139, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_yellow19)).
% 5.89/2.12  tff(f_167, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow19)).
% 5.89/2.12  tff(f_111, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 5.89/2.12  tff(f_210, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 5.89/2.12  tff(f_191, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, B)) <=> r2_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow19)).
% 5.89/2.12  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.89/2.12  tff(f_83, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_connsp_2)).
% 5.89/2.12  tff(c_78, plain, (~r2_waybel_7('#skF_3', '#skF_4', '#skF_5') | ~r2_hidden('#skF_5', k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.89/2.12  tff(c_123, plain, (~r2_hidden('#skF_5', k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')))), inference(splitLeft, [status(thm)], [c_78])).
% 5.89/2.12  tff(c_72, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.89/2.12  tff(c_26, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.89/2.12  tff(c_103, plain, (![A_52]: (u1_struct_0(A_52)=k2_struct_0(A_52) | ~l1_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.89/2.12  tff(c_108, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_26, c_103])).
% 5.89/2.12  tff(c_112, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_72, c_108])).
% 5.89/2.12  tff(c_60, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.89/2.12  tff(c_113, plain, (m1_subset_1('#skF_5', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_60])).
% 5.89/2.12  tff(c_84, plain, (r2_hidden('#skF_5', k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | r2_waybel_7('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.89/2.12  tff(c_189, plain, (r2_waybel_7('#skF_3', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_84])).
% 5.89/2.12  tff(c_76, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.89/2.12  tff(c_129, plain, (![A_58]: (m1_subset_1(k2_struct_0(A_58), k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.89/2.12  tff(c_135, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_112, c_129])).
% 5.89/2.12  tff(c_191, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_135])).
% 5.89/2.12  tff(c_194, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_191])).
% 5.89/2.12  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_194])).
% 5.89/2.12  tff(c_200, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_135])).
% 5.89/2.12  tff(c_74, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.89/2.12  tff(c_376, plain, (![A_102, B_103]: (m1_subset_1(k1_connsp_2(A_102, B_103), k1_zfmisc_1(u1_struct_0(A_102))) | ~m1_subset_1(B_103, u1_struct_0(A_102)) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.89/2.12  tff(c_382, plain, (![B_103]: (m1_subset_1(k1_connsp_2('#skF_3', B_103), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_103, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_376])).
% 5.89/2.12  tff(c_385, plain, (![B_103]: (m1_subset_1(k1_connsp_2('#skF_3', B_103), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_103, k2_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_112, c_382])).
% 5.89/2.12  tff(c_387, plain, (![B_104]: (m1_subset_1(k1_connsp_2('#skF_3', B_104), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_104, k2_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_76, c_385])).
% 5.89/2.12  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.89/2.12  tff(c_392, plain, (![B_105]: (r1_tarski(k1_connsp_2('#skF_3', B_105), k2_struct_0('#skF_3')) | ~m1_subset_1(B_105, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_387, c_18])).
% 5.89/2.12  tff(c_136, plain, (![A_58]: (r1_tarski(k2_struct_0(A_58), u1_struct_0(A_58)) | ~l1_struct_0(A_58))), inference(resolution, [status(thm)], [c_129, c_18])).
% 5.89/2.12  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.89/2.12  tff(c_206, plain, (![C_72, B_73, A_74]: (r2_hidden(C_72, B_73) | ~r2_hidden(C_72, A_74) | ~r1_tarski(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.89/2.12  tff(c_218, plain, (![A_75, B_76]: (r2_hidden('#skF_1'(A_75), B_76) | ~r1_tarski(A_75, B_76) | v1_xboole_0(A_75))), inference(resolution, [status(thm)], [c_4, c_206])).
% 5.89/2.12  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.89/2.12  tff(c_306, plain, (![A_92, B_93, B_94]: (r2_hidden('#skF_1'(A_92), B_93) | ~r1_tarski(B_94, B_93) | ~r1_tarski(A_92, B_94) | v1_xboole_0(A_92))), inference(resolution, [status(thm)], [c_218, c_6])).
% 5.89/2.12  tff(c_347, plain, (![A_98, A_99]: (r2_hidden('#skF_1'(A_98), u1_struct_0(A_99)) | ~r1_tarski(A_98, k2_struct_0(A_99)) | v1_xboole_0(A_98) | ~l1_struct_0(A_99))), inference(resolution, [status(thm)], [c_136, c_306])).
% 5.89/2.12  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.89/2.12  tff(c_357, plain, (![A_99, A_98]: (~v1_xboole_0(u1_struct_0(A_99)) | ~r1_tarski(A_98, k2_struct_0(A_99)) | v1_xboole_0(A_98) | ~l1_struct_0(A_99))), inference(resolution, [status(thm)], [c_347, c_2])).
% 5.89/2.12  tff(c_395, plain, (![B_105]: (~v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(k1_connsp_2('#skF_3', B_105)) | ~l1_struct_0('#skF_3') | ~m1_subset_1(B_105, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_392, c_357])).
% 5.89/2.12  tff(c_413, plain, (![B_105]: (~v1_xboole_0(k2_struct_0('#skF_3')) | v1_xboole_0(k1_connsp_2('#skF_3', B_105)) | ~m1_subset_1(B_105, k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_112, c_395])).
% 5.89/2.12  tff(c_422, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_413])).
% 5.89/2.12  tff(c_70, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.89/2.12  tff(c_199, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_135])).
% 5.89/2.12  tff(c_66, plain, (v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.89/2.12  tff(c_64, plain, (v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.89/2.12  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.89/2.12  tff(c_24, plain, (![A_15]: (m1_subset_1(k2_struct_0(A_15), k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.89/2.12  tff(c_860, plain, (![A_157, B_158, C_159]: (v4_orders_2(k3_yellow19(A_157, B_158, C_159)) | ~m1_subset_1(C_159, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_158)))) | ~v13_waybel_0(C_159, k3_yellow_1(B_158)) | ~v2_waybel_0(C_159, k3_yellow_1(B_158)) | v1_xboole_0(C_159) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_157))) | v1_xboole_0(B_158) | ~l1_struct_0(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.89/2.12  tff(c_871, plain, (![A_157]: (v4_orders_2(k3_yellow19(A_157, k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_157))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_157) | v2_struct_0(A_157))), inference(resolution, [status(thm)], [c_62, c_860])).
% 5.89/2.12  tff(c_877, plain, (![A_157]: (v4_orders_2(k3_yellow19(A_157, k2_struct_0('#skF_3'), '#skF_4')) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_157))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_157) | v2_struct_0(A_157))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_871])).
% 5.89/2.12  tff(c_879, plain, (![A_160]: (v4_orders_2(k3_yellow19(A_160, k2_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_struct_0(A_160) | v2_struct_0(A_160))), inference(negUnitSimplification, [status(thm)], [c_422, c_70, c_877])).
% 5.89/2.12  tff(c_883, plain, (v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_879])).
% 5.89/2.12  tff(c_892, plain, (v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_883])).
% 5.89/2.12  tff(c_893, plain, (v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_76, c_892])).
% 5.89/2.12  tff(c_68, plain, (v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.89/2.12  tff(c_1349, plain, (![A_212, B_213, C_214]: (v7_waybel_0(k3_yellow19(A_212, B_213, C_214)) | ~m1_subset_1(C_214, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_213)))) | ~v13_waybel_0(C_214, k3_yellow_1(B_213)) | ~v2_waybel_0(C_214, k3_yellow_1(B_213)) | ~v1_subset_1(C_214, u1_struct_0(k3_yellow_1(B_213))) | v1_xboole_0(C_214) | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0(A_212))) | v1_xboole_0(B_213) | ~l1_struct_0(A_212) | v2_struct_0(A_212))), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.89/2.12  tff(c_1360, plain, (![A_212]: (v7_waybel_0(k3_yellow19(A_212, k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_212))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_212) | v2_struct_0(A_212))), inference(resolution, [status(thm)], [c_62, c_1349])).
% 5.89/2.12  tff(c_1366, plain, (![A_212]: (v7_waybel_0(k3_yellow19(A_212, k2_struct_0('#skF_3'), '#skF_4')) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_212))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_212) | v2_struct_0(A_212))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_1360])).
% 5.89/2.12  tff(c_1368, plain, (![A_215]: (v7_waybel_0(k3_yellow19(A_215, k2_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_215))) | ~l1_struct_0(A_215) | v2_struct_0(A_215))), inference(negUnitSimplification, [status(thm)], [c_422, c_70, c_1366])).
% 5.89/2.12  tff(c_1372, plain, (v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_1368])).
% 5.89/2.12  tff(c_1381, plain, (v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_1372])).
% 5.89/2.12  tff(c_1382, plain, (v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_76, c_1381])).
% 5.89/2.12  tff(c_1136, plain, (![A_190, B_191, C_192]: (l1_waybel_0(k3_yellow19(A_190, B_191, C_192), A_190) | ~m1_subset_1(C_192, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_191)))) | ~v13_waybel_0(C_192, k3_yellow_1(B_191)) | ~v2_waybel_0(C_192, k3_yellow_1(B_191)) | v1_xboole_0(C_192) | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0(A_190))) | v1_xboole_0(B_191) | ~l1_struct_0(A_190) | v2_struct_0(A_190))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.89/2.12  tff(c_1147, plain, (![A_190]: (l1_waybel_0(k3_yellow19(A_190, k2_struct_0('#skF_3'), '#skF_4'), A_190) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_190))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_190) | v2_struct_0(A_190))), inference(resolution, [status(thm)], [c_62, c_1136])).
% 5.89/2.12  tff(c_1153, plain, (![A_190]: (l1_waybel_0(k3_yellow19(A_190, k2_struct_0('#skF_3'), '#skF_4'), A_190) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_190))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_190) | v2_struct_0(A_190))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1147])).
% 5.89/2.12  tff(c_1182, plain, (![A_197]: (l1_waybel_0(k3_yellow19(A_197, k2_struct_0('#skF_3'), '#skF_4'), A_197) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_197))) | ~l1_struct_0(A_197) | v2_struct_0(A_197))), inference(negUnitSimplification, [status(thm)], [c_422, c_70, c_1153])).
% 5.89/2.12  tff(c_1185, plain, (l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_1182])).
% 5.89/2.12  tff(c_1193, plain, (l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_1185])).
% 5.89/2.12  tff(c_1194, plain, (l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_76, c_1193])).
% 5.89/2.12  tff(c_1515, plain, (![A_230, B_231]: (k2_yellow19(A_230, k3_yellow19(A_230, k2_struct_0(A_230), B_231))=B_231 | ~m1_subset_1(B_231, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_230))))) | ~v13_waybel_0(B_231, k3_yellow_1(k2_struct_0(A_230))) | ~v2_waybel_0(B_231, k3_yellow_1(k2_struct_0(A_230))) | ~v1_subset_1(B_231, u1_struct_0(k3_yellow_1(k2_struct_0(A_230)))) | v1_xboole_0(B_231) | ~l1_struct_0(A_230) | v2_struct_0(A_230))), inference(cnfTransformation, [status(thm)], [f_210])).
% 5.89/2.12  tff(c_1526, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))='#skF_4' | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) | v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1515])).
% 5.89/2.12  tff(c_1532, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))='#skF_4' | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_68, c_66, c_64, c_1526])).
% 5.89/2.12  tff(c_1533, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_1532])).
% 5.89/2.12  tff(c_54, plain, (![C_38, A_32, B_36]: (r2_hidden(C_38, k10_yellow_6(A_32, B_36)) | ~r2_waybel_7(A_32, k2_yellow19(A_32, B_36), C_38) | ~m1_subset_1(C_38, u1_struct_0(A_32)) | ~l1_waybel_0(B_36, A_32) | ~v7_waybel_0(B_36) | ~v4_orders_2(B_36) | v2_struct_0(B_36) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.89/2.12  tff(c_1540, plain, (![C_38]: (r2_hidden(C_38, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~r2_waybel_7('#skF_3', '#skF_4', C_38) | ~m1_subset_1(C_38, u1_struct_0('#skF_3')) | ~l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1533, c_54])).
% 5.89/2.12  tff(c_1547, plain, (![C_38]: (r2_hidden(C_38, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~r2_waybel_7('#skF_3', '#skF_4', C_38) | ~m1_subset_1(C_38, k2_struct_0('#skF_3')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_893, c_1382, c_1194, c_112, c_1540])).
% 5.89/2.12  tff(c_1548, plain, (![C_38]: (r2_hidden(C_38, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~r2_waybel_7('#skF_3', '#skF_4', C_38) | ~m1_subset_1(C_38, k2_struct_0('#skF_3')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_76, c_1547])).
% 5.89/2.12  tff(c_1576, plain, (v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_1548])).
% 5.89/2.12  tff(c_46, plain, (![A_26, B_27, C_28]: (~v2_struct_0(k3_yellow19(A_26, B_27, C_28)) | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_27)))) | ~v13_waybel_0(C_28, k3_yellow_1(B_27)) | ~v2_waybel_0(C_28, k3_yellow_1(B_27)) | v1_xboole_0(C_28) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | v1_xboole_0(B_27) | ~l1_struct_0(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.89/2.12  tff(c_1578, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1576, c_46])).
% 5.89/2.12  tff(c_1581, plain, (v1_xboole_0('#skF_4') | v1_xboole_0(k2_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_199, c_112, c_66, c_64, c_62, c_1578])).
% 5.89/2.12  tff(c_1583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_422, c_70, c_1581])).
% 5.89/2.12  tff(c_1586, plain, (![C_234]: (r2_hidden(C_234, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~r2_waybel_7('#skF_3', '#skF_4', C_234) | ~m1_subset_1(C_234, k2_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_1548])).
% 5.89/2.12  tff(c_1589, plain, (~r2_waybel_7('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1586, c_123])).
% 5.89/2.12  tff(c_1602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_189, c_1589])).
% 5.89/2.12  tff(c_1604, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_413])).
% 5.89/2.12  tff(c_1618, plain, (![B_239]: (v1_xboole_0(k1_connsp_2('#skF_3', B_239)) | ~m1_subset_1(B_239, k2_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_413])).
% 5.89/2.12  tff(c_1622, plain, (v1_xboole_0(k1_connsp_2('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_113, c_1618])).
% 5.89/2.12  tff(c_142, plain, (![A_60, B_61]: (r2_hidden('#skF_2'(A_60, B_61), A_60) | r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.89/2.12  tff(c_146, plain, (![A_60, B_61]: (~v1_xboole_0(A_60) | r1_tarski(A_60, B_61))), inference(resolution, [status(thm)], [c_142, c_2])).
% 5.89/2.12  tff(c_155, plain, (![B_66, A_67]: (B_66=A_67 | ~r1_tarski(B_66, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.89/2.12  tff(c_171, plain, (![B_68, A_69]: (B_68=A_69 | ~r1_tarski(B_68, A_69) | ~v1_xboole_0(A_69))), inference(resolution, [status(thm)], [c_146, c_155])).
% 5.89/2.12  tff(c_184, plain, (![B_61, A_60]: (B_61=A_60 | ~v1_xboole_0(B_61) | ~v1_xboole_0(A_60))), inference(resolution, [status(thm)], [c_146, c_171])).
% 5.89/2.12  tff(c_1610, plain, (![A_60]: (k2_struct_0('#skF_3')=A_60 | ~v1_xboole_0(A_60))), inference(resolution, [status(thm)], [c_1604, c_184])).
% 5.89/2.12  tff(c_1630, plain, (k1_connsp_2('#skF_3', '#skF_5')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1622, c_1610])).
% 5.89/2.12  tff(c_30, plain, (![B_21, A_19]: (r2_hidden(B_21, k1_connsp_2(A_19, B_21)) | ~m1_subset_1(B_21, u1_struct_0(A_19)) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.89/2.12  tff(c_1647, plain, (r2_hidden('#skF_5', k2_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1630, c_30])).
% 5.89/2.12  tff(c_1658, plain, (r2_hidden('#skF_5', k2_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_113, c_112, c_1647])).
% 5.89/2.12  tff(c_1659, plain, (r2_hidden('#skF_5', k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_76, c_1658])).
% 5.89/2.12  tff(c_1665, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1659, c_2])).
% 5.89/2.12  tff(c_1670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1604, c_1665])).
% 5.89/2.12  tff(c_1671, plain, (r2_hidden('#skF_5', k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')))), inference(splitRight, [status(thm)], [c_84])).
% 5.89/2.12  tff(c_1701, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_1671])).
% 5.89/2.12  tff(c_1702, plain, (~r2_waybel_7('#skF_3', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_78])).
% 5.89/2.12  tff(c_1703, plain, (r2_hidden('#skF_5', k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')))), inference(splitRight, [status(thm)], [c_78])).
% 5.89/2.12  tff(c_1909, plain, (![A_282, B_283]: (m1_subset_1(k1_connsp_2(A_282, B_283), k1_zfmisc_1(u1_struct_0(A_282))) | ~m1_subset_1(B_283, u1_struct_0(A_282)) | ~l1_pre_topc(A_282) | ~v2_pre_topc(A_282) | v2_struct_0(A_282))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.89/2.12  tff(c_1915, plain, (![B_283]: (m1_subset_1(k1_connsp_2('#skF_3', B_283), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_283, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_1909])).
% 5.89/2.12  tff(c_1918, plain, (![B_283]: (m1_subset_1(k1_connsp_2('#skF_3', B_283), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_283, k2_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_112, c_1915])).
% 5.89/2.12  tff(c_1920, plain, (![B_284]: (m1_subset_1(k1_connsp_2('#skF_3', B_284), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_284, k2_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_76, c_1918])).
% 5.89/2.12  tff(c_1925, plain, (![B_285]: (r1_tarski(k1_connsp_2('#skF_3', B_285), k2_struct_0('#skF_3')) | ~m1_subset_1(B_285, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1920, c_18])).
% 5.89/2.12  tff(c_1800, plain, (![C_261, B_262, A_263]: (r2_hidden(C_261, B_262) | ~r2_hidden(C_261, A_263) | ~r1_tarski(A_263, B_262))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.89/2.12  tff(c_1810, plain, (![A_264, B_265]: (r2_hidden('#skF_1'(A_264), B_265) | ~r1_tarski(A_264, B_265) | v1_xboole_0(A_264))), inference(resolution, [status(thm)], [c_4, c_1800])).
% 5.89/2.12  tff(c_1817, plain, (![B_265, A_264]: (~v1_xboole_0(B_265) | ~r1_tarski(A_264, B_265) | v1_xboole_0(A_264))), inference(resolution, [status(thm)], [c_1810, c_2])).
% 5.89/2.12  tff(c_1937, plain, (![B_285]: (~v1_xboole_0(k2_struct_0('#skF_3')) | v1_xboole_0(k1_connsp_2('#skF_3', B_285)) | ~m1_subset_1(B_285, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1925, c_1817])).
% 5.89/2.12  tff(c_1940, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1937])).
% 5.89/2.12  tff(c_1723, plain, (![A_249]: (m1_subset_1(k2_struct_0(A_249), k1_zfmisc_1(u1_struct_0(A_249))) | ~l1_struct_0(A_249))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.89/2.12  tff(c_1729, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_112, c_1723])).
% 5.89/2.12  tff(c_1779, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1729])).
% 5.89/2.12  tff(c_1782, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_1779])).
% 5.89/2.12  tff(c_1786, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_1782])).
% 5.89/2.12  tff(c_1788, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1729])).
% 5.89/2.12  tff(c_1787, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_1729])).
% 5.89/2.12  tff(c_2386, plain, (![A_344, B_345, C_346]: (v4_orders_2(k3_yellow19(A_344, B_345, C_346)) | ~m1_subset_1(C_346, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_345)))) | ~v13_waybel_0(C_346, k3_yellow_1(B_345)) | ~v2_waybel_0(C_346, k3_yellow_1(B_345)) | v1_xboole_0(C_346) | ~m1_subset_1(B_345, k1_zfmisc_1(u1_struct_0(A_344))) | v1_xboole_0(B_345) | ~l1_struct_0(A_344) | v2_struct_0(A_344))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.89/2.12  tff(c_2397, plain, (![A_344]: (v4_orders_2(k3_yellow19(A_344, k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_344))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_344) | v2_struct_0(A_344))), inference(resolution, [status(thm)], [c_62, c_2386])).
% 5.89/2.12  tff(c_2403, plain, (![A_344]: (v4_orders_2(k3_yellow19(A_344, k2_struct_0('#skF_3'), '#skF_4')) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_344))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_344) | v2_struct_0(A_344))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_2397])).
% 5.89/2.12  tff(c_2410, plain, (![A_348]: (v4_orders_2(k3_yellow19(A_348, k2_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_348))) | ~l1_struct_0(A_348) | v2_struct_0(A_348))), inference(negUnitSimplification, [status(thm)], [c_1940, c_70, c_2403])).
% 5.89/2.12  tff(c_2414, plain, (v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_2410])).
% 5.89/2.12  tff(c_2423, plain, (v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1788, c_2414])).
% 5.89/2.12  tff(c_2424, plain, (v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_76, c_2423])).
% 5.89/2.12  tff(c_2790, plain, (![A_383, B_384, C_385]: (l1_waybel_0(k3_yellow19(A_383, B_384, C_385), A_383) | ~m1_subset_1(C_385, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_384)))) | ~v13_waybel_0(C_385, k3_yellow_1(B_384)) | ~v2_waybel_0(C_385, k3_yellow_1(B_384)) | v1_xboole_0(C_385) | ~m1_subset_1(B_384, k1_zfmisc_1(u1_struct_0(A_383))) | v1_xboole_0(B_384) | ~l1_struct_0(A_383) | v2_struct_0(A_383))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.89/2.12  tff(c_2801, plain, (![A_383]: (l1_waybel_0(k3_yellow19(A_383, k2_struct_0('#skF_3'), '#skF_4'), A_383) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_383))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_383) | v2_struct_0(A_383))), inference(resolution, [status(thm)], [c_62, c_2790])).
% 5.89/2.12  tff(c_2807, plain, (![A_383]: (l1_waybel_0(k3_yellow19(A_383, k2_struct_0('#skF_3'), '#skF_4'), A_383) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_383))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_383) | v2_struct_0(A_383))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_2801])).
% 5.89/2.12  tff(c_2827, plain, (![A_388]: (l1_waybel_0(k3_yellow19(A_388, k2_struct_0('#skF_3'), '#skF_4'), A_388) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_388))) | ~l1_struct_0(A_388) | v2_struct_0(A_388))), inference(negUnitSimplification, [status(thm)], [c_1940, c_70, c_2807])).
% 5.89/2.12  tff(c_2830, plain, (l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_2827])).
% 5.89/2.12  tff(c_2838, plain, (l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1788, c_2830])).
% 5.89/2.12  tff(c_2839, plain, (l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_76, c_2838])).
% 5.89/2.12  tff(c_2911, plain, (![A_393, B_394]: (k2_yellow19(A_393, k3_yellow19(A_393, k2_struct_0(A_393), B_394))=B_394 | ~m1_subset_1(B_394, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_393))))) | ~v13_waybel_0(B_394, k3_yellow_1(k2_struct_0(A_393))) | ~v2_waybel_0(B_394, k3_yellow_1(k2_struct_0(A_393))) | ~v1_subset_1(B_394, u1_struct_0(k3_yellow_1(k2_struct_0(A_393)))) | v1_xboole_0(B_394) | ~l1_struct_0(A_393) | v2_struct_0(A_393))), inference(cnfTransformation, [status(thm)], [f_210])).
% 5.89/2.12  tff(c_2922, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))='#skF_4' | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) | v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_2911])).
% 5.89/2.12  tff(c_2928, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))='#skF_4' | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1788, c_68, c_66, c_64, c_2922])).
% 5.89/2.12  tff(c_2929, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_2928])).
% 5.89/2.12  tff(c_2933, plain, (![C_38]: (r2_hidden(C_38, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~r2_waybel_7('#skF_3', '#skF_4', C_38) | ~m1_subset_1(C_38, u1_struct_0('#skF_3')) | ~l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2929, c_54])).
% 5.89/2.12  tff(c_2940, plain, (![C_38]: (r2_hidden(C_38, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~r2_waybel_7('#skF_3', '#skF_4', C_38) | ~m1_subset_1(C_38, k2_struct_0('#skF_3')) | ~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_2424, c_2839, c_112, c_2933])).
% 5.89/2.12  tff(c_2941, plain, (![C_38]: (r2_hidden(C_38, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~r2_waybel_7('#skF_3', '#skF_4', C_38) | ~m1_subset_1(C_38, k2_struct_0('#skF_3')) | ~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_76, c_2940])).
% 5.89/2.12  tff(c_2981, plain, (~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_2941])).
% 5.89/2.12  tff(c_3031, plain, (![A_408, B_409, C_410]: (v7_waybel_0(k3_yellow19(A_408, B_409, C_410)) | ~m1_subset_1(C_410, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_409)))) | ~v13_waybel_0(C_410, k3_yellow_1(B_409)) | ~v2_waybel_0(C_410, k3_yellow_1(B_409)) | ~v1_subset_1(C_410, u1_struct_0(k3_yellow_1(B_409))) | v1_xboole_0(C_410) | ~m1_subset_1(B_409, k1_zfmisc_1(u1_struct_0(A_408))) | v1_xboole_0(B_409) | ~l1_struct_0(A_408) | v2_struct_0(A_408))), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.89/2.12  tff(c_3042, plain, (![A_408]: (v7_waybel_0(k3_yellow19(A_408, k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_408))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_408) | v2_struct_0(A_408))), inference(resolution, [status(thm)], [c_62, c_3031])).
% 5.89/2.12  tff(c_3048, plain, (![A_408]: (v7_waybel_0(k3_yellow19(A_408, k2_struct_0('#skF_3'), '#skF_4')) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_408))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_408) | v2_struct_0(A_408))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_3042])).
% 5.89/2.12  tff(c_3050, plain, (![A_411]: (v7_waybel_0(k3_yellow19(A_411, k2_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_411))) | ~l1_struct_0(A_411) | v2_struct_0(A_411))), inference(negUnitSimplification, [status(thm)], [c_1940, c_70, c_3048])).
% 5.89/2.12  tff(c_3054, plain, (v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_3050])).
% 5.89/2.12  tff(c_3063, plain, (v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1788, c_3054])).
% 5.89/2.12  tff(c_3065, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_2981, c_3063])).
% 5.89/2.12  tff(c_3067, plain, (v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(splitRight, [status(thm)], [c_2941])).
% 5.89/2.12  tff(c_56, plain, (![A_32, B_36, C_38]: (r2_waybel_7(A_32, k2_yellow19(A_32, B_36), C_38) | ~r2_hidden(C_38, k10_yellow_6(A_32, B_36)) | ~m1_subset_1(C_38, u1_struct_0(A_32)) | ~l1_waybel_0(B_36, A_32) | ~v7_waybel_0(B_36) | ~v4_orders_2(B_36) | v2_struct_0(B_36) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.89/2.12  tff(c_2936, plain, (![C_38]: (r2_waybel_7('#skF_3', '#skF_4', C_38) | ~r2_hidden(C_38, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~m1_subset_1(C_38, u1_struct_0('#skF_3')) | ~l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2929, c_56])).
% 5.89/2.12  tff(c_2943, plain, (![C_38]: (r2_waybel_7('#skF_3', '#skF_4', C_38) | ~r2_hidden(C_38, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~m1_subset_1(C_38, k2_struct_0('#skF_3')) | ~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_2424, c_2839, c_112, c_2936])).
% 5.89/2.12  tff(c_2944, plain, (![C_38]: (r2_waybel_7('#skF_3', '#skF_4', C_38) | ~r2_hidden(C_38, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~m1_subset_1(C_38, k2_struct_0('#skF_3')) | ~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_76, c_2943])).
% 5.89/2.12  tff(c_3069, plain, (![C_38]: (r2_waybel_7('#skF_3', '#skF_4', C_38) | ~r2_hidden(C_38, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~m1_subset_1(C_38, k2_struct_0('#skF_3')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_3067, c_2944])).
% 5.89/2.12  tff(c_3070, plain, (v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_3069])).
% 5.89/2.12  tff(c_3072, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_3070, c_46])).
% 5.89/2.12  tff(c_3075, plain, (v1_xboole_0('#skF_4') | v1_xboole_0(k2_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1788, c_1787, c_112, c_66, c_64, c_62, c_3072])).
% 5.89/2.12  tff(c_3077, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1940, c_70, c_3075])).
% 5.89/2.12  tff(c_3080, plain, (![C_412]: (r2_waybel_7('#skF_3', '#skF_4', C_412) | ~r2_hidden(C_412, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~m1_subset_1(C_412, k2_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_3069])).
% 5.89/2.12  tff(c_3095, plain, (r2_waybel_7('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1703, c_3080])).
% 5.89/2.12  tff(c_3105, plain, (r2_waybel_7('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_3095])).
% 5.89/2.12  tff(c_3107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1702, c_3105])).
% 5.89/2.12  tff(c_3109, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1937])).
% 5.89/2.12  tff(c_3123, plain, (![B_417]: (v1_xboole_0(k1_connsp_2('#skF_3', B_417)) | ~m1_subset_1(B_417, k2_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_1937])).
% 5.89/2.12  tff(c_3127, plain, (v1_xboole_0(k1_connsp_2('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_113, c_3123])).
% 5.89/2.12  tff(c_1743, plain, (![A_251, B_252]: (r2_hidden('#skF_2'(A_251, B_252), A_251) | r1_tarski(A_251, B_252))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.89/2.12  tff(c_1747, plain, (![A_251, B_252]: (~v1_xboole_0(A_251) | r1_tarski(A_251, B_252))), inference(resolution, [status(thm)], [c_1743, c_2])).
% 5.89/2.12  tff(c_1748, plain, (![A_253, B_254]: (~v1_xboole_0(A_253) | r1_tarski(A_253, B_254))), inference(resolution, [status(thm)], [c_1743, c_2])).
% 5.89/2.12  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.89/2.12  tff(c_1752, plain, (![B_255, A_256]: (B_255=A_256 | ~r1_tarski(B_255, A_256) | ~v1_xboole_0(A_256))), inference(resolution, [status(thm)], [c_1748, c_12])).
% 5.89/2.12  tff(c_1765, plain, (![B_252, A_251]: (B_252=A_251 | ~v1_xboole_0(B_252) | ~v1_xboole_0(A_251))), inference(resolution, [status(thm)], [c_1747, c_1752])).
% 5.89/2.12  tff(c_3115, plain, (![A_251]: (k2_struct_0('#skF_3')=A_251 | ~v1_xboole_0(A_251))), inference(resolution, [status(thm)], [c_3109, c_1765])).
% 5.89/2.12  tff(c_3135, plain, (k1_connsp_2('#skF_3', '#skF_5')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_3127, c_3115])).
% 5.89/2.12  tff(c_3152, plain, (r2_hidden('#skF_5', k2_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3135, c_30])).
% 5.89/2.12  tff(c_3163, plain, (r2_hidden('#skF_5', k2_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_113, c_112, c_3152])).
% 5.89/2.12  tff(c_3164, plain, (r2_hidden('#skF_5', k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_76, c_3163])).
% 5.89/2.12  tff(c_3170, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_3164, c_2])).
% 5.89/2.12  tff(c_3175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3109, c_3170])).
% 5.89/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.12  
% 5.89/2.12  Inference rules
% 5.89/2.12  ----------------------
% 5.89/2.12  #Ref     : 0
% 5.89/2.12  #Sup     : 661
% 5.89/2.12  #Fact    : 0
% 5.89/2.12  #Define  : 0
% 5.89/2.12  #Split   : 20
% 5.89/2.12  #Chain   : 0
% 5.89/2.12  #Close   : 0
% 5.89/2.12  
% 5.89/2.12  Ordering : KBO
% 5.89/2.12  
% 5.89/2.12  Simplification rules
% 5.89/2.12  ----------------------
% 5.89/2.12  #Subsume      : 251
% 5.89/2.12  #Demod        : 363
% 5.89/2.12  #Tautology    : 98
% 5.89/2.12  #SimpNegUnit  : 92
% 5.89/2.12  #BackRed      : 3
% 5.89/2.12  
% 5.89/2.12  #Partial instantiations: 0
% 5.89/2.12  #Strategies tried      : 1
% 5.89/2.12  
% 5.89/2.12  Timing (in seconds)
% 5.89/2.12  ----------------------
% 5.89/2.13  Preprocessing        : 0.39
% 5.89/2.13  Parsing              : 0.20
% 5.89/2.13  CNF conversion       : 0.03
% 5.89/2.13  Main loop            : 0.93
% 5.89/2.13  Inferencing          : 0.32
% 5.89/2.13  Reduction            : 0.28
% 5.89/2.13  Demodulation         : 0.18
% 5.89/2.13  BG Simplification    : 0.04
% 5.89/2.13  Subsumption          : 0.23
% 5.89/2.13  Abstraction          : 0.04
% 5.89/2.13  MUC search           : 0.00
% 5.89/2.13  Cooper               : 0.00
% 5.89/2.13  Total                : 1.39
% 5.89/2.13  Index Insertion      : 0.00
% 5.89/2.13  Index Deletion       : 0.00
% 5.89/2.13  Index Matching       : 0.00
% 5.89/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
