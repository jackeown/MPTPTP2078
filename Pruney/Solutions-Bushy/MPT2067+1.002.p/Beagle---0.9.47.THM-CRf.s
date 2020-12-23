%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2067+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:50 EST 2020

% Result     : Theorem 7.06s
% Output     : CNFRefutation 7.69s
% Verified   : 
% Statistics : Number of formulae       :  568 (2651 expanded)
%              Number of leaves         :   48 ( 896 expanded)
%              Depth                    :   25
%              Number of atoms          : 2700 (15945 expanded)
%              Number of equality atoms :    5 (  30 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_7 > r1_waybel_0 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k2_pre_topc > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_306,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_hidden(C,k2_pre_topc(A,B))
                <=> ? [D] :
                      ( ~ v1_xboole_0(D)
                      & v1_subset_1(D,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
                      & v2_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                      & v13_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                      & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))
                      & r2_hidden(B,D)
                      & r1_waybel_7(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow19)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_191,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r2_hidden(C,k2_yellow19(A,B))
            <=> ( r1_waybel_0(A,B,C)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_yellow19)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_137,axiom,(
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

tff(f_145,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_72,axiom,(
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

tff(f_234,axiom,(
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

tff(f_173,axiom,(
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

tff(f_215,axiom,(
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

tff(f_263,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ? [D] :
                    ( ~ v2_struct_0(D)
                    & v4_orders_2(D)
                    & v7_waybel_0(D)
                    & l1_waybel_0(D,A)
                    & r1_waybel_0(A,D,B)
                    & r3_waybel_9(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow19)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A) )
     => ( ~ v1_xboole_0(k2_yellow19(A,B))
        & v13_waybel_0(k2_yellow19(A,B),k3_yellow_1(k2_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_yellow19)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => ( v1_subset_1(k2_yellow19(A,B),u1_struct_0(k3_yellow_1(k2_struct_0(A))))
        & v2_waybel_0(k2_yellow19(A,B),k3_yellow_1(k2_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_yellow19)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A) )
     => m1_subset_1(k2_yellow19(A,B),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow19)).

tff(f_274,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(c_70,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_110,plain,
    ( r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_113,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_106,plain,
    ( r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_124,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_102,plain,
    ( r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_122,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_98,plain,
    ( r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_123,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_90,plain,
    ( r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_114,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_86,plain,
    ( r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | r1_waybel_7('#skF_2','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_121,plain,(
    r1_waybel_7('#skF_2','#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_94,plain,
    ( r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_134,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_74,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_14,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_155,plain,(
    ! [C_120,A_121,B_122] :
      ( r2_hidden(C_120,k2_yellow19(A_121,B_122))
      | ~ m1_subset_1(C_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ r1_waybel_0(A_121,B_122,C_120)
      | ~ l1_waybel_0(B_122,A_121)
      | v2_struct_0(B_122)
      | ~ l1_struct_0(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_165,plain,(
    ! [B_122] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_122))
      | ~ r1_waybel_0('#skF_2',B_122,'#skF_3')
      | ~ l1_waybel_0(B_122,'#skF_2')
      | v2_struct_0(B_122)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_155])).

tff(c_172,plain,(
    ! [B_122] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_122))
      | ~ r1_waybel_0('#skF_2',B_122,'#skF_3')
      | ~ l1_waybel_0(B_122,'#skF_2')
      | v2_struct_0(B_122)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_165])).

tff(c_174,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_177,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_174])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_177])).

tff(c_183,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_4,plain,(
    ! [A_3] :
      ( m1_subset_1(k2_struct_0(A_3),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_307,plain,(
    ! [A_171,B_172,C_173] :
      ( v4_orders_2(k3_yellow19(A_171,B_172,C_173))
      | ~ m1_subset_1(C_173,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_172))))
      | ~ v13_waybel_0(C_173,k3_yellow_1(B_172))
      | ~ v2_waybel_0(C_173,k3_yellow_1(B_172))
      | v1_xboole_0(C_173)
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0(A_171)))
      | v1_xboole_0(B_172)
      | ~ l1_struct_0(A_171)
      | v2_struct_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_314,plain,(
    ! [A_171] :
      ( v4_orders_2(k3_yellow19(A_171,k2_struct_0('#skF_2'),'#skF_5'))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_171)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_171)
      | v2_struct_0(A_171) ) ),
    inference(resolution,[status(thm)],[c_134,c_307])).

tff(c_322,plain,(
    ! [A_171] :
      ( v4_orders_2(k3_yellow19(A_171,k2_struct_0('#skF_2'),'#skF_5'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_171)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_171)
      | v2_struct_0(A_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_123,c_314])).

tff(c_323,plain,(
    ! [A_171] :
      ( v4_orders_2(k3_yellow19(A_171,k2_struct_0('#skF_2'),'#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_171)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_171)
      | v2_struct_0(A_171) ) ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_322])).

tff(c_325,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_323])).

tff(c_32,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(k2_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_328,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_325,c_32])).

tff(c_331,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_328])).

tff(c_333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_331])).

tff(c_335,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_323])).

tff(c_373,plain,(
    ! [A_179,B_180,C_181] :
      ( l1_waybel_0(k3_yellow19(A_179,B_180,C_181),A_179)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_180))))
      | ~ v13_waybel_0(C_181,k3_yellow_1(B_180))
      | ~ v2_waybel_0(C_181,k3_yellow_1(B_180))
      | v1_xboole_0(C_181)
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_179)))
      | v1_xboole_0(B_180)
      | ~ l1_struct_0(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_380,plain,(
    ! [A_179] :
      ( l1_waybel_0(k3_yellow19(A_179,k2_struct_0('#skF_2'),'#skF_5'),A_179)
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_179)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_179)
      | v2_struct_0(A_179) ) ),
    inference(resolution,[status(thm)],[c_134,c_373])).

tff(c_388,plain,(
    ! [A_179] :
      ( l1_waybel_0(k3_yellow19(A_179,k2_struct_0('#skF_2'),'#skF_5'),A_179)
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_179)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_179)
      | v2_struct_0(A_179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_123,c_380])).

tff(c_391,plain,(
    ! [A_182] :
      ( l1_waybel_0(k3_yellow19(A_182,k2_struct_0('#skF_2'),'#skF_5'),A_182)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_struct_0(A_182)
      | v2_struct_0(A_182) ) ),
    inference(negUnitSimplification,[status(thm)],[c_335,c_113,c_388])).

tff(c_394,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_391])).

tff(c_397,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_394])).

tff(c_398,plain,(
    l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_397])).

tff(c_470,plain,(
    ! [A_198,B_199] :
      ( k2_yellow19(A_198,k3_yellow19(A_198,k2_struct_0(A_198),B_199)) = B_199
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_198)))))
      | ~ v13_waybel_0(B_199,k3_yellow_1(k2_struct_0(A_198)))
      | ~ v2_waybel_0(B_199,k3_yellow_1(k2_struct_0(A_198)))
      | ~ v1_subset_1(B_199,u1_struct_0(k3_yellow_1(k2_struct_0(A_198))))
      | v1_xboole_0(B_199)
      | ~ l1_struct_0(A_198)
      | v2_struct_0(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_477,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5')) = '#skF_5'
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_134,c_470])).

tff(c_485,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_124,c_122,c_123,c_477])).

tff(c_486,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_113,c_485])).

tff(c_42,plain,(
    ! [C_27,A_21,B_25] :
      ( m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ r2_hidden(C_27,k2_yellow19(A_21,B_25))
      | ~ l1_waybel_0(B_25,A_21)
      | v2_struct_0(B_25)
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_516,plain,(
    ! [C_27] :
      ( m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_27,'#skF_5')
      | ~ l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'),'#skF_2')
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'))
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_42])).

tff(c_557,plain,(
    ! [C_27] :
      ( m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_27,'#skF_5')
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_398,c_516])).

tff(c_558,plain,(
    ! [C_27] :
      ( m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_27,'#skF_5')
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_557])).

tff(c_572,plain,(
    v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_558])).

tff(c_30,plain,(
    ! [A_14,B_15,C_16] :
      ( ~ v2_struct_0(k3_yellow19(A_14,B_15,C_16))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_15))))
      | ~ v13_waybel_0(C_16,k3_yellow_1(B_15))
      | ~ v2_waybel_0(C_16,k3_yellow_1(B_15))
      | v1_xboole_0(C_16)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | v1_xboole_0(B_15)
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_575,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_2')))
    | v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_572,c_30])).

tff(c_578,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_122,c_123,c_134,c_575])).

tff(c_579,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_335,c_113,c_578])).

tff(c_582,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_579])).

tff(c_586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_582])).

tff(c_588,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_558])).

tff(c_44,plain,(
    ! [A_21,B_25,C_27] :
      ( r1_waybel_0(A_21,B_25,C_27)
      | ~ r2_hidden(C_27,k2_yellow19(A_21,B_25))
      | ~ l1_waybel_0(B_25,A_21)
      | v2_struct_0(B_25)
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_522,plain,(
    ! [C_27] :
      ( r1_waybel_0('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'),C_27)
      | ~ r2_hidden(C_27,'#skF_5')
      | ~ l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'),'#skF_2')
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'))
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_44])).

tff(c_563,plain,(
    ! [C_27] :
      ( r1_waybel_0('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'),C_27)
      | ~ r2_hidden(C_27,'#skF_5')
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_398,c_522])).

tff(c_564,plain,(
    ! [C_27] :
      ( r1_waybel_0('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'),C_27)
      | ~ r2_hidden(C_27,'#skF_5')
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_563])).

tff(c_664,plain,(
    ! [C_27] :
      ( r1_waybel_0('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'),C_27)
      | ~ r2_hidden(C_27,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_588,c_564])).

tff(c_76,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_354,plain,(
    ! [A_177] :
      ( v4_orders_2(k3_yellow19(A_177,k2_struct_0('#skF_2'),'#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_struct_0(A_177)
      | v2_struct_0(A_177) ) ),
    inference(splitRight,[status(thm)],[c_323])).

tff(c_358,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'))
    | v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_354])).

tff(c_361,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_358])).

tff(c_362,plain,(
    v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_361])).

tff(c_443,plain,(
    ! [A_194,B_195,C_196] :
      ( v7_waybel_0(k3_yellow19(A_194,B_195,C_196))
      | ~ m1_subset_1(C_196,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_195))))
      | ~ v13_waybel_0(C_196,k3_yellow_1(B_195))
      | ~ v2_waybel_0(C_196,k3_yellow_1(B_195))
      | ~ v1_subset_1(C_196,u1_struct_0(k3_yellow_1(B_195)))
      | v1_xboole_0(C_196)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(u1_struct_0(A_194)))
      | v1_xboole_0(B_195)
      | ~ l1_struct_0(A_194)
      | v2_struct_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_450,plain,(
    ! [A_194] :
      ( v7_waybel_0(k3_yellow19(A_194,k2_struct_0('#skF_2'),'#skF_5'))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_194)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_194)
      | v2_struct_0(A_194) ) ),
    inference(resolution,[status(thm)],[c_134,c_443])).

tff(c_458,plain,(
    ! [A_194] :
      ( v7_waybel_0(k3_yellow19(A_194,k2_struct_0('#skF_2'),'#skF_5'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_194)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_194)
      | v2_struct_0(A_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_123,c_450])).

tff(c_461,plain,(
    ! [A_197] :
      ( v7_waybel_0(k3_yellow19(A_197,k2_struct_0('#skF_2'),'#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ l1_struct_0(A_197)
      | v2_struct_0(A_197) ) ),
    inference(negUnitSimplification,[status(thm)],[c_335,c_113,c_458])).

tff(c_465,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'))
    | v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_461])).

tff(c_468,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_465])).

tff(c_469,plain,(
    v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_468])).

tff(c_46,plain,(
    ! [A_28,B_32,C_34] :
      ( r3_waybel_9(A_28,B_32,C_34)
      | ~ r1_waybel_7(A_28,k2_yellow19(A_28,B_32),C_34)
      | ~ m1_subset_1(C_34,u1_struct_0(A_28))
      | ~ l1_waybel_0(B_32,A_28)
      | ~ v7_waybel_0(B_32)
      | ~ v4_orders_2(B_32)
      | v2_struct_0(B_32)
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_497,plain,(
    ! [C_34] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'),C_34)
      | ~ r1_waybel_7('#skF_2','#skF_5',C_34)
      | ~ m1_subset_1(C_34,u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'),'#skF_2')
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'))
      | ~ v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_46])).

tff(c_538,plain,(
    ! [C_34] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'),C_34)
      | ~ r1_waybel_7('#skF_2','#skF_5',C_34)
      | ~ m1_subset_1(C_34,u1_struct_0('#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_362,c_469,c_398,c_497])).

tff(c_539,plain,(
    ! [C_34] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'),C_34)
      | ~ r1_waybel_7('#skF_2','#skF_5',C_34)
      | ~ m1_subset_1(C_34,u1_struct_0('#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_538])).

tff(c_750,plain,(
    ! [C_214] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'),C_214)
      | ~ r1_waybel_7('#skF_2','#skF_5',C_214)
      | ~ m1_subset_1(C_214,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_588,c_539])).

tff(c_52,plain,(
    ! [C_56,A_38,B_50,D_59] :
      ( r2_hidden(C_56,k2_pre_topc(A_38,B_50))
      | ~ r3_waybel_9(A_38,D_59,C_56)
      | ~ r1_waybel_0(A_38,D_59,B_50)
      | ~ l1_waybel_0(D_59,A_38)
      | ~ v7_waybel_0(D_59)
      | ~ v4_orders_2(D_59)
      | v2_struct_0(D_59)
      | ~ m1_subset_1(C_56,u1_struct_0(A_38))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_752,plain,(
    ! [C_214,B_50] :
      ( r2_hidden(C_214,k2_pre_topc('#skF_2',B_50))
      | ~ r1_waybel_0('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'),B_50)
      | ~ l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'),'#skF_2')
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'))
      | ~ v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_waybel_7('#skF_2','#skF_5',C_214)
      | ~ m1_subset_1(C_214,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_750,c_52])).

tff(c_755,plain,(
    ! [C_214,B_50] :
      ( r2_hidden(C_214,k2_pre_topc('#skF_2',B_50))
      | ~ r1_waybel_0('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'),B_50)
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | ~ r1_waybel_7('#skF_2','#skF_5',C_214)
      | ~ m1_subset_1(C_214,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_362,c_469,c_398,c_752])).

tff(c_793,plain,(
    ! [C_221,B_222] :
      ( r2_hidden(C_221,k2_pre_topc('#skF_2',B_222))
      | ~ r1_waybel_0('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_5'),B_222)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_waybel_7('#skF_2','#skF_5',C_221)
      | ~ m1_subset_1(C_221,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_588,c_755])).

tff(c_798,plain,(
    ! [C_225,C_226] :
      ( r2_hidden(C_225,k2_pre_topc('#skF_2',C_226))
      | ~ m1_subset_1(C_226,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_waybel_7('#skF_2','#skF_5',C_225)
      | ~ m1_subset_1(C_225,u1_struct_0('#skF_2'))
      | ~ r2_hidden(C_226,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_664,c_793])).

tff(c_808,plain,(
    ! [C_225] :
      ( r2_hidden(C_225,k2_pre_topc('#skF_2','#skF_3'))
      | ~ r1_waybel_7('#skF_2','#skF_5',C_225)
      | ~ m1_subset_1(C_225,u1_struct_0('#skF_2'))
      | ~ r2_hidden('#skF_3','#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_798])).

tff(c_819,plain,(
    ! [C_227] :
      ( r2_hidden(C_227,k2_pre_topc('#skF_2','#skF_3'))
      | ~ r1_waybel_7('#skF_2','#skF_5',C_227)
      | ~ m1_subset_1(C_227,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_808])).

tff(c_80,plain,(
    ! [D_83] :
      ( ~ r1_waybel_7('#skF_2',D_83,'#skF_4')
      | ~ r2_hidden('#skF_3',D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
      | ~ v13_waybel_0(D_83,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(D_83,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(D_83,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(D_83)
      | ~ r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_372,plain,(
    ~ r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_824,plain,
    ( ~ r1_waybel_7('#skF_2','#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_819,c_372])).

tff(c_842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_121,c_824])).

tff(c_879,plain,(
    ! [D_228] :
      ( ~ r1_waybel_7('#skF_2',D_228,'#skF_4')
      | ~ r2_hidden('#skF_3',D_228)
      | ~ m1_subset_1(D_228,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
      | ~ v13_waybel_0(D_228,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(D_228,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(D_228,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(D_228) ) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_890,plain,
    ( ~ r1_waybel_7('#skF_2','#skF_5','#skF_4')
    | ~ r2_hidden('#skF_3','#skF_5')
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_134,c_879])).

tff(c_902,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_123,c_114,c_121,c_890])).

tff(c_904,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_902])).

tff(c_905,plain,(
    r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_1048,plain,(
    ! [A_280,B_281,C_282] :
      ( r1_waybel_0(A_280,'#skF_1'(A_280,B_281,C_282),B_281)
      | ~ r2_hidden(C_282,k2_pre_topc(A_280,B_281))
      | ~ m1_subset_1(C_282,u1_struct_0(A_280))
      | ~ m1_subset_1(B_281,k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_1056,plain,(
    ! [C_282] :
      ( r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3',C_282),'#skF_3')
      | ~ r2_hidden(C_282,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_282,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_1048])).

tff(c_1062,plain,(
    ! [C_282] :
      ( r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3',C_282),'#skF_3')
      | ~ r2_hidden(C_282,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_282,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1056])).

tff(c_1063,plain,(
    ! [C_282] :
      ( r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3',C_282),'#skF_3')
      | ~ r2_hidden(C_282,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_282,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1062])).

tff(c_1015,plain,(
    ! [A_268,B_269,C_270] :
      ( ~ v2_struct_0('#skF_1'(A_268,B_269,C_270))
      | ~ r2_hidden(C_270,k2_pre_topc(A_268,B_269))
      | ~ m1_subset_1(C_270,u1_struct_0(A_268))
      | ~ m1_subset_1(B_269,k1_zfmisc_1(u1_struct_0(A_268)))
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_1017,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_905,c_1015])).

tff(c_1020,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_1017])).

tff(c_1021,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1020])).

tff(c_1022,plain,(
    ! [A_271,B_272,C_273] :
      ( l1_waybel_0('#skF_1'(A_271,B_272,C_273),A_271)
      | ~ r2_hidden(C_273,k2_pre_topc(A_271,B_272))
      | ~ m1_subset_1(C_273,u1_struct_0(A_271))
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271)
      | v2_struct_0(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_1024,plain,
    ( l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_905,c_1022])).

tff(c_1027,plain,
    ( l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_1024])).

tff(c_1028,plain,(
    l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1027])).

tff(c_958,plain,(
    ! [A_256,B_257,C_258] :
      ( v4_orders_2('#skF_1'(A_256,B_257,C_258))
      | ~ r2_hidden(C_258,k2_pre_topc(A_256,B_257))
      | ~ m1_subset_1(C_258,u1_struct_0(A_256))
      | ~ m1_subset_1(B_257,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256)
      | v2_struct_0(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_960,plain,
    ( v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_905,c_958])).

tff(c_963,plain,
    ( v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_960])).

tff(c_964,plain,(
    v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_963])).

tff(c_1008,plain,(
    ! [A_265,B_266,C_267] :
      ( v7_waybel_0('#skF_1'(A_265,B_266,C_267))
      | ~ r2_hidden(C_267,k2_pre_topc(A_265,B_266))
      | ~ m1_subset_1(C_267,u1_struct_0(A_265))
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ l1_pre_topc(A_265)
      | ~ v2_pre_topc(A_265)
      | v2_struct_0(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_1010,plain,
    ( v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_905,c_1008])).

tff(c_1013,plain,
    ( v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_1010])).

tff(c_1014,plain,(
    v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1013])).

tff(c_1030,plain,(
    ! [A_274,B_275,C_276] :
      ( r3_waybel_9(A_274,'#skF_1'(A_274,B_275,C_276),C_276)
      | ~ r2_hidden(C_276,k2_pre_topc(A_274,B_275))
      | ~ m1_subset_1(C_276,u1_struct_0(A_274))
      | ~ m1_subset_1(B_275,k1_zfmisc_1(u1_struct_0(A_274)))
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_1038,plain,(
    ! [C_276] :
      ( r3_waybel_9('#skF_2','#skF_1'('#skF_2','#skF_3',C_276),C_276)
      | ~ r2_hidden(C_276,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_276,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_1030])).

tff(c_1044,plain,(
    ! [C_276] :
      ( r3_waybel_9('#skF_2','#skF_1'('#skF_2','#skF_3',C_276),C_276)
      | ~ r2_hidden(C_276,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_276,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1038])).

tff(c_1045,plain,(
    ! [C_276] :
      ( r3_waybel_9('#skF_2','#skF_1'('#skF_2','#skF_3',C_276),C_276)
      | ~ r2_hidden(C_276,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_276,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1044])).

tff(c_933,plain,(
    ! [C_253,A_254,B_255] :
      ( r2_hidden(C_253,k2_yellow19(A_254,B_255))
      | ~ m1_subset_1(C_253,k1_zfmisc_1(u1_struct_0(A_254)))
      | ~ r1_waybel_0(A_254,B_255,C_253)
      | ~ l1_waybel_0(B_255,A_254)
      | v2_struct_0(B_255)
      | ~ l1_struct_0(A_254)
      | v2_struct_0(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_941,plain,(
    ! [B_255] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_255))
      | ~ r1_waybel_0('#skF_2',B_255,'#skF_3')
      | ~ l1_waybel_0(B_255,'#skF_2')
      | v2_struct_0(B_255)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_933])).

tff(c_947,plain,(
    ! [B_255] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_255))
      | ~ r1_waybel_0('#skF_2',B_255,'#skF_3')
      | ~ l1_waybel_0(B_255,'#skF_2')
      | v2_struct_0(B_255)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_941])).

tff(c_948,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_947])).

tff(c_951,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_948])).

tff(c_955,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_951])).

tff(c_956,plain,(
    ! [B_255] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_255))
      | ~ r1_waybel_0('#skF_2',B_255,'#skF_3')
      | ~ l1_waybel_0(B_255,'#skF_2')
      | v2_struct_0(B_255) ) ),
    inference(splitRight,[status(thm)],[c_947])).

tff(c_48,plain,(
    ! [A_28,B_32,C_34] :
      ( r1_waybel_7(A_28,k2_yellow19(A_28,B_32),C_34)
      | ~ r3_waybel_9(A_28,B_32,C_34)
      | ~ m1_subset_1(C_34,u1_struct_0(A_28))
      | ~ l1_waybel_0(B_32,A_28)
      | ~ v7_waybel_0(B_32)
      | ~ v4_orders_2(B_32)
      | v2_struct_0(B_32)
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_957,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_947])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( v13_waybel_0(k2_yellow19(A_10,B_11),k3_yellow_1(k2_struct_0(A_10)))
      | ~ l1_waybel_0(B_11,A_10)
      | v2_struct_0(B_11)
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( v2_waybel_0(k2_yellow19(A_12,B_13),k3_yellow_1(k2_struct_0(A_12)))
      | ~ l1_waybel_0(B_13,A_12)
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( v1_subset_1(k2_yellow19(A_12,B_13),u1_struct_0(k3_yellow_1(k2_struct_0(A_12))))
      | ~ l1_waybel_0(B_13,A_12)
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k2_yellow19(A_4,B_5),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_4)))))
      | ~ l1_waybel_0(B_5,A_4)
      | v2_struct_0(B_5)
      | ~ l1_struct_0(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1077,plain,(
    ! [D_292] :
      ( ~ r1_waybel_7('#skF_2',D_292,'#skF_4')
      | ~ r2_hidden('#skF_3',D_292)
      | ~ m1_subset_1(D_292,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
      | ~ v13_waybel_0(D_292,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(D_292,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(D_292,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(D_292) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_80])).

tff(c_1081,plain,(
    ! [B_5] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_5),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_5))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(k2_yellow19('#skF_2',B_5),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_yellow19('#skF_2',B_5))
      | ~ l1_waybel_0(B_5,'#skF_2')
      | v2_struct_0(B_5)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_1077])).

tff(c_1092,plain,(
    ! [B_5] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_5),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_5))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(k2_yellow19('#skF_2',B_5),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_yellow19('#skF_2',B_5))
      | ~ l1_waybel_0(B_5,'#skF_2')
      | v2_struct_0(B_5)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_957,c_1081])).

tff(c_1226,plain,(
    ! [B_342] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_342),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_342))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_342),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_342),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(k2_yellow19('#skF_2',B_342),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_yellow19('#skF_2',B_342))
      | ~ l1_waybel_0(B_342,'#skF_2')
      | v2_struct_0(B_342) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1092])).

tff(c_1230,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_1226])).

tff(c_1233,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_957,c_1230])).

tff(c_1235,plain,(
    ! [B_343] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_343),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_343))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_343),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_343),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_343))
      | ~ l1_waybel_0(B_343,'#skF_2')
      | ~ v7_waybel_0(B_343)
      | ~ v4_orders_2(B_343)
      | v2_struct_0(B_343) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1233])).

tff(c_1239,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_1235])).

tff(c_1242,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_957,c_1239])).

tff(c_1244,plain,(
    ! [B_344] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_344),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_344))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_344),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_344))
      | ~ l1_waybel_0(B_344,'#skF_2')
      | ~ v7_waybel_0(B_344)
      | ~ v4_orders_2(B_344)
      | v2_struct_0(B_344) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1242])).

tff(c_1248,plain,(
    ! [B_11] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_11),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_11))
      | v1_xboole_0(k2_yellow19('#skF_2',B_11))
      | ~ v7_waybel_0(B_11)
      | ~ v4_orders_2(B_11)
      | ~ l1_waybel_0(B_11,'#skF_2')
      | v2_struct_0(B_11)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_1244])).

tff(c_1251,plain,(
    ! [B_11] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_11),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_11))
      | v1_xboole_0(k2_yellow19('#skF_2',B_11))
      | ~ v7_waybel_0(B_11)
      | ~ v4_orders_2(B_11)
      | ~ l1_waybel_0(B_11,'#skF_2')
      | v2_struct_0(B_11)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_957,c_1248])).

tff(c_1253,plain,(
    ! [B_345] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_345),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_345))
      | v1_xboole_0(k2_yellow19('#skF_2',B_345))
      | ~ v7_waybel_0(B_345)
      | ~ v4_orders_2(B_345)
      | ~ l1_waybel_0(B_345,'#skF_2')
      | v2_struct_0(B_345) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1251])).

tff(c_1257,plain,(
    ! [B_32] :
      ( ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_32))
      | v1_xboole_0(k2_yellow19('#skF_2',B_32))
      | ~ r3_waybel_9('#skF_2',B_32,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_32,'#skF_2')
      | ~ v7_waybel_0(B_32)
      | ~ v4_orders_2(B_32)
      | v2_struct_0(B_32)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_1253])).

tff(c_1260,plain,(
    ! [B_32] :
      ( ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_32))
      | v1_xboole_0(k2_yellow19('#skF_2',B_32))
      | ~ r3_waybel_9('#skF_2',B_32,'#skF_4')
      | ~ l1_waybel_0(B_32,'#skF_2')
      | ~ v7_waybel_0(B_32)
      | ~ v4_orders_2(B_32)
      | v2_struct_0(B_32)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_1257])).

tff(c_1263,plain,(
    ! [B_348] :
      ( ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_348))
      | v1_xboole_0(k2_yellow19('#skF_2',B_348))
      | ~ r3_waybel_9('#skF_2',B_348,'#skF_4')
      | ~ l1_waybel_0(B_348,'#skF_2')
      | ~ v7_waybel_0(B_348)
      | ~ v4_orders_2(B_348)
      | v2_struct_0(B_348) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1260])).

tff(c_1268,plain,(
    ! [B_349] :
      ( v1_xboole_0(k2_yellow19('#skF_2',B_349))
      | ~ r3_waybel_9('#skF_2',B_349,'#skF_4')
      | ~ v7_waybel_0(B_349)
      | ~ v4_orders_2(B_349)
      | ~ r1_waybel_0('#skF_2',B_349,'#skF_3')
      | ~ l1_waybel_0(B_349,'#skF_2')
      | v2_struct_0(B_349) ) ),
    inference(resolution,[status(thm)],[c_956,c_1263])).

tff(c_965,plain,(
    ! [B_259] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_259))
      | ~ r1_waybel_0('#skF_2',B_259,'#skF_3')
      | ~ l1_waybel_0(B_259,'#skF_2')
      | v2_struct_0(B_259) ) ),
    inference(splitRight,[status(thm)],[c_947])).

tff(c_68,plain,(
    ! [B_64,A_63] :
      ( ~ v1_xboole_0(B_64)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_988,plain,(
    ! [B_259] :
      ( ~ v1_xboole_0(k2_yellow19('#skF_2',B_259))
      | ~ r1_waybel_0('#skF_2',B_259,'#skF_3')
      | ~ l1_waybel_0(B_259,'#skF_2')
      | v2_struct_0(B_259) ) ),
    inference(resolution,[status(thm)],[c_965,c_68])).

tff(c_1280,plain,(
    ! [B_350] :
      ( ~ r3_waybel_9('#skF_2',B_350,'#skF_4')
      | ~ v7_waybel_0(B_350)
      | ~ v4_orders_2(B_350)
      | ~ r1_waybel_0('#skF_2',B_350,'#skF_3')
      | ~ l1_waybel_0(B_350,'#skF_2')
      | v2_struct_0(B_350) ) ),
    inference(resolution,[status(thm)],[c_1268,c_988])).

tff(c_1292,plain,
    ( ~ v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | ~ l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1045,c_1280])).

tff(c_1303,plain,
    ( ~ r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_905,c_1028,c_964,c_1014,c_1292])).

tff(c_1304,plain,(
    ~ r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1021,c_1303])).

tff(c_1307,plain,
    ( ~ r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1063,c_1304])).

tff(c_1311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_905,c_1307])).

tff(c_1312,plain,(
    r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_1447,plain,(
    ! [A_402,B_403,C_404] :
      ( r1_waybel_0(A_402,'#skF_1'(A_402,B_403,C_404),B_403)
      | ~ r2_hidden(C_404,k2_pre_topc(A_402,B_403))
      | ~ m1_subset_1(C_404,u1_struct_0(A_402))
      | ~ m1_subset_1(B_403,k1_zfmisc_1(u1_struct_0(A_402)))
      | ~ l1_pre_topc(A_402)
      | ~ v2_pre_topc(A_402)
      | v2_struct_0(A_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_1455,plain,(
    ! [C_404] :
      ( r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3',C_404),'#skF_3')
      | ~ r2_hidden(C_404,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_404,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_1447])).

tff(c_1461,plain,(
    ! [C_404] :
      ( r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3',C_404),'#skF_3')
      | ~ r2_hidden(C_404,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_404,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1455])).

tff(c_1462,plain,(
    ! [C_404] :
      ( r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3',C_404),'#skF_3')
      | ~ r2_hidden(C_404,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_404,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1461])).

tff(c_1425,plain,(
    ! [A_393,B_394,C_395] :
      ( ~ v2_struct_0('#skF_1'(A_393,B_394,C_395))
      | ~ r2_hidden(C_395,k2_pre_topc(A_393,B_394))
      | ~ m1_subset_1(C_395,u1_struct_0(A_393))
      | ~ m1_subset_1(B_394,k1_zfmisc_1(u1_struct_0(A_393)))
      | ~ l1_pre_topc(A_393)
      | ~ v2_pre_topc(A_393)
      | v2_struct_0(A_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_1427,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1312,c_1425])).

tff(c_1430,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_1427])).

tff(c_1431,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1430])).

tff(c_1439,plain,(
    ! [A_399,B_400,C_401] :
      ( l1_waybel_0('#skF_1'(A_399,B_400,C_401),A_399)
      | ~ r2_hidden(C_401,k2_pre_topc(A_399,B_400))
      | ~ m1_subset_1(C_401,u1_struct_0(A_399))
      | ~ m1_subset_1(B_400,k1_zfmisc_1(u1_struct_0(A_399)))
      | ~ l1_pre_topc(A_399)
      | ~ v2_pre_topc(A_399)
      | v2_struct_0(A_399) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_1441,plain,
    ( l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1312,c_1439])).

tff(c_1444,plain,
    ( l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_1441])).

tff(c_1445,plain,(
    l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1444])).

tff(c_1399,plain,(
    ! [A_385,B_386,C_387] :
      ( v4_orders_2('#skF_1'(A_385,B_386,C_387))
      | ~ r2_hidden(C_387,k2_pre_topc(A_385,B_386))
      | ~ m1_subset_1(C_387,u1_struct_0(A_385))
      | ~ m1_subset_1(B_386,k1_zfmisc_1(u1_struct_0(A_385)))
      | ~ l1_pre_topc(A_385)
      | ~ v2_pre_topc(A_385)
      | v2_struct_0(A_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_1401,plain,
    ( v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1312,c_1399])).

tff(c_1404,plain,
    ( v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_1401])).

tff(c_1405,plain,(
    v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1404])).

tff(c_1432,plain,(
    ! [A_396,B_397,C_398] :
      ( v7_waybel_0('#skF_1'(A_396,B_397,C_398))
      | ~ r2_hidden(C_398,k2_pre_topc(A_396,B_397))
      | ~ m1_subset_1(C_398,u1_struct_0(A_396))
      | ~ m1_subset_1(B_397,k1_zfmisc_1(u1_struct_0(A_396)))
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_1434,plain,
    ( v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1312,c_1432])).

tff(c_1437,plain,
    ( v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_1434])).

tff(c_1438,plain,(
    v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1437])).

tff(c_1464,plain,(
    ! [A_406,B_407,C_408] :
      ( r3_waybel_9(A_406,'#skF_1'(A_406,B_407,C_408),C_408)
      | ~ r2_hidden(C_408,k2_pre_topc(A_406,B_407))
      | ~ m1_subset_1(C_408,u1_struct_0(A_406))
      | ~ m1_subset_1(B_407,k1_zfmisc_1(u1_struct_0(A_406)))
      | ~ l1_pre_topc(A_406)
      | ~ v2_pre_topc(A_406)
      | v2_struct_0(A_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_1472,plain,(
    ! [C_408] :
      ( r3_waybel_9('#skF_2','#skF_1'('#skF_2','#skF_3',C_408),C_408)
      | ~ r2_hidden(C_408,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_408,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_1464])).

tff(c_1478,plain,(
    ! [C_408] :
      ( r3_waybel_9('#skF_2','#skF_1'('#skF_2','#skF_3',C_408),C_408)
      | ~ r2_hidden(C_408,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_408,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1472])).

tff(c_1479,plain,(
    ! [C_408] :
      ( r3_waybel_9('#skF_2','#skF_1'('#skF_2','#skF_3',C_408),C_408)
      | ~ r2_hidden(C_408,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_408,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1478])).

tff(c_1350,plain,(
    ! [C_381,A_382,B_383] :
      ( r2_hidden(C_381,k2_yellow19(A_382,B_383))
      | ~ m1_subset_1(C_381,k1_zfmisc_1(u1_struct_0(A_382)))
      | ~ r1_waybel_0(A_382,B_383,C_381)
      | ~ l1_waybel_0(B_383,A_382)
      | v2_struct_0(B_383)
      | ~ l1_struct_0(A_382)
      | v2_struct_0(A_382) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1358,plain,(
    ! [B_383] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_383))
      | ~ r1_waybel_0('#skF_2',B_383,'#skF_3')
      | ~ l1_waybel_0(B_383,'#skF_2')
      | v2_struct_0(B_383)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_1350])).

tff(c_1364,plain,(
    ! [B_383] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_383))
      | ~ r1_waybel_0('#skF_2',B_383,'#skF_3')
      | ~ l1_waybel_0(B_383,'#skF_2')
      | v2_struct_0(B_383)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1358])).

tff(c_1365,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1364])).

tff(c_1368,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_1365])).

tff(c_1372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1368])).

tff(c_1373,plain,(
    ! [B_383] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_383))
      | ~ r1_waybel_0('#skF_2',B_383,'#skF_3')
      | ~ l1_waybel_0(B_383,'#skF_2')
      | v2_struct_0(B_383) ) ),
    inference(splitRight,[status(thm)],[c_1364])).

tff(c_1374,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1364])).

tff(c_1509,plain,(
    ! [D_423] :
      ( ~ r1_waybel_7('#skF_2',D_423,'#skF_4')
      | ~ r2_hidden('#skF_3',D_423)
      | ~ m1_subset_1(D_423,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
      | ~ v13_waybel_0(D_423,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(D_423,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(D_423,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(D_423) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1312,c_80])).

tff(c_1513,plain,(
    ! [B_5] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_5),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_5))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(k2_yellow19('#skF_2',B_5),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_yellow19('#skF_2',B_5))
      | ~ l1_waybel_0(B_5,'#skF_2')
      | v2_struct_0(B_5)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_1509])).

tff(c_1524,plain,(
    ! [B_5] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_5),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_5))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(k2_yellow19('#skF_2',B_5),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_yellow19('#skF_2',B_5))
      | ~ l1_waybel_0(B_5,'#skF_2')
      | v2_struct_0(B_5)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1374,c_1513])).

tff(c_1627,plain,(
    ! [B_467] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_467),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_467))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_467),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_467),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(k2_yellow19('#skF_2',B_467),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_yellow19('#skF_2',B_467))
      | ~ l1_waybel_0(B_467,'#skF_2')
      | v2_struct_0(B_467) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1524])).

tff(c_1631,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_1627])).

tff(c_1634,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1374,c_1631])).

tff(c_1636,plain,(
    ! [B_468] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_468),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_468))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_468),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_468),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_468))
      | ~ l1_waybel_0(B_468,'#skF_2')
      | ~ v7_waybel_0(B_468)
      | ~ v4_orders_2(B_468)
      | v2_struct_0(B_468) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1634])).

tff(c_1640,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_1636])).

tff(c_1643,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1374,c_1640])).

tff(c_1645,plain,(
    ! [B_469] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_469),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_469))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_469),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_469))
      | ~ l1_waybel_0(B_469,'#skF_2')
      | ~ v7_waybel_0(B_469)
      | ~ v4_orders_2(B_469)
      | v2_struct_0(B_469) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1643])).

tff(c_1649,plain,(
    ! [B_11] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_11),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_11))
      | v1_xboole_0(k2_yellow19('#skF_2',B_11))
      | ~ v7_waybel_0(B_11)
      | ~ v4_orders_2(B_11)
      | ~ l1_waybel_0(B_11,'#skF_2')
      | v2_struct_0(B_11)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_1645])).

tff(c_1652,plain,(
    ! [B_11] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_11),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_11))
      | v1_xboole_0(k2_yellow19('#skF_2',B_11))
      | ~ v7_waybel_0(B_11)
      | ~ v4_orders_2(B_11)
      | ~ l1_waybel_0(B_11,'#skF_2')
      | v2_struct_0(B_11)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1374,c_1649])).

tff(c_1654,plain,(
    ! [B_470] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_470),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_470))
      | v1_xboole_0(k2_yellow19('#skF_2',B_470))
      | ~ v7_waybel_0(B_470)
      | ~ v4_orders_2(B_470)
      | ~ l1_waybel_0(B_470,'#skF_2')
      | v2_struct_0(B_470) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1652])).

tff(c_1658,plain,(
    ! [B_32] :
      ( ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_32))
      | v1_xboole_0(k2_yellow19('#skF_2',B_32))
      | ~ r3_waybel_9('#skF_2',B_32,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_32,'#skF_2')
      | ~ v7_waybel_0(B_32)
      | ~ v4_orders_2(B_32)
      | v2_struct_0(B_32)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_1654])).

tff(c_1661,plain,(
    ! [B_32] :
      ( ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_32))
      | v1_xboole_0(k2_yellow19('#skF_2',B_32))
      | ~ r3_waybel_9('#skF_2',B_32,'#skF_4')
      | ~ l1_waybel_0(B_32,'#skF_2')
      | ~ v7_waybel_0(B_32)
      | ~ v4_orders_2(B_32)
      | v2_struct_0(B_32)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_1658])).

tff(c_1663,plain,(
    ! [B_471] :
      ( ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_471))
      | v1_xboole_0(k2_yellow19('#skF_2',B_471))
      | ~ r3_waybel_9('#skF_2',B_471,'#skF_4')
      | ~ l1_waybel_0(B_471,'#skF_2')
      | ~ v7_waybel_0(B_471)
      | ~ v4_orders_2(B_471)
      | v2_struct_0(B_471) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1661])).

tff(c_1668,plain,(
    ! [B_472] :
      ( v1_xboole_0(k2_yellow19('#skF_2',B_472))
      | ~ r3_waybel_9('#skF_2',B_472,'#skF_4')
      | ~ v7_waybel_0(B_472)
      | ~ v4_orders_2(B_472)
      | ~ r1_waybel_0('#skF_2',B_472,'#skF_3')
      | ~ l1_waybel_0(B_472,'#skF_2')
      | v2_struct_0(B_472) ) ),
    inference(resolution,[status(thm)],[c_1373,c_1663])).

tff(c_1375,plain,(
    ! [B_384] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_384))
      | ~ r1_waybel_0('#skF_2',B_384,'#skF_3')
      | ~ l1_waybel_0(B_384,'#skF_2')
      | v2_struct_0(B_384) ) ),
    inference(splitRight,[status(thm)],[c_1364])).

tff(c_1398,plain,(
    ! [B_384] :
      ( ~ v1_xboole_0(k2_yellow19('#skF_2',B_384))
      | ~ r1_waybel_0('#skF_2',B_384,'#skF_3')
      | ~ l1_waybel_0(B_384,'#skF_2')
      | v2_struct_0(B_384) ) ),
    inference(resolution,[status(thm)],[c_1375,c_68])).

tff(c_1695,plain,(
    ! [B_476] :
      ( ~ r3_waybel_9('#skF_2',B_476,'#skF_4')
      | ~ v7_waybel_0(B_476)
      | ~ v4_orders_2(B_476)
      | ~ r1_waybel_0('#skF_2',B_476,'#skF_3')
      | ~ l1_waybel_0(B_476,'#skF_2')
      | v2_struct_0(B_476) ) ),
    inference(resolution,[status(thm)],[c_1668,c_1398])).

tff(c_1707,plain,
    ( ~ v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | ~ l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1479,c_1695])).

tff(c_1718,plain,
    ( ~ r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1312,c_1445,c_1405,c_1438,c_1707])).

tff(c_1719,plain,(
    ~ r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1431,c_1718])).

tff(c_1722,plain,
    ( ~ r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1462,c_1719])).

tff(c_1726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1312,c_1722])).

tff(c_1727,plain,(
    r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_1881,plain,(
    ! [A_534,B_535,C_536] :
      ( r1_waybel_0(A_534,'#skF_1'(A_534,B_535,C_536),B_535)
      | ~ r2_hidden(C_536,k2_pre_topc(A_534,B_535))
      | ~ m1_subset_1(C_536,u1_struct_0(A_534))
      | ~ m1_subset_1(B_535,k1_zfmisc_1(u1_struct_0(A_534)))
      | ~ l1_pre_topc(A_534)
      | ~ v2_pre_topc(A_534)
      | v2_struct_0(A_534) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_1889,plain,(
    ! [C_536] :
      ( r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3',C_536),'#skF_3')
      | ~ r2_hidden(C_536,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_536,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_1881])).

tff(c_1895,plain,(
    ! [C_536] :
      ( r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3',C_536),'#skF_3')
      | ~ r2_hidden(C_536,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_536,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1889])).

tff(c_1896,plain,(
    ! [C_536] :
      ( r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3',C_536),'#skF_3')
      | ~ r2_hidden(C_536,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_536,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1895])).

tff(c_1841,plain,(
    ! [A_519,B_520,C_521] :
      ( ~ v2_struct_0('#skF_1'(A_519,B_520,C_521))
      | ~ r2_hidden(C_521,k2_pre_topc(A_519,B_520))
      | ~ m1_subset_1(C_521,u1_struct_0(A_519))
      | ~ m1_subset_1(B_520,k1_zfmisc_1(u1_struct_0(A_519)))
      | ~ l1_pre_topc(A_519)
      | ~ v2_pre_topc(A_519)
      | v2_struct_0(A_519) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_1843,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1727,c_1841])).

tff(c_1846,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_1843])).

tff(c_1847,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1846])).

tff(c_1855,plain,(
    ! [A_525,B_526,C_527] :
      ( l1_waybel_0('#skF_1'(A_525,B_526,C_527),A_525)
      | ~ r2_hidden(C_527,k2_pre_topc(A_525,B_526))
      | ~ m1_subset_1(C_527,u1_struct_0(A_525))
      | ~ m1_subset_1(B_526,k1_zfmisc_1(u1_struct_0(A_525)))
      | ~ l1_pre_topc(A_525)
      | ~ v2_pre_topc(A_525)
      | v2_struct_0(A_525) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_1857,plain,
    ( l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1727,c_1855])).

tff(c_1860,plain,
    ( l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_1857])).

tff(c_1861,plain,(
    l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1860])).

tff(c_1817,plain,(
    ! [A_512,B_513,C_514] :
      ( v4_orders_2('#skF_1'(A_512,B_513,C_514))
      | ~ r2_hidden(C_514,k2_pre_topc(A_512,B_513))
      | ~ m1_subset_1(C_514,u1_struct_0(A_512))
      | ~ m1_subset_1(B_513,k1_zfmisc_1(u1_struct_0(A_512)))
      | ~ l1_pre_topc(A_512)
      | ~ v2_pre_topc(A_512)
      | v2_struct_0(A_512) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_1819,plain,
    ( v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1727,c_1817])).

tff(c_1822,plain,
    ( v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_1819])).

tff(c_1823,plain,(
    v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1822])).

tff(c_1848,plain,(
    ! [A_522,B_523,C_524] :
      ( v7_waybel_0('#skF_1'(A_522,B_523,C_524))
      | ~ r2_hidden(C_524,k2_pre_topc(A_522,B_523))
      | ~ m1_subset_1(C_524,u1_struct_0(A_522))
      | ~ m1_subset_1(B_523,k1_zfmisc_1(u1_struct_0(A_522)))
      | ~ l1_pre_topc(A_522)
      | ~ v2_pre_topc(A_522)
      | v2_struct_0(A_522) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_1850,plain,
    ( v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1727,c_1848])).

tff(c_1853,plain,
    ( v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_1850])).

tff(c_1854,plain,(
    v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1853])).

tff(c_1862,plain,(
    ! [A_528,B_529,C_530] :
      ( r3_waybel_9(A_528,'#skF_1'(A_528,B_529,C_530),C_530)
      | ~ r2_hidden(C_530,k2_pre_topc(A_528,B_529))
      | ~ m1_subset_1(C_530,u1_struct_0(A_528))
      | ~ m1_subset_1(B_529,k1_zfmisc_1(u1_struct_0(A_528)))
      | ~ l1_pre_topc(A_528)
      | ~ v2_pre_topc(A_528)
      | v2_struct_0(A_528) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_1870,plain,(
    ! [C_530] :
      ( r3_waybel_9('#skF_2','#skF_1'('#skF_2','#skF_3',C_530),C_530)
      | ~ r2_hidden(C_530,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_530,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_1862])).

tff(c_1876,plain,(
    ! [C_530] :
      ( r3_waybel_9('#skF_2','#skF_1'('#skF_2','#skF_3',C_530),C_530)
      | ~ r2_hidden(C_530,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_530,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1870])).

tff(c_1877,plain,(
    ! [C_530] :
      ( r3_waybel_9('#skF_2','#skF_1'('#skF_2','#skF_3',C_530),C_530)
      | ~ r2_hidden(C_530,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_530,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1876])).

tff(c_1765,plain,(
    ! [C_507,A_508,B_509] :
      ( r2_hidden(C_507,k2_yellow19(A_508,B_509))
      | ~ m1_subset_1(C_507,k1_zfmisc_1(u1_struct_0(A_508)))
      | ~ r1_waybel_0(A_508,B_509,C_507)
      | ~ l1_waybel_0(B_509,A_508)
      | v2_struct_0(B_509)
      | ~ l1_struct_0(A_508)
      | v2_struct_0(A_508) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1773,plain,(
    ! [B_509] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_509))
      | ~ r1_waybel_0('#skF_2',B_509,'#skF_3')
      | ~ l1_waybel_0(B_509,'#skF_2')
      | v2_struct_0(B_509)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_1765])).

tff(c_1779,plain,(
    ! [B_509] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_509))
      | ~ r1_waybel_0('#skF_2',B_509,'#skF_3')
      | ~ l1_waybel_0(B_509,'#skF_2')
      | v2_struct_0(B_509)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1773])).

tff(c_1780,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1779])).

tff(c_1784,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_1780])).

tff(c_1788,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1784])).

tff(c_1789,plain,(
    ! [B_509] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_509))
      | ~ r1_waybel_0('#skF_2',B_509,'#skF_3')
      | ~ l1_waybel_0(B_509,'#skF_2')
      | v2_struct_0(B_509) ) ),
    inference(splitRight,[status(thm)],[c_1779])).

tff(c_1790,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1779])).

tff(c_1728,plain,(
    ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_96,plain,(
    ! [D_83] :
      ( ~ r1_waybel_7('#skF_2',D_83,'#skF_4')
      | ~ r2_hidden('#skF_3',D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
      | ~ v13_waybel_0(D_83,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(D_83,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(D_83,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(D_83)
      | v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_1976,plain,(
    ! [D_570] :
      ( ~ r1_waybel_7('#skF_2',D_570,'#skF_4')
      | ~ r2_hidden('#skF_3',D_570)
      | ~ m1_subset_1(D_570,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
      | ~ v13_waybel_0(D_570,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(D_570,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(D_570,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(D_570) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1728,c_96])).

tff(c_1980,plain,(
    ! [B_5] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_5),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_5))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(k2_yellow19('#skF_2',B_5),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_yellow19('#skF_2',B_5))
      | ~ l1_waybel_0(B_5,'#skF_2')
      | v2_struct_0(B_5)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_1976])).

tff(c_1991,plain,(
    ! [B_5] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_5),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_5))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(k2_yellow19('#skF_2',B_5),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_yellow19('#skF_2',B_5))
      | ~ l1_waybel_0(B_5,'#skF_2')
      | v2_struct_0(B_5)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1790,c_1980])).

tff(c_2058,plain,(
    ! [B_596] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_596),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_596))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_596),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_596),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(k2_yellow19('#skF_2',B_596),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_yellow19('#skF_2',B_596))
      | ~ l1_waybel_0(B_596,'#skF_2')
      | v2_struct_0(B_596) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1991])).

tff(c_2062,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_2058])).

tff(c_2065,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1790,c_2062])).

tff(c_2067,plain,(
    ! [B_597] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_597),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_597))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_597),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_597),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_597))
      | ~ l1_waybel_0(B_597,'#skF_2')
      | ~ v7_waybel_0(B_597)
      | ~ v4_orders_2(B_597)
      | v2_struct_0(B_597) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2065])).

tff(c_2071,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_2067])).

tff(c_2074,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1790,c_2071])).

tff(c_2076,plain,(
    ! [B_598] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_598),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_598))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_598),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_598))
      | ~ l1_waybel_0(B_598,'#skF_2')
      | ~ v7_waybel_0(B_598)
      | ~ v4_orders_2(B_598)
      | v2_struct_0(B_598) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2074])).

tff(c_2080,plain,(
    ! [B_11] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_11),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_11))
      | v1_xboole_0(k2_yellow19('#skF_2',B_11))
      | ~ v7_waybel_0(B_11)
      | ~ v4_orders_2(B_11)
      | ~ l1_waybel_0(B_11,'#skF_2')
      | v2_struct_0(B_11)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_2076])).

tff(c_2083,plain,(
    ! [B_11] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_11),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_11))
      | v1_xboole_0(k2_yellow19('#skF_2',B_11))
      | ~ v7_waybel_0(B_11)
      | ~ v4_orders_2(B_11)
      | ~ l1_waybel_0(B_11,'#skF_2')
      | v2_struct_0(B_11)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1790,c_2080])).

tff(c_2085,plain,(
    ! [B_599] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_599),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_599))
      | v1_xboole_0(k2_yellow19('#skF_2',B_599))
      | ~ v7_waybel_0(B_599)
      | ~ v4_orders_2(B_599)
      | ~ l1_waybel_0(B_599,'#skF_2')
      | v2_struct_0(B_599) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2083])).

tff(c_2089,plain,(
    ! [B_32] :
      ( ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_32))
      | v1_xboole_0(k2_yellow19('#skF_2',B_32))
      | ~ r3_waybel_9('#skF_2',B_32,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_32,'#skF_2')
      | ~ v7_waybel_0(B_32)
      | ~ v4_orders_2(B_32)
      | v2_struct_0(B_32)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_2085])).

tff(c_2092,plain,(
    ! [B_32] :
      ( ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_32))
      | v1_xboole_0(k2_yellow19('#skF_2',B_32))
      | ~ r3_waybel_9('#skF_2',B_32,'#skF_4')
      | ~ l1_waybel_0(B_32,'#skF_2')
      | ~ v7_waybel_0(B_32)
      | ~ v4_orders_2(B_32)
      | v2_struct_0(B_32)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_2089])).

tff(c_2094,plain,(
    ! [B_600] :
      ( ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_600))
      | v1_xboole_0(k2_yellow19('#skF_2',B_600))
      | ~ r3_waybel_9('#skF_2',B_600,'#skF_4')
      | ~ l1_waybel_0(B_600,'#skF_2')
      | ~ v7_waybel_0(B_600)
      | ~ v4_orders_2(B_600)
      | v2_struct_0(B_600) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2092])).

tff(c_2099,plain,(
    ! [B_601] :
      ( v1_xboole_0(k2_yellow19('#skF_2',B_601))
      | ~ r3_waybel_9('#skF_2',B_601,'#skF_4')
      | ~ v7_waybel_0(B_601)
      | ~ v4_orders_2(B_601)
      | ~ r1_waybel_0('#skF_2',B_601,'#skF_3')
      | ~ l1_waybel_0(B_601,'#skF_2')
      | v2_struct_0(B_601) ) ),
    inference(resolution,[status(thm)],[c_1789,c_2094])).

tff(c_1791,plain,(
    ! [B_510] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_510))
      | ~ r1_waybel_0('#skF_2',B_510,'#skF_3')
      | ~ l1_waybel_0(B_510,'#skF_2')
      | v2_struct_0(B_510) ) ),
    inference(splitRight,[status(thm)],[c_1779])).

tff(c_1814,plain,(
    ! [B_510] :
      ( ~ v1_xboole_0(k2_yellow19('#skF_2',B_510))
      | ~ r1_waybel_0('#skF_2',B_510,'#skF_3')
      | ~ l1_waybel_0(B_510,'#skF_2')
      | v2_struct_0(B_510) ) ),
    inference(resolution,[status(thm)],[c_1791,c_68])).

tff(c_2112,plain,(
    ! [B_604] :
      ( ~ r3_waybel_9('#skF_2',B_604,'#skF_4')
      | ~ v7_waybel_0(B_604)
      | ~ v4_orders_2(B_604)
      | ~ r1_waybel_0('#skF_2',B_604,'#skF_3')
      | ~ l1_waybel_0(B_604,'#skF_2')
      | v2_struct_0(B_604) ) ),
    inference(resolution,[status(thm)],[c_2099,c_1814])).

tff(c_2124,plain,
    ( ~ v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | ~ l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1877,c_2112])).

tff(c_2135,plain,
    ( ~ r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1727,c_1861,c_1823,c_1854,c_2124])).

tff(c_2136,plain,(
    ~ r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1847,c_2135])).

tff(c_2139,plain,
    ( ~ r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1896,c_2136])).

tff(c_2143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1727,c_2139])).

tff(c_2144,plain,(
    r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_2318,plain,(
    ! [A_663,B_664,C_665] :
      ( r1_waybel_0(A_663,'#skF_1'(A_663,B_664,C_665),B_664)
      | ~ r2_hidden(C_665,k2_pre_topc(A_663,B_664))
      | ~ m1_subset_1(C_665,u1_struct_0(A_663))
      | ~ m1_subset_1(B_664,k1_zfmisc_1(u1_struct_0(A_663)))
      | ~ l1_pre_topc(A_663)
      | ~ v2_pre_topc(A_663)
      | v2_struct_0(A_663) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_2326,plain,(
    ! [C_665] :
      ( r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3',C_665),'#skF_3')
      | ~ r2_hidden(C_665,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_665,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_2318])).

tff(c_2332,plain,(
    ! [C_665] :
      ( r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3',C_665),'#skF_3')
      | ~ r2_hidden(C_665,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_665,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_2326])).

tff(c_2333,plain,(
    ! [C_665] :
      ( r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3',C_665),'#skF_3')
      | ~ r2_hidden(C_665,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_665,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2332])).

tff(c_2234,plain,(
    ! [A_640,B_641,C_642] :
      ( ~ v2_struct_0('#skF_1'(A_640,B_641,C_642))
      | ~ r2_hidden(C_642,k2_pre_topc(A_640,B_641))
      | ~ m1_subset_1(C_642,u1_struct_0(A_640))
      | ~ m1_subset_1(B_641,k1_zfmisc_1(u1_struct_0(A_640)))
      | ~ l1_pre_topc(A_640)
      | ~ v2_pre_topc(A_640)
      | v2_struct_0(A_640) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_2236,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2144,c_2234])).

tff(c_2239,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_2236])).

tff(c_2240,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2239])).

tff(c_2273,plain,(
    ! [A_653,B_654,C_655] :
      ( l1_waybel_0('#skF_1'(A_653,B_654,C_655),A_653)
      | ~ r2_hidden(C_655,k2_pre_topc(A_653,B_654))
      | ~ m1_subset_1(C_655,u1_struct_0(A_653))
      | ~ m1_subset_1(B_654,k1_zfmisc_1(u1_struct_0(A_653)))
      | ~ l1_pre_topc(A_653)
      | ~ v2_pre_topc(A_653)
      | v2_struct_0(A_653) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_2275,plain,
    ( l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2144,c_2273])).

tff(c_2278,plain,
    ( l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_2275])).

tff(c_2279,plain,(
    l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2278])).

tff(c_2266,plain,(
    ! [A_650,B_651,C_652] :
      ( v4_orders_2('#skF_1'(A_650,B_651,C_652))
      | ~ r2_hidden(C_652,k2_pre_topc(A_650,B_651))
      | ~ m1_subset_1(C_652,u1_struct_0(A_650))
      | ~ m1_subset_1(B_651,k1_zfmisc_1(u1_struct_0(A_650)))
      | ~ l1_pre_topc(A_650)
      | ~ v2_pre_topc(A_650)
      | v2_struct_0(A_650) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_2268,plain,
    ( v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2144,c_2266])).

tff(c_2271,plain,
    ( v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_2268])).

tff(c_2272,plain,(
    v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2271])).

tff(c_2259,plain,(
    ! [A_647,B_648,C_649] :
      ( v7_waybel_0('#skF_1'(A_647,B_648,C_649))
      | ~ r2_hidden(C_649,k2_pre_topc(A_647,B_648))
      | ~ m1_subset_1(C_649,u1_struct_0(A_647))
      | ~ m1_subset_1(B_648,k1_zfmisc_1(u1_struct_0(A_647)))
      | ~ l1_pre_topc(A_647)
      | ~ v2_pre_topc(A_647)
      | v2_struct_0(A_647) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_2261,plain,
    ( v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2144,c_2259])).

tff(c_2264,plain,
    ( v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_2261])).

tff(c_2265,plain,(
    v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2264])).

tff(c_2280,plain,(
    ! [A_656,B_657,C_658] :
      ( r3_waybel_9(A_656,'#skF_1'(A_656,B_657,C_658),C_658)
      | ~ r2_hidden(C_658,k2_pre_topc(A_656,B_657))
      | ~ m1_subset_1(C_658,u1_struct_0(A_656))
      | ~ m1_subset_1(B_657,k1_zfmisc_1(u1_struct_0(A_656)))
      | ~ l1_pre_topc(A_656)
      | ~ v2_pre_topc(A_656)
      | v2_struct_0(A_656) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_2288,plain,(
    ! [C_658] :
      ( r3_waybel_9('#skF_2','#skF_1'('#skF_2','#skF_3',C_658),C_658)
      | ~ r2_hidden(C_658,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_658,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_2280])).

tff(c_2294,plain,(
    ! [C_658] :
      ( r3_waybel_9('#skF_2','#skF_1'('#skF_2','#skF_3',C_658),C_658)
      | ~ r2_hidden(C_658,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_658,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_2288])).

tff(c_2295,plain,(
    ! [C_658] :
      ( r3_waybel_9('#skF_2','#skF_1'('#skF_2','#skF_3',C_658),C_658)
      | ~ r2_hidden(C_658,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_658,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2294])).

tff(c_2183,plain,(
    ! [C_635,A_636,B_637] :
      ( r2_hidden(C_635,k2_yellow19(A_636,B_637))
      | ~ m1_subset_1(C_635,k1_zfmisc_1(u1_struct_0(A_636)))
      | ~ r1_waybel_0(A_636,B_637,C_635)
      | ~ l1_waybel_0(B_637,A_636)
      | v2_struct_0(B_637)
      | ~ l1_struct_0(A_636)
      | v2_struct_0(A_636) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_2191,plain,(
    ! [B_637] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_637))
      | ~ r1_waybel_0('#skF_2',B_637,'#skF_3')
      | ~ l1_waybel_0(B_637,'#skF_2')
      | v2_struct_0(B_637)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_2183])).

tff(c_2197,plain,(
    ! [B_637] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_637))
      | ~ r1_waybel_0('#skF_2',B_637,'#skF_3')
      | ~ l1_waybel_0(B_637,'#skF_2')
      | v2_struct_0(B_637)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2191])).

tff(c_2199,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2197])).

tff(c_2202,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_2199])).

tff(c_2206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2202])).

tff(c_2207,plain,(
    ! [B_637] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_637))
      | ~ r1_waybel_0('#skF_2',B_637,'#skF_3')
      | ~ l1_waybel_0(B_637,'#skF_2')
      | v2_struct_0(B_637) ) ),
    inference(splitRight,[status(thm)],[c_2197])).

tff(c_2208,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2197])).

tff(c_2145,plain,(
    ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_100,plain,(
    ! [D_83] :
      ( ~ r1_waybel_7('#skF_2',D_83,'#skF_4')
      | ~ r2_hidden('#skF_3',D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
      | ~ v13_waybel_0(D_83,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(D_83,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(D_83,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(D_83)
      | v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_2297,plain,(
    ! [D_659] :
      ( ~ r1_waybel_7('#skF_2',D_659,'#skF_4')
      | ~ r2_hidden('#skF_3',D_659)
      | ~ m1_subset_1(D_659,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
      | ~ v13_waybel_0(D_659,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(D_659,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(D_659,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(D_659) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2145,c_100])).

tff(c_2301,plain,(
    ! [B_5] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_5),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_5))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(k2_yellow19('#skF_2',B_5),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_yellow19('#skF_2',B_5))
      | ~ l1_waybel_0(B_5,'#skF_2')
      | v2_struct_0(B_5)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_2297])).

tff(c_2312,plain,(
    ! [B_5] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_5),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_5))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(k2_yellow19('#skF_2',B_5),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_yellow19('#skF_2',B_5))
      | ~ l1_waybel_0(B_5,'#skF_2')
      | v2_struct_0(B_5)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2208,c_2301])).

tff(c_2474,plain,(
    ! [B_724] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_724),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_724))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_724),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_724),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(k2_yellow19('#skF_2',B_724),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_yellow19('#skF_2',B_724))
      | ~ l1_waybel_0(B_724,'#skF_2')
      | v2_struct_0(B_724) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2312])).

tff(c_2478,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_2474])).

tff(c_2481,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2208,c_2478])).

tff(c_2483,plain,(
    ! [B_725] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_725),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_725))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_725),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_725),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_725))
      | ~ l1_waybel_0(B_725,'#skF_2')
      | ~ v7_waybel_0(B_725)
      | ~ v4_orders_2(B_725)
      | v2_struct_0(B_725) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2481])).

tff(c_2487,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_2483])).

tff(c_2490,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2208,c_2487])).

tff(c_2492,plain,(
    ! [B_726] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_726),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_726))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_726),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_726))
      | ~ l1_waybel_0(B_726,'#skF_2')
      | ~ v7_waybel_0(B_726)
      | ~ v4_orders_2(B_726)
      | v2_struct_0(B_726) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2490])).

tff(c_2496,plain,(
    ! [B_11] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_11),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_11))
      | v1_xboole_0(k2_yellow19('#skF_2',B_11))
      | ~ v7_waybel_0(B_11)
      | ~ v4_orders_2(B_11)
      | ~ l1_waybel_0(B_11,'#skF_2')
      | v2_struct_0(B_11)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_2492])).

tff(c_2499,plain,(
    ! [B_11] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_11),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_11))
      | v1_xboole_0(k2_yellow19('#skF_2',B_11))
      | ~ v7_waybel_0(B_11)
      | ~ v4_orders_2(B_11)
      | ~ l1_waybel_0(B_11,'#skF_2')
      | v2_struct_0(B_11)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2208,c_2496])).

tff(c_2501,plain,(
    ! [B_727] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_727),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_727))
      | v1_xboole_0(k2_yellow19('#skF_2',B_727))
      | ~ v7_waybel_0(B_727)
      | ~ v4_orders_2(B_727)
      | ~ l1_waybel_0(B_727,'#skF_2')
      | v2_struct_0(B_727) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2499])).

tff(c_2505,plain,(
    ! [B_32] :
      ( ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_32))
      | v1_xboole_0(k2_yellow19('#skF_2',B_32))
      | ~ r3_waybel_9('#skF_2',B_32,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_32,'#skF_2')
      | ~ v7_waybel_0(B_32)
      | ~ v4_orders_2(B_32)
      | v2_struct_0(B_32)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_2501])).

tff(c_2508,plain,(
    ! [B_32] :
      ( ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_32))
      | v1_xboole_0(k2_yellow19('#skF_2',B_32))
      | ~ r3_waybel_9('#skF_2',B_32,'#skF_4')
      | ~ l1_waybel_0(B_32,'#skF_2')
      | ~ v7_waybel_0(B_32)
      | ~ v4_orders_2(B_32)
      | v2_struct_0(B_32)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_2505])).

tff(c_2510,plain,(
    ! [B_728] :
      ( ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_728))
      | v1_xboole_0(k2_yellow19('#skF_2',B_728))
      | ~ r3_waybel_9('#skF_2',B_728,'#skF_4')
      | ~ l1_waybel_0(B_728,'#skF_2')
      | ~ v7_waybel_0(B_728)
      | ~ v4_orders_2(B_728)
      | v2_struct_0(B_728) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2508])).

tff(c_2515,plain,(
    ! [B_729] :
      ( v1_xboole_0(k2_yellow19('#skF_2',B_729))
      | ~ r3_waybel_9('#skF_2',B_729,'#skF_4')
      | ~ v7_waybel_0(B_729)
      | ~ v4_orders_2(B_729)
      | ~ r1_waybel_0('#skF_2',B_729,'#skF_3')
      | ~ l1_waybel_0(B_729,'#skF_2')
      | v2_struct_0(B_729) ) ),
    inference(resolution,[status(thm)],[c_2207,c_2510])).

tff(c_2209,plain,(
    ! [B_638] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_638))
      | ~ r1_waybel_0('#skF_2',B_638,'#skF_3')
      | ~ l1_waybel_0(B_638,'#skF_2')
      | v2_struct_0(B_638) ) ),
    inference(splitRight,[status(thm)],[c_2197])).

tff(c_2232,plain,(
    ! [B_638] :
      ( ~ v1_xboole_0(k2_yellow19('#skF_2',B_638))
      | ~ r1_waybel_0('#skF_2',B_638,'#skF_3')
      | ~ l1_waybel_0(B_638,'#skF_2')
      | v2_struct_0(B_638) ) ),
    inference(resolution,[status(thm)],[c_2209,c_68])).

tff(c_2528,plain,(
    ! [B_732] :
      ( ~ r3_waybel_9('#skF_2',B_732,'#skF_4')
      | ~ v7_waybel_0(B_732)
      | ~ v4_orders_2(B_732)
      | ~ r1_waybel_0('#skF_2',B_732,'#skF_3')
      | ~ l1_waybel_0(B_732,'#skF_2')
      | v2_struct_0(B_732) ) ),
    inference(resolution,[status(thm)],[c_2515,c_2232])).

tff(c_2540,plain,
    ( ~ v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | ~ l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2295,c_2528])).

tff(c_2551,plain,
    ( ~ r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2144,c_2279,c_2272,c_2265,c_2540])).

tff(c_2552,plain,(
    ~ r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_2240,c_2551])).

tff(c_2555,plain,
    ( ~ r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2333,c_2552])).

tff(c_2559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2144,c_2555])).

tff(c_2560,plain,(
    r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_2735,plain,(
    ! [A_791,B_792,C_793] :
      ( r1_waybel_0(A_791,'#skF_1'(A_791,B_792,C_793),B_792)
      | ~ r2_hidden(C_793,k2_pre_topc(A_791,B_792))
      | ~ m1_subset_1(C_793,u1_struct_0(A_791))
      | ~ m1_subset_1(B_792,k1_zfmisc_1(u1_struct_0(A_791)))
      | ~ l1_pre_topc(A_791)
      | ~ v2_pre_topc(A_791)
      | v2_struct_0(A_791) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_2743,plain,(
    ! [C_793] :
      ( r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3',C_793),'#skF_3')
      | ~ r2_hidden(C_793,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_793,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_2735])).

tff(c_2749,plain,(
    ! [C_793] :
      ( r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3',C_793),'#skF_3')
      | ~ r2_hidden(C_793,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_793,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_2743])).

tff(c_2750,plain,(
    ! [C_793] :
      ( r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3',C_793),'#skF_3')
      | ~ r2_hidden(C_793,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_793,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2749])).

tff(c_2695,plain,(
    ! [A_776,B_777,C_778] :
      ( ~ v2_struct_0('#skF_1'(A_776,B_777,C_778))
      | ~ r2_hidden(C_778,k2_pre_topc(A_776,B_777))
      | ~ m1_subset_1(C_778,u1_struct_0(A_776))
      | ~ m1_subset_1(B_777,k1_zfmisc_1(u1_struct_0(A_776)))
      | ~ l1_pre_topc(A_776)
      | ~ v2_pre_topc(A_776)
      | v2_struct_0(A_776) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_2697,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2560,c_2695])).

tff(c_2700,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_2697])).

tff(c_2701,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2700])).

tff(c_2709,plain,(
    ! [A_782,B_783,C_784] :
      ( l1_waybel_0('#skF_1'(A_782,B_783,C_784),A_782)
      | ~ r2_hidden(C_784,k2_pre_topc(A_782,B_783))
      | ~ m1_subset_1(C_784,u1_struct_0(A_782))
      | ~ m1_subset_1(B_783,k1_zfmisc_1(u1_struct_0(A_782)))
      | ~ l1_pre_topc(A_782)
      | ~ v2_pre_topc(A_782)
      | v2_struct_0(A_782) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_2711,plain,
    ( l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2560,c_2709])).

tff(c_2714,plain,
    ( l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_2711])).

tff(c_2715,plain,(
    l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2714])).

tff(c_2626,plain,(
    ! [A_766,B_767,C_768] :
      ( v4_orders_2('#skF_1'(A_766,B_767,C_768))
      | ~ r2_hidden(C_768,k2_pre_topc(A_766,B_767))
      | ~ m1_subset_1(C_768,u1_struct_0(A_766))
      | ~ m1_subset_1(B_767,k1_zfmisc_1(u1_struct_0(A_766)))
      | ~ l1_pre_topc(A_766)
      | ~ v2_pre_topc(A_766)
      | v2_struct_0(A_766) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_2628,plain,
    ( v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2560,c_2626])).

tff(c_2631,plain,
    ( v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_2628])).

tff(c_2632,plain,(
    v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2631])).

tff(c_2702,plain,(
    ! [A_779,B_780,C_781] :
      ( v7_waybel_0('#skF_1'(A_779,B_780,C_781))
      | ~ r2_hidden(C_781,k2_pre_topc(A_779,B_780))
      | ~ m1_subset_1(C_781,u1_struct_0(A_779))
      | ~ m1_subset_1(B_780,k1_zfmisc_1(u1_struct_0(A_779)))
      | ~ l1_pre_topc(A_779)
      | ~ v2_pre_topc(A_779)
      | v2_struct_0(A_779) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_2704,plain,
    ( v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2560,c_2702])).

tff(c_2707,plain,
    ( v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_2704])).

tff(c_2708,plain,(
    v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2707])).

tff(c_2717,plain,(
    ! [A_785,B_786,C_787] :
      ( r3_waybel_9(A_785,'#skF_1'(A_785,B_786,C_787),C_787)
      | ~ r2_hidden(C_787,k2_pre_topc(A_785,B_786))
      | ~ m1_subset_1(C_787,u1_struct_0(A_785))
      | ~ m1_subset_1(B_786,k1_zfmisc_1(u1_struct_0(A_785)))
      | ~ l1_pre_topc(A_785)
      | ~ v2_pre_topc(A_785)
      | v2_struct_0(A_785) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_2725,plain,(
    ! [C_787] :
      ( r3_waybel_9('#skF_2','#skF_1'('#skF_2','#skF_3',C_787),C_787)
      | ~ r2_hidden(C_787,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_787,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_2717])).

tff(c_2731,plain,(
    ! [C_787] :
      ( r3_waybel_9('#skF_2','#skF_1'('#skF_2','#skF_3',C_787),C_787)
      | ~ r2_hidden(C_787,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_787,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_2725])).

tff(c_2732,plain,(
    ! [C_787] :
      ( r3_waybel_9('#skF_2','#skF_1'('#skF_2','#skF_3',C_787),C_787)
      | ~ r2_hidden(C_787,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_787,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2731])).

tff(c_2601,plain,(
    ! [C_763,A_764,B_765] :
      ( r2_hidden(C_763,k2_yellow19(A_764,B_765))
      | ~ m1_subset_1(C_763,k1_zfmisc_1(u1_struct_0(A_764)))
      | ~ r1_waybel_0(A_764,B_765,C_763)
      | ~ l1_waybel_0(B_765,A_764)
      | v2_struct_0(B_765)
      | ~ l1_struct_0(A_764)
      | v2_struct_0(A_764) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_2609,plain,(
    ! [B_765] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_765))
      | ~ r1_waybel_0('#skF_2',B_765,'#skF_3')
      | ~ l1_waybel_0(B_765,'#skF_2')
      | v2_struct_0(B_765)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_2601])).

tff(c_2615,plain,(
    ! [B_765] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_765))
      | ~ r1_waybel_0('#skF_2',B_765,'#skF_3')
      | ~ l1_waybel_0(B_765,'#skF_2')
      | v2_struct_0(B_765)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2609])).

tff(c_2616,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2615])).

tff(c_2619,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_2616])).

tff(c_2623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2619])).

tff(c_2624,plain,(
    ! [B_765] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_765))
      | ~ r1_waybel_0('#skF_2',B_765,'#skF_3')
      | ~ l1_waybel_0(B_765,'#skF_2')
      | v2_struct_0(B_765) ) ),
    inference(splitRight,[status(thm)],[c_2615])).

tff(c_2625,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2615])).

tff(c_2561,plain,(
    ~ r1_waybel_7('#skF_2','#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_84,plain,(
    ! [D_83] :
      ( ~ r1_waybel_7('#skF_2',D_83,'#skF_4')
      | ~ r2_hidden('#skF_3',D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
      | ~ v13_waybel_0(D_83,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(D_83,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(D_83,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(D_83)
      | r1_waybel_7('#skF_2','#skF_5','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_2659,plain,(
    ! [D_771] :
      ( ~ r1_waybel_7('#skF_2',D_771,'#skF_4')
      | ~ r2_hidden('#skF_3',D_771)
      | ~ m1_subset_1(D_771,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
      | ~ v13_waybel_0(D_771,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(D_771,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(D_771,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(D_771) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2561,c_84])).

tff(c_2663,plain,(
    ! [B_5] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_5),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_5))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(k2_yellow19('#skF_2',B_5),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_yellow19('#skF_2',B_5))
      | ~ l1_waybel_0(B_5,'#skF_2')
      | v2_struct_0(B_5)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_2659])).

tff(c_2674,plain,(
    ! [B_5] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_5),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_5))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(k2_yellow19('#skF_2',B_5),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_yellow19('#skF_2',B_5))
      | ~ l1_waybel_0(B_5,'#skF_2')
      | v2_struct_0(B_5)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2625,c_2663])).

tff(c_2891,plain,(
    ! [B_852] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_852),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_852))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_852),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_852),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(k2_yellow19('#skF_2',B_852),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_yellow19('#skF_2',B_852))
      | ~ l1_waybel_0(B_852,'#skF_2')
      | v2_struct_0(B_852) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2674])).

tff(c_2895,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_2891])).

tff(c_2898,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2625,c_2895])).

tff(c_2900,plain,(
    ! [B_853] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_853),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_853))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_853),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_853),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_853))
      | ~ l1_waybel_0(B_853,'#skF_2')
      | ~ v7_waybel_0(B_853)
      | ~ v4_orders_2(B_853)
      | v2_struct_0(B_853) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2898])).

tff(c_2904,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_2900])).

tff(c_2907,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2625,c_2904])).

tff(c_2909,plain,(
    ! [B_854] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_854),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_854))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_854),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_854))
      | ~ l1_waybel_0(B_854,'#skF_2')
      | ~ v7_waybel_0(B_854)
      | ~ v4_orders_2(B_854)
      | v2_struct_0(B_854) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2907])).

tff(c_2913,plain,(
    ! [B_11] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_11),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_11))
      | v1_xboole_0(k2_yellow19('#skF_2',B_11))
      | ~ v7_waybel_0(B_11)
      | ~ v4_orders_2(B_11)
      | ~ l1_waybel_0(B_11,'#skF_2')
      | v2_struct_0(B_11)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_2909])).

tff(c_2916,plain,(
    ! [B_11] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_11),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_11))
      | v1_xboole_0(k2_yellow19('#skF_2',B_11))
      | ~ v7_waybel_0(B_11)
      | ~ v4_orders_2(B_11)
      | ~ l1_waybel_0(B_11,'#skF_2')
      | v2_struct_0(B_11)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2625,c_2913])).

tff(c_2918,plain,(
    ! [B_855] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_855),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_855))
      | v1_xboole_0(k2_yellow19('#skF_2',B_855))
      | ~ v7_waybel_0(B_855)
      | ~ v4_orders_2(B_855)
      | ~ l1_waybel_0(B_855,'#skF_2')
      | v2_struct_0(B_855) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2916])).

tff(c_2922,plain,(
    ! [B_32] :
      ( ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_32))
      | v1_xboole_0(k2_yellow19('#skF_2',B_32))
      | ~ r3_waybel_9('#skF_2',B_32,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_32,'#skF_2')
      | ~ v7_waybel_0(B_32)
      | ~ v4_orders_2(B_32)
      | v2_struct_0(B_32)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_2918])).

tff(c_2925,plain,(
    ! [B_32] :
      ( ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_32))
      | v1_xboole_0(k2_yellow19('#skF_2',B_32))
      | ~ r3_waybel_9('#skF_2',B_32,'#skF_4')
      | ~ l1_waybel_0(B_32,'#skF_2')
      | ~ v7_waybel_0(B_32)
      | ~ v4_orders_2(B_32)
      | v2_struct_0(B_32)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_2922])).

tff(c_2928,plain,(
    ! [B_858] :
      ( ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_858))
      | v1_xboole_0(k2_yellow19('#skF_2',B_858))
      | ~ r3_waybel_9('#skF_2',B_858,'#skF_4')
      | ~ l1_waybel_0(B_858,'#skF_2')
      | ~ v7_waybel_0(B_858)
      | ~ v4_orders_2(B_858)
      | v2_struct_0(B_858) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2925])).

tff(c_2933,plain,(
    ! [B_859] :
      ( v1_xboole_0(k2_yellow19('#skF_2',B_859))
      | ~ r3_waybel_9('#skF_2',B_859,'#skF_4')
      | ~ v7_waybel_0(B_859)
      | ~ v4_orders_2(B_859)
      | ~ r1_waybel_0('#skF_2',B_859,'#skF_3')
      | ~ l1_waybel_0(B_859,'#skF_2')
      | v2_struct_0(B_859) ) ),
    inference(resolution,[status(thm)],[c_2624,c_2928])).

tff(c_2633,plain,(
    ! [B_769] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_769))
      | ~ r1_waybel_0('#skF_2',B_769,'#skF_3')
      | ~ l1_waybel_0(B_769,'#skF_2')
      | v2_struct_0(B_769) ) ),
    inference(splitRight,[status(thm)],[c_2615])).

tff(c_2656,plain,(
    ! [B_769] :
      ( ~ v1_xboole_0(k2_yellow19('#skF_2',B_769))
      | ~ r1_waybel_0('#skF_2',B_769,'#skF_3')
      | ~ l1_waybel_0(B_769,'#skF_2')
      | v2_struct_0(B_769) ) ),
    inference(resolution,[status(thm)],[c_2633,c_68])).

tff(c_2945,plain,(
    ! [B_860] :
      ( ~ r3_waybel_9('#skF_2',B_860,'#skF_4')
      | ~ v7_waybel_0(B_860)
      | ~ v4_orders_2(B_860)
      | ~ r1_waybel_0('#skF_2',B_860,'#skF_3')
      | ~ l1_waybel_0(B_860,'#skF_2')
      | v2_struct_0(B_860) ) ),
    inference(resolution,[status(thm)],[c_2933,c_2656])).

tff(c_2957,plain,
    ( ~ v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | ~ l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2732,c_2945])).

tff(c_2968,plain,
    ( ~ r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2560,c_2715,c_2632,c_2708,c_2957])).

tff(c_2969,plain,(
    ~ r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_2701,c_2968])).

tff(c_2972,plain,
    ( ~ r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2750,c_2969])).

tff(c_2976,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2560,c_2972])).

tff(c_2977,plain,(
    r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_3153,plain,(
    ! [A_921,B_922,C_923] :
      ( r1_waybel_0(A_921,'#skF_1'(A_921,B_922,C_923),B_922)
      | ~ r2_hidden(C_923,k2_pre_topc(A_921,B_922))
      | ~ m1_subset_1(C_923,u1_struct_0(A_921))
      | ~ m1_subset_1(B_922,k1_zfmisc_1(u1_struct_0(A_921)))
      | ~ l1_pre_topc(A_921)
      | ~ v2_pre_topc(A_921)
      | v2_struct_0(A_921) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_3161,plain,(
    ! [C_923] :
      ( r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3',C_923),'#skF_3')
      | ~ r2_hidden(C_923,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_923,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_3153])).

tff(c_3167,plain,(
    ! [C_923] :
      ( r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3',C_923),'#skF_3')
      | ~ r2_hidden(C_923,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_923,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_3161])).

tff(c_3168,plain,(
    ! [C_923] :
      ( r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3',C_923),'#skF_3')
      | ~ r2_hidden(C_923,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_923,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3167])).

tff(c_3106,plain,(
    ! [A_901,B_902,C_903] :
      ( ~ v2_struct_0('#skF_1'(A_901,B_902,C_903))
      | ~ r2_hidden(C_903,k2_pre_topc(A_901,B_902))
      | ~ m1_subset_1(C_903,u1_struct_0(A_901))
      | ~ m1_subset_1(B_902,k1_zfmisc_1(u1_struct_0(A_901)))
      | ~ l1_pre_topc(A_901)
      | ~ v2_pre_topc(A_901)
      | v2_struct_0(A_901) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_3108,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2977,c_3106])).

tff(c_3111,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_3108])).

tff(c_3112,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3111])).

tff(c_3128,plain,(
    ! [A_912,B_913,C_914] :
      ( l1_waybel_0('#skF_1'(A_912,B_913,C_914),A_912)
      | ~ r2_hidden(C_914,k2_pre_topc(A_912,B_913))
      | ~ m1_subset_1(C_914,u1_struct_0(A_912))
      | ~ m1_subset_1(B_913,k1_zfmisc_1(u1_struct_0(A_912)))
      | ~ l1_pre_topc(A_912)
      | ~ v2_pre_topc(A_912)
      | v2_struct_0(A_912) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_3130,plain,
    ( l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2977,c_3128])).

tff(c_3133,plain,
    ( l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_3130])).

tff(c_3134,plain,(
    l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3133])).

tff(c_3121,plain,(
    ! [A_909,B_910,C_911] :
      ( v4_orders_2('#skF_1'(A_909,B_910,C_911))
      | ~ r2_hidden(C_911,k2_pre_topc(A_909,B_910))
      | ~ m1_subset_1(C_911,u1_struct_0(A_909))
      | ~ m1_subset_1(B_910,k1_zfmisc_1(u1_struct_0(A_909)))
      | ~ l1_pre_topc(A_909)
      | ~ v2_pre_topc(A_909)
      | v2_struct_0(A_909) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_3123,plain,
    ( v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2977,c_3121])).

tff(c_3126,plain,
    ( v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_3123])).

tff(c_3127,plain,(
    v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3126])).

tff(c_3114,plain,(
    ! [A_906,B_907,C_908] :
      ( v7_waybel_0('#skF_1'(A_906,B_907,C_908))
      | ~ r2_hidden(C_908,k2_pre_topc(A_906,B_907))
      | ~ m1_subset_1(C_908,u1_struct_0(A_906))
      | ~ m1_subset_1(B_907,k1_zfmisc_1(u1_struct_0(A_906)))
      | ~ l1_pre_topc(A_906)
      | ~ v2_pre_topc(A_906)
      | v2_struct_0(A_906) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_3116,plain,
    ( v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2977,c_3114])).

tff(c_3119,plain,
    ( v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_3116])).

tff(c_3120,plain,(
    v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3119])).

tff(c_3135,plain,(
    ! [A_915,B_916,C_917] :
      ( r3_waybel_9(A_915,'#skF_1'(A_915,B_916,C_917),C_917)
      | ~ r2_hidden(C_917,k2_pre_topc(A_915,B_916))
      | ~ m1_subset_1(C_917,u1_struct_0(A_915))
      | ~ m1_subset_1(B_916,k1_zfmisc_1(u1_struct_0(A_915)))
      | ~ l1_pre_topc(A_915)
      | ~ v2_pre_topc(A_915)
      | v2_struct_0(A_915) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_3143,plain,(
    ! [C_917] :
      ( r3_waybel_9('#skF_2','#skF_1'('#skF_2','#skF_3',C_917),C_917)
      | ~ r2_hidden(C_917,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_917,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_3135])).

tff(c_3149,plain,(
    ! [C_917] :
      ( r3_waybel_9('#skF_2','#skF_1'('#skF_2','#skF_3',C_917),C_917)
      | ~ r2_hidden(C_917,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_917,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_3143])).

tff(c_3150,plain,(
    ! [C_917] :
      ( r3_waybel_9('#skF_2','#skF_1'('#skF_2','#skF_3',C_917),C_917)
      | ~ r2_hidden(C_917,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_917,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3149])).

tff(c_3020,plain,(
    ! [C_893,A_894,B_895] :
      ( r2_hidden(C_893,k2_yellow19(A_894,B_895))
      | ~ m1_subset_1(C_893,k1_zfmisc_1(u1_struct_0(A_894)))
      | ~ r1_waybel_0(A_894,B_895,C_893)
      | ~ l1_waybel_0(B_895,A_894)
      | v2_struct_0(B_895)
      | ~ l1_struct_0(A_894)
      | v2_struct_0(A_894) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_3028,plain,(
    ! [B_895] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_895))
      | ~ r1_waybel_0('#skF_2',B_895,'#skF_3')
      | ~ l1_waybel_0(B_895,'#skF_2')
      | v2_struct_0(B_895)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_3020])).

tff(c_3034,plain,(
    ! [B_895] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_895))
      | ~ r1_waybel_0('#skF_2',B_895,'#skF_3')
      | ~ l1_waybel_0(B_895,'#skF_2')
      | v2_struct_0(B_895)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3028])).

tff(c_3035,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3034])).

tff(c_3038,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_3035])).

tff(c_3042,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3038])).

tff(c_3043,plain,(
    ! [B_895] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_895))
      | ~ r1_waybel_0('#skF_2',B_895,'#skF_3')
      | ~ l1_waybel_0(B_895,'#skF_2')
      | v2_struct_0(B_895) ) ),
    inference(splitRight,[status(thm)],[c_3034])).

tff(c_3044,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3034])).

tff(c_2978,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_88,plain,(
    ! [D_83] :
      ( ~ r1_waybel_7('#skF_2',D_83,'#skF_4')
      | ~ r2_hidden('#skF_3',D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
      | ~ v13_waybel_0(D_83,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(D_83,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(D_83,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(D_83)
      | r2_hidden('#skF_3','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_3046,plain,(
    ! [D_896] :
      ( ~ r1_waybel_7('#skF_2',D_896,'#skF_4')
      | ~ r2_hidden('#skF_3',D_896)
      | ~ m1_subset_1(D_896,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
      | ~ v13_waybel_0(D_896,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(D_896,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(D_896,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(D_896) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2978,c_88])).

tff(c_3050,plain,(
    ! [B_5] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_5),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_5))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(k2_yellow19('#skF_2',B_5),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_yellow19('#skF_2',B_5))
      | ~ l1_waybel_0(B_5,'#skF_2')
      | v2_struct_0(B_5)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_3046])).

tff(c_3061,plain,(
    ! [B_5] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_5),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_5))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_5),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(k2_yellow19('#skF_2',B_5),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_yellow19('#skF_2',B_5))
      | ~ l1_waybel_0(B_5,'#skF_2')
      | v2_struct_0(B_5)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3044,c_3050])).

tff(c_3309,plain,(
    ! [B_982] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_982),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_982))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_982),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_982),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(k2_yellow19('#skF_2',B_982),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_yellow19('#skF_2',B_982))
      | ~ l1_waybel_0(B_982,'#skF_2')
      | v2_struct_0(B_982) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3061])).

tff(c_3313,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_3309])).

tff(c_3316,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3044,c_3313])).

tff(c_3318,plain,(
    ! [B_983] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_983),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_983))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_983),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_983),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_983))
      | ~ l1_waybel_0(B_983,'#skF_2')
      | ~ v7_waybel_0(B_983)
      | ~ v4_orders_2(B_983)
      | v2_struct_0(B_983) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3316])).

tff(c_3322,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_3318])).

tff(c_3325,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3044,c_3322])).

tff(c_3327,plain,(
    ! [B_984] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_984),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_984))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_984),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_984))
      | ~ l1_waybel_0(B_984,'#skF_2')
      | ~ v7_waybel_0(B_984)
      | ~ v4_orders_2(B_984)
      | v2_struct_0(B_984) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3325])).

tff(c_3331,plain,(
    ! [B_11] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_11),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_11))
      | v1_xboole_0(k2_yellow19('#skF_2',B_11))
      | ~ v7_waybel_0(B_11)
      | ~ v4_orders_2(B_11)
      | ~ l1_waybel_0(B_11,'#skF_2')
      | v2_struct_0(B_11)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_3327])).

tff(c_3334,plain,(
    ! [B_11] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_11),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_11))
      | v1_xboole_0(k2_yellow19('#skF_2',B_11))
      | ~ v7_waybel_0(B_11)
      | ~ v4_orders_2(B_11)
      | ~ l1_waybel_0(B_11,'#skF_2')
      | v2_struct_0(B_11)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3044,c_3331])).

tff(c_3336,plain,(
    ! [B_985] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_985),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_985))
      | v1_xboole_0(k2_yellow19('#skF_2',B_985))
      | ~ v7_waybel_0(B_985)
      | ~ v4_orders_2(B_985)
      | ~ l1_waybel_0(B_985,'#skF_2')
      | v2_struct_0(B_985) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3334])).

tff(c_3340,plain,(
    ! [B_32] :
      ( ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_32))
      | v1_xboole_0(k2_yellow19('#skF_2',B_32))
      | ~ r3_waybel_9('#skF_2',B_32,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_32,'#skF_2')
      | ~ v7_waybel_0(B_32)
      | ~ v4_orders_2(B_32)
      | v2_struct_0(B_32)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_3336])).

tff(c_3343,plain,(
    ! [B_32] :
      ( ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_32))
      | v1_xboole_0(k2_yellow19('#skF_2',B_32))
      | ~ r3_waybel_9('#skF_2',B_32,'#skF_4')
      | ~ l1_waybel_0(B_32,'#skF_2')
      | ~ v7_waybel_0(B_32)
      | ~ v4_orders_2(B_32)
      | v2_struct_0(B_32)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_3340])).

tff(c_3345,plain,(
    ! [B_986] :
      ( ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_986))
      | v1_xboole_0(k2_yellow19('#skF_2',B_986))
      | ~ r3_waybel_9('#skF_2',B_986,'#skF_4')
      | ~ l1_waybel_0(B_986,'#skF_2')
      | ~ v7_waybel_0(B_986)
      | ~ v4_orders_2(B_986)
      | v2_struct_0(B_986) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3343])).

tff(c_3350,plain,(
    ! [B_987] :
      ( v1_xboole_0(k2_yellow19('#skF_2',B_987))
      | ~ r3_waybel_9('#skF_2',B_987,'#skF_4')
      | ~ v7_waybel_0(B_987)
      | ~ v4_orders_2(B_987)
      | ~ r1_waybel_0('#skF_2',B_987,'#skF_3')
      | ~ l1_waybel_0(B_987,'#skF_2')
      | v2_struct_0(B_987) ) ),
    inference(resolution,[status(thm)],[c_3043,c_3345])).

tff(c_3065,plain,(
    ! [B_897] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_897))
      | ~ r1_waybel_0('#skF_2',B_897,'#skF_3')
      | ~ l1_waybel_0(B_897,'#skF_2')
      | v2_struct_0(B_897) ) ),
    inference(splitRight,[status(thm)],[c_3034])).

tff(c_3088,plain,(
    ! [B_897] :
      ( ~ v1_xboole_0(k2_yellow19('#skF_2',B_897))
      | ~ r1_waybel_0('#skF_2',B_897,'#skF_3')
      | ~ l1_waybel_0(B_897,'#skF_2')
      | v2_struct_0(B_897) ) ),
    inference(resolution,[status(thm)],[c_3065,c_68])).

tff(c_3362,plain,(
    ! [B_988] :
      ( ~ r3_waybel_9('#skF_2',B_988,'#skF_4')
      | ~ v7_waybel_0(B_988)
      | ~ v4_orders_2(B_988)
      | ~ r1_waybel_0('#skF_2',B_988,'#skF_3')
      | ~ l1_waybel_0(B_988,'#skF_2')
      | v2_struct_0(B_988) ) ),
    inference(resolution,[status(thm)],[c_3350,c_3088])).

tff(c_3374,plain,
    ( ~ v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | ~ l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3150,c_3362])).

tff(c_3385,plain,
    ( ~ r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2977,c_3134,c_3127,c_3120,c_3374])).

tff(c_3386,plain,(
    ~ r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_3112,c_3385])).

tff(c_3389,plain,
    ( ~ r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3168,c_3386])).

tff(c_3393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2977,c_3389])).

tff(c_3394,plain,(
    r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_3553,plain,(
    ! [A_1043,B_1044,C_1045] :
      ( r1_waybel_0(A_1043,'#skF_1'(A_1043,B_1044,C_1045),B_1044)
      | ~ r2_hidden(C_1045,k2_pre_topc(A_1043,B_1044))
      | ~ m1_subset_1(C_1045,u1_struct_0(A_1043))
      | ~ m1_subset_1(B_1044,k1_zfmisc_1(u1_struct_0(A_1043)))
      | ~ l1_pre_topc(A_1043)
      | ~ v2_pre_topc(A_1043)
      | v2_struct_0(A_1043) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_3561,plain,(
    ! [C_1045] :
      ( r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3',C_1045),'#skF_3')
      | ~ r2_hidden(C_1045,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_1045,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_3553])).

tff(c_3567,plain,(
    ! [C_1045] :
      ( r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3',C_1045),'#skF_3')
      | ~ r2_hidden(C_1045,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_1045,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_3561])).

tff(c_3568,plain,(
    ! [C_1045] :
      ( r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3',C_1045),'#skF_3')
      | ~ r2_hidden(C_1045,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_1045,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3567])).

tff(c_3507,plain,(
    ! [A_1026,B_1027,C_1028] :
      ( ~ v2_struct_0('#skF_1'(A_1026,B_1027,C_1028))
      | ~ r2_hidden(C_1028,k2_pre_topc(A_1026,B_1027))
      | ~ m1_subset_1(C_1028,u1_struct_0(A_1026))
      | ~ m1_subset_1(B_1027,k1_zfmisc_1(u1_struct_0(A_1026)))
      | ~ l1_pre_topc(A_1026)
      | ~ v2_pre_topc(A_1026)
      | v2_struct_0(A_1026) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_3509,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_3394,c_3507])).

tff(c_3512,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_3509])).

tff(c_3513,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3512])).

tff(c_3546,plain,(
    ! [A_1040,B_1041,C_1042] :
      ( l1_waybel_0('#skF_1'(A_1040,B_1041,C_1042),A_1040)
      | ~ r2_hidden(C_1042,k2_pre_topc(A_1040,B_1041))
      | ~ m1_subset_1(C_1042,u1_struct_0(A_1040))
      | ~ m1_subset_1(B_1041,k1_zfmisc_1(u1_struct_0(A_1040)))
      | ~ l1_pre_topc(A_1040)
      | ~ v2_pre_topc(A_1040)
      | v2_struct_0(A_1040) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_3548,plain,
    ( l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_3394,c_3546])).

tff(c_3551,plain,
    ( l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_3548])).

tff(c_3552,plain,(
    l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3551])).

tff(c_3539,plain,(
    ! [A_1037,B_1038,C_1039] :
      ( v4_orders_2('#skF_1'(A_1037,B_1038,C_1039))
      | ~ r2_hidden(C_1039,k2_pre_topc(A_1037,B_1038))
      | ~ m1_subset_1(C_1039,u1_struct_0(A_1037))
      | ~ m1_subset_1(B_1038,k1_zfmisc_1(u1_struct_0(A_1037)))
      | ~ l1_pre_topc(A_1037)
      | ~ v2_pre_topc(A_1037)
      | v2_struct_0(A_1037) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_3541,plain,
    ( v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_3394,c_3539])).

tff(c_3544,plain,
    ( v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_3541])).

tff(c_3545,plain,(
    v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3544])).

tff(c_3532,plain,(
    ! [A_1034,B_1035,C_1036] :
      ( v7_waybel_0('#skF_1'(A_1034,B_1035,C_1036))
      | ~ r2_hidden(C_1036,k2_pre_topc(A_1034,B_1035))
      | ~ m1_subset_1(C_1036,u1_struct_0(A_1034))
      | ~ m1_subset_1(B_1035,k1_zfmisc_1(u1_struct_0(A_1034)))
      | ~ l1_pre_topc(A_1034)
      | ~ v2_pre_topc(A_1034)
      | v2_struct_0(A_1034) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_3534,plain,
    ( v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_3394,c_3532])).

tff(c_3537,plain,
    ( v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_3534])).

tff(c_3538,plain,(
    v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3537])).

tff(c_3570,plain,(
    ! [A_1047,B_1048,C_1049] :
      ( r3_waybel_9(A_1047,'#skF_1'(A_1047,B_1048,C_1049),C_1049)
      | ~ r2_hidden(C_1049,k2_pre_topc(A_1047,B_1048))
      | ~ m1_subset_1(C_1049,u1_struct_0(A_1047))
      | ~ m1_subset_1(B_1048,k1_zfmisc_1(u1_struct_0(A_1047)))
      | ~ l1_pre_topc(A_1047)
      | ~ v2_pre_topc(A_1047)
      | v2_struct_0(A_1047) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_3578,plain,(
    ! [C_1049] :
      ( r3_waybel_9('#skF_2','#skF_1'('#skF_2','#skF_3',C_1049),C_1049)
      | ~ r2_hidden(C_1049,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_1049,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_3570])).

tff(c_3584,plain,(
    ! [C_1049] :
      ( r3_waybel_9('#skF_2','#skF_1'('#skF_2','#skF_3',C_1049),C_1049)
      | ~ r2_hidden(C_1049,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_1049,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_3578])).

tff(c_3585,plain,(
    ! [C_1049] :
      ( r3_waybel_9('#skF_2','#skF_1'('#skF_2','#skF_3',C_1049),C_1049)
      | ~ r2_hidden(C_1049,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_1049,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3584])).

tff(c_3458,plain,(
    ! [C_1022,A_1023,B_1024] :
      ( r2_hidden(C_1022,k2_yellow19(A_1023,B_1024))
      | ~ m1_subset_1(C_1022,k1_zfmisc_1(u1_struct_0(A_1023)))
      | ~ r1_waybel_0(A_1023,B_1024,C_1022)
      | ~ l1_waybel_0(B_1024,A_1023)
      | v2_struct_0(B_1024)
      | ~ l1_struct_0(A_1023)
      | v2_struct_0(A_1023) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_3466,plain,(
    ! [B_1024] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_1024))
      | ~ r1_waybel_0('#skF_2',B_1024,'#skF_3')
      | ~ l1_waybel_0(B_1024,'#skF_2')
      | v2_struct_0(B_1024)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_3458])).

tff(c_3472,plain,(
    ! [B_1024] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_1024))
      | ~ r1_waybel_0('#skF_2',B_1024,'#skF_3')
      | ~ l1_waybel_0(B_1024,'#skF_2')
      | v2_struct_0(B_1024)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3466])).

tff(c_3473,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3472])).

tff(c_3476,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_3473])).

tff(c_3480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3476])).

tff(c_3481,plain,(
    ! [B_1024] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_1024))
      | ~ r1_waybel_0('#skF_2',B_1024,'#skF_3')
      | ~ l1_waybel_0(B_1024,'#skF_2')
      | v2_struct_0(B_1024) ) ),
    inference(splitRight,[status(thm)],[c_3472])).

tff(c_3482,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3472])).

tff(c_3442,plain,(
    ! [A_1007,B_1008] :
      ( m1_subset_1(k2_yellow19(A_1007,B_1008),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_1007)))))
      | ~ l1_waybel_0(B_1008,A_1007)
      | v2_struct_0(B_1008)
      | ~ l1_struct_0(A_1007)
      | v2_struct_0(A_1007) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3395,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_108,plain,(
    ! [D_83] :
      ( ~ r1_waybel_7('#skF_2',D_83,'#skF_4')
      | ~ r2_hidden('#skF_3',D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
      | ~ v13_waybel_0(D_83,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(D_83,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(D_83,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(D_83)
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_3419,plain,(
    ! [D_83] :
      ( ~ r1_waybel_7('#skF_2',D_83,'#skF_4')
      | ~ r2_hidden('#skF_3',D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
      | ~ v13_waybel_0(D_83,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(D_83,k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(D_83,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(D_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3395,c_108])).

tff(c_3446,plain,(
    ! [B_1008] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_1008),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_1008))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_1008),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_1008),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(k2_yellow19('#skF_2',B_1008),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_yellow19('#skF_2',B_1008))
      | ~ l1_waybel_0(B_1008,'#skF_2')
      | v2_struct_0(B_1008)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3442,c_3419])).

tff(c_3451,plain,(
    ! [B_1008] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_1008),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_1008))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_1008),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_1008),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(k2_yellow19('#skF_2',B_1008),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_yellow19('#skF_2',B_1008))
      | ~ l1_waybel_0(B_1008,'#skF_2')
      | v2_struct_0(B_1008)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3446])).

tff(c_3714,plain,(
    ! [B_1107] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_1107),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_1107))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_1107),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_1107),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1(k2_yellow19('#skF_2',B_1107),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0(k2_yellow19('#skF_2',B_1107))
      | ~ l1_waybel_0(B_1107,'#skF_2')
      | v2_struct_0(B_1107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3482,c_3451])).

tff(c_3718,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_3714])).

tff(c_3721,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3482,c_3718])).

tff(c_3723,plain,(
    ! [B_1108] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_1108),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_1108))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_1108),k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0(k2_yellow19('#skF_2',B_1108),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_1108))
      | ~ l1_waybel_0(B_1108,'#skF_2')
      | ~ v7_waybel_0(B_1108)
      | ~ v4_orders_2(B_1108)
      | v2_struct_0(B_1108) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3721])).

tff(c_3727,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_3723])).

tff(c_3730,plain,(
    ! [B_13] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_13),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_13))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_13),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_13))
      | ~ l1_waybel_0(B_13,'#skF_2')
      | ~ v7_waybel_0(B_13)
      | ~ v4_orders_2(B_13)
      | v2_struct_0(B_13)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3482,c_3727])).

tff(c_3732,plain,(
    ! [B_1109] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_1109),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_1109))
      | ~ v13_waybel_0(k2_yellow19('#skF_2',B_1109),k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0(k2_yellow19('#skF_2',B_1109))
      | ~ l1_waybel_0(B_1109,'#skF_2')
      | ~ v7_waybel_0(B_1109)
      | ~ v4_orders_2(B_1109)
      | v2_struct_0(B_1109) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3730])).

tff(c_3736,plain,(
    ! [B_11] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_11),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_11))
      | v1_xboole_0(k2_yellow19('#skF_2',B_11))
      | ~ v7_waybel_0(B_11)
      | ~ v4_orders_2(B_11)
      | ~ l1_waybel_0(B_11,'#skF_2')
      | v2_struct_0(B_11)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_3732])).

tff(c_3739,plain,(
    ! [B_11] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_11),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_11))
      | v1_xboole_0(k2_yellow19('#skF_2',B_11))
      | ~ v7_waybel_0(B_11)
      | ~ v4_orders_2(B_11)
      | ~ l1_waybel_0(B_11,'#skF_2')
      | v2_struct_0(B_11)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3482,c_3736])).

tff(c_3741,plain,(
    ! [B_1110] :
      ( ~ r1_waybel_7('#skF_2',k2_yellow19('#skF_2',B_1110),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_1110))
      | v1_xboole_0(k2_yellow19('#skF_2',B_1110))
      | ~ v7_waybel_0(B_1110)
      | ~ v4_orders_2(B_1110)
      | ~ l1_waybel_0(B_1110,'#skF_2')
      | v2_struct_0(B_1110) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3739])).

tff(c_3745,plain,(
    ! [B_32] :
      ( ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_32))
      | v1_xboole_0(k2_yellow19('#skF_2',B_32))
      | ~ r3_waybel_9('#skF_2',B_32,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_32,'#skF_2')
      | ~ v7_waybel_0(B_32)
      | ~ v4_orders_2(B_32)
      | v2_struct_0(B_32)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_3741])).

tff(c_3748,plain,(
    ! [B_32] :
      ( ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_32))
      | v1_xboole_0(k2_yellow19('#skF_2',B_32))
      | ~ r3_waybel_9('#skF_2',B_32,'#skF_4')
      | ~ l1_waybel_0(B_32,'#skF_2')
      | ~ v7_waybel_0(B_32)
      | ~ v4_orders_2(B_32)
      | v2_struct_0(B_32)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_3745])).

tff(c_3750,plain,(
    ! [B_1111] :
      ( ~ r2_hidden('#skF_3',k2_yellow19('#skF_2',B_1111))
      | v1_xboole_0(k2_yellow19('#skF_2',B_1111))
      | ~ r3_waybel_9('#skF_2',B_1111,'#skF_4')
      | ~ l1_waybel_0(B_1111,'#skF_2')
      | ~ v7_waybel_0(B_1111)
      | ~ v4_orders_2(B_1111)
      | v2_struct_0(B_1111) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3748])).

tff(c_3755,plain,(
    ! [B_1112] :
      ( v1_xboole_0(k2_yellow19('#skF_2',B_1112))
      | ~ r3_waybel_9('#skF_2',B_1112,'#skF_4')
      | ~ v7_waybel_0(B_1112)
      | ~ v4_orders_2(B_1112)
      | ~ r1_waybel_0('#skF_2',B_1112,'#skF_3')
      | ~ l1_waybel_0(B_1112,'#skF_2')
      | v2_struct_0(B_1112) ) ),
    inference(resolution,[status(thm)],[c_3481,c_3750])).

tff(c_3483,plain,(
    ! [B_1025] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_2',B_1025))
      | ~ r1_waybel_0('#skF_2',B_1025,'#skF_3')
      | ~ l1_waybel_0(B_1025,'#skF_2')
      | v2_struct_0(B_1025) ) ),
    inference(splitRight,[status(thm)],[c_3472])).

tff(c_3506,plain,(
    ! [B_1025] :
      ( ~ v1_xboole_0(k2_yellow19('#skF_2',B_1025))
      | ~ r1_waybel_0('#skF_2',B_1025,'#skF_3')
      | ~ l1_waybel_0(B_1025,'#skF_2')
      | v2_struct_0(B_1025) ) ),
    inference(resolution,[status(thm)],[c_3483,c_68])).

tff(c_3782,plain,(
    ! [B_1116] :
      ( ~ r3_waybel_9('#skF_2',B_1116,'#skF_4')
      | ~ v7_waybel_0(B_1116)
      | ~ v4_orders_2(B_1116)
      | ~ r1_waybel_0('#skF_2',B_1116,'#skF_3')
      | ~ l1_waybel_0(B_1116,'#skF_2')
      | v2_struct_0(B_1116) ) ),
    inference(resolution,[status(thm)],[c_3755,c_3506])).

tff(c_3794,plain,
    ( ~ v7_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ v4_orders_2('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | ~ l1_waybel_0('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3585,c_3782])).

tff(c_3805,plain,
    ( ~ r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3394,c_3552,c_3545,c_3538,c_3794])).

tff(c_3806,plain,(
    ~ r1_waybel_0('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_3513,c_3805])).

tff(c_3809,plain,
    ( ~ r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3568,c_3806])).

tff(c_3813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3394,c_3809])).

%------------------------------------------------------------------------------
