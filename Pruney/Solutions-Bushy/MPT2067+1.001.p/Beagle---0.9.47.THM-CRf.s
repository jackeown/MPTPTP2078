%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2067+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:50 EST 2020

% Result     : Theorem 8.18s
% Output     : CNFRefutation 8.79s
% Verified   : 
% Statistics : Number of formulae       :  710 (9833 expanded)
%              Number of leaves         :   53 (3437 expanded)
%              Depth                    :   30
%              Number of atoms          : 2509 (58244 expanded)
%              Number of equality atoms :   41 ( 456 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_7 > r1_waybel_0 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k2_pre_topc > a_2_1_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(a_2_1_yellow19,type,(
    a_2_1_yellow19: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_331,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow19)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_217,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_yellow19)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_144,axiom,(
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

tff(f_152,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

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

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => k2_yellow19(A,B) = a_2_1_yellow19(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_yellow19)).

tff(f_260,axiom,(
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

tff(f_264,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_299,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_199,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & l1_struct_0(B)
        & ~ v2_struct_0(C)
        & l1_waybel_0(C,B) )
     => ( r2_hidden(A,a_2_1_yellow19(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
            & A = D
            & r1_waybel_0(B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_yellow19)).

tff(f_116,axiom,(
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

tff(f_180,axiom,(
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

tff(f_241,axiom,(
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

tff(f_293,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow19)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A) )
     => ( ~ v1_xboole_0(k2_yellow19(A,B))
        & v13_waybel_0(k2_yellow19(A,B),k3_yellow_1(k2_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_yellow19)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A) )
     => m1_subset_1(k2_yellow19(A,B),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow19)).

tff(c_78,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_118,plain,
    ( r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_121,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_114,plain,
    ( r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_137,plain,(
    v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_110,plain,
    ( r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_136,plain,(
    v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_106,plain,
    ( r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_135,plain,(
    v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_98,plain,
    ( r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_122,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_94,plain,
    ( r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | r1_waybel_7('#skF_3','#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_134,plain,(
    r1_waybel_7('#skF_3','#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_102,plain,
    ( r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_138,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_82,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_14,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_165,plain,(
    ! [C_127,A_128,B_129] :
      ( r2_hidden(C_127,k2_yellow19(A_128,B_129))
      | ~ m1_subset_1(C_127,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ r1_waybel_0(A_128,B_129,C_127)
      | ~ l1_waybel_0(B_129,A_128)
      | v2_struct_0(B_129)
      | ~ l1_struct_0(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_175,plain,(
    ! [B_129] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_129))
      | ~ r1_waybel_0('#skF_3',B_129,'#skF_4')
      | ~ l1_waybel_0(B_129,'#skF_3')
      | v2_struct_0(B_129)
      | ~ l1_struct_0('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_165])).

tff(c_182,plain,(
    ! [B_129] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_129))
      | ~ r1_waybel_0('#skF_3',B_129,'#skF_4')
      | ~ l1_waybel_0(B_129,'#skF_3')
      | v2_struct_0(B_129)
      | ~ l1_struct_0('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_175])).

tff(c_184,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_187,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_184])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_187])).

tff(c_193,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_4,plain,(
    ! [A_4] :
      ( m1_subset_1(k2_struct_0(A_4),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_482,plain,(
    ! [A_208,B_209,C_210] :
      ( v4_orders_2(k3_yellow19(A_208,B_209,C_210))
      | ~ m1_subset_1(C_210,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_209))))
      | ~ v13_waybel_0(C_210,k3_yellow_1(B_209))
      | ~ v2_waybel_0(C_210,k3_yellow_1(B_209))
      | v1_xboole_0(C_210)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0(A_208)))
      | v1_xboole_0(B_209)
      | ~ l1_struct_0(A_208)
      | v2_struct_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_489,plain,(
    ! [A_208] :
      ( v4_orders_2(k3_yellow19(A_208,k2_struct_0('#skF_3'),'#skF_6'))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_208)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_208)
      | v2_struct_0(A_208) ) ),
    inference(resolution,[status(thm)],[c_138,c_482])).

tff(c_497,plain,(
    ! [A_208] :
      ( v4_orders_2(k3_yellow19(A_208,k2_struct_0('#skF_3'),'#skF_6'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_208)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_208)
      | v2_struct_0(A_208) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_135,c_489])).

tff(c_498,plain,(
    ! [A_208] :
      ( v4_orders_2(k3_yellow19(A_208,k2_struct_0('#skF_3'),'#skF_6'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_208)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_208)
      | v2_struct_0(A_208) ) ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_497])).

tff(c_500,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_498])).

tff(c_32,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(k2_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_503,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_500,c_32])).

tff(c_506,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_503])).

tff(c_508,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_506])).

tff(c_510,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_498])).

tff(c_549,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_556,plain,(
    ! [A_216] :
      ( l1_waybel_0(k3_yellow19(A_216,k2_struct_0('#skF_3'),'#skF_6'),A_216)
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_216)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_216)
      | v2_struct_0(A_216) ) ),
    inference(resolution,[status(thm)],[c_138,c_549])).

tff(c_564,plain,(
    ! [A_216] :
      ( l1_waybel_0(k3_yellow19(A_216,k2_struct_0('#skF_3'),'#skF_6'),A_216)
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_216)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_216)
      | v2_struct_0(A_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_135,c_556])).

tff(c_567,plain,(
    ! [A_219] :
      ( l1_waybel_0(k3_yellow19(A_219,k2_struct_0('#skF_3'),'#skF_6'),A_219)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ l1_struct_0(A_219)
      | v2_struct_0(A_219) ) ),
    inference(negUnitSimplification,[status(thm)],[c_510,c_121,c_564])).

tff(c_570,plain,
    ( l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'),'#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_567])).

tff(c_573,plain,
    ( l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_570])).

tff(c_574,plain,(
    l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_573])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k2_yellow19(A_1,B_3) = a_2_1_yellow19(A_1,B_3)
      | ~ l1_waybel_0(B_3,A_1)
      | v2_struct_0(B_3)
      | ~ l1_struct_0(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_577,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')) = a_2_1_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
    | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_574,c_2])).

tff(c_580,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')) = a_2_1_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
    | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_577])).

tff(c_581,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')) = a_2_1_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
    | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_580])).

tff(c_582,plain,(
    v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_581])).

tff(c_30,plain,(
    ! [A_15,B_16,C_17] :
      ( ~ v2_struct_0(k3_yellow19(A_15,B_16,C_17))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_16))))
      | ~ v13_waybel_0(C_17,k3_yellow_1(B_16))
      | ~ v2_waybel_0(C_17,k3_yellow_1(B_16))
      | v1_xboole_0(C_17)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | v1_xboole_0(B_16)
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_602,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_3')))
    | v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_582,c_30])).

tff(c_605,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(k2_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_136,c_135,c_138,c_602])).

tff(c_606,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_510,c_121,c_605])).

tff(c_609,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_606])).

tff(c_613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_609])).

tff(c_615,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')) ),
    inference(splitRight,[status(thm)],[c_581])).

tff(c_614,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')) = a_2_1_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')) ),
    inference(splitRight,[status(thm)],[c_581])).

tff(c_1709,plain,(
    ! [A_247,B_248] :
      ( k2_yellow19(A_247,k3_yellow19(A_247,k2_struct_0(A_247),B_248)) = B_248
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_247)))))
      | ~ v13_waybel_0(B_248,k3_yellow_1(k2_struct_0(A_247)))
      | ~ v2_waybel_0(B_248,k3_yellow_1(k2_struct_0(A_247)))
      | ~ v1_subset_1(B_248,u1_struct_0(k3_yellow_1(k2_struct_0(A_247))))
      | v1_xboole_0(B_248)
      | ~ l1_struct_0(A_247)
      | v2_struct_0(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_1718,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')) = '#skF_6'
    | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0('#skF_6')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_138,c_1709])).

tff(c_1730,plain,
    ( a_2_1_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_137,c_136,c_135,c_614,c_1718])).

tff(c_1731,plain,(
    a_2_1_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_121,c_1730])).

tff(c_60,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(A_45,B_46)
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_126,plain,(
    m1_subset_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_122,c_60])).

tff(c_1738,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1731,c_614])).

tff(c_76,plain,(
    ! [A_69,B_70] :
      ( r2_hidden(A_69,B_70)
      | v1_xboole_0(B_70)
      | ~ m1_subset_1(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_142,plain,(
    ! [A_103,B_104,C_105] :
      ( r1_waybel_0(A_103,B_104,C_105)
      | ~ r2_hidden(C_105,k2_yellow19(A_103,B_104))
      | ~ l1_waybel_0(B_104,A_103)
      | v2_struct_0(B_104)
      | ~ l1_struct_0(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_147,plain,(
    ! [A_103,B_104,A_69] :
      ( r1_waybel_0(A_103,B_104,A_69)
      | ~ l1_waybel_0(B_104,A_103)
      | v2_struct_0(B_104)
      | ~ l1_struct_0(A_103)
      | v2_struct_0(A_103)
      | v1_xboole_0(k2_yellow19(A_103,B_104))
      | ~ m1_subset_1(A_69,k2_yellow19(A_103,B_104)) ) ),
    inference(resolution,[status(thm)],[c_76,c_142])).

tff(c_1804,plain,(
    ! [A_69] :
      ( r1_waybel_0('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'),A_69)
      | ~ l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'),'#skF_3')
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
      | ~ l1_struct_0('#skF_3')
      | v2_struct_0('#skF_3')
      | v1_xboole_0(k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')))
      | ~ m1_subset_1(A_69,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1738,c_147])).

tff(c_1849,plain,(
    ! [A_69] :
      ( r1_waybel_0('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'),A_69)
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
      | v2_struct_0('#skF_3')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_69,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1738,c_193,c_574,c_1804])).

tff(c_2017,plain,(
    ! [A_251] :
      ( r1_waybel_0('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'),A_251)
      | ~ m1_subset_1(A_251,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_86,c_615,c_1849])).

tff(c_220,plain,(
    ! [D_132,B_133,C_134] :
      ( r2_hidden(D_132,a_2_1_yellow19(B_133,C_134))
      | ~ r1_waybel_0(B_133,C_134,D_132)
      | ~ m1_subset_1(D_132,k1_zfmisc_1(u1_struct_0(B_133)))
      | ~ l1_waybel_0(C_134,B_133)
      | v2_struct_0(C_134)
      | ~ l1_struct_0(B_133)
      | v2_struct_0(B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_230,plain,(
    ! [C_134] :
      ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3',C_134))
      | ~ r1_waybel_0('#skF_3',C_134,'#skF_4')
      | ~ l1_waybel_0(C_134,'#skF_3')
      | v2_struct_0(C_134)
      | ~ l1_struct_0('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_220])).

tff(c_237,plain,(
    ! [C_134] :
      ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3',C_134))
      | ~ r1_waybel_0('#skF_3',C_134,'#skF_4')
      | ~ l1_waybel_0(C_134,'#skF_3')
      | v2_struct_0(C_134)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_230])).

tff(c_239,plain,(
    ! [C_135] :
      ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3',C_135))
      | ~ r1_waybel_0('#skF_3',C_135,'#skF_4')
      | ~ l1_waybel_0(C_135,'#skF_3')
      | v2_struct_0(C_135) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_237])).

tff(c_44,plain,(
    ! [A_22,B_23,C_24] :
      ( '#skF_1'(A_22,B_23,C_24) = A_22
      | ~ r2_hidden(A_22,a_2_1_yellow19(B_23,C_24))
      | ~ l1_waybel_0(C_24,B_23)
      | v2_struct_0(C_24)
      | ~ l1_struct_0(B_23)
      | v2_struct_0(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_242,plain,(
    ! [C_135] :
      ( '#skF_1'('#skF_4','#skF_3',C_135) = '#skF_4'
      | ~ l1_struct_0('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',C_135,'#skF_4')
      | ~ l1_waybel_0(C_135,'#skF_3')
      | v2_struct_0(C_135) ) ),
    inference(resolution,[status(thm)],[c_239,c_44])).

tff(c_248,plain,(
    ! [C_135] :
      ( '#skF_1'('#skF_4','#skF_3',C_135) = '#skF_4'
      | v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',C_135,'#skF_4')
      | ~ l1_waybel_0(C_135,'#skF_3')
      | v2_struct_0(C_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_242])).

tff(c_249,plain,(
    ! [C_135] :
      ( '#skF_1'('#skF_4','#skF_3',C_135) = '#skF_4'
      | ~ r1_waybel_0('#skF_3',C_135,'#skF_4')
      | ~ l1_waybel_0(C_135,'#skF_3')
      | v2_struct_0(C_135) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_248])).

tff(c_2028,plain,
    ( '#skF_1'('#skF_4','#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')) = '#skF_4'
    | ~ l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'),'#skF_3')
    | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
    | ~ m1_subset_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_2017,c_249])).

tff(c_2036,plain,
    ( '#skF_1'('#skF_4','#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')) = '#skF_4'
    | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_574,c_2028])).

tff(c_2037,plain,(
    '#skF_1'('#skF_4','#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_615,c_2036])).

tff(c_42,plain,(
    ! [B_23,C_24,A_22] :
      ( r1_waybel_0(B_23,C_24,'#skF_1'(A_22,B_23,C_24))
      | ~ r2_hidden(A_22,a_2_1_yellow19(B_23,C_24))
      | ~ l1_waybel_0(C_24,B_23)
      | v2_struct_0(C_24)
      | ~ l1_struct_0(B_23)
      | v2_struct_0(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_2044,plain,
    ( r1_waybel_0('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'),'#skF_4')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')))
    | ~ l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'),'#skF_3')
    | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2037,c_42])).

tff(c_2051,plain,
    ( r1_waybel_0('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'),'#skF_4')
    | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_574,c_122,c_1731,c_2044])).

tff(c_2052,plain,(
    r1_waybel_0('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_615,c_2051])).

tff(c_84,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_511,plain,(
    ! [A_211] :
      ( v4_orders_2(k3_yellow19(A_211,k2_struct_0('#skF_3'),'#skF_6'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_211)))
      | ~ l1_struct_0(A_211)
      | v2_struct_0(A_211) ) ),
    inference(splitRight,[status(thm)],[c_498])).

tff(c_515,plain,
    ( v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_511])).

tff(c_518,plain,
    ( v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_515])).

tff(c_519,plain,(
    v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_518])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( v2_waybel_0(k2_yellow19(A_13,B_14),k3_yellow_1(k2_struct_0(A_13)))
      | ~ l1_waybel_0(B_14,A_13)
      | ~ v7_waybel_0(B_14)
      | ~ v4_orders_2(B_14)
      | v2_struct_0(B_14)
      | ~ l1_struct_0(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_645,plain,
    ( v2_waybel_0(a_2_1_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'),'#skF_3')
    | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
    | ~ v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
    | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_20])).

tff(c_690,plain,
    ( v2_waybel_0(a_2_1_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
    | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_519,c_574,c_645])).

tff(c_691,plain,
    ( v2_waybel_0(a_2_1_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_615,c_690])).

tff(c_816,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_691])).

tff(c_1562,plain,(
    ! [A_240,B_241,C_242] :
      ( v7_waybel_0(k3_yellow19(A_240,B_241,C_242))
      | ~ m1_subset_1(C_242,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_241))))
      | ~ v13_waybel_0(C_242,k3_yellow_1(B_241))
      | ~ v2_waybel_0(C_242,k3_yellow_1(B_241))
      | ~ v1_subset_1(C_242,u1_struct_0(k3_yellow_1(B_241)))
      | v1_xboole_0(C_242)
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0(A_240)))
      | v1_xboole_0(B_241)
      | ~ l1_struct_0(A_240)
      | v2_struct_0(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_1569,plain,(
    ! [A_240] :
      ( v7_waybel_0(k3_yellow19(A_240,k2_struct_0('#skF_3'),'#skF_6'))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_240)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_240)
      | v2_struct_0(A_240) ) ),
    inference(resolution,[status(thm)],[c_138,c_1562])).

tff(c_1577,plain,(
    ! [A_240] :
      ( v7_waybel_0(k3_yellow19(A_240,k2_struct_0('#skF_3'),'#skF_6'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_240)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_240)
      | v2_struct_0(A_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_136,c_135,c_1569])).

tff(c_1681,plain,(
    ! [A_246] :
      ( v7_waybel_0(k3_yellow19(A_246,k2_struct_0('#skF_3'),'#skF_6'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_246)))
      | ~ l1_struct_0(A_246)
      | v2_struct_0(A_246) ) ),
    inference(negUnitSimplification,[status(thm)],[c_510,c_121,c_1577])).

tff(c_1693,plain,
    ( v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_1681])).

tff(c_1704,plain,
    ( v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_1693])).

tff(c_1706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_816,c_1704])).

tff(c_1708,plain,(
    v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6')) ),
    inference(splitRight,[status(thm)],[c_691])).

tff(c_54,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_1784,plain,(
    ! [C_41] :
      ( r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'),C_41)
      | ~ r1_waybel_7('#skF_3','#skF_6',C_41)
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'),'#skF_3')
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
      | ~ v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1738,c_54])).

tff(c_1828,plain,(
    ! [C_41] :
      ( r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'),C_41)
      | ~ r1_waybel_7('#skF_3','#skF_6',C_41)
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_519,c_1708,c_574,c_1784])).

tff(c_2216,plain,(
    ! [C_264] :
      ( r3_waybel_9('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'),C_264)
      | ~ r1_waybel_7('#skF_3','#skF_6',C_264)
      | ~ m1_subset_1(C_264,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_615,c_1828])).

tff(c_62,plain,(
    ! [C_65,A_47,B_59,D_68] :
      ( r2_hidden(C_65,k2_pre_topc(A_47,B_59))
      | ~ r3_waybel_9(A_47,D_68,C_65)
      | ~ r1_waybel_0(A_47,D_68,B_59)
      | ~ l1_waybel_0(D_68,A_47)
      | ~ v7_waybel_0(D_68)
      | ~ v4_orders_2(D_68)
      | v2_struct_0(D_68)
      | ~ m1_subset_1(C_65,u1_struct_0(A_47))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_2221,plain,(
    ! [C_264,B_59] :
      ( r2_hidden(C_264,k2_pre_topc('#skF_3',B_59))
      | ~ r1_waybel_0('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'),B_59)
      | ~ l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'),'#skF_3')
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
      | ~ v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_waybel_7('#skF_3','#skF_6',C_264)
      | ~ m1_subset_1(C_264,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2216,c_62])).

tff(c_2225,plain,(
    ! [C_264,B_59] :
      ( r2_hidden(C_264,k2_pre_topc('#skF_3',B_59))
      | ~ r1_waybel_0('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'),B_59)
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | ~ r1_waybel_7('#skF_3','#skF_6',C_264)
      | ~ m1_subset_1(C_264,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_519,c_1708,c_574,c_2221])).

tff(c_2767,plain,(
    ! [C_324,B_325] :
      ( r2_hidden(C_324,k2_pre_topc('#skF_3',B_325))
      | ~ r1_waybel_0('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_6'),B_325)
      | ~ m1_subset_1(B_325,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_waybel_7('#skF_3','#skF_6',C_324)
      | ~ m1_subset_1(C_324,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_615,c_2225])).

tff(c_2771,plain,(
    ! [C_324] :
      ( r2_hidden(C_324,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_waybel_7('#skF_3','#skF_6',C_324)
      | ~ m1_subset_1(C_324,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2052,c_2767])).

tff(c_2786,plain,(
    ! [C_326] :
      ( r2_hidden(C_326,k2_pre_topc('#skF_3','#skF_4'))
      | ~ r1_waybel_7('#skF_3','#skF_6',C_326)
      | ~ m1_subset_1(C_326,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2771])).

tff(c_88,plain,(
    ! [D_89] :
      ( ~ r1_waybel_7('#skF_3',D_89,'#skF_5')
      | ~ r2_hidden('#skF_4',D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
      | ~ v13_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1(D_89,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0(D_89)
      | ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_413,plain,(
    ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_2789,plain,
    ( ~ r1_waybel_7('#skF_3','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2786,c_413])).

tff(c_2807,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_134,c_2789])).

tff(c_3166,plain,(
    ! [D_340] :
      ( ~ r1_waybel_7('#skF_3',D_340,'#skF_5')
      | ~ r2_hidden('#skF_4',D_340)
      | ~ m1_subset_1(D_340,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
      | ~ v13_waybel_0(D_340,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0(D_340,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1(D_340,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0(D_340) ) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_3180,plain,
    ( ~ r1_waybel_7('#skF_3','#skF_6','#skF_5')
    | ~ r2_hidden('#skF_4','#skF_6')
    | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_138,c_3166])).

tff(c_3196,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_136,c_135,c_122,c_134,c_3180])).

tff(c_3198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_3196])).

tff(c_3199,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_3532,plain,(
    ! [A_414,B_415,C_416] :
      ( r3_waybel_9(A_414,'#skF_2'(A_414,B_415,C_416),C_416)
      | ~ r2_hidden(C_416,k2_pre_topc(A_414,B_415))
      | ~ m1_subset_1(C_416,u1_struct_0(A_414))
      | ~ m1_subset_1(B_415,k1_zfmisc_1(u1_struct_0(A_414)))
      | ~ l1_pre_topc(A_414)
      | ~ v2_pre_topc(A_414)
      | v2_struct_0(A_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_3540,plain,(
    ! [C_416] :
      ( r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4',C_416),C_416)
      | ~ r2_hidden(C_416,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_416,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_3532])).

tff(c_3546,plain,(
    ! [C_416] :
      ( r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4',C_416),C_416)
      | ~ r2_hidden(C_416,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_416,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_3540])).

tff(c_3547,plain,(
    ! [C_416] :
      ( r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4',C_416),C_416)
      | ~ r2_hidden(C_416,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_416,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3546])).

tff(c_3422,plain,(
    ! [A_408,B_409,C_410] :
      ( ~ v2_struct_0('#skF_2'(A_408,B_409,C_410))
      | ~ r2_hidden(C_410,k2_pre_topc(A_408,B_409))
      | ~ m1_subset_1(C_410,u1_struct_0(A_408))
      | ~ m1_subset_1(B_409,k1_zfmisc_1(u1_struct_0(A_408)))
      | ~ l1_pre_topc(A_408)
      | ~ v2_pre_topc(A_408)
      | v2_struct_0(A_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_3424,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3199,c_3422])).

tff(c_3430,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_3424])).

tff(c_3431,plain,(
    ~ v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3430])).

tff(c_3411,plain,(
    ! [A_405,B_406,C_407] :
      ( v4_orders_2('#skF_2'(A_405,B_406,C_407))
      | ~ r2_hidden(C_407,k2_pre_topc(A_405,B_406))
      | ~ m1_subset_1(C_407,u1_struct_0(A_405))
      | ~ m1_subset_1(B_406,k1_zfmisc_1(u1_struct_0(A_405)))
      | ~ l1_pre_topc(A_405)
      | ~ v2_pre_topc(A_405)
      | v2_struct_0(A_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_3413,plain,
    ( v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3199,c_3411])).

tff(c_3419,plain,
    ( v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_3413])).

tff(c_3420,plain,(
    v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3419])).

tff(c_3344,plain,(
    ! [A_387,B_388,C_389] :
      ( v7_waybel_0('#skF_2'(A_387,B_388,C_389))
      | ~ r2_hidden(C_389,k2_pre_topc(A_387,B_388))
      | ~ m1_subset_1(C_389,u1_struct_0(A_387))
      | ~ m1_subset_1(B_388,k1_zfmisc_1(u1_struct_0(A_387)))
      | ~ l1_pre_topc(A_387)
      | ~ v2_pre_topc(A_387)
      | v2_struct_0(A_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_3346,plain,
    ( v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3199,c_3344])).

tff(c_3352,plain,
    ( v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_3346])).

tff(c_3353,plain,(
    v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3352])).

tff(c_3434,plain,(
    ! [A_411,B_412,C_413] :
      ( l1_waybel_0('#skF_2'(A_411,B_412,C_413),A_411)
      | ~ r2_hidden(C_413,k2_pre_topc(A_411,B_412))
      | ~ m1_subset_1(C_413,u1_struct_0(A_411))
      | ~ m1_subset_1(B_412,k1_zfmisc_1(u1_struct_0(A_411)))
      | ~ l1_pre_topc(A_411)
      | ~ v2_pre_topc(A_411)
      | v2_struct_0(A_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_3436,plain,
    ( l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3199,c_3434])).

tff(c_3442,plain,
    ( l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_3436])).

tff(c_3443,plain,(
    l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3442])).

tff(c_3232,plain,(
    ! [C_371,A_372,B_373] :
      ( r2_hidden(C_371,k2_yellow19(A_372,B_373))
      | ~ m1_subset_1(C_371,k1_zfmisc_1(u1_struct_0(A_372)))
      | ~ r1_waybel_0(A_372,B_373,C_371)
      | ~ l1_waybel_0(B_373,A_372)
      | v2_struct_0(B_373)
      | ~ l1_struct_0(A_372)
      | v2_struct_0(A_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_3240,plain,(
    ! [B_373] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_373))
      | ~ r1_waybel_0('#skF_3',B_373,'#skF_4')
      | ~ l1_waybel_0(B_373,'#skF_3')
      | v2_struct_0(B_373)
      | ~ l1_struct_0('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_3232])).

tff(c_3246,plain,(
    ! [B_373] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_373))
      | ~ r1_waybel_0('#skF_3',B_373,'#skF_4')
      | ~ l1_waybel_0(B_373,'#skF_3')
      | v2_struct_0(B_373)
      | ~ l1_struct_0('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3240])).

tff(c_3247,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3246])).

tff(c_3265,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_3247])).

tff(c_3269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3265])).

tff(c_3271,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3246])).

tff(c_3447,plain,
    ( k2_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) = a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3443,c_2])).

tff(c_3450,plain,
    ( k2_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) = a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3271,c_3447])).

tff(c_3451,plain,(
    k2_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) = a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3431,c_3450])).

tff(c_3801,plain,(
    ! [A_432,B_433,C_434] :
      ( r1_waybel_7(A_432,k2_yellow19(A_432,B_433),C_434)
      | ~ r3_waybel_9(A_432,B_433,C_434)
      | ~ m1_subset_1(C_434,u1_struct_0(A_432))
      | ~ l1_waybel_0(B_433,A_432)
      | ~ v7_waybel_0(B_433)
      | ~ v4_orders_2(B_433)
      | v2_struct_0(B_433)
      | ~ l1_pre_topc(A_432)
      | ~ v2_pre_topc(A_432)
      | v2_struct_0(A_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_3807,plain,(
    ! [C_434] :
      ( r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),C_434)
      | ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),C_434)
      | ~ m1_subset_1(C_434,u1_struct_0('#skF_3'))
      | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3451,c_3801])).

tff(c_3810,plain,(
    ! [C_434] :
      ( r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),C_434)
      | ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),C_434)
      | ~ m1_subset_1(C_434,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_3420,c_3353,c_3443,c_3807])).

tff(c_3816,plain,(
    ! [C_436] :
      ( r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),C_436)
      | ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),C_436)
      | ~ m1_subset_1(C_436,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3431,c_3810])).

tff(c_3607,plain,(
    ! [A_419,B_420,C_421] :
      ( r1_waybel_0(A_419,'#skF_2'(A_419,B_420,C_421),B_420)
      | ~ r2_hidden(C_421,k2_pre_topc(A_419,B_420))
      | ~ m1_subset_1(C_421,u1_struct_0(A_419))
      | ~ m1_subset_1(B_420,k1_zfmisc_1(u1_struct_0(A_419)))
      | ~ l1_pre_topc(A_419)
      | ~ v2_pre_topc(A_419)
      | v2_struct_0(A_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_3617,plain,(
    ! [C_421] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_421),'#skF_4')
      | ~ r2_hidden(C_421,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_421,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_3607])).

tff(c_3624,plain,(
    ! [C_421] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_421),'#skF_4')
      | ~ r2_hidden(C_421,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_421,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_3617])).

tff(c_3670,plain,(
    ! [C_425] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_425),'#skF_4')
      | ~ r2_hidden(C_425,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_425,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3624])).

tff(c_3270,plain,(
    ! [B_373] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_373))
      | ~ r1_waybel_0('#skF_3',B_373,'#skF_4')
      | ~ l1_waybel_0(B_373,'#skF_3')
      | v2_struct_0(B_373) ) ),
    inference(splitRight,[status(thm)],[c_3246])).

tff(c_3466,plain,
    ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3451,c_3270])).

tff(c_3505,plain,
    ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3443,c_3466])).

tff(c_3506,plain,
    ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_3431,c_3505])).

tff(c_3626,plain,(
    ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3506])).

tff(c_3673,plain,
    ( ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3670,c_3626])).

tff(c_3680,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3199,c_3673])).

tff(c_3681,plain,(
    r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_3506])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( ~ v1_xboole_0(k2_yellow19(A_11,B_12))
      | ~ l1_waybel_0(B_12,A_11)
      | v2_struct_0(B_12)
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3489,plain,
    ( ~ v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3451,c_18])).

tff(c_3529,plain,
    ( ~ v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3271,c_3443,c_3489])).

tff(c_3530,plain,(
    ~ v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3431,c_3529])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( v1_subset_1(k2_yellow19(A_13,B_14),u1_struct_0(k3_yellow_1(k2_struct_0(A_13))))
      | ~ l1_waybel_0(B_14,A_13)
      | ~ v7_waybel_0(B_14)
      | ~ v4_orders_2(B_14)
      | v2_struct_0(B_14)
      | ~ l1_struct_0(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3472,plain,
    ( v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3451,c_22])).

tff(c_3511,plain,
    ( v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3271,c_3420,c_3353,c_3443,c_3472])).

tff(c_3512,plain,(
    v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3431,c_3511])).

tff(c_3475,plain,
    ( v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3451,c_20])).

tff(c_3514,plain,
    ( v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3271,c_3420,c_3353,c_3443,c_3475])).

tff(c_3515,plain,(
    v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3431,c_3514])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( v13_waybel_0(k2_yellow19(A_11,B_12),k3_yellow_1(k2_struct_0(A_11)))
      | ~ l1_waybel_0(B_12,A_11)
      | v2_struct_0(B_12)
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3486,plain,
    ( v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3451,c_16])).

tff(c_3526,plain,
    ( v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3271,c_3443,c_3486])).

tff(c_3527,plain,(
    v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3431,c_3526])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k2_yellow19(A_5,B_6),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_5)))))
      | ~ l1_waybel_0(B_6,A_5)
      | v2_struct_0(B_6)
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3483,plain,
    ( m1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3451,c_6])).

tff(c_3523,plain,
    ( m1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3271,c_3443,c_3483])).

tff(c_3524,plain,(
    m1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3431,c_3523])).

tff(c_3358,plain,(
    ! [D_89] :
      ( ~ r1_waybel_7('#skF_3',D_89,'#skF_5')
      | ~ r2_hidden('#skF_4',D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
      | ~ v13_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1(D_89,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0(D_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3199,c_88])).

tff(c_3552,plain,
    ( ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_3524,c_3358])).

tff(c_3560,plain,
    ( ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3512,c_3515,c_3527,c_3552])).

tff(c_3561,plain,
    ( ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_3530,c_3560])).

tff(c_3815,plain,(
    ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3681,c_3561])).

tff(c_3819,plain,
    ( ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3816,c_3815])).

tff(c_3822,plain,(
    ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3819])).

tff(c_3825,plain,
    ( ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3547,c_3822])).

tff(c_3829,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3199,c_3825])).

tff(c_3830,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_4359,plain,(
    ! [A_519,B_520,C_521] :
      ( r3_waybel_9(A_519,'#skF_2'(A_519,B_520,C_521),C_521)
      | ~ r2_hidden(C_521,k2_pre_topc(A_519,B_520))
      | ~ m1_subset_1(C_521,u1_struct_0(A_519))
      | ~ m1_subset_1(B_520,k1_zfmisc_1(u1_struct_0(A_519)))
      | ~ l1_pre_topc(A_519)
      | ~ v2_pre_topc(A_519)
      | v2_struct_0(A_519) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_4369,plain,(
    ! [C_521] :
      ( r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4',C_521),C_521)
      | ~ r2_hidden(C_521,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_521,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_4359])).

tff(c_4376,plain,(
    ! [C_521] :
      ( r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4',C_521),C_521)
      | ~ r2_hidden(C_521,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_521,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_4369])).

tff(c_4377,plain,(
    ! [C_521] :
      ( r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4',C_521),C_521)
      | ~ r2_hidden(C_521,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_521,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4376])).

tff(c_4008,plain,(
    ! [A_497,B_498,C_499] :
      ( ~ v2_struct_0('#skF_2'(A_497,B_498,C_499))
      | ~ r2_hidden(C_499,k2_pre_topc(A_497,B_498))
      | ~ m1_subset_1(C_499,u1_struct_0(A_497))
      | ~ m1_subset_1(B_498,k1_zfmisc_1(u1_struct_0(A_497)))
      | ~ l1_pre_topc(A_497)
      | ~ v2_pre_topc(A_497)
      | v2_struct_0(A_497) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_4010,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3830,c_4008])).

tff(c_4016,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_4010])).

tff(c_4017,plain,(
    ~ v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4016])).

tff(c_3972,plain,(
    ! [A_484,B_485,C_486] :
      ( v4_orders_2('#skF_2'(A_484,B_485,C_486))
      | ~ r2_hidden(C_486,k2_pre_topc(A_484,B_485))
      | ~ m1_subset_1(C_486,u1_struct_0(A_484))
      | ~ m1_subset_1(B_485,k1_zfmisc_1(u1_struct_0(A_484)))
      | ~ l1_pre_topc(A_484)
      | ~ v2_pre_topc(A_484)
      | v2_struct_0(A_484) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_3974,plain,
    ( v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3830,c_3972])).

tff(c_3980,plain,
    ( v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_3974])).

tff(c_3981,plain,(
    v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3980])).

tff(c_4019,plain,(
    ! [A_500,B_501,C_502] :
      ( v7_waybel_0('#skF_2'(A_500,B_501,C_502))
      | ~ r2_hidden(C_502,k2_pre_topc(A_500,B_501))
      | ~ m1_subset_1(C_502,u1_struct_0(A_500))
      | ~ m1_subset_1(B_501,k1_zfmisc_1(u1_struct_0(A_500)))
      | ~ l1_pre_topc(A_500)
      | ~ v2_pre_topc(A_500)
      | v2_struct_0(A_500) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_4021,plain,
    ( v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3830,c_4019])).

tff(c_4027,plain,
    ( v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_4021])).

tff(c_4028,plain,(
    v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4027])).

tff(c_4030,plain,(
    ! [A_503,B_504,C_505] :
      ( l1_waybel_0('#skF_2'(A_503,B_504,C_505),A_503)
      | ~ r2_hidden(C_505,k2_pre_topc(A_503,B_504))
      | ~ m1_subset_1(C_505,u1_struct_0(A_503))
      | ~ m1_subset_1(B_504,k1_zfmisc_1(u1_struct_0(A_503)))
      | ~ l1_pre_topc(A_503)
      | ~ v2_pre_topc(A_503)
      | v2_struct_0(A_503) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_4032,plain,
    ( l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3830,c_4030])).

tff(c_4038,plain,
    ( l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_4032])).

tff(c_4039,plain,(
    l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4038])).

tff(c_3864,plain,(
    ! [D_467,B_468,C_469] :
      ( r2_hidden(D_467,a_2_1_yellow19(B_468,C_469))
      | ~ r1_waybel_0(B_468,C_469,D_467)
      | ~ m1_subset_1(D_467,k1_zfmisc_1(u1_struct_0(B_468)))
      | ~ l1_waybel_0(C_469,B_468)
      | v2_struct_0(C_469)
      | ~ l1_struct_0(B_468)
      | v2_struct_0(B_468) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_3872,plain,(
    ! [C_469] :
      ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3',C_469))
      | ~ r1_waybel_0('#skF_3',C_469,'#skF_4')
      | ~ l1_waybel_0(C_469,'#skF_3')
      | v2_struct_0(C_469)
      | ~ l1_struct_0('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_3864])).

tff(c_3878,plain,(
    ! [C_469] :
      ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3',C_469))
      | ~ r1_waybel_0('#skF_3',C_469,'#skF_4')
      | ~ l1_waybel_0(C_469,'#skF_3')
      | v2_struct_0(C_469)
      | ~ l1_struct_0('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3872])).

tff(c_3879,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3878])).

tff(c_3882,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_3879])).

tff(c_3886,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3882])).

tff(c_3888,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3878])).

tff(c_4043,plain,
    ( k2_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) = a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4039,c_2])).

tff(c_4046,plain,
    ( k2_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) = a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3888,c_4043])).

tff(c_4047,plain,(
    k2_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) = a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4017,c_4046])).

tff(c_4476,plain,(
    ! [A_535,B_536,C_537] :
      ( r1_waybel_7(A_535,k2_yellow19(A_535,B_536),C_537)
      | ~ r3_waybel_9(A_535,B_536,C_537)
      | ~ m1_subset_1(C_537,u1_struct_0(A_535))
      | ~ l1_waybel_0(B_536,A_535)
      | ~ v7_waybel_0(B_536)
      | ~ v4_orders_2(B_536)
      | v2_struct_0(B_536)
      | ~ l1_pre_topc(A_535)
      | ~ v2_pre_topc(A_535)
      | v2_struct_0(A_535) ) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_4482,plain,(
    ! [C_537] :
      ( r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),C_537)
      | ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),C_537)
      | ~ m1_subset_1(C_537,u1_struct_0('#skF_3'))
      | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4047,c_4476])).

tff(c_4485,plain,(
    ! [C_537] :
      ( r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),C_537)
      | ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),C_537)
      | ~ m1_subset_1(C_537,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_3981,c_4028,c_4039,c_4482])).

tff(c_4487,plain,(
    ! [C_538] :
      ( r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),C_538)
      | ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),C_538)
      | ~ m1_subset_1(C_538,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4017,c_4485])).

tff(c_4135,plain,(
    ! [A_506,B_507,C_508] :
      ( r1_waybel_0(A_506,'#skF_2'(A_506,B_507,C_508),B_507)
      | ~ r2_hidden(C_508,k2_pre_topc(A_506,B_507))
      | ~ m1_subset_1(C_508,u1_struct_0(A_506))
      | ~ m1_subset_1(B_507,k1_zfmisc_1(u1_struct_0(A_506)))
      | ~ l1_pre_topc(A_506)
      | ~ v2_pre_topc(A_506)
      | v2_struct_0(A_506) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_4145,plain,(
    ! [C_508] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_508),'#skF_4')
      | ~ r2_hidden(C_508,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_508,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_4135])).

tff(c_4152,plain,(
    ! [C_508] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_508),'#skF_4')
      | ~ r2_hidden(C_508,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_508,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_4145])).

tff(c_4285,plain,(
    ! [C_517] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_517),'#skF_4')
      | ~ r2_hidden(C_517,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_517,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4152])).

tff(c_3889,plain,(
    ! [C_470,A_471,B_472] :
      ( r2_hidden(C_470,k2_yellow19(A_471,B_472))
      | ~ m1_subset_1(C_470,k1_zfmisc_1(u1_struct_0(A_471)))
      | ~ r1_waybel_0(A_471,B_472,C_470)
      | ~ l1_waybel_0(B_472,A_471)
      | v2_struct_0(B_472)
      | ~ l1_struct_0(A_471)
      | v2_struct_0(A_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_3897,plain,(
    ! [B_472] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_472))
      | ~ r1_waybel_0('#skF_3',B_472,'#skF_4')
      | ~ l1_waybel_0(B_472,'#skF_3')
      | v2_struct_0(B_472)
      | ~ l1_struct_0('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_3889])).

tff(c_3903,plain,(
    ! [B_472] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_472))
      | ~ r1_waybel_0('#skF_3',B_472,'#skF_4')
      | ~ l1_waybel_0(B_472,'#skF_3')
      | v2_struct_0(B_472)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3888,c_3897])).

tff(c_3917,plain,(
    ! [B_474] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_474))
      | ~ r1_waybel_0('#skF_3',B_474,'#skF_4')
      | ~ l1_waybel_0(B_474,'#skF_3')
      | v2_struct_0(B_474) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3903])).

tff(c_3934,plain,(
    ! [B_474] :
      ( m1_subset_1('#skF_4',k2_yellow19('#skF_3',B_474))
      | ~ r1_waybel_0('#skF_3',B_474,'#skF_4')
      | ~ l1_waybel_0(B_474,'#skF_3')
      | v2_struct_0(B_474) ) ),
    inference(resolution,[status(thm)],[c_3917,c_60])).

tff(c_4059,plain,
    ( m1_subset_1('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4047,c_3934])).

tff(c_4098,plain,
    ( m1_subset_1('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4039,c_4059])).

tff(c_4099,plain,
    ( m1_subset_1('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_4017,c_4098])).

tff(c_4224,plain,(
    ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4099])).

tff(c_4288,plain,
    ( ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4285,c_4224])).

tff(c_4295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3830,c_4288])).

tff(c_4297,plain,(
    r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_4099])).

tff(c_3904,plain,(
    ! [B_472] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_472))
      | ~ r1_waybel_0('#skF_3',B_472,'#skF_4')
      | ~ l1_waybel_0(B_472,'#skF_3')
      | v2_struct_0(B_472) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3903])).

tff(c_4062,plain,
    ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4047,c_3904])).

tff(c_4101,plain,
    ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4039,c_4062])).

tff(c_4102,plain,
    ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_4017,c_4101])).

tff(c_4379,plain,(
    r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4297,c_4102])).

tff(c_4085,plain,
    ( ~ v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4047,c_18])).

tff(c_4125,plain,
    ( ~ v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3888,c_4039,c_4085])).

tff(c_4126,plain,(
    ~ v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4017,c_4125])).

tff(c_4068,plain,
    ( v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4047,c_22])).

tff(c_4107,plain,
    ( v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3888,c_3981,c_4028,c_4039,c_4068])).

tff(c_4108,plain,(
    v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4017,c_4107])).

tff(c_4071,plain,
    ( v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4047,c_20])).

tff(c_4110,plain,
    ( v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3888,c_3981,c_4028,c_4039,c_4071])).

tff(c_4111,plain,(
    v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4017,c_4110])).

tff(c_4082,plain,
    ( v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4047,c_16])).

tff(c_4122,plain,
    ( v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3888,c_4039,c_4082])).

tff(c_4123,plain,(
    v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4017,c_4122])).

tff(c_4079,plain,
    ( m1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4047,c_6])).

tff(c_4119,plain,
    ( m1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3888,c_4039,c_4079])).

tff(c_4120,plain,(
    m1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4017,c_4119])).

tff(c_4198,plain,(
    ! [D_511] :
      ( ~ r1_waybel_7('#skF_3',D_511,'#skF_5')
      | ~ r2_hidden('#skF_4',D_511)
      | ~ m1_subset_1(D_511,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
      | ~ v13_waybel_0(D_511,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0(D_511,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1(D_511,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0(D_511) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3830,c_88])).

tff(c_4201,plain,
    ( ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_4120,c_4198])).

tff(c_4216,plain,
    ( ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4108,c_4111,c_4123,c_4201])).

tff(c_4217,plain,
    ( ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_4126,c_4216])).

tff(c_4431,plain,(
    ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4379,c_4217])).

tff(c_4493,plain,
    ( ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4487,c_4431])).

tff(c_4497,plain,(
    ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4493])).

tff(c_4500,plain,
    ( ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4377,c_4497])).

tff(c_4504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3830,c_4500])).

tff(c_4505,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_4838,plain,(
    ! [A_612,B_613,C_614] :
      ( r3_waybel_9(A_612,'#skF_2'(A_612,B_613,C_614),C_614)
      | ~ r2_hidden(C_614,k2_pre_topc(A_612,B_613))
      | ~ m1_subset_1(C_614,u1_struct_0(A_612))
      | ~ m1_subset_1(B_613,k1_zfmisc_1(u1_struct_0(A_612)))
      | ~ l1_pre_topc(A_612)
      | ~ v2_pre_topc(A_612)
      | v2_struct_0(A_612) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_4846,plain,(
    ! [C_614] :
      ( r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4',C_614),C_614)
      | ~ r2_hidden(C_614,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_614,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_4838])).

tff(c_4852,plain,(
    ! [C_614] :
      ( r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4',C_614),C_614)
      | ~ r2_hidden(C_614,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_614,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_4846])).

tff(c_4853,plain,(
    ! [C_614] :
      ( r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4',C_614),C_614)
      | ~ r2_hidden(C_614,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_614,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4852])).

tff(c_4698,plain,(
    ! [A_602,B_603,C_604] :
      ( ~ v2_struct_0('#skF_2'(A_602,B_603,C_604))
      | ~ r2_hidden(C_604,k2_pre_topc(A_602,B_603))
      | ~ m1_subset_1(C_604,u1_struct_0(A_602))
      | ~ m1_subset_1(B_603,k1_zfmisc_1(u1_struct_0(A_602)))
      | ~ l1_pre_topc(A_602)
      | ~ v2_pre_topc(A_602)
      | v2_struct_0(A_602) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_4700,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4505,c_4698])).

tff(c_4706,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_4700])).

tff(c_4707,plain,(
    ~ v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4706])).

tff(c_4651,plain,(
    ! [A_585,B_586,C_587] :
      ( v4_orders_2('#skF_2'(A_585,B_586,C_587))
      | ~ r2_hidden(C_587,k2_pre_topc(A_585,B_586))
      | ~ m1_subset_1(C_587,u1_struct_0(A_585))
      | ~ m1_subset_1(B_586,k1_zfmisc_1(u1_struct_0(A_585)))
      | ~ l1_pre_topc(A_585)
      | ~ v2_pre_topc(A_585)
      | v2_struct_0(A_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_4653,plain,
    ( v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4505,c_4651])).

tff(c_4659,plain,
    ( v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_4653])).

tff(c_4660,plain,(
    v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4659])).

tff(c_4709,plain,(
    ! [A_605,B_606,C_607] :
      ( v7_waybel_0('#skF_2'(A_605,B_606,C_607))
      | ~ r2_hidden(C_607,k2_pre_topc(A_605,B_606))
      | ~ m1_subset_1(C_607,u1_struct_0(A_605))
      | ~ m1_subset_1(B_606,k1_zfmisc_1(u1_struct_0(A_605)))
      | ~ l1_pre_topc(A_605)
      | ~ v2_pre_topc(A_605)
      | v2_struct_0(A_605) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_4711,plain,
    ( v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4505,c_4709])).

tff(c_4717,plain,
    ( v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_4711])).

tff(c_4718,plain,(
    v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4717])).

tff(c_4740,plain,(
    ! [A_609,B_610,C_611] :
      ( l1_waybel_0('#skF_2'(A_609,B_610,C_611),A_609)
      | ~ r2_hidden(C_611,k2_pre_topc(A_609,B_610))
      | ~ m1_subset_1(C_611,u1_struct_0(A_609))
      | ~ m1_subset_1(B_610,k1_zfmisc_1(u1_struct_0(A_609)))
      | ~ l1_pre_topc(A_609)
      | ~ v2_pre_topc(A_609)
      | v2_struct_0(A_609) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_4742,plain,
    ( l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4505,c_4740])).

tff(c_4748,plain,
    ( l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_4742])).

tff(c_4749,plain,(
    l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4748])).

tff(c_4539,plain,(
    ! [C_569,A_570,B_571] :
      ( r2_hidden(C_569,k2_yellow19(A_570,B_571))
      | ~ m1_subset_1(C_569,k1_zfmisc_1(u1_struct_0(A_570)))
      | ~ r1_waybel_0(A_570,B_571,C_569)
      | ~ l1_waybel_0(B_571,A_570)
      | v2_struct_0(B_571)
      | ~ l1_struct_0(A_570)
      | v2_struct_0(A_570) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_4547,plain,(
    ! [B_571] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_571))
      | ~ r1_waybel_0('#skF_3',B_571,'#skF_4')
      | ~ l1_waybel_0(B_571,'#skF_3')
      | v2_struct_0(B_571)
      | ~ l1_struct_0('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_4539])).

tff(c_4553,plain,(
    ! [B_571] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_571))
      | ~ r1_waybel_0('#skF_3',B_571,'#skF_4')
      | ~ l1_waybel_0(B_571,'#skF_3')
      | v2_struct_0(B_571)
      | ~ l1_struct_0('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4547])).

tff(c_4554,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4553])).

tff(c_4572,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_4554])).

tff(c_4576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_4572])).

tff(c_4578,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_4553])).

tff(c_4753,plain,
    ( k2_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) = a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4749,c_2])).

tff(c_4756,plain,
    ( k2_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) = a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4578,c_4753])).

tff(c_4757,plain,(
    k2_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) = a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4707,c_4756])).

tff(c_4997,plain,(
    ! [A_624,B_625,C_626] :
      ( r1_waybel_7(A_624,k2_yellow19(A_624,B_625),C_626)
      | ~ r3_waybel_9(A_624,B_625,C_626)
      | ~ m1_subset_1(C_626,u1_struct_0(A_624))
      | ~ l1_waybel_0(B_625,A_624)
      | ~ v7_waybel_0(B_625)
      | ~ v4_orders_2(B_625)
      | v2_struct_0(B_625)
      | ~ l1_pre_topc(A_624)
      | ~ v2_pre_topc(A_624)
      | v2_struct_0(A_624) ) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_5000,plain,(
    ! [C_626] :
      ( r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),C_626)
      | ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),C_626)
      | ~ m1_subset_1(C_626,u1_struct_0('#skF_3'))
      | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4757,c_4997])).

tff(c_5002,plain,(
    ! [C_626] :
      ( r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),C_626)
      | ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),C_626)
      | ~ m1_subset_1(C_626,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_4660,c_4718,c_4749,c_5000])).

tff(c_5124,plain,(
    ! [C_635] :
      ( r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),C_635)
      | ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),C_635)
      | ~ m1_subset_1(C_635,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4707,c_5002])).

tff(c_4914,plain,(
    ! [A_617,B_618,C_619] :
      ( r1_waybel_0(A_617,'#skF_2'(A_617,B_618,C_619),B_618)
      | ~ r2_hidden(C_619,k2_pre_topc(A_617,B_618))
      | ~ m1_subset_1(C_619,u1_struct_0(A_617))
      | ~ m1_subset_1(B_618,k1_zfmisc_1(u1_struct_0(A_617)))
      | ~ l1_pre_topc(A_617)
      | ~ v2_pre_topc(A_617)
      | v2_struct_0(A_617) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_4924,plain,(
    ! [C_619] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_619),'#skF_4')
      | ~ r2_hidden(C_619,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_619,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_4914])).

tff(c_4931,plain,(
    ! [C_619] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_619),'#skF_4')
      | ~ r2_hidden(C_619,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_619,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_4924])).

tff(c_4977,plain,(
    ! [C_623] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_623),'#skF_4')
      | ~ r2_hidden(C_623,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_623,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4931])).

tff(c_4579,plain,(
    ! [B_575] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_575))
      | ~ r1_waybel_0('#skF_3',B_575,'#skF_4')
      | ~ l1_waybel_0(B_575,'#skF_3')
      | v2_struct_0(B_575) ) ),
    inference(splitRight,[status(thm)],[c_4553])).

tff(c_4596,plain,(
    ! [B_575] :
      ( m1_subset_1('#skF_4',k2_yellow19('#skF_3',B_575))
      | ~ r1_waybel_0('#skF_3',B_575,'#skF_4')
      | ~ l1_waybel_0(B_575,'#skF_3')
      | v2_struct_0(B_575) ) ),
    inference(resolution,[status(thm)],[c_4579,c_60])).

tff(c_4769,plain,
    ( m1_subset_1('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4757,c_4596])).

tff(c_4808,plain,
    ( m1_subset_1('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4749,c_4769])).

tff(c_4809,plain,
    ( m1_subset_1('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_4707,c_4808])).

tff(c_4933,plain,(
    ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4809])).

tff(c_4980,plain,
    ( ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4977,c_4933])).

tff(c_4987,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4505,c_4980])).

tff(c_4989,plain,(
    r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_4809])).

tff(c_4577,plain,(
    ! [B_571] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_571))
      | ~ r1_waybel_0('#skF_3',B_571,'#skF_4')
      | ~ l1_waybel_0(B_571,'#skF_3')
      | v2_struct_0(B_571) ) ),
    inference(splitRight,[status(thm)],[c_4553])).

tff(c_4772,plain,
    ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4757,c_4577])).

tff(c_4811,plain,
    ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4749,c_4772])).

tff(c_4812,plain,
    ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_4707,c_4811])).

tff(c_5059,plain,(
    r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4989,c_4812])).

tff(c_4795,plain,
    ( ~ v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4757,c_18])).

tff(c_4835,plain,
    ( ~ v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4578,c_4749,c_4795])).

tff(c_4836,plain,(
    ~ v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4707,c_4835])).

tff(c_4778,plain,
    ( v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4757,c_22])).

tff(c_4817,plain,
    ( v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4578,c_4660,c_4718,c_4749,c_4778])).

tff(c_4818,plain,(
    v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4707,c_4817])).

tff(c_4781,plain,
    ( v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4757,c_20])).

tff(c_4820,plain,
    ( v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4578,c_4660,c_4718,c_4749,c_4781])).

tff(c_4821,plain,(
    v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4707,c_4820])).

tff(c_4792,plain,
    ( v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4757,c_16])).

tff(c_4832,plain,
    ( v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4578,c_4749,c_4792])).

tff(c_4833,plain,(
    v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4707,c_4832])).

tff(c_4789,plain,
    ( m1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4757,c_6])).

tff(c_4829,plain,
    ( m1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4578,c_4749,c_4789])).

tff(c_4830,plain,(
    m1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4707,c_4829])).

tff(c_4506,plain,(
    ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_108,plain,(
    ! [D_89] :
      ( ~ r1_waybel_7('#skF_3',D_89,'#skF_5')
      | ~ r2_hidden('#skF_4',D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
      | ~ v13_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1(D_89,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0(D_89)
      | v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_4720,plain,(
    ! [D_89] :
      ( ~ r1_waybel_7('#skF_3',D_89,'#skF_5')
      | ~ r2_hidden('#skF_4',D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
      | ~ v13_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1(D_89,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0(D_89) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4506,c_108])).

tff(c_4858,plain,
    ( ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_4830,c_4720])).

tff(c_4866,plain,
    ( ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4818,c_4821,c_4833,c_4858])).

tff(c_4867,plain,
    ( ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_4836,c_4866])).

tff(c_5122,plain,(
    ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5059,c_4867])).

tff(c_5130,plain,
    ( ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5124,c_5122])).

tff(c_5134,plain,(
    ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5130])).

tff(c_5137,plain,
    ( ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4853,c_5134])).

tff(c_5141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4505,c_5137])).

tff(c_5142,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_5477,plain,(
    ! [A_709,B_710,C_711] :
      ( r3_waybel_9(A_709,'#skF_2'(A_709,B_710,C_711),C_711)
      | ~ r2_hidden(C_711,k2_pre_topc(A_709,B_710))
      | ~ m1_subset_1(C_711,u1_struct_0(A_709))
      | ~ m1_subset_1(B_710,k1_zfmisc_1(u1_struct_0(A_709)))
      | ~ l1_pre_topc(A_709)
      | ~ v2_pre_topc(A_709)
      | v2_struct_0(A_709) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_5485,plain,(
    ! [C_711] :
      ( r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4',C_711),C_711)
      | ~ r2_hidden(C_711,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_711,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_5477])).

tff(c_5491,plain,(
    ! [C_711] :
      ( r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4',C_711),C_711)
      | ~ r2_hidden(C_711,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_711,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_5485])).

tff(c_5492,plain,(
    ! [C_711] :
      ( r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4',C_711),C_711)
      | ~ r2_hidden(C_711,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_711,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5491])).

tff(c_5368,plain,(
    ! [A_703,B_704,C_705] :
      ( ~ v2_struct_0('#skF_2'(A_703,B_704,C_705))
      | ~ r2_hidden(C_705,k2_pre_topc(A_703,B_704))
      | ~ m1_subset_1(C_705,u1_struct_0(A_703))
      | ~ m1_subset_1(B_704,k1_zfmisc_1(u1_struct_0(A_703)))
      | ~ l1_pre_topc(A_703)
      | ~ v2_pre_topc(A_703)
      | v2_struct_0(A_703) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_5370,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5142,c_5368])).

tff(c_5376,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_5370])).

tff(c_5377,plain,(
    ~ v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5376])).

tff(c_5357,plain,(
    ! [A_700,B_701,C_702] :
      ( v4_orders_2('#skF_2'(A_700,B_701,C_702))
      | ~ r2_hidden(C_702,k2_pre_topc(A_700,B_701))
      | ~ m1_subset_1(C_702,u1_struct_0(A_700))
      | ~ m1_subset_1(B_701,k1_zfmisc_1(u1_struct_0(A_700)))
      | ~ l1_pre_topc(A_700)
      | ~ v2_pre_topc(A_700)
      | v2_struct_0(A_700) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_5359,plain,
    ( v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5142,c_5357])).

tff(c_5365,plain,
    ( v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_5359])).

tff(c_5366,plain,(
    v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5365])).

tff(c_5290,plain,(
    ! [A_682,B_683,C_684] :
      ( v7_waybel_0('#skF_2'(A_682,B_683,C_684))
      | ~ r2_hidden(C_684,k2_pre_topc(A_682,B_683))
      | ~ m1_subset_1(C_684,u1_struct_0(A_682))
      | ~ m1_subset_1(B_683,k1_zfmisc_1(u1_struct_0(A_682)))
      | ~ l1_pre_topc(A_682)
      | ~ v2_pre_topc(A_682)
      | v2_struct_0(A_682) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_5292,plain,
    ( v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5142,c_5290])).

tff(c_5298,plain,
    ( v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_5292])).

tff(c_5299,plain,(
    v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5298])).

tff(c_5379,plain,(
    ! [A_706,B_707,C_708] :
      ( l1_waybel_0('#skF_2'(A_706,B_707,C_708),A_706)
      | ~ r2_hidden(C_708,k2_pre_topc(A_706,B_707))
      | ~ m1_subset_1(C_708,u1_struct_0(A_706))
      | ~ m1_subset_1(B_707,k1_zfmisc_1(u1_struct_0(A_706)))
      | ~ l1_pre_topc(A_706)
      | ~ v2_pre_topc(A_706)
      | v2_struct_0(A_706) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_5381,plain,
    ( l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5142,c_5379])).

tff(c_5387,plain,
    ( l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_5381])).

tff(c_5388,plain,(
    l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5387])).

tff(c_5178,plain,(
    ! [C_666,A_667,B_668] :
      ( r2_hidden(C_666,k2_yellow19(A_667,B_668))
      | ~ m1_subset_1(C_666,k1_zfmisc_1(u1_struct_0(A_667)))
      | ~ r1_waybel_0(A_667,B_668,C_666)
      | ~ l1_waybel_0(B_668,A_667)
      | v2_struct_0(B_668)
      | ~ l1_struct_0(A_667)
      | v2_struct_0(A_667) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_5186,plain,(
    ! [B_668] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_668))
      | ~ r1_waybel_0('#skF_3',B_668,'#skF_4')
      | ~ l1_waybel_0(B_668,'#skF_3')
      | v2_struct_0(B_668)
      | ~ l1_struct_0('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_5178])).

tff(c_5192,plain,(
    ! [B_668] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_668))
      | ~ r1_waybel_0('#skF_3',B_668,'#skF_4')
      | ~ l1_waybel_0(B_668,'#skF_3')
      | v2_struct_0(B_668)
      | ~ l1_struct_0('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5186])).

tff(c_5193,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5192])).

tff(c_5211,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_5193])).

tff(c_5215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_5211])).

tff(c_5217,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5192])).

tff(c_5392,plain,
    ( k2_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) = a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5388,c_2])).

tff(c_5395,plain,
    ( k2_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) = a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5217,c_5392])).

tff(c_5396,plain,(
    k2_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) = a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5377,c_5395])).

tff(c_5744,plain,(
    ! [A_727,B_728,C_729] :
      ( r1_waybel_7(A_727,k2_yellow19(A_727,B_728),C_729)
      | ~ r3_waybel_9(A_727,B_728,C_729)
      | ~ m1_subset_1(C_729,u1_struct_0(A_727))
      | ~ l1_waybel_0(B_728,A_727)
      | ~ v7_waybel_0(B_728)
      | ~ v4_orders_2(B_728)
      | v2_struct_0(B_728)
      | ~ l1_pre_topc(A_727)
      | ~ v2_pre_topc(A_727)
      | v2_struct_0(A_727) ) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_5750,plain,(
    ! [C_729] :
      ( r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),C_729)
      | ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),C_729)
      | ~ m1_subset_1(C_729,u1_struct_0('#skF_3'))
      | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5396,c_5744])).

tff(c_5753,plain,(
    ! [C_729] :
      ( r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),C_729)
      | ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),C_729)
      | ~ m1_subset_1(C_729,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_5366,c_5299,c_5388,c_5750])).

tff(c_5758,plain,(
    ! [C_731] :
      ( r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),C_731)
      | ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),C_731)
      | ~ m1_subset_1(C_731,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5377,c_5753])).

tff(c_5552,plain,(
    ! [A_714,B_715,C_716] :
      ( r1_waybel_0(A_714,'#skF_2'(A_714,B_715,C_716),B_715)
      | ~ r2_hidden(C_716,k2_pre_topc(A_714,B_715))
      | ~ m1_subset_1(C_716,u1_struct_0(A_714))
      | ~ m1_subset_1(B_715,k1_zfmisc_1(u1_struct_0(A_714)))
      | ~ l1_pre_topc(A_714)
      | ~ v2_pre_topc(A_714)
      | v2_struct_0(A_714) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_5562,plain,(
    ! [C_716] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_716),'#skF_4')
      | ~ r2_hidden(C_716,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_716,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_5552])).

tff(c_5569,plain,(
    ! [C_716] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_716),'#skF_4')
      | ~ r2_hidden(C_716,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_716,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_5562])).

tff(c_5614,plain,(
    ! [C_720] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_720),'#skF_4')
      | ~ r2_hidden(C_720,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_720,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5569])).

tff(c_5216,plain,(
    ! [B_668] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_668))
      | ~ r1_waybel_0('#skF_3',B_668,'#skF_4')
      | ~ l1_waybel_0(B_668,'#skF_3')
      | v2_struct_0(B_668) ) ),
    inference(splitRight,[status(thm)],[c_5192])).

tff(c_5411,plain,
    ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5396,c_5216])).

tff(c_5450,plain,
    ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5388,c_5411])).

tff(c_5451,plain,
    ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_5377,c_5450])).

tff(c_5571,plain,(
    ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5451])).

tff(c_5617,plain,
    ( ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5614,c_5571])).

tff(c_5624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5142,c_5617])).

tff(c_5625,plain,(
    r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_5451])).

tff(c_5434,plain,
    ( ~ v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5396,c_18])).

tff(c_5474,plain,
    ( ~ v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5217,c_5388,c_5434])).

tff(c_5475,plain,(
    ~ v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5377,c_5474])).

tff(c_5417,plain,
    ( v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5396,c_22])).

tff(c_5456,plain,
    ( v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5217,c_5366,c_5299,c_5388,c_5417])).

tff(c_5457,plain,(
    v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5377,c_5456])).

tff(c_5420,plain,
    ( v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5396,c_20])).

tff(c_5459,plain,
    ( v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5217,c_5366,c_5299,c_5388,c_5420])).

tff(c_5460,plain,(
    v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5377,c_5459])).

tff(c_5431,plain,
    ( v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5396,c_16])).

tff(c_5471,plain,
    ( v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5217,c_5388,c_5431])).

tff(c_5472,plain,(
    v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5377,c_5471])).

tff(c_5425,plain,
    ( m1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5396,c_6])).

tff(c_5465,plain,
    ( m1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5217,c_5388,c_5425])).

tff(c_5466,plain,(
    m1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5377,c_5465])).

tff(c_5304,plain,(
    ! [D_89] :
      ( ~ r1_waybel_7('#skF_3',D_89,'#skF_5')
      | ~ r2_hidden('#skF_4',D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
      | ~ v13_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1(D_89,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0(D_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5142,c_88])).

tff(c_5497,plain,
    ( ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_5466,c_5304])).

tff(c_5505,plain,
    ( ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5457,c_5460,c_5472,c_5497])).

tff(c_5506,plain,
    ( ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_5475,c_5505])).

tff(c_5757,plain,(
    ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5625,c_5506])).

tff(c_5761,plain,
    ( ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5758,c_5757])).

tff(c_5764,plain,(
    ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5761])).

tff(c_5767,plain,
    ( ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5492,c_5764])).

tff(c_5771,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5142,c_5767])).

tff(c_5772,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_6106,plain,(
    ! [A_805,B_806,C_807] :
      ( r3_waybel_9(A_805,'#skF_2'(A_805,B_806,C_807),C_807)
      | ~ r2_hidden(C_807,k2_pre_topc(A_805,B_806))
      | ~ m1_subset_1(C_807,u1_struct_0(A_805))
      | ~ m1_subset_1(B_806,k1_zfmisc_1(u1_struct_0(A_805)))
      | ~ l1_pre_topc(A_805)
      | ~ v2_pre_topc(A_805)
      | v2_struct_0(A_805) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_6114,plain,(
    ! [C_807] :
      ( r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4',C_807),C_807)
      | ~ r2_hidden(C_807,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_807,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_6106])).

tff(c_6120,plain,(
    ! [C_807] :
      ( r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4',C_807),C_807)
      | ~ r2_hidden(C_807,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_807,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_6114])).

tff(c_6121,plain,(
    ! [C_807] :
      ( r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4',C_807),C_807)
      | ~ r2_hidden(C_807,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_807,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6120])).

tff(c_5920,plain,(
    ! [A_778,B_779,C_780] :
      ( ~ v2_struct_0('#skF_2'(A_778,B_779,C_780))
      | ~ r2_hidden(C_780,k2_pre_topc(A_778,B_779))
      | ~ m1_subset_1(C_780,u1_struct_0(A_778))
      | ~ m1_subset_1(B_779,k1_zfmisc_1(u1_struct_0(A_778)))
      | ~ l1_pre_topc(A_778)
      | ~ v2_pre_topc(A_778)
      | v2_struct_0(A_778) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_5922,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5772,c_5920])).

tff(c_5928,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_5922])).

tff(c_5929,plain,(
    ~ v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5928])).

tff(c_5997,plain,(
    ! [A_799,B_800,C_801] :
      ( v4_orders_2('#skF_2'(A_799,B_800,C_801))
      | ~ r2_hidden(C_801,k2_pre_topc(A_799,B_800))
      | ~ m1_subset_1(C_801,u1_struct_0(A_799))
      | ~ m1_subset_1(B_800,k1_zfmisc_1(u1_struct_0(A_799)))
      | ~ l1_pre_topc(A_799)
      | ~ v2_pre_topc(A_799)
      | v2_struct_0(A_799) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_5999,plain,
    ( v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5772,c_5997])).

tff(c_6005,plain,
    ( v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_5999])).

tff(c_6006,plain,(
    v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6005])).

tff(c_5986,plain,(
    ! [A_796,B_797,C_798] :
      ( v7_waybel_0('#skF_2'(A_796,B_797,C_798))
      | ~ r2_hidden(C_798,k2_pre_topc(A_796,B_797))
      | ~ m1_subset_1(C_798,u1_struct_0(A_796))
      | ~ m1_subset_1(B_797,k1_zfmisc_1(u1_struct_0(A_796)))
      | ~ l1_pre_topc(A_796)
      | ~ v2_pre_topc(A_796)
      | v2_struct_0(A_796) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_5988,plain,
    ( v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5772,c_5986])).

tff(c_5994,plain,
    ( v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_5988])).

tff(c_5995,plain,(
    v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5994])).

tff(c_6008,plain,(
    ! [A_802,B_803,C_804] :
      ( l1_waybel_0('#skF_2'(A_802,B_803,C_804),A_802)
      | ~ r2_hidden(C_804,k2_pre_topc(A_802,B_803))
      | ~ m1_subset_1(C_804,u1_struct_0(A_802))
      | ~ m1_subset_1(B_803,k1_zfmisc_1(u1_struct_0(A_802)))
      | ~ l1_pre_topc(A_802)
      | ~ v2_pre_topc(A_802)
      | v2_struct_0(A_802) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_6010,plain,
    ( l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5772,c_6008])).

tff(c_6016,plain,
    ( l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_6010])).

tff(c_6017,plain,(
    l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6016])).

tff(c_5808,plain,(
    ! [C_762,A_763,B_764] :
      ( r2_hidden(C_762,k2_yellow19(A_763,B_764))
      | ~ m1_subset_1(C_762,k1_zfmisc_1(u1_struct_0(A_763)))
      | ~ r1_waybel_0(A_763,B_764,C_762)
      | ~ l1_waybel_0(B_764,A_763)
      | v2_struct_0(B_764)
      | ~ l1_struct_0(A_763)
      | v2_struct_0(A_763) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_5816,plain,(
    ! [B_764] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_764))
      | ~ r1_waybel_0('#skF_3',B_764,'#skF_4')
      | ~ l1_waybel_0(B_764,'#skF_3')
      | v2_struct_0(B_764)
      | ~ l1_struct_0('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_5808])).

tff(c_5822,plain,(
    ! [B_764] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_764))
      | ~ r1_waybel_0('#skF_3',B_764,'#skF_4')
      | ~ l1_waybel_0(B_764,'#skF_3')
      | v2_struct_0(B_764)
      | ~ l1_struct_0('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5816])).

tff(c_5823,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5822])).

tff(c_5841,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_5823])).

tff(c_5845,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_5841])).

tff(c_5847,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5822])).

tff(c_6021,plain,
    ( k2_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) = a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6017,c_2])).

tff(c_6024,plain,
    ( k2_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) = a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5847,c_6021])).

tff(c_6025,plain,(
    k2_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) = a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5929,c_6024])).

tff(c_6376,plain,(
    ! [A_824,B_825,C_826] :
      ( r1_waybel_7(A_824,k2_yellow19(A_824,B_825),C_826)
      | ~ r3_waybel_9(A_824,B_825,C_826)
      | ~ m1_subset_1(C_826,u1_struct_0(A_824))
      | ~ l1_waybel_0(B_825,A_824)
      | ~ v7_waybel_0(B_825)
      | ~ v4_orders_2(B_825)
      | v2_struct_0(B_825)
      | ~ l1_pre_topc(A_824)
      | ~ v2_pre_topc(A_824)
      | v2_struct_0(A_824) ) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_6382,plain,(
    ! [C_826] :
      ( r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),C_826)
      | ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),C_826)
      | ~ m1_subset_1(C_826,u1_struct_0('#skF_3'))
      | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6025,c_6376])).

tff(c_6385,plain,(
    ! [C_826] :
      ( r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),C_826)
      | ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),C_826)
      | ~ m1_subset_1(C_826,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_6006,c_5995,c_6017,c_6382])).

tff(c_6389,plain,(
    ! [C_827] :
      ( r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),C_827)
      | ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),C_827)
      | ~ m1_subset_1(C_827,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5929,c_6385])).

tff(c_6182,plain,(
    ! [A_810,B_811,C_812] :
      ( r1_waybel_0(A_810,'#skF_2'(A_810,B_811,C_812),B_811)
      | ~ r2_hidden(C_812,k2_pre_topc(A_810,B_811))
      | ~ m1_subset_1(C_812,u1_struct_0(A_810))
      | ~ m1_subset_1(B_811,k1_zfmisc_1(u1_struct_0(A_810)))
      | ~ l1_pre_topc(A_810)
      | ~ v2_pre_topc(A_810)
      | v2_struct_0(A_810) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_6192,plain,(
    ! [C_812] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_812),'#skF_4')
      | ~ r2_hidden(C_812,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_812,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_6182])).

tff(c_6199,plain,(
    ! [C_812] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_812),'#skF_4')
      | ~ r2_hidden(C_812,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_812,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_6192])).

tff(c_6244,plain,(
    ! [C_816] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_816),'#skF_4')
      | ~ r2_hidden(C_816,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_816,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6199])).

tff(c_5848,plain,(
    ! [B_768] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_768))
      | ~ r1_waybel_0('#skF_3',B_768,'#skF_4')
      | ~ l1_waybel_0(B_768,'#skF_3')
      | v2_struct_0(B_768) ) ),
    inference(splitRight,[status(thm)],[c_5822])).

tff(c_5865,plain,(
    ! [B_768] :
      ( m1_subset_1('#skF_4',k2_yellow19('#skF_3',B_768))
      | ~ r1_waybel_0('#skF_3',B_768,'#skF_4')
      | ~ l1_waybel_0(B_768,'#skF_3')
      | v2_struct_0(B_768) ) ),
    inference(resolution,[status(thm)],[c_5848,c_60])).

tff(c_6037,plain,
    ( m1_subset_1('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6025,c_5865])).

tff(c_6076,plain,
    ( m1_subset_1('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6017,c_6037])).

tff(c_6077,plain,
    ( m1_subset_1('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_5929,c_6076])).

tff(c_6201,plain,(
    ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6077])).

tff(c_6247,plain,
    ( ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6244,c_6201])).

tff(c_6254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5772,c_6247])).

tff(c_6256,plain,(
    r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_6077])).

tff(c_5846,plain,(
    ! [B_764] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_764))
      | ~ r1_waybel_0('#skF_3',B_764,'#skF_4')
      | ~ l1_waybel_0(B_764,'#skF_3')
      | v2_struct_0(B_764) ) ),
    inference(splitRight,[status(thm)],[c_5822])).

tff(c_6040,plain,
    ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6025,c_5846])).

tff(c_6079,plain,
    ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6017,c_6040])).

tff(c_6080,plain,
    ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_5929,c_6079])).

tff(c_6325,plain,(
    r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6256,c_6080])).

tff(c_6063,plain,
    ( ~ v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6025,c_18])).

tff(c_6103,plain,
    ( ~ v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5847,c_6017,c_6063])).

tff(c_6104,plain,(
    ~ v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5929,c_6103])).

tff(c_6046,plain,
    ( v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6025,c_22])).

tff(c_6085,plain,
    ( v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5847,c_6006,c_5995,c_6017,c_6046])).

tff(c_6086,plain,(
    v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5929,c_6085])).

tff(c_6049,plain,
    ( v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6025,c_20])).

tff(c_6088,plain,
    ( v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5847,c_6006,c_5995,c_6017,c_6049])).

tff(c_6089,plain,(
    v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5929,c_6088])).

tff(c_6060,plain,
    ( v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6025,c_16])).

tff(c_6100,plain,
    ( v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5847,c_6017,c_6060])).

tff(c_6101,plain,(
    v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5929,c_6100])).

tff(c_6057,plain,
    ( m1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6025,c_6])).

tff(c_6097,plain,
    ( m1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5847,c_6017,c_6057])).

tff(c_6098,plain,(
    m1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5929,c_6097])).

tff(c_5773,plain,(
    ~ r1_waybel_7('#skF_3','#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_92,plain,(
    ! [D_89] :
      ( ~ r1_waybel_7('#skF_3',D_89,'#skF_5')
      | ~ r2_hidden('#skF_4',D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
      | ~ v13_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1(D_89,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0(D_89)
      | r1_waybel_7('#skF_3','#skF_6','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_5933,plain,(
    ! [D_89] :
      ( ~ r1_waybel_7('#skF_3',D_89,'#skF_5')
      | ~ r2_hidden('#skF_4',D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
      | ~ v13_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1(D_89,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0(D_89) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5773,c_92])).

tff(c_6126,plain,
    ( ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_6098,c_5933])).

tff(c_6134,plain,
    ( ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6086,c_6089,c_6101,c_6126])).

tff(c_6135,plain,
    ( ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_6104,c_6134])).

tff(c_6388,plain,(
    ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6325,c_6135])).

tff(c_6392,plain,
    ( ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6389,c_6388])).

tff(c_6395,plain,(
    ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_6392])).

tff(c_6398,plain,
    ( ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6121,c_6395])).

tff(c_6402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5772,c_6398])).

tff(c_6403,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_6829,plain,(
    ! [A_908,B_909,C_910] :
      ( r3_waybel_9(A_908,'#skF_2'(A_908,B_909,C_910),C_910)
      | ~ r2_hidden(C_910,k2_pre_topc(A_908,B_909))
      | ~ m1_subset_1(C_910,u1_struct_0(A_908))
      | ~ m1_subset_1(B_909,k1_zfmisc_1(u1_struct_0(A_908)))
      | ~ l1_pre_topc(A_908)
      | ~ v2_pre_topc(A_908)
      | v2_struct_0(A_908) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_6839,plain,(
    ! [C_910] :
      ( r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4',C_910),C_910)
      | ~ r2_hidden(C_910,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_910,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_6829])).

tff(c_6846,plain,(
    ! [C_910] :
      ( r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4',C_910),C_910)
      | ~ r2_hidden(C_910,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_910,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_6839])).

tff(c_6847,plain,(
    ! [C_910] :
      ( r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4',C_910),C_910)
      | ~ r2_hidden(C_910,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_910,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6846])).

tff(c_6613,plain,(
    ! [A_888,B_889,C_890] :
      ( ~ v2_struct_0('#skF_2'(A_888,B_889,C_890))
      | ~ r2_hidden(C_890,k2_pre_topc(A_888,B_889))
      | ~ m1_subset_1(C_890,u1_struct_0(A_888))
      | ~ m1_subset_1(B_889,k1_zfmisc_1(u1_struct_0(A_888)))
      | ~ l1_pre_topc(A_888)
      | ~ v2_pre_topc(A_888)
      | v2_struct_0(A_888) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_6618,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6403,c_6613])).

tff(c_6622,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_6618])).

tff(c_6623,plain,(
    ~ v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6622])).

tff(c_6645,plain,(
    ! [A_897,B_898,C_899] :
      ( v4_orders_2('#skF_2'(A_897,B_898,C_899))
      | ~ r2_hidden(C_899,k2_pre_topc(A_897,B_898))
      | ~ m1_subset_1(C_899,u1_struct_0(A_897))
      | ~ m1_subset_1(B_898,k1_zfmisc_1(u1_struct_0(A_897)))
      | ~ l1_pre_topc(A_897)
      | ~ v2_pre_topc(A_897)
      | v2_struct_0(A_897) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_6650,plain,
    ( v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6403,c_6645])).

tff(c_6654,plain,
    ( v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_6650])).

tff(c_6655,plain,(
    v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6654])).

tff(c_6634,plain,(
    ! [A_894,B_895,C_896] :
      ( v7_waybel_0('#skF_2'(A_894,B_895,C_896))
      | ~ r2_hidden(C_896,k2_pre_topc(A_894,B_895))
      | ~ m1_subset_1(C_896,u1_struct_0(A_894))
      | ~ m1_subset_1(B_895,k1_zfmisc_1(u1_struct_0(A_894)))
      | ~ l1_pre_topc(A_894)
      | ~ v2_pre_topc(A_894)
      | v2_struct_0(A_894) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_6639,plain,
    ( v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6403,c_6634])).

tff(c_6643,plain,
    ( v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_6639])).

tff(c_6644,plain,(
    v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6643])).

tff(c_6656,plain,(
    ! [A_900,B_901,C_902] :
      ( l1_waybel_0('#skF_2'(A_900,B_901,C_902),A_900)
      | ~ r2_hidden(C_902,k2_pre_topc(A_900,B_901))
      | ~ m1_subset_1(C_902,u1_struct_0(A_900))
      | ~ m1_subset_1(B_901,k1_zfmisc_1(u1_struct_0(A_900)))
      | ~ l1_pre_topc(A_900)
      | ~ v2_pre_topc(A_900)
      | v2_struct_0(A_900) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_6661,plain,
    ( l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6403,c_6656])).

tff(c_6665,plain,
    ( l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_6661])).

tff(c_6666,plain,(
    l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6665])).

tff(c_6453,plain,(
    ! [C_862,A_863,B_864] :
      ( r2_hidden(C_862,k2_yellow19(A_863,B_864))
      | ~ m1_subset_1(C_862,k1_zfmisc_1(u1_struct_0(A_863)))
      | ~ r1_waybel_0(A_863,B_864,C_862)
      | ~ l1_waybel_0(B_864,A_863)
      | v2_struct_0(B_864)
      | ~ l1_struct_0(A_863)
      | v2_struct_0(A_863) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_6461,plain,(
    ! [B_864] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_864))
      | ~ r1_waybel_0('#skF_3',B_864,'#skF_4')
      | ~ l1_waybel_0(B_864,'#skF_3')
      | v2_struct_0(B_864)
      | ~ l1_struct_0('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_6453])).

tff(c_6467,plain,(
    ! [B_864] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_864))
      | ~ r1_waybel_0('#skF_3',B_864,'#skF_4')
      | ~ l1_waybel_0(B_864,'#skF_3')
      | v2_struct_0(B_864)
      | ~ l1_struct_0('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6461])).

tff(c_6468,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6467])).

tff(c_6490,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_6468])).

tff(c_6494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_6490])).

tff(c_6496,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_6467])).

tff(c_6669,plain,
    ( k2_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) = a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6666,c_2])).

tff(c_6672,plain,
    ( k2_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) = a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6496,c_6669])).

tff(c_6673,plain,(
    k2_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) = a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6623,c_6672])).

tff(c_7010,plain,(
    ! [A_924,B_925,C_926] :
      ( r1_waybel_7(A_924,k2_yellow19(A_924,B_925),C_926)
      | ~ r3_waybel_9(A_924,B_925,C_926)
      | ~ m1_subset_1(C_926,u1_struct_0(A_924))
      | ~ l1_waybel_0(B_925,A_924)
      | ~ v7_waybel_0(B_925)
      | ~ v4_orders_2(B_925)
      | v2_struct_0(B_925)
      | ~ l1_pre_topc(A_924)
      | ~ v2_pre_topc(A_924)
      | v2_struct_0(A_924) ) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_7016,plain,(
    ! [C_926] :
      ( r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),C_926)
      | ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),C_926)
      | ~ m1_subset_1(C_926,u1_struct_0('#skF_3'))
      | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6673,c_7010])).

tff(c_7019,plain,(
    ! [C_926] :
      ( r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),C_926)
      | ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),C_926)
      | ~ m1_subset_1(C_926,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_6655,c_6644,c_6666,c_7016])).

tff(c_7021,plain,(
    ! [C_927] :
      ( r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),C_927)
      | ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),C_927)
      | ~ m1_subset_1(C_927,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6623,c_7019])).

tff(c_6674,plain,(
    ! [A_903,B_904,C_905] :
      ( r1_waybel_0(A_903,'#skF_2'(A_903,B_904,C_905),B_904)
      | ~ r2_hidden(C_905,k2_pre_topc(A_903,B_904))
      | ~ m1_subset_1(C_905,u1_struct_0(A_903))
      | ~ m1_subset_1(B_904,k1_zfmisc_1(u1_struct_0(A_903)))
      | ~ l1_pre_topc(A_903)
      | ~ v2_pre_topc(A_903)
      | v2_struct_0(A_903) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_6682,plain,(
    ! [C_905] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_905),'#skF_4')
      | ~ r2_hidden(C_905,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_905,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_6674])).

tff(c_6688,plain,(
    ! [C_905] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_905),'#skF_4')
      | ~ r2_hidden(C_905,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_905,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_6682])).

tff(c_6898,plain,(
    ! [C_916] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_916),'#skF_4')
      | ~ r2_hidden(C_916,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_916,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6688])).

tff(c_6495,plain,(
    ! [B_864] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_864))
      | ~ r1_waybel_0('#skF_3',B_864,'#skF_4')
      | ~ l1_waybel_0(B_864,'#skF_3')
      | v2_struct_0(B_864) ) ),
    inference(splitRight,[status(thm)],[c_6467])).

tff(c_6704,plain,
    ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6673,c_6495])).

tff(c_6743,plain,
    ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6666,c_6704])).

tff(c_6744,plain,
    ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_6623,c_6743])).

tff(c_6873,plain,(
    ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6744])).

tff(c_6901,plain,
    ( ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6898,c_6873])).

tff(c_6908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_6403,c_6901])).

tff(c_6909,plain,(
    r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_6744])).

tff(c_6727,plain,
    ( ~ v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6673,c_18])).

tff(c_6767,plain,
    ( ~ v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6496,c_6666,c_6727])).

tff(c_6768,plain,(
    ~ v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6623,c_6767])).

tff(c_6710,plain,
    ( v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6673,c_22])).

tff(c_6749,plain,
    ( v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6496,c_6655,c_6644,c_6666,c_6710])).

tff(c_6750,plain,(
    v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6623,c_6749])).

tff(c_6713,plain,
    ( v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6673,c_20])).

tff(c_6752,plain,
    ( v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6496,c_6655,c_6644,c_6666,c_6713])).

tff(c_6753,plain,(
    v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6623,c_6752])).

tff(c_6724,plain,
    ( v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6673,c_16])).

tff(c_6764,plain,
    ( v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6496,c_6666,c_6724])).

tff(c_6765,plain,(
    v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6623,c_6764])).

tff(c_6721,plain,
    ( m1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6673,c_6])).

tff(c_6761,plain,
    ( m1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6496,c_6666,c_6721])).

tff(c_6762,plain,(
    m1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6623,c_6761])).

tff(c_6404,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_96,plain,(
    ! [D_89] :
      ( ~ r1_waybel_7('#skF_3',D_89,'#skF_5')
      | ~ r2_hidden('#skF_4',D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
      | ~ v13_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1(D_89,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0(D_89)
      | r2_hidden('#skF_4','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_6565,plain,(
    ! [D_89] :
      ( ~ r1_waybel_7('#skF_3',D_89,'#skF_5')
      | ~ r2_hidden('#skF_4',D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
      | ~ v13_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1(D_89,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0(D_89) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6404,c_96])).

tff(c_6776,plain,
    ( ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_6762,c_6565])).

tff(c_6784,plain,
    ( ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6750,c_6753,c_6765,c_6776])).

tff(c_6785,plain,
    ( ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_6768,c_6784])).

tff(c_7006,plain,(
    ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6909,c_6785])).

tff(c_7027,plain,
    ( ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7021,c_7006])).

tff(c_7031,plain,(
    ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_7027])).

tff(c_7034,plain,
    ( ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6847,c_7031])).

tff(c_7038,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_6403,c_7034])).

tff(c_7039,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_7447,plain,(
    ! [A_1007,B_1008,C_1009] :
      ( r3_waybel_9(A_1007,'#skF_2'(A_1007,B_1008,C_1009),C_1009)
      | ~ r2_hidden(C_1009,k2_pre_topc(A_1007,B_1008))
      | ~ m1_subset_1(C_1009,u1_struct_0(A_1007))
      | ~ m1_subset_1(B_1008,k1_zfmisc_1(u1_struct_0(A_1007)))
      | ~ l1_pre_topc(A_1007)
      | ~ v2_pre_topc(A_1007)
      | v2_struct_0(A_1007) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_7457,plain,(
    ! [C_1009] :
      ( r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4',C_1009),C_1009)
      | ~ r2_hidden(C_1009,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_1009,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_7447])).

tff(c_7464,plain,(
    ! [C_1009] :
      ( r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4',C_1009),C_1009)
      | ~ r2_hidden(C_1009,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_1009,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_7457])).

tff(c_7465,plain,(
    ! [C_1009] :
      ( r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4',C_1009),C_1009)
      | ~ r2_hidden(C_1009,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_1009,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_7464])).

tff(c_7239,plain,(
    ! [A_990,B_991,C_992] :
      ( ~ v2_struct_0('#skF_2'(A_990,B_991,C_992))
      | ~ r2_hidden(C_992,k2_pre_topc(A_990,B_991))
      | ~ m1_subset_1(C_992,u1_struct_0(A_990))
      | ~ m1_subset_1(B_991,k1_zfmisc_1(u1_struct_0(A_990)))
      | ~ l1_pre_topc(A_990)
      | ~ v2_pre_topc(A_990)
      | v2_struct_0(A_990) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_7244,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_7039,c_7239])).

tff(c_7248,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_7244])).

tff(c_7249,plain,(
    ~ v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_7248])).

tff(c_7193,plain,(
    ! [A_975,B_976,C_977] :
      ( v4_orders_2('#skF_2'(A_975,B_976,C_977))
      | ~ r2_hidden(C_977,k2_pre_topc(A_975,B_976))
      | ~ m1_subset_1(C_977,u1_struct_0(A_975))
      | ~ m1_subset_1(B_976,k1_zfmisc_1(u1_struct_0(A_975)))
      | ~ l1_pre_topc(A_975)
      | ~ v2_pre_topc(A_975)
      | v2_struct_0(A_975) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_7198,plain,
    ( v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_7039,c_7193])).

tff(c_7202,plain,
    ( v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_7198])).

tff(c_7203,plain,(
    v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_7202])).

tff(c_7262,plain,(
    ! [A_996,B_997,C_998] :
      ( v7_waybel_0('#skF_2'(A_996,B_997,C_998))
      | ~ r2_hidden(C_998,k2_pre_topc(A_996,B_997))
      | ~ m1_subset_1(C_998,u1_struct_0(A_996))
      | ~ m1_subset_1(B_997,k1_zfmisc_1(u1_struct_0(A_996)))
      | ~ l1_pre_topc(A_996)
      | ~ v2_pre_topc(A_996)
      | v2_struct_0(A_996) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_7267,plain,
    ( v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_7039,c_7262])).

tff(c_7271,plain,
    ( v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_7267])).

tff(c_7272,plain,(
    v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_7271])).

tff(c_7275,plain,(
    ! [A_999,B_1000,C_1001] :
      ( l1_waybel_0('#skF_2'(A_999,B_1000,C_1001),A_999)
      | ~ r2_hidden(C_1001,k2_pre_topc(A_999,B_1000))
      | ~ m1_subset_1(C_1001,u1_struct_0(A_999))
      | ~ m1_subset_1(B_1000,k1_zfmisc_1(u1_struct_0(A_999)))
      | ~ l1_pre_topc(A_999)
      | ~ v2_pre_topc(A_999)
      | v2_struct_0(A_999) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_7280,plain,
    ( l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_7039,c_7275])).

tff(c_7284,plain,
    ( l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_7280])).

tff(c_7285,plain,(
    l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_7284])).

tff(c_7108,plain,(
    ! [C_963,A_964,B_965] :
      ( r2_hidden(C_963,k2_yellow19(A_964,B_965))
      | ~ m1_subset_1(C_963,k1_zfmisc_1(u1_struct_0(A_964)))
      | ~ r1_waybel_0(A_964,B_965,C_963)
      | ~ l1_waybel_0(B_965,A_964)
      | v2_struct_0(B_965)
      | ~ l1_struct_0(A_964)
      | v2_struct_0(A_964) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_7116,plain,(
    ! [B_965] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_965))
      | ~ r1_waybel_0('#skF_3',B_965,'#skF_4')
      | ~ l1_waybel_0(B_965,'#skF_3')
      | v2_struct_0(B_965)
      | ~ l1_struct_0('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_7108])).

tff(c_7122,plain,(
    ! [B_965] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_965))
      | ~ r1_waybel_0('#skF_3',B_965,'#skF_4')
      | ~ l1_waybel_0(B_965,'#skF_3')
      | v2_struct_0(B_965)
      | ~ l1_struct_0('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_7116])).

tff(c_7123,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_7122])).

tff(c_7126,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_7123])).

tff(c_7130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_7126])).

tff(c_7132,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_7122])).

tff(c_7288,plain,
    ( k2_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) = a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_7285,c_2])).

tff(c_7291,plain,
    ( k2_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) = a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7132,c_7288])).

tff(c_7292,plain,(
    k2_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) = a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_7249,c_7291])).

tff(c_7636,plain,(
    ! [A_1020,B_1021,C_1022] :
      ( r1_waybel_7(A_1020,k2_yellow19(A_1020,B_1021),C_1022)
      | ~ r3_waybel_9(A_1020,B_1021,C_1022)
      | ~ m1_subset_1(C_1022,u1_struct_0(A_1020))
      | ~ l1_waybel_0(B_1021,A_1020)
      | ~ v7_waybel_0(B_1021)
      | ~ v4_orders_2(B_1021)
      | v2_struct_0(B_1021)
      | ~ l1_pre_topc(A_1020)
      | ~ v2_pre_topc(A_1020)
      | v2_struct_0(A_1020) ) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_7642,plain,(
    ! [C_1022] :
      ( r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),C_1022)
      | ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),C_1022)
      | ~ m1_subset_1(C_1022,u1_struct_0('#skF_3'))
      | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7292,c_7636])).

tff(c_7645,plain,(
    ! [C_1022] :
      ( r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),C_1022)
      | ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),C_1022)
      | ~ m1_subset_1(C_1022,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_7203,c_7272,c_7285,c_7642])).

tff(c_7654,plain,(
    ! [C_1024] :
      ( r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),C_1024)
      | ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),C_1024)
      | ~ m1_subset_1(C_1024,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_7249,c_7645])).

tff(c_7373,plain,(
    ! [A_1002,B_1003,C_1004] :
      ( r1_waybel_0(A_1002,'#skF_2'(A_1002,B_1003,C_1004),B_1003)
      | ~ r2_hidden(C_1004,k2_pre_topc(A_1002,B_1003))
      | ~ m1_subset_1(C_1004,u1_struct_0(A_1002))
      | ~ m1_subset_1(B_1003,k1_zfmisc_1(u1_struct_0(A_1002)))
      | ~ l1_pre_topc(A_1002)
      | ~ v2_pre_topc(A_1002)
      | v2_struct_0(A_1002) ) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_7381,plain,(
    ! [C_1004] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_1004),'#skF_4')
      | ~ r2_hidden(C_1004,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_1004,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_7373])).

tff(c_7387,plain,(
    ! [C_1004] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_1004),'#skF_4')
      | ~ r2_hidden(C_1004,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_1004,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_7381])).

tff(c_7509,plain,(
    ! [C_1013] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_1013),'#skF_4')
      | ~ r2_hidden(C_1013,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_1013,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_7387])).

tff(c_7134,plain,(
    ! [B_966] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_966))
      | ~ r1_waybel_0('#skF_3',B_966,'#skF_4')
      | ~ l1_waybel_0(B_966,'#skF_3')
      | v2_struct_0(B_966) ) ),
    inference(splitRight,[status(thm)],[c_7122])).

tff(c_7151,plain,(
    ! [B_966] :
      ( m1_subset_1('#skF_4',k2_yellow19('#skF_3',B_966))
      | ~ r1_waybel_0('#skF_3',B_966,'#skF_4')
      | ~ l1_waybel_0(B_966,'#skF_3')
      | v2_struct_0(B_966) ) ),
    inference(resolution,[status(thm)],[c_7134,c_60])).

tff(c_7304,plain,
    ( m1_subset_1('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7292,c_7151])).

tff(c_7343,plain,
    ( m1_subset_1('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7285,c_7304])).

tff(c_7344,plain,
    ( m1_subset_1('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_7249,c_7343])).

tff(c_7466,plain,(
    ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_7344])).

tff(c_7512,plain,
    ( ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7509,c_7466])).

tff(c_7519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_7039,c_7512])).

tff(c_7521,plain,(
    r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_7344])).

tff(c_7131,plain,(
    ! [B_965] :
      ( r2_hidden('#skF_4',k2_yellow19('#skF_3',B_965))
      | ~ r1_waybel_0('#skF_3',B_965,'#skF_4')
      | ~ l1_waybel_0(B_965,'#skF_3')
      | v2_struct_0(B_965) ) ),
    inference(splitRight,[status(thm)],[c_7122])).

tff(c_7307,plain,
    ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7292,c_7131])).

tff(c_7346,plain,
    ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7285,c_7307])).

tff(c_7347,plain,
    ( r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_7249,c_7346])).

tff(c_7590,plain,(
    r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7521,c_7347])).

tff(c_7330,plain,
    ( ~ v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7292,c_18])).

tff(c_7370,plain,
    ( ~ v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7132,c_7285,c_7330])).

tff(c_7371,plain,(
    ~ v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_7249,c_7370])).

tff(c_7313,plain,
    ( v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7292,c_22])).

tff(c_7352,plain,
    ( v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7132,c_7203,c_7272,c_7285,c_7313])).

tff(c_7353,plain,(
    v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_7249,c_7352])).

tff(c_7316,plain,
    ( v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7292,c_20])).

tff(c_7355,plain,
    ( v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7132,c_7203,c_7272,c_7285,c_7316])).

tff(c_7356,plain,(
    v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_7249,c_7355])).

tff(c_7327,plain,
    ( v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7292,c_16])).

tff(c_7367,plain,
    ( v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7132,c_7285,c_7327])).

tff(c_7368,plain,(
    v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_7249,c_7367])).

tff(c_7321,plain,
    ( m1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7292,c_6])).

tff(c_7361,plain,
    ( m1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7132,c_7285,c_7321])).

tff(c_7362,plain,(
    m1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_7249,c_7361])).

tff(c_7040,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_116,plain,(
    ! [D_89] :
      ( ~ r1_waybel_7('#skF_3',D_89,'#skF_5')
      | ~ r2_hidden('#skF_4',D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
      | ~ v13_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1(D_89,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0(D_89)
      | ~ v1_xboole_0('#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_7084,plain,(
    ! [D_89] :
      ( ~ r1_waybel_7('#skF_3',D_89,'#skF_5')
      | ~ r2_hidden('#skF_4',D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
      | ~ v13_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0(D_89,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1(D_89,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0(D_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7040,c_116])).

tff(c_7397,plain,
    ( ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v13_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_7362,c_7084])).

tff(c_7403,plain,
    ( ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | v1_xboole_0(a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7353,c_7356,c_7368,c_7397])).

tff(c_7404,plain,
    ( ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_7371,c_7403])).

tff(c_7653,plain,(
    ~ r1_waybel_7('#skF_3',a_2_1_yellow19('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7590,c_7404])).

tff(c_7657,plain,
    ( ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7654,c_7653])).

tff(c_7660,plain,(
    ~ r3_waybel_9('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_7657])).

tff(c_7663,plain,
    ( ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7465,c_7660])).

tff(c_7667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_7039,c_7663])).

%------------------------------------------------------------------------------
