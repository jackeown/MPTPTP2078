%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1981+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:45 EST 2020

% Result     : Theorem 26.68s
% Output     : CNFRefutation 26.83s
% Verified   : 
% Statistics : Number of formulae       :  283 (26627 expanded)
%              Number of leaves         :   65 (9527 expanded)
%              Depth                    :   26
%              Number of atoms          : 1178 (181466 expanded)
%              Number of equality atoms :   22 (3638 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_waybel_7 > v2_waybel_7 > v2_waybel_0 > v1_waybel_0 > v1_subset_1 > v13_waybel_0 > v12_waybel_0 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v7_struct_0 > v5_orders_2 > v4_orders_2 > v3_yellow_0 > v3_orders_2 > v2_yellow_0 > v2_waybel_1 > v2_struct_0 > v2_lattice3 > v1_yellow_0 > v1_xboole_0 > v1_lattice3 > v11_waybel_1 > v10_waybel_1 > l1_orders_2 > k6_domain_1 > k5_waybel_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_tarski > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v11_waybel_1,type,(
    v11_waybel_1: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r1_subset_1,type,(
    r1_subset_1: ( $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v3_yellow_0,type,(
    v3_yellow_0: $i > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v10_waybel_1,type,(
    v10_waybel_1: $i > $o )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(v2_waybel_1,type,(
    v2_waybel_1: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v12_waybel_0,type,(
    v12_waybel_0: ( $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v2_yellow_0,type,(
    v2_yellow_0: $i > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k5_waybel_0,type,(
    k5_waybel_0: ( $i * $i ) > $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(v1_waybel_0,type,(
    v1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(v3_waybel_7,type,(
    v3_waybel_7: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v2_waybel_7,type,(
    v2_waybel_7: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_351,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v7_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v11_waybel_1(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(A))
              & v2_waybel_0(B,A)
              & v13_waybel_0(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ? [C] :
                ( ~ v1_xboole_0(C)
                & v2_waybel_0(C,A)
                & v13_waybel_0(C,A)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                & r1_tarski(B,C)
                & v3_waybel_7(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_waybel_7)).

tff(f_249,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_72,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_279,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k5_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_waybel_0)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v11_waybel_1(A) )
       => ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & v3_yellow_0(A)
          & v2_waybel_1(A)
          & v10_waybel_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc8_waybel_1)).

tff(f_243,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v2_waybel_1(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_waybel_0(B,A)
            & v12_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ! [C] :
              ( ( ~ v1_xboole_0(C)
                & v2_waybel_0(C,A)
                & v13_waybel_0(C,A)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
             => ~ ( r1_subset_1(B,C)
                  & ! [D] :
                      ( ( ~ v1_xboole_0(D)
                        & v2_waybel_0(D,A)
                        & v13_waybel_0(D,A)
                        & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                     => ~ ( v2_waybel_7(D,A)
                          & r1_tarski(C,D)
                          & r1_subset_1(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_waybel_7)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v3_yellow_0(A)
       => ( v1_yellow_0(A)
          & v2_yellow_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_yellow_0)).

tff(f_120,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_159,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => k5_waybel_0(A,k3_yellow_0(A)) = k6_domain_1(u1_struct_0(A),k3_yellow_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_4)).

tff(f_274,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v4_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => v12_waybel_0(k5_waybel_0(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_waybel_0)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v1_xboole_0(k5_waybel_0(A,B))
        & v1_waybel_0(k5_waybel_0(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_waybel_0)).

tff(f_307,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,A)
            & v13_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v1_subset_1(B,u1_struct_0(A))
          <=> ~ r2_hidden(k3_yellow_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

tff(f_267,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_130,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_140,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
       => r1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_subset_1)).

tff(f_144,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_189,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v11_waybel_1(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,A)
            & v13_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( ( v1_subset_1(B,u1_struct_0(A))
              & v2_waybel_7(B,A) )
          <=> v3_waybel_7(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_waybel_7)).

tff(c_42,plain,(
    ! [A_12] : m1_subset_1('#skF_3'(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_108,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_351])).

tff(c_82,plain,(
    ! [A_44,B_45] :
      ( r2_hidden(A_44,B_45)
      | v1_xboole_0(B_45)
      | ~ m1_subset_1(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_28,plain,(
    ! [C_8] : r2_hidden(C_8,k1_tarski(C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_127,plain,(
    ! [B_66,A_67] :
      ( ~ v1_xboole_0(B_66)
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_131,plain,(
    ! [C_8] : ~ v1_xboole_0(k1_tarski(C_8)) ),
    inference(resolution,[status(thm)],[c_28,c_127])).

tff(c_122,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_351])).

tff(c_120,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_351])).

tff(c_118,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_351])).

tff(c_110,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_351])).

tff(c_112,plain,(
    v2_lattice3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_351])).

tff(c_915,plain,(
    ! [A_203,B_204] :
      ( m1_subset_1(k5_waybel_0(A_203,B_204),k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ m1_subset_1(B_204,u1_struct_0(A_203))
      | ~ l1_orders_2(A_203)
      | v2_struct_0(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_98,plain,(
    ! [C_63] :
      ( ~ v3_waybel_7(C_63,'#skF_6')
      | ~ r1_tarski('#skF_7',C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v13_waybel_0(C_63,'#skF_6')
      | ~ v2_waybel_0(C_63,'#skF_6')
      | v1_xboole_0(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_351])).

tff(c_924,plain,(
    ! [B_204] :
      ( ~ v3_waybel_7(k5_waybel_0('#skF_6',B_204),'#skF_6')
      | ~ r1_tarski('#skF_7',k5_waybel_0('#skF_6',B_204))
      | ~ v13_waybel_0(k5_waybel_0('#skF_6',B_204),'#skF_6')
      | ~ v2_waybel_0(k5_waybel_0('#skF_6',B_204),'#skF_6')
      | v1_xboole_0(k5_waybel_0('#skF_6',B_204))
      | ~ m1_subset_1(B_204,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_915,c_98])).

tff(c_929,plain,(
    ! [B_204] :
      ( ~ v3_waybel_7(k5_waybel_0('#skF_6',B_204),'#skF_6')
      | ~ r1_tarski('#skF_7',k5_waybel_0('#skF_6',B_204))
      | ~ v13_waybel_0(k5_waybel_0('#skF_6',B_204),'#skF_6')
      | ~ v2_waybel_0(k5_waybel_0('#skF_6',B_204),'#skF_6')
      | v1_xboole_0(k5_waybel_0('#skF_6',B_204))
      | ~ m1_subset_1(B_204,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_924])).

tff(c_1077,plain,(
    v2_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_929])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v2_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1080,plain,
    ( ~ v2_lattice3('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_1077,c_2])).

tff(c_1084,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_112,c_1080])).

tff(c_1086,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_929])).

tff(c_116,plain,(
    v11_waybel_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_351])).

tff(c_10,plain,(
    ! [A_3] :
      ( v2_waybel_1(A_3)
      | ~ v11_waybel_1(A_3)
      | v2_struct_0(A_3)
      | ~ l1_orders_2(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_114,plain,(
    v1_lattice3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_351])).

tff(c_104,plain,(
    v2_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_351])).

tff(c_102,plain,(
    v13_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_351])).

tff(c_100,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_351])).

tff(c_4317,plain,(
    ! [B_361,A_362,C_363] :
      ( r1_subset_1(B_361,'#skF_4'(A_362,B_361,C_363))
      | ~ r1_subset_1(B_361,C_363)
      | ~ m1_subset_1(C_363,k1_zfmisc_1(u1_struct_0(A_362)))
      | ~ v13_waybel_0(C_363,A_362)
      | ~ v2_waybel_0(C_363,A_362)
      | v1_xboole_0(C_363)
      | ~ m1_subset_1(B_361,k1_zfmisc_1(u1_struct_0(A_362)))
      | ~ v12_waybel_0(B_361,A_362)
      | ~ v1_waybel_0(B_361,A_362)
      | v1_xboole_0(B_361)
      | ~ l1_orders_2(A_362)
      | ~ v2_lattice3(A_362)
      | ~ v1_lattice3(A_362)
      | ~ v2_waybel_1(A_362)
      | ~ v5_orders_2(A_362)
      | ~ v4_orders_2(A_362)
      | ~ v3_orders_2(A_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_4332,plain,(
    ! [B_361] :
      ( r1_subset_1(B_361,'#skF_4'('#skF_6',B_361,'#skF_7'))
      | ~ r1_subset_1(B_361,'#skF_7')
      | ~ v13_waybel_0('#skF_7','#skF_6')
      | ~ v2_waybel_0('#skF_7','#skF_6')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(B_361,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v12_waybel_0(B_361,'#skF_6')
      | ~ v1_waybel_0(B_361,'#skF_6')
      | v1_xboole_0(B_361)
      | ~ l1_orders_2('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v1_lattice3('#skF_6')
      | ~ v2_waybel_1('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_100,c_4317])).

tff(c_4345,plain,(
    ! [B_361] :
      ( r1_subset_1(B_361,'#skF_4'('#skF_6',B_361,'#skF_7'))
      | ~ r1_subset_1(B_361,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(B_361,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v12_waybel_0(B_361,'#skF_6')
      | ~ v1_waybel_0(B_361,'#skF_6')
      | v1_xboole_0(B_361)
      | ~ v2_waybel_1('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_120,c_118,c_114,c_112,c_110,c_104,c_102,c_4332])).

tff(c_4346,plain,(
    ! [B_361] :
      ( r1_subset_1(B_361,'#skF_4'('#skF_6',B_361,'#skF_7'))
      | ~ r1_subset_1(B_361,'#skF_7')
      | ~ m1_subset_1(B_361,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v12_waybel_0(B_361,'#skF_6')
      | ~ v1_waybel_0(B_361,'#skF_6')
      | v1_xboole_0(B_361)
      | ~ v2_waybel_1('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_4345])).

tff(c_4351,plain,(
    ~ v2_waybel_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_4346])).

tff(c_4354,plain,
    ( ~ v11_waybel_1('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_4351])).

tff(c_4357,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_116,c_4354])).

tff(c_4359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1086,c_4357])).

tff(c_4361,plain,(
    v2_waybel_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_4346])).

tff(c_38,plain,(
    ! [A_9] :
      ( m1_subset_1(k3_yellow_0(A_9),u1_struct_0(A_9))
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_232,plain,(
    ! [A_93] :
      ( v3_yellow_0(A_93)
      | ~ v11_waybel_1(A_93)
      | v2_struct_0(A_93)
      | ~ l1_orders_2(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_2] :
      ( v1_yellow_0(A_2)
      | ~ v3_yellow_0(A_2)
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_262,plain,(
    ! [A_100] :
      ( v1_yellow_0(A_100)
      | ~ v11_waybel_1(A_100)
      | v2_struct_0(A_100)
      | ~ l1_orders_2(A_100) ) ),
    inference(resolution,[status(thm)],[c_232,c_6])).

tff(c_354,plain,(
    ! [A_123] :
      ( ~ v2_lattice3(A_123)
      | v1_yellow_0(A_123)
      | ~ v11_waybel_1(A_123)
      | ~ l1_orders_2(A_123) ) ),
    inference(resolution,[status(thm)],[c_262,c_2])).

tff(c_357,plain,
    ( v1_yellow_0('#skF_6')
    | ~ v11_waybel_1('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_112,c_354])).

tff(c_360,plain,(
    v1_yellow_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_116,c_357])).

tff(c_369,plain,(
    ! [A_128,B_129] :
      ( k6_domain_1(A_128,B_129) = k1_tarski(B_129)
      | ~ m1_subset_1(B_129,A_128)
      | v1_xboole_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_390,plain,(
    ! [A_9] :
      ( k6_domain_1(u1_struct_0(A_9),k3_yellow_0(A_9)) = k1_tarski(k3_yellow_0(A_9))
      | v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_orders_2(A_9) ) ),
    inference(resolution,[status(thm)],[c_38,c_369])).

tff(c_1647,plain,(
    ! [A_250] :
      ( k6_domain_1(u1_struct_0(A_250),k3_yellow_0(A_250)) = k5_waybel_0(A_250,k3_yellow_0(A_250))
      | ~ l1_orders_2(A_250)
      | ~ v1_yellow_0(A_250)
      | ~ v5_orders_2(A_250)
      | ~ v4_orders_2(A_250)
      | ~ v3_orders_2(A_250)
      | v2_struct_0(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_27080,plain,(
    ! [A_1056] :
      ( k5_waybel_0(A_1056,k3_yellow_0(A_1056)) = k1_tarski(k3_yellow_0(A_1056))
      | ~ l1_orders_2(A_1056)
      | ~ v1_yellow_0(A_1056)
      | ~ v5_orders_2(A_1056)
      | ~ v4_orders_2(A_1056)
      | ~ v3_orders_2(A_1056)
      | v2_struct_0(A_1056)
      | v1_xboole_0(u1_struct_0(A_1056))
      | ~ l1_orders_2(A_1056) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_1647])).

tff(c_267,plain,(
    ! [C_101,B_102,A_103] :
      ( ~ v1_xboole_0(C_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(C_101))
      | ~ r2_hidden(A_103,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_273,plain,(
    ! [A_103] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_6'))
      | ~ r2_hidden(A_103,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_100,c_267])).

tff(c_275,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_27153,plain,
    ( k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')) = k1_tarski(k3_yellow_0('#skF_6'))
    | ~ v1_yellow_0('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_27080,c_275])).

tff(c_27163,plain,
    ( k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')) = k1_tarski(k3_yellow_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_122,c_120,c_118,c_360,c_27153])).

tff(c_27164,plain,(
    k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')) = k1_tarski(k3_yellow_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_1086,c_27163])).

tff(c_44,plain,(
    ! [A_14,B_15] :
      ( v12_waybel_0(k5_waybel_0(A_14,B_15),A_14)
      | ~ m1_subset_1(B_15,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14)
      | ~ v4_orders_2(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_27218,plain,
    ( v12_waybel_0(k1_tarski(k3_yellow_0('#skF_6')),'#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_27164,c_44])).

tff(c_27283,plain,
    ( v12_waybel_0(k1_tarski(k3_yellow_0('#skF_6')),'#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_110,c_27218])).

tff(c_27284,plain,
    ( v12_waybel_0(k1_tarski(k3_yellow_0('#skF_6')),'#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_1086,c_27283])).

tff(c_27297,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_27284])).

tff(c_27300,plain,(
    ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_27297])).

tff(c_27304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_27300])).

tff(c_27306,plain,(
    m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_27284])).

tff(c_46,plain,(
    ! [A_16,B_17] :
      ( v1_waybel_0(k5_waybel_0(A_16,B_17),A_16)
      | ~ m1_subset_1(B_17,u1_struct_0(A_16))
      | ~ l1_orders_2(A_16)
      | ~ v3_orders_2(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_27224,plain,
    ( v1_waybel_0(k1_tarski(k3_yellow_0('#skF_6')),'#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_27164,c_46])).

tff(c_27288,plain,
    ( v1_waybel_0(k1_tarski(k3_yellow_0('#skF_6')),'#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_110,c_27224])).

tff(c_27289,plain,
    ( v1_waybel_0(k1_tarski(k3_yellow_0('#skF_6')),'#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_1086,c_27288])).

tff(c_27496,plain,(
    v1_waybel_0(k1_tarski(k3_yellow_0('#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27306,c_27289])).

tff(c_27305,plain,(
    v12_waybel_0(k1_tarski(k3_yellow_0('#skF_6')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_27284])).

tff(c_40,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k5_waybel_0(A_10,B_11),k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ m1_subset_1(B_11,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_27227,plain,
    ( m1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_27164,c_40])).

tff(c_27291,plain,
    ( m1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_27227])).

tff(c_27292,plain,
    ( m1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_1086,c_27291])).

tff(c_28806,plain,(
    m1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27306,c_27292])).

tff(c_4365,plain,(
    ! [C_364,A_365,B_366] :
      ( r1_tarski(C_364,'#skF_4'(A_365,B_366,C_364))
      | ~ r1_subset_1(B_366,C_364)
      | ~ m1_subset_1(C_364,k1_zfmisc_1(u1_struct_0(A_365)))
      | ~ v13_waybel_0(C_364,A_365)
      | ~ v2_waybel_0(C_364,A_365)
      | v1_xboole_0(C_364)
      | ~ m1_subset_1(B_366,k1_zfmisc_1(u1_struct_0(A_365)))
      | ~ v12_waybel_0(B_366,A_365)
      | ~ v1_waybel_0(B_366,A_365)
      | v1_xboole_0(B_366)
      | ~ l1_orders_2(A_365)
      | ~ v2_lattice3(A_365)
      | ~ v1_lattice3(A_365)
      | ~ v2_waybel_1(A_365)
      | ~ v5_orders_2(A_365)
      | ~ v4_orders_2(A_365)
      | ~ v3_orders_2(A_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_4380,plain,(
    ! [B_366] :
      ( r1_tarski('#skF_7','#skF_4'('#skF_6',B_366,'#skF_7'))
      | ~ r1_subset_1(B_366,'#skF_7')
      | ~ v13_waybel_0('#skF_7','#skF_6')
      | ~ v2_waybel_0('#skF_7','#skF_6')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(B_366,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v12_waybel_0(B_366,'#skF_6')
      | ~ v1_waybel_0(B_366,'#skF_6')
      | v1_xboole_0(B_366)
      | ~ l1_orders_2('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v1_lattice3('#skF_6')
      | ~ v2_waybel_1('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_100,c_4365])).

tff(c_4393,plain,(
    ! [B_366] :
      ( r1_tarski('#skF_7','#skF_4'('#skF_6',B_366,'#skF_7'))
      | ~ r1_subset_1(B_366,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(B_366,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v12_waybel_0(B_366,'#skF_6')
      | ~ v1_waybel_0(B_366,'#skF_6')
      | v1_xboole_0(B_366) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_120,c_118,c_4361,c_114,c_112,c_110,c_104,c_102,c_4380])).

tff(c_4429,plain,(
    ! [B_370] :
      ( r1_tarski('#skF_7','#skF_4'('#skF_6',B_370,'#skF_7'))
      | ~ r1_subset_1(B_370,'#skF_7')
      | ~ m1_subset_1(B_370,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v12_waybel_0(B_370,'#skF_6')
      | ~ v1_waybel_0(B_370,'#skF_6')
      | v1_xboole_0(B_370) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_4393])).

tff(c_4436,plain,(
    ! [B_11] :
      ( r1_tarski('#skF_7','#skF_4'('#skF_6',k5_waybel_0('#skF_6',B_11),'#skF_7'))
      | ~ r1_subset_1(k5_waybel_0('#skF_6',B_11),'#skF_7')
      | ~ v12_waybel_0(k5_waybel_0('#skF_6',B_11),'#skF_6')
      | ~ v1_waybel_0(k5_waybel_0('#skF_6',B_11),'#skF_6')
      | v1_xboole_0(k5_waybel_0('#skF_6',B_11))
      | ~ m1_subset_1(B_11,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_4429])).

tff(c_4459,plain,(
    ! [B_11] :
      ( r1_tarski('#skF_7','#skF_4'('#skF_6',k5_waybel_0('#skF_6',B_11),'#skF_7'))
      | ~ r1_subset_1(k5_waybel_0('#skF_6',B_11),'#skF_7')
      | ~ v12_waybel_0(k5_waybel_0('#skF_6',B_11),'#skF_6')
      | ~ v1_waybel_0(k5_waybel_0('#skF_6',B_11),'#skF_6')
      | v1_xboole_0(k5_waybel_0('#skF_6',B_11))
      | ~ m1_subset_1(B_11,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_4436])).

tff(c_28796,plain,(
    ! [B_1074] :
      ( r1_tarski('#skF_7','#skF_4'('#skF_6',k5_waybel_0('#skF_6',B_1074),'#skF_7'))
      | ~ r1_subset_1(k5_waybel_0('#skF_6',B_1074),'#skF_7')
      | ~ v12_waybel_0(k5_waybel_0('#skF_6',B_1074),'#skF_6')
      | ~ v1_waybel_0(k5_waybel_0('#skF_6',B_1074),'#skF_6')
      | v1_xboole_0(k5_waybel_0('#skF_6',B_1074))
      | ~ m1_subset_1(B_1074,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1086,c_4459])).

tff(c_28799,plain,
    ( r1_tarski('#skF_7','#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'))
    | ~ r1_subset_1(k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')),'#skF_7')
    | ~ v12_waybel_0(k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')),'#skF_6')
    | ~ v1_waybel_0(k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')),'#skF_6')
    | v1_xboole_0(k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')))
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_27164,c_28796])).

tff(c_28803,plain,
    ( r1_tarski('#skF_7','#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'))
    | ~ r1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),'#skF_7')
    | v1_xboole_0(k1_tarski(k3_yellow_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27306,c_27164,c_27496,c_27164,c_27305,c_27164,c_27164,c_28799])).

tff(c_28804,plain,
    ( r1_tarski('#skF_7','#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'))
    | ~ r1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_28803])).

tff(c_28935,plain,(
    ~ r1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_28804])).

tff(c_106,plain,(
    v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_351])).

tff(c_2204,plain,(
    ! [A_278,B_279] :
      ( ~ r2_hidden(k3_yellow_0(A_278),B_279)
      | ~ v1_subset_1(B_279,u1_struct_0(A_278))
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ v13_waybel_0(B_279,A_278)
      | ~ v2_waybel_0(B_279,A_278)
      | v1_xboole_0(B_279)
      | ~ l1_orders_2(A_278)
      | ~ v1_yellow_0(A_278)
      | ~ v5_orders_2(A_278)
      | ~ v4_orders_2(A_278)
      | ~ v3_orders_2(A_278)
      | v2_struct_0(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_307])).

tff(c_2225,plain,
    ( ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7')
    | ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ v13_waybel_0('#skF_7','#skF_6')
    | ~ v2_waybel_0('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v1_yellow_0('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_2204])).

tff(c_2240,plain,
    ( ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7')
    | v1_xboole_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_120,c_118,c_360,c_110,c_104,c_102,c_106,c_2225])).

tff(c_2241,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_1086,c_108,c_2240])).

tff(c_2245,plain,
    ( v1_xboole_0('#skF_7')
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_82,c_2241])).

tff(c_2248,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_2245])).

tff(c_176,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_5'(A_83,B_84),B_84)
      | r1_xboole_0(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_26,plain,(
    ! [C_8,A_4] :
      ( C_8 = A_4
      | ~ r2_hidden(C_8,k1_tarski(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_188,plain,(
    ! [A_83,A_4] :
      ( '#skF_5'(A_83,k1_tarski(A_4)) = A_4
      | r1_xboole_0(A_83,k1_tarski(A_4)) ) ),
    inference(resolution,[status(thm)],[c_176,c_26])).

tff(c_424,plain,(
    ! [A_134,B_135] :
      ( r1_subset_1(A_134,B_135)
      | ~ r1_xboole_0(A_134,B_135)
      | v1_xboole_0(B_135)
      | v1_xboole_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_433,plain,(
    ! [A_83,A_4] :
      ( r1_subset_1(A_83,k1_tarski(A_4))
      | v1_xboole_0(k1_tarski(A_4))
      | v1_xboole_0(A_83)
      | '#skF_5'(A_83,k1_tarski(A_4)) = A_4 ) ),
    inference(resolution,[status(thm)],[c_188,c_424])).

tff(c_487,plain,(
    ! [A_144,A_145] :
      ( r1_subset_1(A_144,k1_tarski(A_145))
      | v1_xboole_0(A_144)
      | '#skF_5'(A_144,k1_tarski(A_145)) = A_145 ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_433])).

tff(c_56,plain,(
    ! [B_23,A_22] :
      ( r1_subset_1(B_23,A_22)
      | ~ r1_subset_1(A_22,B_23)
      | v1_xboole_0(B_23)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_489,plain,(
    ! [A_145,A_144] :
      ( r1_subset_1(k1_tarski(A_145),A_144)
      | v1_xboole_0(k1_tarski(A_145))
      | v1_xboole_0(A_144)
      | '#skF_5'(A_144,k1_tarski(A_145)) = A_145 ) ),
    inference(resolution,[status(thm)],[c_487,c_56])).

tff(c_492,plain,(
    ! [A_145,A_144] :
      ( r1_subset_1(k1_tarski(A_145),A_144)
      | v1_xboole_0(A_144)
      | '#skF_5'(A_144,k1_tarski(A_145)) = A_145 ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_489])).

tff(c_28938,plain,
    ( v1_xboole_0('#skF_7')
    | '#skF_5'('#skF_7',k1_tarski(k3_yellow_0('#skF_6'))) = k3_yellow_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_492,c_28935])).

tff(c_28944,plain,(
    '#skF_5'('#skF_7',k1_tarski(k3_yellow_0('#skF_6'))) = k3_yellow_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_28938])).

tff(c_242,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_5'(A_95,B_96),A_95)
      | r1_xboole_0(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_58,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,B_25)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_253,plain,(
    ! [A_95,B_96] :
      ( m1_subset_1('#skF_5'(A_95,B_96),A_95)
      | r1_xboole_0(A_95,B_96) ) ),
    inference(resolution,[status(thm)],[c_242,c_58])).

tff(c_29169,plain,
    ( m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7')
    | r1_xboole_0('#skF_7',k1_tarski(k3_yellow_0('#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_28944,c_253])).

tff(c_29225,plain,(
    r1_xboole_0('#skF_7',k1_tarski(k3_yellow_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2248,c_29169])).

tff(c_52,plain,(
    ! [A_20,B_21] :
      ( r1_subset_1(A_20,B_21)
      | ~ r1_xboole_0(A_20,B_21)
      | v1_xboole_0(B_21)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_29233,plain,
    ( r1_subset_1('#skF_7',k1_tarski(k3_yellow_0('#skF_6')))
    | v1_xboole_0(k1_tarski(k3_yellow_0('#skF_6')))
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_29225,c_52])).

tff(c_29238,plain,(
    r1_subset_1('#skF_7',k1_tarski(k3_yellow_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_131,c_29233])).

tff(c_88,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_5'(A_46,B_47),A_46)
      | r1_xboole_0(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_365,plain,(
    ! [A_126,B_127] :
      ( '#skF_5'(k1_tarski(A_126),B_127) = A_126
      | r1_xboole_0(k1_tarski(A_126),B_127) ) ),
    inference(resolution,[status(thm)],[c_242,c_26])).

tff(c_84,plain,(
    ! [A_46,B_47,C_50] :
      ( ~ r1_xboole_0(A_46,B_47)
      | ~ r2_hidden(C_50,B_47)
      | ~ r2_hidden(C_50,A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_606,plain,(
    ! [C_164,B_165,A_166] :
      ( ~ r2_hidden(C_164,B_165)
      | ~ r2_hidden(C_164,k1_tarski(A_166))
      | '#skF_5'(k1_tarski(A_166),B_165) = A_166 ) ),
    inference(resolution,[status(thm)],[c_365,c_84])).

tff(c_652,plain,(
    ! [C_168,A_169] :
      ( ~ r2_hidden(C_168,k1_tarski(A_169))
      | '#skF_5'(k1_tarski(A_169),k1_tarski(C_168)) = A_169 ) ),
    inference(resolution,[status(thm)],[c_28,c_606])).

tff(c_187,plain,(
    ! [A_83,B_84] :
      ( m1_subset_1('#skF_5'(A_83,B_84),B_84)
      | r1_xboole_0(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_176,c_58])).

tff(c_1484,plain,(
    ! [A_235,C_236] :
      ( m1_subset_1(A_235,k1_tarski(C_236))
      | r1_xboole_0(k1_tarski(A_235),k1_tarski(C_236))
      | ~ r2_hidden(C_236,k1_tarski(A_235)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_652,c_187])).

tff(c_1487,plain,(
    ! [A_235,C_236] :
      ( r1_subset_1(k1_tarski(A_235),k1_tarski(C_236))
      | v1_xboole_0(k1_tarski(C_236))
      | v1_xboole_0(k1_tarski(A_235))
      | m1_subset_1(A_235,k1_tarski(C_236))
      | ~ r2_hidden(C_236,k1_tarski(A_235)) ) ),
    inference(resolution,[status(thm)],[c_1484,c_52])).

tff(c_1524,plain,(
    ! [A_242,C_243] :
      ( r1_subset_1(k1_tarski(A_242),k1_tarski(C_243))
      | m1_subset_1(A_242,k1_tarski(C_243))
      | ~ r2_hidden(C_243,k1_tarski(A_242)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_131,c_1487])).

tff(c_420,plain,(
    ! [A_132,B_133] :
      ( r1_xboole_0(A_132,B_133)
      | ~ r1_subset_1(A_132,B_133)
      | v1_xboole_0(B_133)
      | v1_xboole_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_894,plain,(
    ! [C_200,B_201,A_202] :
      ( ~ r2_hidden(C_200,B_201)
      | ~ r2_hidden(C_200,A_202)
      | ~ r1_subset_1(A_202,B_201)
      | v1_xboole_0(B_201)
      | v1_xboole_0(A_202) ) ),
    inference(resolution,[status(thm)],[c_420,c_84])).

tff(c_906,plain,(
    ! [C_8,A_202] :
      ( ~ r2_hidden(C_8,A_202)
      | ~ r1_subset_1(A_202,k1_tarski(C_8))
      | v1_xboole_0(k1_tarski(C_8))
      | v1_xboole_0(A_202) ) ),
    inference(resolution,[status(thm)],[c_28,c_894])).

tff(c_914,plain,(
    ! [C_8,A_202] :
      ( ~ r2_hidden(C_8,A_202)
      | ~ r1_subset_1(A_202,k1_tarski(C_8))
      | v1_xboole_0(A_202) ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_906])).

tff(c_1532,plain,(
    ! [A_242,C_243] :
      ( v1_xboole_0(k1_tarski(A_242))
      | m1_subset_1(A_242,k1_tarski(C_243))
      | ~ r2_hidden(C_243,k1_tarski(A_242)) ) ),
    inference(resolution,[status(thm)],[c_1524,c_914])).

tff(c_1547,plain,(
    ! [A_244,C_245] :
      ( m1_subset_1(A_244,k1_tarski(C_245))
      | ~ r2_hidden(C_245,k1_tarski(A_244)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_1532])).

tff(c_1573,plain,(
    ! [A_244,B_47] :
      ( m1_subset_1(A_244,k1_tarski('#skF_5'(k1_tarski(A_244),B_47)))
      | r1_xboole_0(k1_tarski(A_244),B_47) ) ),
    inference(resolution,[status(thm)],[c_88,c_1547])).

tff(c_86,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_5'(A_46,B_47),B_47)
      | r1_xboole_0(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_1494,plain,(
    ! [A_237,C_238] :
      ( r2_hidden(A_237,k1_tarski(C_238))
      | r1_xboole_0(k1_tarski(A_237),k1_tarski(C_238))
      | ~ r2_hidden(C_238,k1_tarski(A_237)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_652,c_86])).

tff(c_1497,plain,(
    ! [A_237,C_238] :
      ( r1_subset_1(k1_tarski(A_237),k1_tarski(C_238))
      | v1_xboole_0(k1_tarski(C_238))
      | v1_xboole_0(k1_tarski(A_237))
      | r2_hidden(A_237,k1_tarski(C_238))
      | ~ r2_hidden(C_238,k1_tarski(A_237)) ) ),
    inference(resolution,[status(thm)],[c_1494,c_52])).

tff(c_1741,plain,(
    ! [A_258,C_259] :
      ( r1_subset_1(k1_tarski(A_258),k1_tarski(C_259))
      | r2_hidden(A_258,k1_tarski(C_259))
      | ~ r2_hidden(C_259,k1_tarski(A_258)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_131,c_1497])).

tff(c_1749,plain,(
    ! [A_258,C_259] :
      ( v1_xboole_0(k1_tarski(A_258))
      | r2_hidden(A_258,k1_tarski(C_259))
      | ~ r2_hidden(C_259,k1_tarski(A_258)) ) ),
    inference(resolution,[status(thm)],[c_1741,c_914])).

tff(c_1764,plain,(
    ! [A_260,C_261] :
      ( r2_hidden(A_260,k1_tarski(C_261))
      | ~ r2_hidden(C_261,k1_tarski(A_260)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_1749])).

tff(c_1776,plain,(
    ! [A_260,A_44] :
      ( r2_hidden(A_260,k1_tarski(A_44))
      | v1_xboole_0(k1_tarski(A_260))
      | ~ m1_subset_1(A_44,k1_tarski(A_260)) ) ),
    inference(resolution,[status(thm)],[c_82,c_1764])).

tff(c_1787,plain,(
    ! [A_260,A_44] :
      ( r2_hidden(A_260,k1_tarski(A_44))
      | ~ m1_subset_1(A_44,k1_tarski(A_260)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_1776])).

tff(c_10323,plain,(
    ! [A_585,B_586,A_587] :
      ( ~ r2_hidden('#skF_5'(A_585,B_586),A_587)
      | ~ r1_subset_1(A_587,A_585)
      | v1_xboole_0(A_585)
      | v1_xboole_0(A_587)
      | r1_xboole_0(A_585,B_586) ) ),
    inference(resolution,[status(thm)],[c_88,c_894])).

tff(c_10443,plain,(
    ! [B_588,A_589] :
      ( ~ r1_subset_1(B_588,A_589)
      | v1_xboole_0(A_589)
      | v1_xboole_0(B_588)
      | r1_xboole_0(A_589,B_588) ) ),
    inference(resolution,[status(thm)],[c_86,c_10323])).

tff(c_10579,plain,(
    ! [C_596,B_597,A_598] :
      ( ~ r2_hidden(C_596,B_597)
      | ~ r2_hidden(C_596,A_598)
      | ~ r1_subset_1(B_597,A_598)
      | v1_xboole_0(A_598)
      | v1_xboole_0(B_597) ) ),
    inference(resolution,[status(thm)],[c_10443,c_84])).

tff(c_12929,plain,(
    ! [A_664,B_665,A_666] :
      ( ~ r2_hidden('#skF_5'(A_664,B_665),A_666)
      | ~ r1_subset_1(B_665,A_666)
      | v1_xboole_0(A_666)
      | v1_xboole_0(B_665)
      | r1_xboole_0(A_664,B_665) ) ),
    inference(resolution,[status(thm)],[c_86,c_10579])).

tff(c_12987,plain,(
    ! [B_665,A_44,A_664] :
      ( ~ r1_subset_1(B_665,k1_tarski(A_44))
      | v1_xboole_0(k1_tarski(A_44))
      | v1_xboole_0(B_665)
      | r1_xboole_0(A_664,B_665)
      | ~ m1_subset_1(A_44,k1_tarski('#skF_5'(A_664,B_665))) ) ),
    inference(resolution,[status(thm)],[c_1787,c_12929])).

tff(c_13346,plain,(
    ! [B_678,A_679,A_680] :
      ( ~ r1_subset_1(B_678,k1_tarski(A_679))
      | v1_xboole_0(B_678)
      | r1_xboole_0(A_680,B_678)
      | ~ m1_subset_1(A_679,k1_tarski('#skF_5'(A_680,B_678))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_12987])).

tff(c_13475,plain,(
    ! [B_681,A_682] :
      ( ~ r1_subset_1(B_681,k1_tarski(A_682))
      | v1_xboole_0(B_681)
      | r1_xboole_0(k1_tarski(A_682),B_681) ) ),
    inference(resolution,[status(thm)],[c_1573,c_13346])).

tff(c_13478,plain,(
    ! [A_682,B_681] :
      ( r1_subset_1(k1_tarski(A_682),B_681)
      | v1_xboole_0(k1_tarski(A_682))
      | ~ r1_subset_1(B_681,k1_tarski(A_682))
      | v1_xboole_0(B_681) ) ),
    inference(resolution,[status(thm)],[c_13475,c_52])).

tff(c_13489,plain,(
    ! [A_682,B_681] :
      ( r1_subset_1(k1_tarski(A_682),B_681)
      | ~ r1_subset_1(B_681,k1_tarski(A_682))
      | v1_xboole_0(B_681) ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_13478])).

tff(c_29242,plain,
    ( r1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),'#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_29238,c_13489])).

tff(c_29260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_28935,c_29242])).

tff(c_29262,plain,(
    r1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_28804])).

tff(c_5041,plain,(
    ! [A_398,B_399,C_400] :
      ( v2_waybel_0('#skF_4'(A_398,B_399,C_400),A_398)
      | ~ r1_subset_1(B_399,C_400)
      | ~ m1_subset_1(C_400,k1_zfmisc_1(u1_struct_0(A_398)))
      | ~ v13_waybel_0(C_400,A_398)
      | ~ v2_waybel_0(C_400,A_398)
      | v1_xboole_0(C_400)
      | ~ m1_subset_1(B_399,k1_zfmisc_1(u1_struct_0(A_398)))
      | ~ v12_waybel_0(B_399,A_398)
      | ~ v1_waybel_0(B_399,A_398)
      | v1_xboole_0(B_399)
      | ~ l1_orders_2(A_398)
      | ~ v2_lattice3(A_398)
      | ~ v1_lattice3(A_398)
      | ~ v2_waybel_1(A_398)
      | ~ v5_orders_2(A_398)
      | ~ v4_orders_2(A_398)
      | ~ v3_orders_2(A_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_5056,plain,(
    ! [B_399] :
      ( v2_waybel_0('#skF_4'('#skF_6',B_399,'#skF_7'),'#skF_6')
      | ~ r1_subset_1(B_399,'#skF_7')
      | ~ v13_waybel_0('#skF_7','#skF_6')
      | ~ v2_waybel_0('#skF_7','#skF_6')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(B_399,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v12_waybel_0(B_399,'#skF_6')
      | ~ v1_waybel_0(B_399,'#skF_6')
      | v1_xboole_0(B_399)
      | ~ l1_orders_2('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v1_lattice3('#skF_6')
      | ~ v2_waybel_1('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_100,c_5041])).

tff(c_5069,plain,(
    ! [B_399] :
      ( v2_waybel_0('#skF_4'('#skF_6',B_399,'#skF_7'),'#skF_6')
      | ~ r1_subset_1(B_399,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(B_399,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v12_waybel_0(B_399,'#skF_6')
      | ~ v1_waybel_0(B_399,'#skF_6')
      | v1_xboole_0(B_399) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_120,c_118,c_4361,c_114,c_112,c_110,c_104,c_102,c_5056])).

tff(c_6334,plain,(
    ! [B_437] :
      ( v2_waybel_0('#skF_4'('#skF_6',B_437,'#skF_7'),'#skF_6')
      | ~ r1_subset_1(B_437,'#skF_7')
      | ~ m1_subset_1(B_437,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v12_waybel_0(B_437,'#skF_6')
      | ~ v1_waybel_0(B_437,'#skF_6')
      | v1_xboole_0(B_437) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_5069])).

tff(c_6345,plain,(
    ! [B_11] :
      ( v2_waybel_0('#skF_4'('#skF_6',k5_waybel_0('#skF_6',B_11),'#skF_7'),'#skF_6')
      | ~ r1_subset_1(k5_waybel_0('#skF_6',B_11),'#skF_7')
      | ~ v12_waybel_0(k5_waybel_0('#skF_6',B_11),'#skF_6')
      | ~ v1_waybel_0(k5_waybel_0('#skF_6',B_11),'#skF_6')
      | v1_xboole_0(k5_waybel_0('#skF_6',B_11))
      | ~ m1_subset_1(B_11,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_6334])).

tff(c_6371,plain,(
    ! [B_11] :
      ( v2_waybel_0('#skF_4'('#skF_6',k5_waybel_0('#skF_6',B_11),'#skF_7'),'#skF_6')
      | ~ r1_subset_1(k5_waybel_0('#skF_6',B_11),'#skF_7')
      | ~ v12_waybel_0(k5_waybel_0('#skF_6',B_11),'#skF_6')
      | ~ v1_waybel_0(k5_waybel_0('#skF_6',B_11),'#skF_6')
      | v1_xboole_0(k5_waybel_0('#skF_6',B_11))
      | ~ m1_subset_1(B_11,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_6345])).

tff(c_28040,plain,(
    ! [B_1060] :
      ( v2_waybel_0('#skF_4'('#skF_6',k5_waybel_0('#skF_6',B_1060),'#skF_7'),'#skF_6')
      | ~ r1_subset_1(k5_waybel_0('#skF_6',B_1060),'#skF_7')
      | ~ v12_waybel_0(k5_waybel_0('#skF_6',B_1060),'#skF_6')
      | ~ v1_waybel_0(k5_waybel_0('#skF_6',B_1060),'#skF_6')
      | v1_xboole_0(k5_waybel_0('#skF_6',B_1060))
      | ~ m1_subset_1(B_1060,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1086,c_6371])).

tff(c_28043,plain,
    ( v2_waybel_0('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'),'#skF_6')
    | ~ r1_subset_1(k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')),'#skF_7')
    | ~ v12_waybel_0(k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')),'#skF_6')
    | ~ v1_waybel_0(k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')),'#skF_6')
    | v1_xboole_0(k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')))
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_27164,c_28040])).

tff(c_28047,plain,
    ( v2_waybel_0('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'),'#skF_6')
    | ~ r1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),'#skF_7')
    | v1_xboole_0(k1_tarski(k3_yellow_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27306,c_27164,c_27496,c_27164,c_27305,c_27164,c_27164,c_28043])).

tff(c_28048,plain,
    ( v2_waybel_0('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'),'#skF_6')
    | ~ r1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_28047])).

tff(c_29961,plain,(
    v2_waybel_0('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29262,c_28048])).

tff(c_4820,plain,(
    ! [A_379,B_380,C_381] :
      ( v13_waybel_0('#skF_4'(A_379,B_380,C_381),A_379)
      | ~ r1_subset_1(B_380,C_381)
      | ~ m1_subset_1(C_381,k1_zfmisc_1(u1_struct_0(A_379)))
      | ~ v13_waybel_0(C_381,A_379)
      | ~ v2_waybel_0(C_381,A_379)
      | v1_xboole_0(C_381)
      | ~ m1_subset_1(B_380,k1_zfmisc_1(u1_struct_0(A_379)))
      | ~ v12_waybel_0(B_380,A_379)
      | ~ v1_waybel_0(B_380,A_379)
      | v1_xboole_0(B_380)
      | ~ l1_orders_2(A_379)
      | ~ v2_lattice3(A_379)
      | ~ v1_lattice3(A_379)
      | ~ v2_waybel_1(A_379)
      | ~ v5_orders_2(A_379)
      | ~ v4_orders_2(A_379)
      | ~ v3_orders_2(A_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_4835,plain,(
    ! [B_380] :
      ( v13_waybel_0('#skF_4'('#skF_6',B_380,'#skF_7'),'#skF_6')
      | ~ r1_subset_1(B_380,'#skF_7')
      | ~ v13_waybel_0('#skF_7','#skF_6')
      | ~ v2_waybel_0('#skF_7','#skF_6')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(B_380,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v12_waybel_0(B_380,'#skF_6')
      | ~ v1_waybel_0(B_380,'#skF_6')
      | v1_xboole_0(B_380)
      | ~ l1_orders_2('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v1_lattice3('#skF_6')
      | ~ v2_waybel_1('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_100,c_4820])).

tff(c_4848,plain,(
    ! [B_380] :
      ( v13_waybel_0('#skF_4'('#skF_6',B_380,'#skF_7'),'#skF_6')
      | ~ r1_subset_1(B_380,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(B_380,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v12_waybel_0(B_380,'#skF_6')
      | ~ v1_waybel_0(B_380,'#skF_6')
      | v1_xboole_0(B_380) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_120,c_118,c_4361,c_114,c_112,c_110,c_104,c_102,c_4835])).

tff(c_5375,plain,(
    ! [B_407] :
      ( v13_waybel_0('#skF_4'('#skF_6',B_407,'#skF_7'),'#skF_6')
      | ~ r1_subset_1(B_407,'#skF_7')
      | ~ m1_subset_1(B_407,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v12_waybel_0(B_407,'#skF_6')
      | ~ v1_waybel_0(B_407,'#skF_6')
      | v1_xboole_0(B_407) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_4848])).

tff(c_5382,plain,(
    ! [B_11] :
      ( v13_waybel_0('#skF_4'('#skF_6',k5_waybel_0('#skF_6',B_11),'#skF_7'),'#skF_6')
      | ~ r1_subset_1(k5_waybel_0('#skF_6',B_11),'#skF_7')
      | ~ v12_waybel_0(k5_waybel_0('#skF_6',B_11),'#skF_6')
      | ~ v1_waybel_0(k5_waybel_0('#skF_6',B_11),'#skF_6')
      | v1_xboole_0(k5_waybel_0('#skF_6',B_11))
      | ~ m1_subset_1(B_11,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_5375])).

tff(c_5405,plain,(
    ! [B_11] :
      ( v13_waybel_0('#skF_4'('#skF_6',k5_waybel_0('#skF_6',B_11),'#skF_7'),'#skF_6')
      | ~ r1_subset_1(k5_waybel_0('#skF_6',B_11),'#skF_7')
      | ~ v12_waybel_0(k5_waybel_0('#skF_6',B_11),'#skF_6')
      | ~ v1_waybel_0(k5_waybel_0('#skF_6',B_11),'#skF_6')
      | v1_xboole_0(k5_waybel_0('#skF_6',B_11))
      | ~ m1_subset_1(B_11,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_5382])).

tff(c_28469,plain,(
    ! [B_1064] :
      ( v13_waybel_0('#skF_4'('#skF_6',k5_waybel_0('#skF_6',B_1064),'#skF_7'),'#skF_6')
      | ~ r1_subset_1(k5_waybel_0('#skF_6',B_1064),'#skF_7')
      | ~ v12_waybel_0(k5_waybel_0('#skF_6',B_1064),'#skF_6')
      | ~ v1_waybel_0(k5_waybel_0('#skF_6',B_1064),'#skF_6')
      | v1_xboole_0(k5_waybel_0('#skF_6',B_1064))
      | ~ m1_subset_1(B_1064,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1086,c_5405])).

tff(c_28472,plain,
    ( v13_waybel_0('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'),'#skF_6')
    | ~ r1_subset_1(k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')),'#skF_7')
    | ~ v12_waybel_0(k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')),'#skF_6')
    | ~ v1_waybel_0(k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')),'#skF_6')
    | v1_xboole_0(k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')))
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_27164,c_28469])).

tff(c_28476,plain,
    ( v13_waybel_0('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'),'#skF_6')
    | ~ r1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),'#skF_7')
    | v1_xboole_0(k1_tarski(k3_yellow_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27306,c_27164,c_27496,c_27164,c_27305,c_27164,c_27164,c_28472])).

tff(c_28477,plain,
    ( v13_waybel_0('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'),'#skF_6')
    | ~ r1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_28476])).

tff(c_29963,plain,(
    v13_waybel_0('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29262,c_28477])).

tff(c_5641,plain,(
    ! [A_413,B_414,C_415] :
      ( v2_waybel_7('#skF_4'(A_413,B_414,C_415),A_413)
      | ~ r1_subset_1(B_414,C_415)
      | ~ m1_subset_1(C_415,k1_zfmisc_1(u1_struct_0(A_413)))
      | ~ v13_waybel_0(C_415,A_413)
      | ~ v2_waybel_0(C_415,A_413)
      | v1_xboole_0(C_415)
      | ~ m1_subset_1(B_414,k1_zfmisc_1(u1_struct_0(A_413)))
      | ~ v12_waybel_0(B_414,A_413)
      | ~ v1_waybel_0(B_414,A_413)
      | v1_xboole_0(B_414)
      | ~ l1_orders_2(A_413)
      | ~ v2_lattice3(A_413)
      | ~ v1_lattice3(A_413)
      | ~ v2_waybel_1(A_413)
      | ~ v5_orders_2(A_413)
      | ~ v4_orders_2(A_413)
      | ~ v3_orders_2(A_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_5656,plain,(
    ! [B_414] :
      ( v2_waybel_7('#skF_4'('#skF_6',B_414,'#skF_7'),'#skF_6')
      | ~ r1_subset_1(B_414,'#skF_7')
      | ~ v13_waybel_0('#skF_7','#skF_6')
      | ~ v2_waybel_0('#skF_7','#skF_6')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(B_414,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v12_waybel_0(B_414,'#skF_6')
      | ~ v1_waybel_0(B_414,'#skF_6')
      | v1_xboole_0(B_414)
      | ~ l1_orders_2('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v1_lattice3('#skF_6')
      | ~ v2_waybel_1('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_100,c_5641])).

tff(c_5669,plain,(
    ! [B_414] :
      ( v2_waybel_7('#skF_4'('#skF_6',B_414,'#skF_7'),'#skF_6')
      | ~ r1_subset_1(B_414,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(B_414,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v12_waybel_0(B_414,'#skF_6')
      | ~ v1_waybel_0(B_414,'#skF_6')
      | v1_xboole_0(B_414) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_120,c_118,c_4361,c_114,c_112,c_110,c_104,c_102,c_5656])).

tff(c_5989,plain,(
    ! [B_419] :
      ( v2_waybel_7('#skF_4'('#skF_6',B_419,'#skF_7'),'#skF_6')
      | ~ r1_subset_1(B_419,'#skF_7')
      | ~ m1_subset_1(B_419,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v12_waybel_0(B_419,'#skF_6')
      | ~ v1_waybel_0(B_419,'#skF_6')
      | v1_xboole_0(B_419) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_5669])).

tff(c_5996,plain,(
    ! [B_11] :
      ( v2_waybel_7('#skF_4'('#skF_6',k5_waybel_0('#skF_6',B_11),'#skF_7'),'#skF_6')
      | ~ r1_subset_1(k5_waybel_0('#skF_6',B_11),'#skF_7')
      | ~ v12_waybel_0(k5_waybel_0('#skF_6',B_11),'#skF_6')
      | ~ v1_waybel_0(k5_waybel_0('#skF_6',B_11),'#skF_6')
      | v1_xboole_0(k5_waybel_0('#skF_6',B_11))
      | ~ m1_subset_1(B_11,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_5989])).

tff(c_6019,plain,(
    ! [B_11] :
      ( v2_waybel_7('#skF_4'('#skF_6',k5_waybel_0('#skF_6',B_11),'#skF_7'),'#skF_6')
      | ~ r1_subset_1(k5_waybel_0('#skF_6',B_11),'#skF_7')
      | ~ v12_waybel_0(k5_waybel_0('#skF_6',B_11),'#skF_6')
      | ~ v1_waybel_0(k5_waybel_0('#skF_6',B_11),'#skF_6')
      | v1_xboole_0(k5_waybel_0('#skF_6',B_11))
      | ~ m1_subset_1(B_11,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_5996])).

tff(c_28680,plain,(
    ! [B_1070] :
      ( v2_waybel_7('#skF_4'('#skF_6',k5_waybel_0('#skF_6',B_1070),'#skF_7'),'#skF_6')
      | ~ r1_subset_1(k5_waybel_0('#skF_6',B_1070),'#skF_7')
      | ~ v12_waybel_0(k5_waybel_0('#skF_6',B_1070),'#skF_6')
      | ~ v1_waybel_0(k5_waybel_0('#skF_6',B_1070),'#skF_6')
      | v1_xboole_0(k5_waybel_0('#skF_6',B_1070))
      | ~ m1_subset_1(B_1070,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1086,c_6019])).

tff(c_28683,plain,
    ( v2_waybel_7('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'),'#skF_6')
    | ~ r1_subset_1(k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')),'#skF_7')
    | ~ v12_waybel_0(k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')),'#skF_6')
    | ~ v1_waybel_0(k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')),'#skF_6')
    | v1_xboole_0(k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')))
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_27164,c_28680])).

tff(c_28687,plain,
    ( v2_waybel_7('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'),'#skF_6')
    | ~ r1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),'#skF_7')
    | v1_xboole_0(k1_tarski(k3_yellow_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27306,c_27164,c_27496,c_27164,c_27305,c_27164,c_27164,c_28683])).

tff(c_28688,plain,
    ( v2_waybel_7('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'),'#skF_6')
    | ~ r1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_28687])).

tff(c_29965,plain,(
    v2_waybel_7('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29262,c_28688])).

tff(c_6156,plain,(
    ! [A_429,B_430,C_431] :
      ( m1_subset_1('#skF_4'(A_429,B_430,C_431),k1_zfmisc_1(u1_struct_0(A_429)))
      | ~ r1_subset_1(B_430,C_431)
      | ~ m1_subset_1(C_431,k1_zfmisc_1(u1_struct_0(A_429)))
      | ~ v13_waybel_0(C_431,A_429)
      | ~ v2_waybel_0(C_431,A_429)
      | v1_xboole_0(C_431)
      | ~ m1_subset_1(B_430,k1_zfmisc_1(u1_struct_0(A_429)))
      | ~ v12_waybel_0(B_430,A_429)
      | ~ v1_waybel_0(B_430,A_429)
      | v1_xboole_0(B_430)
      | ~ l1_orders_2(A_429)
      | ~ v2_lattice3(A_429)
      | ~ v1_lattice3(A_429)
      | ~ v2_waybel_1(A_429)
      | ~ v5_orders_2(A_429)
      | ~ v4_orders_2(A_429)
      | ~ v3_orders_2(A_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_94,plain,(
    ! [B_58,A_56] :
      ( v1_subset_1(B_58,u1_struct_0(A_56))
      | r2_hidden(k3_yellow_0(A_56),B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ v13_waybel_0(B_58,A_56)
      | ~ v2_waybel_0(B_58,A_56)
      | v1_xboole_0(B_58)
      | ~ l1_orders_2(A_56)
      | ~ v1_yellow_0(A_56)
      | ~ v5_orders_2(A_56)
      | ~ v4_orders_2(A_56)
      | ~ v3_orders_2(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_307])).

tff(c_6222,plain,(
    ! [A_429,B_430,C_431] :
      ( v1_subset_1('#skF_4'(A_429,B_430,C_431),u1_struct_0(A_429))
      | r2_hidden(k3_yellow_0(A_429),'#skF_4'(A_429,B_430,C_431))
      | ~ v13_waybel_0('#skF_4'(A_429,B_430,C_431),A_429)
      | ~ v2_waybel_0('#skF_4'(A_429,B_430,C_431),A_429)
      | v1_xboole_0('#skF_4'(A_429,B_430,C_431))
      | ~ v1_yellow_0(A_429)
      | v2_struct_0(A_429)
      | ~ r1_subset_1(B_430,C_431)
      | ~ m1_subset_1(C_431,k1_zfmisc_1(u1_struct_0(A_429)))
      | ~ v13_waybel_0(C_431,A_429)
      | ~ v2_waybel_0(C_431,A_429)
      | v1_xboole_0(C_431)
      | ~ m1_subset_1(B_430,k1_zfmisc_1(u1_struct_0(A_429)))
      | ~ v12_waybel_0(B_430,A_429)
      | ~ v1_waybel_0(B_430,A_429)
      | v1_xboole_0(B_430)
      | ~ l1_orders_2(A_429)
      | ~ v2_lattice3(A_429)
      | ~ v1_lattice3(A_429)
      | ~ v2_waybel_1(A_429)
      | ~ v5_orders_2(A_429)
      | ~ v4_orders_2(A_429)
      | ~ v3_orders_2(A_429) ) ),
    inference(resolution,[status(thm)],[c_6156,c_94])).

tff(c_62,plain,(
    ! [B_29,A_27] :
      ( v3_waybel_7(B_29,A_27)
      | ~ v2_waybel_7(B_29,A_27)
      | ~ v1_subset_1(B_29,u1_struct_0(A_27))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ v13_waybel_0(B_29,A_27)
      | ~ v2_waybel_0(B_29,A_27)
      | v1_xboole_0(B_29)
      | ~ l1_orders_2(A_27)
      | ~ v2_lattice3(A_27)
      | ~ v1_lattice3(A_27)
      | ~ v11_waybel_1(A_27)
      | ~ v5_orders_2(A_27)
      | ~ v4_orders_2(A_27)
      | ~ v3_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_18067,plain,(
    ! [A_843,B_844,C_845] :
      ( v3_waybel_7('#skF_4'(A_843,B_844,C_845),A_843)
      | ~ v2_waybel_7('#skF_4'(A_843,B_844,C_845),A_843)
      | ~ v1_subset_1('#skF_4'(A_843,B_844,C_845),u1_struct_0(A_843))
      | ~ v13_waybel_0('#skF_4'(A_843,B_844,C_845),A_843)
      | ~ v2_waybel_0('#skF_4'(A_843,B_844,C_845),A_843)
      | v1_xboole_0('#skF_4'(A_843,B_844,C_845))
      | ~ v11_waybel_1(A_843)
      | ~ r1_subset_1(B_844,C_845)
      | ~ m1_subset_1(C_845,k1_zfmisc_1(u1_struct_0(A_843)))
      | ~ v13_waybel_0(C_845,A_843)
      | ~ v2_waybel_0(C_845,A_843)
      | v1_xboole_0(C_845)
      | ~ m1_subset_1(B_844,k1_zfmisc_1(u1_struct_0(A_843)))
      | ~ v12_waybel_0(B_844,A_843)
      | ~ v1_waybel_0(B_844,A_843)
      | v1_xboole_0(B_844)
      | ~ l1_orders_2(A_843)
      | ~ v2_lattice3(A_843)
      | ~ v1_lattice3(A_843)
      | ~ v2_waybel_1(A_843)
      | ~ v5_orders_2(A_843)
      | ~ v4_orders_2(A_843)
      | ~ v3_orders_2(A_843) ) ),
    inference(resolution,[status(thm)],[c_6156,c_62])).

tff(c_53088,plain,(
    ! [A_1471,B_1472,C_1473] :
      ( v3_waybel_7('#skF_4'(A_1471,B_1472,C_1473),A_1471)
      | ~ v2_waybel_7('#skF_4'(A_1471,B_1472,C_1473),A_1471)
      | ~ v11_waybel_1(A_1471)
      | r2_hidden(k3_yellow_0(A_1471),'#skF_4'(A_1471,B_1472,C_1473))
      | ~ v13_waybel_0('#skF_4'(A_1471,B_1472,C_1473),A_1471)
      | ~ v2_waybel_0('#skF_4'(A_1471,B_1472,C_1473),A_1471)
      | v1_xboole_0('#skF_4'(A_1471,B_1472,C_1473))
      | ~ v1_yellow_0(A_1471)
      | v2_struct_0(A_1471)
      | ~ r1_subset_1(B_1472,C_1473)
      | ~ m1_subset_1(C_1473,k1_zfmisc_1(u1_struct_0(A_1471)))
      | ~ v13_waybel_0(C_1473,A_1471)
      | ~ v2_waybel_0(C_1473,A_1471)
      | v1_xboole_0(C_1473)
      | ~ m1_subset_1(B_1472,k1_zfmisc_1(u1_struct_0(A_1471)))
      | ~ v12_waybel_0(B_1472,A_1471)
      | ~ v1_waybel_0(B_1472,A_1471)
      | v1_xboole_0(B_1472)
      | ~ l1_orders_2(A_1471)
      | ~ v2_lattice3(A_1471)
      | ~ v1_lattice3(A_1471)
      | ~ v2_waybel_1(A_1471)
      | ~ v5_orders_2(A_1471)
      | ~ v4_orders_2(A_1471)
      | ~ v3_orders_2(A_1471) ) ),
    inference(resolution,[status(thm)],[c_6222,c_18067])).

tff(c_6600,plain,(
    ! [B_457] :
      ( r1_subset_1(B_457,'#skF_4'('#skF_6',B_457,'#skF_7'))
      | ~ r1_subset_1(B_457,'#skF_7')
      | ~ m1_subset_1(B_457,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v12_waybel_0(B_457,'#skF_6')
      | ~ v1_waybel_0(B_457,'#skF_6')
      | v1_xboole_0(B_457) ) ),
    inference(splitRight,[status(thm)],[c_4346])).

tff(c_6608,plain,(
    ! [B_11] :
      ( r1_subset_1(k5_waybel_0('#skF_6',B_11),'#skF_4'('#skF_6',k5_waybel_0('#skF_6',B_11),'#skF_7'))
      | ~ r1_subset_1(k5_waybel_0('#skF_6',B_11),'#skF_7')
      | ~ v12_waybel_0(k5_waybel_0('#skF_6',B_11),'#skF_6')
      | ~ v1_waybel_0(k5_waybel_0('#skF_6',B_11),'#skF_6')
      | v1_xboole_0(k5_waybel_0('#skF_6',B_11))
      | ~ m1_subset_1(B_11,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_6600])).

tff(c_6629,plain,(
    ! [B_11] :
      ( r1_subset_1(k5_waybel_0('#skF_6',B_11),'#skF_4'('#skF_6',k5_waybel_0('#skF_6',B_11),'#skF_7'))
      | ~ r1_subset_1(k5_waybel_0('#skF_6',B_11),'#skF_7')
      | ~ v12_waybel_0(k5_waybel_0('#skF_6',B_11),'#skF_6')
      | ~ v1_waybel_0(k5_waybel_0('#skF_6',B_11),'#skF_6')
      | v1_xboole_0(k5_waybel_0('#skF_6',B_11))
      | ~ m1_subset_1(B_11,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_6608])).

tff(c_29368,plain,(
    ! [B_1077] :
      ( r1_subset_1(k5_waybel_0('#skF_6',B_1077),'#skF_4'('#skF_6',k5_waybel_0('#skF_6',B_1077),'#skF_7'))
      | ~ r1_subset_1(k5_waybel_0('#skF_6',B_1077),'#skF_7')
      | ~ v12_waybel_0(k5_waybel_0('#skF_6',B_1077),'#skF_6')
      | ~ v1_waybel_0(k5_waybel_0('#skF_6',B_1077),'#skF_6')
      | v1_xboole_0(k5_waybel_0('#skF_6',B_1077))
      | ~ m1_subset_1(B_1077,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1086,c_6629])).

tff(c_29378,plain,
    ( r1_subset_1(k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')),'#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'))
    | ~ r1_subset_1(k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')),'#skF_7')
    | ~ v12_waybel_0(k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')),'#skF_6')
    | ~ v1_waybel_0(k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')),'#skF_6')
    | v1_xboole_0(k5_waybel_0('#skF_6',k3_yellow_0('#skF_6')))
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_27164,c_29368])).

tff(c_29389,plain,
    ( r1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),'#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'))
    | v1_xboole_0(k1_tarski(k3_yellow_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27306,c_27164,c_27496,c_27164,c_27305,c_27164,c_29262,c_27164,c_27164,c_29378])).

tff(c_29390,plain,(
    r1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),'#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_29389])).

tff(c_10601,plain,(
    ! [C_8,A_598] :
      ( ~ r2_hidden(C_8,A_598)
      | ~ r1_subset_1(k1_tarski(C_8),A_598)
      | v1_xboole_0(A_598)
      | v1_xboole_0(k1_tarski(C_8)) ) ),
    inference(resolution,[status(thm)],[c_28,c_10579])).

tff(c_10622,plain,(
    ! [C_8,A_598] :
      ( ~ r2_hidden(C_8,A_598)
      | ~ r1_subset_1(k1_tarski(C_8),A_598)
      | v1_xboole_0(A_598) ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_10601])).

tff(c_29444,plain,
    ( ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'))
    | v1_xboole_0('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7')) ),
    inference(resolution,[status(thm)],[c_29390,c_10622])).

tff(c_32342,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_29444])).

tff(c_53099,plain,
    ( v3_waybel_7('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'),'#skF_6')
    | ~ v2_waybel_7('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'),'#skF_6')
    | ~ v11_waybel_1('#skF_6')
    | ~ v13_waybel_0('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'),'#skF_6')
    | ~ v2_waybel_0('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'))
    | ~ v1_yellow_0('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ r1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),'#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v13_waybel_0('#skF_7','#skF_6')
    | ~ v2_waybel_0('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ m1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0('#skF_6')),'#skF_6')
    | ~ v1_waybel_0(k1_tarski(k3_yellow_0('#skF_6')),'#skF_6')
    | v1_xboole_0(k1_tarski(k3_yellow_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v2_waybel_1('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_53088,c_32342])).

tff(c_53149,plain,
    ( v3_waybel_7('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'))
    | v2_struct_0('#skF_6')
    | v1_xboole_0('#skF_7')
    | v1_xboole_0(k1_tarski(k3_yellow_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_120,c_118,c_4361,c_114,c_112,c_110,c_27496,c_27305,c_28806,c_104,c_102,c_100,c_29262,c_360,c_29961,c_29963,c_116,c_29965,c_53099])).

tff(c_53150,plain,
    ( v3_waybel_7('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_108,c_1086,c_53149])).

tff(c_53298,plain,(
    v1_xboole_0('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_53150])).

tff(c_80,plain,(
    ! [A_30,B_38,C_42] :
      ( ~ v1_xboole_0('#skF_4'(A_30,B_38,C_42))
      | ~ r1_subset_1(B_38,C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ v13_waybel_0(C_42,A_30)
      | ~ v2_waybel_0(C_42,A_30)
      | v1_xboole_0(C_42)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ v12_waybel_0(B_38,A_30)
      | ~ v1_waybel_0(B_38,A_30)
      | v1_xboole_0(B_38)
      | ~ l1_orders_2(A_30)
      | ~ v2_lattice3(A_30)
      | ~ v1_lattice3(A_30)
      | ~ v2_waybel_1(A_30)
      | ~ v5_orders_2(A_30)
      | ~ v4_orders_2(A_30)
      | ~ v3_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_53300,plain,
    ( ~ r1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),'#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v13_waybel_0('#skF_7','#skF_6')
    | ~ v2_waybel_0('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ m1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0('#skF_6')),'#skF_6')
    | ~ v1_waybel_0(k1_tarski(k3_yellow_0('#skF_6')),'#skF_6')
    | v1_xboole_0(k1_tarski(k3_yellow_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v2_waybel_1('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_53298,c_80])).

tff(c_53305,plain,
    ( v1_xboole_0('#skF_7')
    | v1_xboole_0(k1_tarski(k3_yellow_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_120,c_118,c_4361,c_114,c_112,c_110,c_27496,c_27305,c_28806,c_104,c_102,c_100,c_29262,c_53300])).

tff(c_53307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_108,c_53305])).

tff(c_53309,plain,(
    ~ v1_xboole_0('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_53150])).

tff(c_29261,plain,(
    r1_tarski('#skF_7','#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_28804])).

tff(c_53308,plain,(
    v3_waybel_7('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_53150])).

tff(c_6204,plain,(
    ! [B_430,C_431] :
      ( ~ v3_waybel_7('#skF_4'('#skF_6',B_430,C_431),'#skF_6')
      | ~ r1_tarski('#skF_7','#skF_4'('#skF_6',B_430,C_431))
      | ~ v13_waybel_0('#skF_4'('#skF_6',B_430,C_431),'#skF_6')
      | ~ v2_waybel_0('#skF_4'('#skF_6',B_430,C_431),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_6',B_430,C_431))
      | ~ r1_subset_1(B_430,C_431)
      | ~ m1_subset_1(C_431,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v13_waybel_0(C_431,'#skF_6')
      | ~ v2_waybel_0(C_431,'#skF_6')
      | v1_xboole_0(C_431)
      | ~ m1_subset_1(B_430,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v12_waybel_0(B_430,'#skF_6')
      | ~ v1_waybel_0(B_430,'#skF_6')
      | v1_xboole_0(B_430)
      | ~ l1_orders_2('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v1_lattice3('#skF_6')
      | ~ v2_waybel_1('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6156,c_98])).

tff(c_6229,plain,(
    ! [B_430,C_431] :
      ( ~ v3_waybel_7('#skF_4'('#skF_6',B_430,C_431),'#skF_6')
      | ~ r1_tarski('#skF_7','#skF_4'('#skF_6',B_430,C_431))
      | ~ v13_waybel_0('#skF_4'('#skF_6',B_430,C_431),'#skF_6')
      | ~ v2_waybel_0('#skF_4'('#skF_6',B_430,C_431),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_6',B_430,C_431))
      | ~ r1_subset_1(B_430,C_431)
      | ~ m1_subset_1(C_431,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v13_waybel_0(C_431,'#skF_6')
      | ~ v2_waybel_0(C_431,'#skF_6')
      | v1_xboole_0(C_431)
      | ~ m1_subset_1(B_430,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v12_waybel_0(B_430,'#skF_6')
      | ~ v1_waybel_0(B_430,'#skF_6')
      | v1_xboole_0(B_430) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_120,c_118,c_4361,c_114,c_112,c_110,c_6204])).

tff(c_53311,plain,
    ( ~ r1_tarski('#skF_7','#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'))
    | ~ v13_waybel_0('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'),'#skF_6')
    | ~ v2_waybel_0('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'))
    | ~ r1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),'#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v13_waybel_0('#skF_7','#skF_6')
    | ~ v2_waybel_0('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ m1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0('#skF_6')),'#skF_6')
    | ~ v1_waybel_0(k1_tarski(k3_yellow_0('#skF_6')),'#skF_6')
    | v1_xboole_0(k1_tarski(k3_yellow_0('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_53308,c_6229])).

tff(c_53314,plain,
    ( v1_xboole_0('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7'))
    | v1_xboole_0('#skF_7')
    | v1_xboole_0(k1_tarski(k3_yellow_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27496,c_27305,c_28806,c_104,c_102,c_100,c_29262,c_29961,c_29963,c_29261,c_53311])).

tff(c_53316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_108,c_53309,c_53314])).

tff(c_53317,plain,(
    v1_xboole_0('#skF_4'('#skF_6',k1_tarski(k3_yellow_0('#skF_6')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_29444])).

tff(c_53320,plain,
    ( ~ r1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),'#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v13_waybel_0('#skF_7','#skF_6')
    | ~ v2_waybel_0('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ m1_subset_1(k1_tarski(k3_yellow_0('#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v12_waybel_0(k1_tarski(k3_yellow_0('#skF_6')),'#skF_6')
    | ~ v1_waybel_0(k1_tarski(k3_yellow_0('#skF_6')),'#skF_6')
    | v1_xboole_0(k1_tarski(k3_yellow_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v2_waybel_1('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_53317,c_80])).

tff(c_53325,plain,
    ( v1_xboole_0('#skF_7')
    | v1_xboole_0(k1_tarski(k3_yellow_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_120,c_118,c_4361,c_114,c_112,c_110,c_27496,c_27305,c_28806,c_104,c_102,c_100,c_29262,c_53320])).

tff(c_53327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_108,c_53325])).

tff(c_53330,plain,(
    ! [A_1480] : ~ r2_hidden(A_1480,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_53338,plain,(
    ! [A_44] :
      ( v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_44,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_82,c_53330])).

tff(c_53359,plain,(
    ! [A_1485] : ~ m1_subset_1(A_1485,'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_53338])).

tff(c_53364,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_42,c_53359])).

%------------------------------------------------------------------------------
