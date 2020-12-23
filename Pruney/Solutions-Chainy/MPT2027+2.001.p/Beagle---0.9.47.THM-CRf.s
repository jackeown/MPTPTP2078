%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:17 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 4.13s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 914 expanded)
%              Number of leaves         :   54 ( 356 expanded)
%              Depth                    :   22
%              Number of atoms          :  571 (5481 expanded)
%              Number of equality atoms :   36 (  83 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v3_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k6_waybel_9 > k3_funct_2 > k2_yellow_6 > k3_waybel_2 > k12_lattice3 > k11_lattice3 > k4_waybel_1 > k2_zfmisc_1 > k1_funct_1 > k11_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k10_yellow_6,type,(
    k10_yellow_6: ( $i * $i ) > $i )).

tff(v3_yellow_6,type,(
    v3_yellow_6: ( $i * $i ) > $o )).

tff(k6_waybel_9,type,(
    k6_waybel_9: ( $i * $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_waybel_2,type,(
    k3_waybel_2: ( $i * $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff(k2_yellow_6,type,(
    k2_yellow_6: ( $i * $i * $i * $i ) > $i )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k4_waybel_1,type,(
    k4_waybel_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k11_yellow_6,type,(
    k11_yellow_6: ( $i * $i ) > $i )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(l1_waybel_9,type,(
    l1_waybel_9: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_239,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & v8_pre_topc(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & l1_waybel_9(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & v3_yellow_6(B,A)
              & l1_waybel_0(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( v5_pre_topc(k4_waybel_1(A,C),A,A)
                 => r2_hidden(k12_lattice3(A,C,k11_yellow_6(A,B)),k10_yellow_6(A,k3_waybel_2(A,C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_waybel_9)).

tff(f_148,axiom,(
    ! [A] :
      ( l1_waybel_9(A)
     => ( l1_pre_topc(A)
        & l1_orders_2(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

tff(f_142,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( v1_funct_1(k4_waybel_1(A,B))
        & v1_funct_2(k4_waybel_1(A,B),u1_struct_0(A),u1_struct_0(A))
        & m1_subset_1(k4_waybel_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v8_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & v3_yellow_6(B,A)
        & l1_waybel_0(B,A) )
     => m1_subset_1(k11_yellow_6(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_yellow_6)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ( v2_struct_0(A)
      <=> v1_xboole_0(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_struct_0)).

tff(f_164,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k6_waybel_9(A,A,k4_waybel_1(A,C),B) = k3_waybel_2(A,C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_waybel_9)).

tff(f_203,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & v8_pre_topc(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_waybel_9(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & v3_yellow_6(B,A)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) )
             => ( v5_pre_topc(C,A,A)
               => r2_hidden(k2_yellow_6(u1_struct_0(A),A,C,k11_yellow_6(A,B)),k10_yellow_6(A,k6_waybel_9(A,A,C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_waybel_9)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) )
             => ( C = k4_waybel_1(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => k3_funct_2(u1_struct_0(A),u1_struct_0(A),C,D) = k11_lattice3(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_waybel_1)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v2_struct_0(B)
        & l1_orders_2(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,u1_struct_0(B))))
        & m1_subset_1(D,A) )
     => k2_yellow_6(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_yellow_6)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_50,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_48,plain,(
    v7_waybel_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_46,plain,(
    v3_yellow_6('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_44,plain,(
    l1_waybel_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_54,plain,(
    l1_waybel_9('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_75,plain,(
    ! [A_62] :
      ( l1_orders_2(A_62)
      | ~ l1_waybel_9(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_79,plain,(
    l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_75])).

tff(c_58,plain,(
    v1_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_87,plain,(
    ! [A_66,B_67] :
      ( v1_funct_1(k4_waybel_1(A_66,B_67))
      | ~ m1_subset_1(B_67,u1_struct_0(A_66))
      | ~ l1_orders_2(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_90,plain,
    ( v1_funct_1(k4_waybel_1('#skF_2','#skF_4'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_87])).

tff(c_93,plain,
    ( v1_funct_1(k4_waybel_1('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_90])).

tff(c_94,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_6,plain,(
    ! [A_6] :
      ( ~ v2_struct_0(A_6)
      | ~ v1_lattice3(A_6)
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_97,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_94,c_6])).

tff(c_101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_58,c_97])).

tff(c_103,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_66,plain,(
    v8_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_69,plain,(
    ! [A_60] :
      ( l1_pre_topc(A_60)
      | ~ l1_waybel_9(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_73,plain,(
    l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_69])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k11_yellow_6(A_11,B_12),u1_struct_0(A_11))
      | ~ l1_waybel_0(B_12,A_11)
      | ~ v3_yellow_6(B_12,A_11)
      | ~ v7_waybel_0(B_12)
      | ~ v4_orders_2(B_12)
      | v2_struct_0(B_12)
      | ~ l1_pre_topc(A_11)
      | ~ v8_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_102,plain,(
    v1_funct_1(k4_waybel_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_4,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_137,plain,(
    ! [A_80,B_81,C_82,D_83] :
      ( k3_funct_2(A_80,B_81,C_82,D_83) = k1_funct_1(C_82,D_83)
      | ~ m1_subset_1(D_83,A_80)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_2(C_82,A_80,B_81)
      | ~ v1_funct_1(C_82)
      | v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_143,plain,(
    ! [B_81,C_82] :
      ( k3_funct_2(u1_struct_0('#skF_2'),B_81,C_82,'#skF_4') = k1_funct_1(C_82,'#skF_4')
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),B_81)))
      | ~ v1_funct_2(C_82,u1_struct_0('#skF_2'),B_81)
      | ~ v1_funct_1(C_82)
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_42,c_137])).

tff(c_166,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_10,plain,(
    ! [A_10] :
      ( v2_struct_0(A_10)
      | ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_169,plain,
    ( v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_166,c_10])).

tff(c_172,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_169])).

tff(c_175,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_172])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_175])).

tff(c_181,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_26,plain,(
    ! [A_39,B_40] :
      ( v1_funct_2(k4_waybel_1(A_39,B_40),u1_struct_0(A_39),u1_struct_0(A_39))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_64,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_62,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_60,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_56,plain,(
    v2_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_40,plain,(
    v5_pre_topc(k4_waybel_1('#skF_2','#skF_4'),'#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_121,plain,(
    ! [A_76,C_77,B_78] :
      ( k6_waybel_9(A_76,A_76,k4_waybel_1(A_76,C_77),B_78) = k3_waybel_2(A_76,C_77,B_78)
      | ~ m1_subset_1(C_77,u1_struct_0(A_76))
      | ~ l1_waybel_0(B_78,A_76)
      | v2_struct_0(B_78)
      | ~ l1_orders_2(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_123,plain,(
    ! [B_78] :
      ( k6_waybel_9('#skF_2','#skF_2',k4_waybel_1('#skF_2','#skF_4'),B_78) = k3_waybel_2('#skF_2','#skF_4',B_78)
      | ~ l1_waybel_0(B_78,'#skF_2')
      | v2_struct_0(B_78)
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_121])).

tff(c_126,plain,(
    ! [B_78] :
      ( k6_waybel_9('#skF_2','#skF_2',k4_waybel_1('#skF_2','#skF_4'),B_78) = k3_waybel_2('#skF_2','#skF_4',B_78)
      | ~ l1_waybel_0(B_78,'#skF_2')
      | v2_struct_0(B_78)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_123])).

tff(c_127,plain,(
    ! [B_78] :
      ( k6_waybel_9('#skF_2','#skF_2',k4_waybel_1('#skF_2','#skF_4'),B_78) = k3_waybel_2('#skF_2','#skF_4',B_78)
      | ~ l1_waybel_0(B_78,'#skF_2')
      | v2_struct_0(B_78) ) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_126])).

tff(c_376,plain,(
    ! [A_134,C_135,B_136] :
      ( r2_hidden(k2_yellow_6(u1_struct_0(A_134),A_134,C_135,k11_yellow_6(A_134,B_136)),k10_yellow_6(A_134,k6_waybel_9(A_134,A_134,C_135,B_136)))
      | ~ v5_pre_topc(C_135,A_134,A_134)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_134),u1_struct_0(A_134))))
      | ~ v1_funct_2(C_135,u1_struct_0(A_134),u1_struct_0(A_134))
      | ~ v1_funct_1(C_135)
      | ~ l1_waybel_0(B_136,A_134)
      | ~ v3_yellow_6(B_136,A_134)
      | ~ v7_waybel_0(B_136)
      | ~ v4_orders_2(B_136)
      | v2_struct_0(B_136)
      | ~ l1_waybel_9(A_134)
      | ~ v2_lattice3(A_134)
      | ~ v1_lattice3(A_134)
      | ~ v5_orders_2(A_134)
      | ~ v4_orders_2(A_134)
      | ~ v3_orders_2(A_134)
      | ~ v8_pre_topc(A_134)
      | ~ v2_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_382,plain,(
    ! [B_78] :
      ( r2_hidden(k2_yellow_6(u1_struct_0('#skF_2'),'#skF_2',k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_78)),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4',B_78)))
      | ~ v5_pre_topc(k4_waybel_1('#skF_2','#skF_4'),'#skF_2','#skF_2')
      | ~ m1_subset_1(k4_waybel_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_4'))
      | ~ l1_waybel_0(B_78,'#skF_2')
      | ~ v3_yellow_6(B_78,'#skF_2')
      | ~ v7_waybel_0(B_78)
      | ~ v4_orders_2(B_78)
      | v2_struct_0(B_78)
      | ~ l1_waybel_9('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_waybel_0(B_78,'#skF_2')
      | v2_struct_0(B_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_376])).

tff(c_384,plain,(
    ! [B_78] :
      ( r2_hidden(k2_yellow_6(u1_struct_0('#skF_2'),'#skF_2',k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_78)),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4',B_78)))
      | ~ m1_subset_1(k4_waybel_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v3_yellow_6(B_78,'#skF_2')
      | ~ v7_waybel_0(B_78)
      | ~ v4_orders_2(B_78)
      | ~ l1_waybel_0(B_78,'#skF_2')
      | v2_struct_0(B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_60,c_58,c_56,c_54,c_102,c_40,c_382])).

tff(c_448,plain,(
    ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_384])).

tff(c_451,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_448])).

tff(c_454,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_42,c_451])).

tff(c_456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_454])).

tff(c_458,plain,(
    v1_funct_2(k4_waybel_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_384])).

tff(c_24,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(k4_waybel_1(A_39,B_40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_39),u1_struct_0(A_39))))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_457,plain,(
    ! [B_78] :
      ( ~ m1_subset_1(k4_waybel_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))))
      | r2_hidden(k2_yellow_6(u1_struct_0('#skF_2'),'#skF_2',k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_78)),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4',B_78)))
      | ~ v3_yellow_6(B_78,'#skF_2')
      | ~ v7_waybel_0(B_78)
      | ~ v4_orders_2(B_78)
      | ~ l1_waybel_0(B_78,'#skF_2')
      | v2_struct_0(B_78) ) ),
    inference(splitRight,[status(thm)],[c_384])).

tff(c_463,plain,(
    ~ m1_subset_1(k4_waybel_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_457])).

tff(c_466,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_463])).

tff(c_469,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_42,c_466])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_469])).

tff(c_473,plain,(
    m1_subset_1(k4_waybel_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_457])).

tff(c_144,plain,(
    ! [A_84,B_85] :
      ( m1_subset_1(k11_yellow_6(A_84,B_85),u1_struct_0(A_84))
      | ~ l1_waybel_0(B_85,A_84)
      | ~ v3_yellow_6(B_85,A_84)
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85)
      | ~ l1_pre_topc(A_84)
      | ~ v8_pre_topc(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( k3_funct_2(A_1,B_2,C_3,D_4) = k1_funct_1(C_3,D_4)
      | ~ m1_subset_1(D_4,A_1)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_158,plain,(
    ! [A_84,B_2,C_3,B_85] :
      ( k3_funct_2(u1_struct_0(A_84),B_2,C_3,k11_yellow_6(A_84,B_85)) = k1_funct_1(C_3,k11_yellow_6(A_84,B_85))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_84),B_2)))
      | ~ v1_funct_2(C_3,u1_struct_0(A_84),B_2)
      | ~ v1_funct_1(C_3)
      | v1_xboole_0(u1_struct_0(A_84))
      | ~ l1_waybel_0(B_85,A_84)
      | ~ v3_yellow_6(B_85,A_84)
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85)
      | ~ l1_pre_topc(A_84)
      | ~ v8_pre_topc(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_144,c_2])).

tff(c_475,plain,(
    ! [B_85] :
      ( k3_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_85)) = k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_85))
      | ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_85,'#skF_2')
      | ~ v3_yellow_6(B_85,'#skF_2')
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85)
      | ~ l1_pre_topc('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_473,c_158])).

tff(c_490,plain,(
    ! [B_85] :
      ( k3_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_85)) = k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_85))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_85,'#skF_2')
      | ~ v3_yellow_6(B_85,'#skF_2')
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_73,c_102,c_458,c_475])).

tff(c_615,plain,(
    ! [B_156] :
      ( k3_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_156)) = k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_156))
      | ~ l1_waybel_0(B_156,'#skF_2')
      | ~ v3_yellow_6(B_156,'#skF_2')
      | ~ v7_waybel_0(B_156)
      | ~ v4_orders_2(B_156)
      | v2_struct_0(B_156) ) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_181,c_490])).

tff(c_343,plain,(
    ! [A_125,B_126,D_127] :
      ( k3_funct_2(u1_struct_0(A_125),u1_struct_0(A_125),k4_waybel_1(A_125,B_126),D_127) = k11_lattice3(A_125,B_126,D_127)
      | ~ m1_subset_1(D_127,u1_struct_0(A_125))
      | ~ m1_subset_1(k4_waybel_1(A_125,B_126),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_125),u1_struct_0(A_125))))
      | ~ v1_funct_2(k4_waybel_1(A_125,B_126),u1_struct_0(A_125),u1_struct_0(A_125))
      | ~ v1_funct_1(k4_waybel_1(A_125,B_126))
      | ~ m1_subset_1(B_126,u1_struct_0(A_125))
      | ~ l1_orders_2(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_347,plain,(
    ! [A_128,B_129,D_130] :
      ( k3_funct_2(u1_struct_0(A_128),u1_struct_0(A_128),k4_waybel_1(A_128,B_129),D_130) = k11_lattice3(A_128,B_129,D_130)
      | ~ m1_subset_1(D_130,u1_struct_0(A_128))
      | ~ v1_funct_2(k4_waybel_1(A_128,B_129),u1_struct_0(A_128),u1_struct_0(A_128))
      | ~ v1_funct_1(k4_waybel_1(A_128,B_129))
      | ~ m1_subset_1(B_129,u1_struct_0(A_128))
      | ~ l1_orders_2(A_128)
      | v2_struct_0(A_128) ) ),
    inference(resolution,[status(thm)],[c_24,c_343])).

tff(c_350,plain,(
    ! [A_39,B_40,D_130] :
      ( k3_funct_2(u1_struct_0(A_39),u1_struct_0(A_39),k4_waybel_1(A_39,B_40),D_130) = k11_lattice3(A_39,B_40,D_130)
      | ~ m1_subset_1(D_130,u1_struct_0(A_39))
      | ~ v1_funct_1(k4_waybel_1(A_39,B_40))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39)
      | v2_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_26,c_347])).

tff(c_621,plain,(
    ! [B_156] :
      ( k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_156)) = k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_156))
      | ~ m1_subset_1(k11_yellow_6('#skF_2',B_156),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_4'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_waybel_0(B_156,'#skF_2')
      | ~ v3_yellow_6(B_156,'#skF_2')
      | ~ v7_waybel_0(B_156)
      | ~ v4_orders_2(B_156)
      | v2_struct_0(B_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_350])).

tff(c_630,plain,(
    ! [B_156] :
      ( k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_156)) = k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_156))
      | ~ m1_subset_1(k11_yellow_6('#skF_2',B_156),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ l1_waybel_0(B_156,'#skF_2')
      | ~ v3_yellow_6(B_156,'#skF_2')
      | ~ v7_waybel_0(B_156)
      | ~ v4_orders_2(B_156)
      | v2_struct_0(B_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_42,c_102,c_621])).

tff(c_636,plain,(
    ! [B_157] :
      ( k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_157)) = k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_157))
      | ~ m1_subset_1(k11_yellow_6('#skF_2',B_157),u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_157,'#skF_2')
      | ~ v3_yellow_6(B_157,'#skF_2')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_630])).

tff(c_640,plain,(
    ! [B_12] :
      ( k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_12)) = k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_12))
      | ~ l1_waybel_0(B_12,'#skF_2')
      | ~ v3_yellow_6(B_12,'#skF_2')
      | ~ v7_waybel_0(B_12)
      | ~ v4_orders_2(B_12)
      | v2_struct_0(B_12)
      | ~ l1_pre_topc('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_636])).

tff(c_643,plain,(
    ! [B_12] :
      ( k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_12)) = k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_12))
      | ~ l1_waybel_0(B_12,'#skF_2')
      | ~ v3_yellow_6(B_12,'#skF_2')
      | ~ v7_waybel_0(B_12)
      | ~ v4_orders_2(B_12)
      | v2_struct_0(B_12)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_73,c_640])).

tff(c_644,plain,(
    ! [B_12] :
      ( k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_12)) = k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_12))
      | ~ l1_waybel_0(B_12,'#skF_2')
      | ~ v3_yellow_6(B_12,'#skF_2')
      | ~ v7_waybel_0(B_12)
      | ~ v4_orders_2(B_12)
      | v2_struct_0(B_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_643])).

tff(c_204,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( k2_yellow_6(A_89,B_90,C_91,D_92) = k1_funct_1(C_91,D_92)
      | ~ m1_subset_1(D_92,A_89)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,u1_struct_0(B_90))))
      | ~ v1_funct_2(C_91,A_89,u1_struct_0(B_90))
      | ~ v1_funct_1(C_91)
      | ~ l1_orders_2(B_90)
      | v2_struct_0(B_90)
      | v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_703,plain,(
    ! [A_166,B_167,C_168,B_169] :
      ( k2_yellow_6(u1_struct_0(A_166),B_167,C_168,k11_yellow_6(A_166,B_169)) = k1_funct_1(C_168,k11_yellow_6(A_166,B_169))
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_166),u1_struct_0(B_167))))
      | ~ v1_funct_2(C_168,u1_struct_0(A_166),u1_struct_0(B_167))
      | ~ v1_funct_1(C_168)
      | ~ l1_orders_2(B_167)
      | v2_struct_0(B_167)
      | v1_xboole_0(u1_struct_0(A_166))
      | ~ l1_waybel_0(B_169,A_166)
      | ~ v3_yellow_6(B_169,A_166)
      | ~ v7_waybel_0(B_169)
      | ~ v4_orders_2(B_169)
      | v2_struct_0(B_169)
      | ~ l1_pre_topc(A_166)
      | ~ v8_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_14,c_204])).

tff(c_705,plain,(
    ! [B_169] :
      ( k2_yellow_6(u1_struct_0('#skF_2'),'#skF_2',k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_169)) = k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_169))
      | ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_4'))
      | ~ l1_orders_2('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_169,'#skF_2')
      | ~ v3_yellow_6(B_169,'#skF_2')
      | ~ v7_waybel_0(B_169)
      | ~ v4_orders_2(B_169)
      | v2_struct_0(B_169)
      | ~ l1_pre_topc('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_473,c_703])).

tff(c_710,plain,(
    ! [B_169] :
      ( k2_yellow_6(u1_struct_0('#skF_2'),'#skF_2',k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_169)) = k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_169))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_169,'#skF_2')
      | ~ v3_yellow_6(B_169,'#skF_2')
      | ~ v7_waybel_0(B_169)
      | ~ v4_orders_2(B_169)
      | v2_struct_0(B_169)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_73,c_79,c_102,c_458,c_705])).

tff(c_713,plain,(
    ! [B_170] :
      ( k2_yellow_6(u1_struct_0('#skF_2'),'#skF_2',k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_170)) = k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_170))
      | ~ l1_waybel_0(B_170,'#skF_2')
      | ~ v3_yellow_6(B_170,'#skF_2')
      | ~ v7_waybel_0(B_170)
      | ~ v4_orders_2(B_170)
      | v2_struct_0(B_170) ) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_181,c_710])).

tff(c_36,plain,(
    ! [A_49,C_55,B_53] :
      ( r2_hidden(k2_yellow_6(u1_struct_0(A_49),A_49,C_55,k11_yellow_6(A_49,B_53)),k10_yellow_6(A_49,k6_waybel_9(A_49,A_49,C_55,B_53)))
      | ~ v5_pre_topc(C_55,A_49,A_49)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_49),u1_struct_0(A_49))))
      | ~ v1_funct_2(C_55,u1_struct_0(A_49),u1_struct_0(A_49))
      | ~ v1_funct_1(C_55)
      | ~ l1_waybel_0(B_53,A_49)
      | ~ v3_yellow_6(B_53,A_49)
      | ~ v7_waybel_0(B_53)
      | ~ v4_orders_2(B_53)
      | v2_struct_0(B_53)
      | ~ l1_waybel_9(A_49)
      | ~ v2_lattice3(A_49)
      | ~ v1_lattice3(A_49)
      | ~ v5_orders_2(A_49)
      | ~ v4_orders_2(A_49)
      | ~ v3_orders_2(A_49)
      | ~ v8_pre_topc(A_49)
      | ~ v2_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_722,plain,(
    ! [B_170] :
      ( r2_hidden(k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_170)),k10_yellow_6('#skF_2',k6_waybel_9('#skF_2','#skF_2',k4_waybel_1('#skF_2','#skF_4'),B_170)))
      | ~ v5_pre_topc(k4_waybel_1('#skF_2','#skF_4'),'#skF_2','#skF_2')
      | ~ m1_subset_1(k4_waybel_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_4'))
      | ~ l1_waybel_0(B_170,'#skF_2')
      | ~ v3_yellow_6(B_170,'#skF_2')
      | ~ v7_waybel_0(B_170)
      | ~ v4_orders_2(B_170)
      | v2_struct_0(B_170)
      | ~ l1_waybel_9('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_waybel_0(B_170,'#skF_2')
      | ~ v3_yellow_6(B_170,'#skF_2')
      | ~ v7_waybel_0(B_170)
      | ~ v4_orders_2(B_170)
      | v2_struct_0(B_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_713,c_36])).

tff(c_730,plain,(
    ! [B_171] :
      ( r2_hidden(k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_171)),k10_yellow_6('#skF_2',k6_waybel_9('#skF_2','#skF_2',k4_waybel_1('#skF_2','#skF_4'),B_171)))
      | ~ l1_waybel_0(B_171,'#skF_2')
      | ~ v3_yellow_6(B_171,'#skF_2')
      | ~ v7_waybel_0(B_171)
      | ~ v4_orders_2(B_171)
      | v2_struct_0(B_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_60,c_58,c_56,c_54,c_102,c_458,c_473,c_40,c_722])).

tff(c_737,plain,(
    ! [B_172] :
      ( r2_hidden(k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_172)),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4',B_172)))
      | ~ l1_waybel_0(B_172,'#skF_2')
      | ~ v3_yellow_6(B_172,'#skF_2')
      | ~ v7_waybel_0(B_172)
      | ~ v4_orders_2(B_172)
      | v2_struct_0(B_172)
      | ~ l1_waybel_0(B_172,'#skF_2')
      | v2_struct_0(B_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_730])).

tff(c_850,plain,(
    ! [B_189] :
      ( r2_hidden(k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_189)),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4',B_189)))
      | ~ l1_waybel_0(B_189,'#skF_2')
      | ~ v3_yellow_6(B_189,'#skF_2')
      | ~ v7_waybel_0(B_189)
      | ~ v4_orders_2(B_189)
      | v2_struct_0(B_189)
      | ~ l1_waybel_0(B_189,'#skF_2')
      | v2_struct_0(B_189)
      | ~ l1_waybel_0(B_189,'#skF_2')
      | ~ v3_yellow_6(B_189,'#skF_2')
      | ~ v7_waybel_0(B_189)
      | ~ v4_orders_2(B_189)
      | v2_struct_0(B_189) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_737])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( k12_lattice3(A_7,B_8,C_9) = k11_lattice3(A_7,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_7))
      | ~ m1_subset_1(B_8,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7)
      | ~ v2_lattice3(A_7)
      | ~ v5_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_306,plain,(
    ! [A_118,B_119,B_120] :
      ( k12_lattice3(A_118,B_119,k11_yellow_6(A_118,B_120)) = k11_lattice3(A_118,B_119,k11_yellow_6(A_118,B_120))
      | ~ m1_subset_1(B_119,u1_struct_0(A_118))
      | ~ l1_orders_2(A_118)
      | ~ v2_lattice3(A_118)
      | ~ v5_orders_2(A_118)
      | ~ l1_waybel_0(B_120,A_118)
      | ~ v3_yellow_6(B_120,A_118)
      | ~ v7_waybel_0(B_120)
      | ~ v4_orders_2(B_120)
      | v2_struct_0(B_120)
      | ~ l1_pre_topc(A_118)
      | ~ v8_pre_topc(A_118)
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118) ) ),
    inference(resolution,[status(thm)],[c_144,c_8])).

tff(c_312,plain,(
    ! [B_120] :
      ( k12_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_120)) = k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_120))
      | ~ l1_orders_2('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ l1_waybel_0(B_120,'#skF_2')
      | ~ v3_yellow_6(B_120,'#skF_2')
      | ~ v7_waybel_0(B_120)
      | ~ v4_orders_2(B_120)
      | v2_struct_0(B_120)
      | ~ l1_pre_topc('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_306])).

tff(c_317,plain,(
    ! [B_120] :
      ( k12_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_120)) = k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_120))
      | ~ l1_waybel_0(B_120,'#skF_2')
      | ~ v3_yellow_6(B_120,'#skF_2')
      | ~ v7_waybel_0(B_120)
      | ~ v4_orders_2(B_120)
      | v2_struct_0(B_120)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_73,c_60,c_56,c_79,c_312])).

tff(c_319,plain,(
    ! [B_121] :
      ( k12_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_121)) = k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_121))
      | ~ l1_waybel_0(B_121,'#skF_2')
      | ~ v3_yellow_6(B_121,'#skF_2')
      | ~ v7_waybel_0(B_121)
      | ~ v4_orders_2(B_121)
      | v2_struct_0(B_121) ) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_317])).

tff(c_38,plain,(
    ~ r2_hidden(k12_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2','#skF_3')),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_325,plain,
    ( ~ r2_hidden(k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2','#skF_3')),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4','#skF_3')))
    | ~ l1_waybel_0('#skF_3','#skF_2')
    | ~ v3_yellow_6('#skF_3','#skF_2')
    | ~ v7_waybel_0('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_38])).

tff(c_331,plain,
    ( ~ r2_hidden(k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2','#skF_3')),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4','#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_325])).

tff(c_332,plain,(
    ~ r2_hidden(k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2','#skF_3')),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_331])).

tff(c_853,plain,
    ( ~ l1_waybel_0('#skF_3','#skF_2')
    | ~ v3_yellow_6('#skF_3','#skF_2')
    | ~ v7_waybel_0('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_850,c_332])).

tff(c_856,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_853])).

tff(c_858,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_856])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:24:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.66  
% 3.85/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.66  %$ v5_pre_topc > v1_funct_2 > v3_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k6_waybel_9 > k3_funct_2 > k2_yellow_6 > k3_waybel_2 > k12_lattice3 > k11_lattice3 > k4_waybel_1 > k2_zfmisc_1 > k1_funct_1 > k11_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.85/1.66  
% 3.85/1.66  %Foreground sorts:
% 3.85/1.66  
% 3.85/1.66  
% 3.85/1.66  %Background operators:
% 3.85/1.66  
% 3.85/1.66  
% 3.85/1.66  %Foreground operators:
% 3.85/1.66  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.85/1.66  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 3.85/1.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.85/1.66  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.85/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.85/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.85/1.66  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 3.85/1.66  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 3.85/1.66  tff(k6_waybel_9, type, k6_waybel_9: ($i * $i * $i * $i) > $i).
% 3.85/1.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.85/1.66  tff(k3_waybel_2, type, k3_waybel_2: ($i * $i * $i) > $i).
% 3.85/1.66  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.85/1.66  tff(k2_yellow_6, type, k2_yellow_6: ($i * $i * $i * $i) > $i).
% 3.85/1.66  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 3.85/1.66  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 3.85/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.85/1.66  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 3.85/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.85/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.85/1.66  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.85/1.66  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.85/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.85/1.66  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.85/1.66  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.85/1.66  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.85/1.66  tff(k4_waybel_1, type, k4_waybel_1: ($i * $i) > $i).
% 3.85/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.66  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.85/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.85/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.85/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.66  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.85/1.66  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.85/1.66  tff(k11_yellow_6, type, k11_yellow_6: ($i * $i) > $i).
% 3.85/1.66  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 3.85/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.85/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.85/1.66  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.85/1.66  tff(l1_waybel_9, type, l1_waybel_9: $i > $o).
% 3.85/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/1.66  
% 4.13/1.69  tff(f_239, negated_conjecture, ~(![A]: ((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_waybel_9(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (v5_pre_topc(k4_waybel_1(A, C), A, A) => r2_hidden(k12_lattice3(A, C, k11_yellow_6(A, B)), k10_yellow_6(A, k3_waybel_2(A, C, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_waybel_9)).
% 4.13/1.69  tff(f_148, axiom, (![A]: (l1_waybel_9(A) => (l1_pre_topc(A) & l1_orders_2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 4.13/1.69  tff(f_142, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => ((v1_funct_1(k4_waybel_1(A, B)) & v1_funct_2(k4_waybel_1(A, B), u1_struct_0(A), u1_struct_0(A))) & m1_subset_1(k4_waybel_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_waybel_1)).
% 4.13/1.69  tff(f_49, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 4.13/1.69  tff(f_89, axiom, (![A, B]: (((((((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A)) & l1_waybel_0(B, A)) => m1_subset_1(k11_yellow_6(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_yellow_6)).
% 4.13/1.69  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.13/1.69  tff(f_38, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.13/1.69  tff(f_67, axiom, (![A]: (l1_struct_0(A) => (v2_struct_0(A) <=> v1_xboole_0(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_struct_0)).
% 4.13/1.69  tff(f_164, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k6_waybel_9(A, A, k4_waybel_1(A, C), B) = k3_waybel_2(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_waybel_9)).
% 4.13/1.69  tff(f_203, axiom, (![A]: ((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_waybel_9(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A)) & l1_waybel_0(B, A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))) => (v5_pre_topc(C, A, A) => r2_hidden(k2_yellow_6(u1_struct_0(A), A, C, k11_yellow_6(A, B)), k10_yellow_6(A, k6_waybel_9(A, A, C, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_waybel_9)).
% 4.13/1.69  tff(f_129, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))) => ((C = k4_waybel_1(A, B)) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (k3_funct_2(u1_struct_0(A), u1_struct_0(A), C, D) = k11_lattice3(A, B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_waybel_1)).
% 4.13/1.69  tff(f_107, axiom, (![A, B, C, D]: (((((((~v1_xboole_0(A) & ~v2_struct_0(B)) & l1_orders_2(B)) & v1_funct_1(C)) & v1_funct_2(C, A, u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, u1_struct_0(B))))) & m1_subset_1(D, A)) => (k2_yellow_6(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_yellow_6)).
% 4.13/1.69  tff(f_61, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 4.13/1.69  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.13/1.69  tff(c_50, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.13/1.69  tff(c_48, plain, (v7_waybel_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.13/1.69  tff(c_46, plain, (v3_yellow_6('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.13/1.69  tff(c_44, plain, (l1_waybel_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.13/1.69  tff(c_54, plain, (l1_waybel_9('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.13/1.69  tff(c_75, plain, (![A_62]: (l1_orders_2(A_62) | ~l1_waybel_9(A_62))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.13/1.69  tff(c_79, plain, (l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_54, c_75])).
% 4.13/1.69  tff(c_58, plain, (v1_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.13/1.69  tff(c_42, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.13/1.69  tff(c_87, plain, (![A_66, B_67]: (v1_funct_1(k4_waybel_1(A_66, B_67)) | ~m1_subset_1(B_67, u1_struct_0(A_66)) | ~l1_orders_2(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.13/1.69  tff(c_90, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_4')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_87])).
% 4.13/1.69  tff(c_93, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_90])).
% 4.13/1.69  tff(c_94, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_93])).
% 4.13/1.69  tff(c_6, plain, (![A_6]: (~v2_struct_0(A_6) | ~v1_lattice3(A_6) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.13/1.69  tff(c_97, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_94, c_6])).
% 4.13/1.69  tff(c_101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_58, c_97])).
% 4.13/1.69  tff(c_103, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_93])).
% 4.13/1.69  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.13/1.69  tff(c_66, plain, (v8_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.13/1.69  tff(c_69, plain, (![A_60]: (l1_pre_topc(A_60) | ~l1_waybel_9(A_60))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.13/1.69  tff(c_73, plain, (l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_69])).
% 4.13/1.69  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(k11_yellow_6(A_11, B_12), u1_struct_0(A_11)) | ~l1_waybel_0(B_12, A_11) | ~v3_yellow_6(B_12, A_11) | ~v7_waybel_0(B_12) | ~v4_orders_2(B_12) | v2_struct_0(B_12) | ~l1_pre_topc(A_11) | ~v8_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.13/1.69  tff(c_102, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_93])).
% 4.13/1.69  tff(c_4, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.13/1.69  tff(c_137, plain, (![A_80, B_81, C_82, D_83]: (k3_funct_2(A_80, B_81, C_82, D_83)=k1_funct_1(C_82, D_83) | ~m1_subset_1(D_83, A_80) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_2(C_82, A_80, B_81) | ~v1_funct_1(C_82) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.13/1.69  tff(c_143, plain, (![B_81, C_82]: (k3_funct_2(u1_struct_0('#skF_2'), B_81, C_82, '#skF_4')=k1_funct_1(C_82, '#skF_4') | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), B_81))) | ~v1_funct_2(C_82, u1_struct_0('#skF_2'), B_81) | ~v1_funct_1(C_82) | v1_xboole_0(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_42, c_137])).
% 4.13/1.69  tff(c_166, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_143])).
% 4.13/1.69  tff(c_10, plain, (![A_10]: (v2_struct_0(A_10) | ~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.13/1.69  tff(c_169, plain, (v2_struct_0('#skF_2') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_166, c_10])).
% 4.13/1.69  tff(c_172, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_103, c_169])).
% 4.13/1.69  tff(c_175, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_172])).
% 4.13/1.69  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_175])).
% 4.13/1.69  tff(c_181, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_143])).
% 4.13/1.69  tff(c_26, plain, (![A_39, B_40]: (v1_funct_2(k4_waybel_1(A_39, B_40), u1_struct_0(A_39), u1_struct_0(A_39)) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_orders_2(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.13/1.69  tff(c_64, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.13/1.69  tff(c_62, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.13/1.69  tff(c_60, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.13/1.69  tff(c_56, plain, (v2_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.13/1.69  tff(c_40, plain, (v5_pre_topc(k4_waybel_1('#skF_2', '#skF_4'), '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.13/1.69  tff(c_121, plain, (![A_76, C_77, B_78]: (k6_waybel_9(A_76, A_76, k4_waybel_1(A_76, C_77), B_78)=k3_waybel_2(A_76, C_77, B_78) | ~m1_subset_1(C_77, u1_struct_0(A_76)) | ~l1_waybel_0(B_78, A_76) | v2_struct_0(B_78) | ~l1_orders_2(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.13/1.69  tff(c_123, plain, (![B_78]: (k6_waybel_9('#skF_2', '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), B_78)=k3_waybel_2('#skF_2', '#skF_4', B_78) | ~l1_waybel_0(B_78, '#skF_2') | v2_struct_0(B_78) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_121])).
% 4.13/1.69  tff(c_126, plain, (![B_78]: (k6_waybel_9('#skF_2', '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), B_78)=k3_waybel_2('#skF_2', '#skF_4', B_78) | ~l1_waybel_0(B_78, '#skF_2') | v2_struct_0(B_78) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_123])).
% 4.13/1.69  tff(c_127, plain, (![B_78]: (k6_waybel_9('#skF_2', '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), B_78)=k3_waybel_2('#skF_2', '#skF_4', B_78) | ~l1_waybel_0(B_78, '#skF_2') | v2_struct_0(B_78))), inference(negUnitSimplification, [status(thm)], [c_103, c_126])).
% 4.13/1.69  tff(c_376, plain, (![A_134, C_135, B_136]: (r2_hidden(k2_yellow_6(u1_struct_0(A_134), A_134, C_135, k11_yellow_6(A_134, B_136)), k10_yellow_6(A_134, k6_waybel_9(A_134, A_134, C_135, B_136))) | ~v5_pre_topc(C_135, A_134, A_134) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_134), u1_struct_0(A_134)))) | ~v1_funct_2(C_135, u1_struct_0(A_134), u1_struct_0(A_134)) | ~v1_funct_1(C_135) | ~l1_waybel_0(B_136, A_134) | ~v3_yellow_6(B_136, A_134) | ~v7_waybel_0(B_136) | ~v4_orders_2(B_136) | v2_struct_0(B_136) | ~l1_waybel_9(A_134) | ~v2_lattice3(A_134) | ~v1_lattice3(A_134) | ~v5_orders_2(A_134) | ~v4_orders_2(A_134) | ~v3_orders_2(A_134) | ~v8_pre_topc(A_134) | ~v2_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_203])).
% 4.13/1.69  tff(c_382, plain, (![B_78]: (r2_hidden(k2_yellow_6(u1_struct_0('#skF_2'), '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_78)), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', B_78))) | ~v5_pre_topc(k4_waybel_1('#skF_2', '#skF_4'), '#skF_2', '#skF_2') | ~m1_subset_1(k4_waybel_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_waybel_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', '#skF_4')) | ~l1_waybel_0(B_78, '#skF_2') | ~v3_yellow_6(B_78, '#skF_2') | ~v7_waybel_0(B_78) | ~v4_orders_2(B_78) | v2_struct_0(B_78) | ~l1_waybel_9('#skF_2') | ~v2_lattice3('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | ~v8_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_waybel_0(B_78, '#skF_2') | v2_struct_0(B_78))), inference(superposition, [status(thm), theory('equality')], [c_127, c_376])).
% 4.13/1.69  tff(c_384, plain, (![B_78]: (r2_hidden(k2_yellow_6(u1_struct_0('#skF_2'), '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_78)), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', B_78))) | ~m1_subset_1(k4_waybel_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_waybel_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2')) | ~v3_yellow_6(B_78, '#skF_2') | ~v7_waybel_0(B_78) | ~v4_orders_2(B_78) | ~l1_waybel_0(B_78, '#skF_2') | v2_struct_0(B_78))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_60, c_58, c_56, c_54, c_102, c_40, c_382])).
% 4.13/1.69  tff(c_448, plain, (~v1_funct_2(k4_waybel_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_384])).
% 4.13/1.69  tff(c_451, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_448])).
% 4.13/1.69  tff(c_454, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_42, c_451])).
% 4.13/1.69  tff(c_456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_454])).
% 4.13/1.69  tff(c_458, plain, (v1_funct_2(k4_waybel_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_384])).
% 4.13/1.69  tff(c_24, plain, (![A_39, B_40]: (m1_subset_1(k4_waybel_1(A_39, B_40), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_39), u1_struct_0(A_39)))) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_orders_2(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.13/1.69  tff(c_457, plain, (![B_78]: (~m1_subset_1(k4_waybel_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2')))) | r2_hidden(k2_yellow_6(u1_struct_0('#skF_2'), '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_78)), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', B_78))) | ~v3_yellow_6(B_78, '#skF_2') | ~v7_waybel_0(B_78) | ~v4_orders_2(B_78) | ~l1_waybel_0(B_78, '#skF_2') | v2_struct_0(B_78))), inference(splitRight, [status(thm)], [c_384])).
% 4.13/1.69  tff(c_463, plain, (~m1_subset_1(k4_waybel_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_457])).
% 4.13/1.69  tff(c_466, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_463])).
% 4.13/1.69  tff(c_469, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_42, c_466])).
% 4.13/1.69  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_469])).
% 4.13/1.69  tff(c_473, plain, (m1_subset_1(k4_waybel_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_457])).
% 4.13/1.69  tff(c_144, plain, (![A_84, B_85]: (m1_subset_1(k11_yellow_6(A_84, B_85), u1_struct_0(A_84)) | ~l1_waybel_0(B_85, A_84) | ~v3_yellow_6(B_85, A_84) | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85) | ~l1_pre_topc(A_84) | ~v8_pre_topc(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.13/1.69  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k3_funct_2(A_1, B_2, C_3, D_4)=k1_funct_1(C_3, D_4) | ~m1_subset_1(D_4, A_1) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.13/1.69  tff(c_158, plain, (![A_84, B_2, C_3, B_85]: (k3_funct_2(u1_struct_0(A_84), B_2, C_3, k11_yellow_6(A_84, B_85))=k1_funct_1(C_3, k11_yellow_6(A_84, B_85)) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_84), B_2))) | ~v1_funct_2(C_3, u1_struct_0(A_84), B_2) | ~v1_funct_1(C_3) | v1_xboole_0(u1_struct_0(A_84)) | ~l1_waybel_0(B_85, A_84) | ~v3_yellow_6(B_85, A_84) | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85) | ~l1_pre_topc(A_84) | ~v8_pre_topc(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(resolution, [status(thm)], [c_144, c_2])).
% 4.13/1.69  tff(c_475, plain, (![B_85]: (k3_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_85))=k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_85)) | ~v1_funct_2(k4_waybel_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', '#skF_4')) | v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_waybel_0(B_85, '#skF_2') | ~v3_yellow_6(B_85, '#skF_2') | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85) | ~l1_pre_topc('#skF_2') | ~v8_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_473, c_158])).
% 4.13/1.69  tff(c_490, plain, (![B_85]: (k3_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_85))=k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_85)) | v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_waybel_0(B_85, '#skF_2') | ~v3_yellow_6(B_85, '#skF_2') | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_73, c_102, c_458, c_475])).
% 4.13/1.69  tff(c_615, plain, (![B_156]: (k3_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_156))=k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_156)) | ~l1_waybel_0(B_156, '#skF_2') | ~v3_yellow_6(B_156, '#skF_2') | ~v7_waybel_0(B_156) | ~v4_orders_2(B_156) | v2_struct_0(B_156))), inference(negUnitSimplification, [status(thm)], [c_103, c_181, c_490])).
% 4.13/1.69  tff(c_343, plain, (![A_125, B_126, D_127]: (k3_funct_2(u1_struct_0(A_125), u1_struct_0(A_125), k4_waybel_1(A_125, B_126), D_127)=k11_lattice3(A_125, B_126, D_127) | ~m1_subset_1(D_127, u1_struct_0(A_125)) | ~m1_subset_1(k4_waybel_1(A_125, B_126), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_125), u1_struct_0(A_125)))) | ~v1_funct_2(k4_waybel_1(A_125, B_126), u1_struct_0(A_125), u1_struct_0(A_125)) | ~v1_funct_1(k4_waybel_1(A_125, B_126)) | ~m1_subset_1(B_126, u1_struct_0(A_125)) | ~l1_orders_2(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.13/1.69  tff(c_347, plain, (![A_128, B_129, D_130]: (k3_funct_2(u1_struct_0(A_128), u1_struct_0(A_128), k4_waybel_1(A_128, B_129), D_130)=k11_lattice3(A_128, B_129, D_130) | ~m1_subset_1(D_130, u1_struct_0(A_128)) | ~v1_funct_2(k4_waybel_1(A_128, B_129), u1_struct_0(A_128), u1_struct_0(A_128)) | ~v1_funct_1(k4_waybel_1(A_128, B_129)) | ~m1_subset_1(B_129, u1_struct_0(A_128)) | ~l1_orders_2(A_128) | v2_struct_0(A_128))), inference(resolution, [status(thm)], [c_24, c_343])).
% 4.13/1.69  tff(c_350, plain, (![A_39, B_40, D_130]: (k3_funct_2(u1_struct_0(A_39), u1_struct_0(A_39), k4_waybel_1(A_39, B_40), D_130)=k11_lattice3(A_39, B_40, D_130) | ~m1_subset_1(D_130, u1_struct_0(A_39)) | ~v1_funct_1(k4_waybel_1(A_39, B_40)) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_orders_2(A_39) | v2_struct_0(A_39))), inference(resolution, [status(thm)], [c_26, c_347])).
% 4.13/1.69  tff(c_621, plain, (![B_156]: (k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_156))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_156)) | ~m1_subset_1(k11_yellow_6('#skF_2', B_156), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~l1_waybel_0(B_156, '#skF_2') | ~v3_yellow_6(B_156, '#skF_2') | ~v7_waybel_0(B_156) | ~v4_orders_2(B_156) | v2_struct_0(B_156))), inference(superposition, [status(thm), theory('equality')], [c_615, c_350])).
% 4.13/1.69  tff(c_630, plain, (![B_156]: (k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_156))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_156)) | ~m1_subset_1(k11_yellow_6('#skF_2', B_156), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~l1_waybel_0(B_156, '#skF_2') | ~v3_yellow_6(B_156, '#skF_2') | ~v7_waybel_0(B_156) | ~v4_orders_2(B_156) | v2_struct_0(B_156))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_42, c_102, c_621])).
% 4.13/1.69  tff(c_636, plain, (![B_157]: (k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_157))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_157)) | ~m1_subset_1(k11_yellow_6('#skF_2', B_157), u1_struct_0('#skF_2')) | ~l1_waybel_0(B_157, '#skF_2') | ~v3_yellow_6(B_157, '#skF_2') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(negUnitSimplification, [status(thm)], [c_103, c_630])).
% 4.13/1.69  tff(c_640, plain, (![B_12]: (k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_12))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_12)) | ~l1_waybel_0(B_12, '#skF_2') | ~v3_yellow_6(B_12, '#skF_2') | ~v7_waybel_0(B_12) | ~v4_orders_2(B_12) | v2_struct_0(B_12) | ~l1_pre_topc('#skF_2') | ~v8_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_636])).
% 4.13/1.69  tff(c_643, plain, (![B_12]: (k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_12))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_12)) | ~l1_waybel_0(B_12, '#skF_2') | ~v3_yellow_6(B_12, '#skF_2') | ~v7_waybel_0(B_12) | ~v4_orders_2(B_12) | v2_struct_0(B_12) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_73, c_640])).
% 4.13/1.69  tff(c_644, plain, (![B_12]: (k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_12))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_12)) | ~l1_waybel_0(B_12, '#skF_2') | ~v3_yellow_6(B_12, '#skF_2') | ~v7_waybel_0(B_12) | ~v4_orders_2(B_12) | v2_struct_0(B_12))), inference(negUnitSimplification, [status(thm)], [c_103, c_643])).
% 4.13/1.69  tff(c_204, plain, (![A_89, B_90, C_91, D_92]: (k2_yellow_6(A_89, B_90, C_91, D_92)=k1_funct_1(C_91, D_92) | ~m1_subset_1(D_92, A_89) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, u1_struct_0(B_90)))) | ~v1_funct_2(C_91, A_89, u1_struct_0(B_90)) | ~v1_funct_1(C_91) | ~l1_orders_2(B_90) | v2_struct_0(B_90) | v1_xboole_0(A_89))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.13/1.69  tff(c_703, plain, (![A_166, B_167, C_168, B_169]: (k2_yellow_6(u1_struct_0(A_166), B_167, C_168, k11_yellow_6(A_166, B_169))=k1_funct_1(C_168, k11_yellow_6(A_166, B_169)) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_166), u1_struct_0(B_167)))) | ~v1_funct_2(C_168, u1_struct_0(A_166), u1_struct_0(B_167)) | ~v1_funct_1(C_168) | ~l1_orders_2(B_167) | v2_struct_0(B_167) | v1_xboole_0(u1_struct_0(A_166)) | ~l1_waybel_0(B_169, A_166) | ~v3_yellow_6(B_169, A_166) | ~v7_waybel_0(B_169) | ~v4_orders_2(B_169) | v2_struct_0(B_169) | ~l1_pre_topc(A_166) | ~v8_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(resolution, [status(thm)], [c_14, c_204])).
% 4.13/1.69  tff(c_705, plain, (![B_169]: (k2_yellow_6(u1_struct_0('#skF_2'), '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_169))=k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_169)) | ~v1_funct_2(k4_waybel_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', '#skF_4')) | ~l1_orders_2('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_waybel_0(B_169, '#skF_2') | ~v3_yellow_6(B_169, '#skF_2') | ~v7_waybel_0(B_169) | ~v4_orders_2(B_169) | v2_struct_0(B_169) | ~l1_pre_topc('#skF_2') | ~v8_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_473, c_703])).
% 4.13/1.69  tff(c_710, plain, (![B_169]: (k2_yellow_6(u1_struct_0('#skF_2'), '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_169))=k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_169)) | v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_waybel_0(B_169, '#skF_2') | ~v3_yellow_6(B_169, '#skF_2') | ~v7_waybel_0(B_169) | ~v4_orders_2(B_169) | v2_struct_0(B_169) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_73, c_79, c_102, c_458, c_705])).
% 4.13/1.69  tff(c_713, plain, (![B_170]: (k2_yellow_6(u1_struct_0('#skF_2'), '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_170))=k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_170)) | ~l1_waybel_0(B_170, '#skF_2') | ~v3_yellow_6(B_170, '#skF_2') | ~v7_waybel_0(B_170) | ~v4_orders_2(B_170) | v2_struct_0(B_170))), inference(negUnitSimplification, [status(thm)], [c_103, c_181, c_710])).
% 4.13/1.69  tff(c_36, plain, (![A_49, C_55, B_53]: (r2_hidden(k2_yellow_6(u1_struct_0(A_49), A_49, C_55, k11_yellow_6(A_49, B_53)), k10_yellow_6(A_49, k6_waybel_9(A_49, A_49, C_55, B_53))) | ~v5_pre_topc(C_55, A_49, A_49) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_49), u1_struct_0(A_49)))) | ~v1_funct_2(C_55, u1_struct_0(A_49), u1_struct_0(A_49)) | ~v1_funct_1(C_55) | ~l1_waybel_0(B_53, A_49) | ~v3_yellow_6(B_53, A_49) | ~v7_waybel_0(B_53) | ~v4_orders_2(B_53) | v2_struct_0(B_53) | ~l1_waybel_9(A_49) | ~v2_lattice3(A_49) | ~v1_lattice3(A_49) | ~v5_orders_2(A_49) | ~v4_orders_2(A_49) | ~v3_orders_2(A_49) | ~v8_pre_topc(A_49) | ~v2_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_203])).
% 4.13/1.69  tff(c_722, plain, (![B_170]: (r2_hidden(k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_170)), k10_yellow_6('#skF_2', k6_waybel_9('#skF_2', '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), B_170))) | ~v5_pre_topc(k4_waybel_1('#skF_2', '#skF_4'), '#skF_2', '#skF_2') | ~m1_subset_1(k4_waybel_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_waybel_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', '#skF_4')) | ~l1_waybel_0(B_170, '#skF_2') | ~v3_yellow_6(B_170, '#skF_2') | ~v7_waybel_0(B_170) | ~v4_orders_2(B_170) | v2_struct_0(B_170) | ~l1_waybel_9('#skF_2') | ~v2_lattice3('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | ~v8_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_waybel_0(B_170, '#skF_2') | ~v3_yellow_6(B_170, '#skF_2') | ~v7_waybel_0(B_170) | ~v4_orders_2(B_170) | v2_struct_0(B_170))), inference(superposition, [status(thm), theory('equality')], [c_713, c_36])).
% 4.13/1.69  tff(c_730, plain, (![B_171]: (r2_hidden(k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_171)), k10_yellow_6('#skF_2', k6_waybel_9('#skF_2', '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), B_171))) | ~l1_waybel_0(B_171, '#skF_2') | ~v3_yellow_6(B_171, '#skF_2') | ~v7_waybel_0(B_171) | ~v4_orders_2(B_171) | v2_struct_0(B_171))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_60, c_58, c_56, c_54, c_102, c_458, c_473, c_40, c_722])).
% 4.13/1.69  tff(c_737, plain, (![B_172]: (r2_hidden(k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_172)), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', B_172))) | ~l1_waybel_0(B_172, '#skF_2') | ~v3_yellow_6(B_172, '#skF_2') | ~v7_waybel_0(B_172) | ~v4_orders_2(B_172) | v2_struct_0(B_172) | ~l1_waybel_0(B_172, '#skF_2') | v2_struct_0(B_172))), inference(superposition, [status(thm), theory('equality')], [c_127, c_730])).
% 4.13/1.69  tff(c_850, plain, (![B_189]: (r2_hidden(k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_189)), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', B_189))) | ~l1_waybel_0(B_189, '#skF_2') | ~v3_yellow_6(B_189, '#skF_2') | ~v7_waybel_0(B_189) | ~v4_orders_2(B_189) | v2_struct_0(B_189) | ~l1_waybel_0(B_189, '#skF_2') | v2_struct_0(B_189) | ~l1_waybel_0(B_189, '#skF_2') | ~v3_yellow_6(B_189, '#skF_2') | ~v7_waybel_0(B_189) | ~v4_orders_2(B_189) | v2_struct_0(B_189))), inference(superposition, [status(thm), theory('equality')], [c_644, c_737])).
% 4.13/1.69  tff(c_8, plain, (![A_7, B_8, C_9]: (k12_lattice3(A_7, B_8, C_9)=k11_lattice3(A_7, B_8, C_9) | ~m1_subset_1(C_9, u1_struct_0(A_7)) | ~m1_subset_1(B_8, u1_struct_0(A_7)) | ~l1_orders_2(A_7) | ~v2_lattice3(A_7) | ~v5_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.13/1.69  tff(c_306, plain, (![A_118, B_119, B_120]: (k12_lattice3(A_118, B_119, k11_yellow_6(A_118, B_120))=k11_lattice3(A_118, B_119, k11_yellow_6(A_118, B_120)) | ~m1_subset_1(B_119, u1_struct_0(A_118)) | ~l1_orders_2(A_118) | ~v2_lattice3(A_118) | ~v5_orders_2(A_118) | ~l1_waybel_0(B_120, A_118) | ~v3_yellow_6(B_120, A_118) | ~v7_waybel_0(B_120) | ~v4_orders_2(B_120) | v2_struct_0(B_120) | ~l1_pre_topc(A_118) | ~v8_pre_topc(A_118) | ~v2_pre_topc(A_118) | v2_struct_0(A_118))), inference(resolution, [status(thm)], [c_144, c_8])).
% 4.13/1.69  tff(c_312, plain, (![B_120]: (k12_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_120))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_120)) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | ~l1_waybel_0(B_120, '#skF_2') | ~v3_yellow_6(B_120, '#skF_2') | ~v7_waybel_0(B_120) | ~v4_orders_2(B_120) | v2_struct_0(B_120) | ~l1_pre_topc('#skF_2') | ~v8_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_306])).
% 4.13/1.69  tff(c_317, plain, (![B_120]: (k12_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_120))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_120)) | ~l1_waybel_0(B_120, '#skF_2') | ~v3_yellow_6(B_120, '#skF_2') | ~v7_waybel_0(B_120) | ~v4_orders_2(B_120) | v2_struct_0(B_120) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_73, c_60, c_56, c_79, c_312])).
% 4.13/1.69  tff(c_319, plain, (![B_121]: (k12_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_121))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_121)) | ~l1_waybel_0(B_121, '#skF_2') | ~v3_yellow_6(B_121, '#skF_2') | ~v7_waybel_0(B_121) | ~v4_orders_2(B_121) | v2_struct_0(B_121))), inference(negUnitSimplification, [status(thm)], [c_103, c_317])).
% 4.13/1.69  tff(c_38, plain, (~r2_hidden(k12_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', '#skF_3')), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.13/1.69  tff(c_325, plain, (~r2_hidden(k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', '#skF_3')), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', '#skF_3'))) | ~l1_waybel_0('#skF_3', '#skF_2') | ~v3_yellow_6('#skF_3', '#skF_2') | ~v7_waybel_0('#skF_3') | ~v4_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_319, c_38])).
% 4.13/1.69  tff(c_331, plain, (~r2_hidden(k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', '#skF_3')), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', '#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_325])).
% 4.13/1.69  tff(c_332, plain, (~r2_hidden(k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', '#skF_3')), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_331])).
% 4.13/1.69  tff(c_853, plain, (~l1_waybel_0('#skF_3', '#skF_2') | ~v3_yellow_6('#skF_3', '#skF_2') | ~v7_waybel_0('#skF_3') | ~v4_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_850, c_332])).
% 4.13/1.69  tff(c_856, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_853])).
% 4.13/1.69  tff(c_858, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_856])).
% 4.13/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.13/1.69  
% 4.13/1.69  Inference rules
% 4.13/1.69  ----------------------
% 4.13/1.69  #Ref     : 1
% 4.13/1.69  #Sup     : 149
% 4.13/1.69  #Fact    : 0
% 4.13/1.69  #Define  : 0
% 4.13/1.69  #Split   : 4
% 4.13/1.69  #Chain   : 0
% 4.13/1.69  #Close   : 0
% 4.13/1.69  
% 4.13/1.69  Ordering : KBO
% 4.13/1.69  
% 4.13/1.69  Simplification rules
% 4.13/1.69  ----------------------
% 4.13/1.69  #Subsume      : 17
% 4.13/1.69  #Demod        : 172
% 4.13/1.69  #Tautology    : 60
% 4.13/1.69  #SimpNegUnit  : 42
% 4.13/1.69  #BackRed      : 0
% 4.13/1.69  
% 4.13/1.69  #Partial instantiations: 0
% 4.13/1.69  #Strategies tried      : 1
% 4.13/1.69  
% 4.13/1.69  Timing (in seconds)
% 4.13/1.69  ----------------------
% 4.13/1.69  Preprocessing        : 0.37
% 4.13/1.69  Parsing              : 0.20
% 4.13/1.69  CNF conversion       : 0.03
% 4.13/1.69  Main loop            : 0.48
% 4.13/1.69  Inferencing          : 0.20
% 4.13/1.69  Reduction            : 0.14
% 4.13/1.69  Demodulation         : 0.10
% 4.13/1.69  BG Simplification    : 0.03
% 4.13/1.69  Subsumption          : 0.08
% 4.13/1.69  Abstraction          : 0.03
% 4.13/1.69  MUC search           : 0.00
% 4.13/1.69  Cooper               : 0.00
% 4.13/1.69  Total                : 0.90
% 4.13/1.69  Index Insertion      : 0.00
% 4.13/1.69  Index Deletion       : 0.00
% 4.13/1.69  Index Matching       : 0.00
% 4.13/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
