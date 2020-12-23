%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:17 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :  172 (2429 expanded)
%              Number of leaves         :   56 ( 877 expanded)
%              Depth                    :   21
%              Number of atoms          :  643 (10048 expanded)
%              Number of equality atoms :   46 ( 633 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v3_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k6_waybel_9 > k3_funct_2 > k2_yellow_6 > k3_waybel_2 > k12_lattice3 > k11_lattice3 > k4_waybel_1 > k2_zfmisc_1 > k1_funct_1 > k11_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(l1_waybel_9,type,(
    l1_waybel_9: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_245,negated_conjecture,(
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

tff(f_154,axiom,(
    ! [A] :
      ( l1_waybel_9(A)
     => ( l1_pre_topc(A)
        & l1_orders_2(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_148,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( v1_funct_1(k4_waybel_1(A,B))
        & v1_funct_2(k4_waybel_1(A,B),u1_struct_0(A),u1_struct_0(A))
        & m1_subset_1(k4_waybel_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_87,axiom,(
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

tff(f_170,axiom,(
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

tff(f_209,axiom,(
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

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_yellow_0)).

tff(f_135,axiom,(
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

tff(f_113,axiom,(
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

tff(f_65,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_50,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_48,plain,(
    v7_waybel_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_46,plain,(
    v3_yellow_6('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_44,plain,(
    l1_waybel_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_54,plain,(
    l1_waybel_9('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_75,plain,(
    ! [A_63] :
      ( l1_orders_2(A_63)
      | ~ l1_waybel_9(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_79,plain,(
    l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_75])).

tff(c_58,plain,(
    v1_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_69,plain,(
    ! [A_61] :
      ( l1_pre_topc(A_61)
      | ~ l1_waybel_9(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_73,plain,(
    l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_69])).

tff(c_6,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_81,plain,(
    ! [A_65] :
      ( u1_struct_0(A_65) = k2_struct_0(A_65)
      | ~ l1_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_86,plain,(
    ! [A_66] :
      ( u1_struct_0(A_66) = k2_struct_0(A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_6,c_81])).

tff(c_90,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_86])).

tff(c_97,plain,(
    ! [A_68,B_69] :
      ( v1_funct_1(k4_waybel_1(A_68,B_69))
      | ~ m1_subset_1(B_69,u1_struct_0(A_68))
      | ~ l1_orders_2(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_100,plain,(
    ! [B_69] :
      ( v1_funct_1(k4_waybel_1('#skF_2',B_69))
      | ~ m1_subset_1(B_69,k2_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_97])).

tff(c_102,plain,(
    ! [B_69] :
      ( v1_funct_1(k4_waybel_1('#skF_2',B_69))
      | ~ m1_subset_1(B_69,k2_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_100])).

tff(c_103,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ v2_struct_0(A_7)
      | ~ v1_lattice3(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_106,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_103,c_8])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_58,c_106])).

tff(c_112,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_66,plain,(
    v8_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_193,plain,(
    ! [A_93,B_94] :
      ( m1_subset_1(k11_yellow_6(A_93,B_94),u1_struct_0(A_93))
      | ~ l1_waybel_0(B_94,A_93)
      | ~ v3_yellow_6(B_94,A_93)
      | ~ v7_waybel_0(B_94)
      | ~ v4_orders_2(B_94)
      | v2_struct_0(B_94)
      | ~ l1_pre_topc(A_93)
      | ~ v8_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_205,plain,(
    ! [B_94] :
      ( m1_subset_1(k11_yellow_6('#skF_2',B_94),k2_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_94,'#skF_2')
      | ~ v3_yellow_6(B_94,'#skF_2')
      | ~ v7_waybel_0(B_94)
      | ~ v4_orders_2(B_94)
      | v2_struct_0(B_94)
      | ~ l1_pre_topc('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_193])).

tff(c_211,plain,(
    ! [B_94] :
      ( m1_subset_1(k11_yellow_6('#skF_2',B_94),k2_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_94,'#skF_2')
      | ~ v3_yellow_6(B_94,'#skF_2')
      | ~ v7_waybel_0(B_94)
      | ~ v4_orders_2(B_94)
      | v2_struct_0(B_94)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_73,c_205])).

tff(c_212,plain,(
    ! [B_94] :
      ( m1_subset_1(k11_yellow_6('#skF_2',B_94),k2_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_94,'#skF_2')
      | ~ v3_yellow_6(B_94,'#skF_2')
      | ~ v7_waybel_0(B_94)
      | ~ v4_orders_2(B_94)
      | v2_struct_0(B_94) ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_211])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_91,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_42])).

tff(c_113,plain,(
    ! [B_70] :
      ( v1_funct_1(k4_waybel_1('#skF_2',B_70))
      | ~ m1_subset_1(B_70,k2_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_117,plain,(
    v1_funct_1(k4_waybel_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_91,c_113])).

tff(c_118,plain,(
    ! [A_71,B_72] :
      ( v1_funct_2(k4_waybel_1(A_71,B_72),u1_struct_0(A_71),u1_struct_0(A_71))
      | ~ m1_subset_1(B_72,u1_struct_0(A_71))
      | ~ l1_orders_2(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_121,plain,(
    ! [B_72] :
      ( v1_funct_2(k4_waybel_1('#skF_2',B_72),k2_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_72,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_118])).

tff(c_126,plain,(
    ! [B_72] :
      ( v1_funct_2(k4_waybel_1('#skF_2',B_72),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_72,k2_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_90,c_90,c_121])).

tff(c_127,plain,(
    ! [B_72] :
      ( v1_funct_2(k4_waybel_1('#skF_2',B_72),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_72,k2_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_126])).

tff(c_64,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_62,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_60,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_56,plain,(
    v2_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_40,plain,(
    v5_pre_topc(k4_waybel_1('#skF_2','#skF_4'),'#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_164,plain,(
    ! [A_83,C_84,B_85] :
      ( k6_waybel_9(A_83,A_83,k4_waybel_1(A_83,C_84),B_85) = k3_waybel_2(A_83,C_84,B_85)
      | ~ m1_subset_1(C_84,u1_struct_0(A_83))
      | ~ l1_waybel_0(B_85,A_83)
      | v2_struct_0(B_85)
      | ~ l1_orders_2(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_166,plain,(
    ! [C_84,B_85] :
      ( k6_waybel_9('#skF_2','#skF_2',k4_waybel_1('#skF_2',C_84),B_85) = k3_waybel_2('#skF_2',C_84,B_85)
      | ~ m1_subset_1(C_84,k2_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_85,'#skF_2')
      | v2_struct_0(B_85)
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_164])).

tff(c_168,plain,(
    ! [C_84,B_85] :
      ( k6_waybel_9('#skF_2','#skF_2',k4_waybel_1('#skF_2',C_84),B_85) = k3_waybel_2('#skF_2',C_84,B_85)
      | ~ m1_subset_1(C_84,k2_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_85,'#skF_2')
      | v2_struct_0(B_85)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_166])).

tff(c_170,plain,(
    ! [C_86,B_87] :
      ( k6_waybel_9('#skF_2','#skF_2',k4_waybel_1('#skF_2',C_86),B_87) = k3_waybel_2('#skF_2',C_86,B_87)
      | ~ m1_subset_1(C_86,k2_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_87,'#skF_2')
      | v2_struct_0(B_87) ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_168])).

tff(c_173,plain,(
    ! [B_87] :
      ( k6_waybel_9('#skF_2','#skF_2',k4_waybel_1('#skF_2','#skF_4'),B_87) = k3_waybel_2('#skF_2','#skF_4',B_87)
      | ~ l1_waybel_0(B_87,'#skF_2')
      | v2_struct_0(B_87) ) ),
    inference(resolution,[status(thm)],[c_91,c_170])).

tff(c_604,plain,(
    ! [A_176,C_177,B_178] :
      ( r2_hidden(k2_yellow_6(u1_struct_0(A_176),A_176,C_177,k11_yellow_6(A_176,B_178)),k10_yellow_6(A_176,k6_waybel_9(A_176,A_176,C_177,B_178)))
      | ~ v5_pre_topc(C_177,A_176,A_176)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_176),u1_struct_0(A_176))))
      | ~ v1_funct_2(C_177,u1_struct_0(A_176),u1_struct_0(A_176))
      | ~ v1_funct_1(C_177)
      | ~ l1_waybel_0(B_178,A_176)
      | ~ v3_yellow_6(B_178,A_176)
      | ~ v7_waybel_0(B_178)
      | ~ v4_orders_2(B_178)
      | v2_struct_0(B_178)
      | ~ l1_waybel_9(A_176)
      | ~ v2_lattice3(A_176)
      | ~ v1_lattice3(A_176)
      | ~ v5_orders_2(A_176)
      | ~ v4_orders_2(A_176)
      | ~ v3_orders_2(A_176)
      | ~ v8_pre_topc(A_176)
      | ~ v2_pre_topc(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_610,plain,(
    ! [B_87] :
      ( r2_hidden(k2_yellow_6(u1_struct_0('#skF_2'),'#skF_2',k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_87)),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4',B_87)))
      | ~ v5_pre_topc(k4_waybel_1('#skF_2','#skF_4'),'#skF_2','#skF_2')
      | ~ m1_subset_1(k4_waybel_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_4'))
      | ~ l1_waybel_0(B_87,'#skF_2')
      | ~ v3_yellow_6(B_87,'#skF_2')
      | ~ v7_waybel_0(B_87)
      | ~ v4_orders_2(B_87)
      | v2_struct_0(B_87)
      | ~ l1_waybel_9('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_waybel_0(B_87,'#skF_2')
      | v2_struct_0(B_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_604])).

tff(c_617,plain,(
    ! [B_87] :
      ( r2_hidden(k2_yellow_6(k2_struct_0('#skF_2'),'#skF_2',k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_87)),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4',B_87)))
      | ~ m1_subset_1(k4_waybel_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_4'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v3_yellow_6(B_87,'#skF_2')
      | ~ v7_waybel_0(B_87)
      | ~ v4_orders_2(B_87)
      | ~ l1_waybel_0(B_87,'#skF_2')
      | v2_struct_0(B_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_60,c_58,c_56,c_54,c_117,c_90,c_90,c_90,c_90,c_40,c_90,c_610])).

tff(c_629,plain,(
    ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_4'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_617])).

tff(c_632,plain,(
    ~ m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_127,c_629])).

tff(c_636,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_632])).

tff(c_638,plain,(
    v1_funct_2(k4_waybel_1('#skF_2','#skF_4'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_617])).

tff(c_132,plain,(
    ! [A_74,B_75] :
      ( m1_subset_1(k4_waybel_1(A_74,B_75),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_74),u1_struct_0(A_74))))
      | ~ m1_subset_1(B_75,u1_struct_0(A_74))
      | ~ l1_orders_2(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_135,plain,(
    ! [B_75] :
      ( m1_subset_1(k4_waybel_1('#skF_2',B_75),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0('#skF_2'))))
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_132])).

tff(c_140,plain,(
    ! [B_75] :
      ( m1_subset_1(k4_waybel_1('#skF_2',B_75),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ m1_subset_1(B_75,k2_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_90,c_90,c_135])).

tff(c_141,plain,(
    ! [B_75] :
      ( m1_subset_1(k4_waybel_1('#skF_2',B_75),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ m1_subset_1(B_75,k2_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_140])).

tff(c_637,plain,(
    ! [B_87] :
      ( ~ m1_subset_1(k4_waybel_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | r2_hidden(k2_yellow_6(k2_struct_0('#skF_2'),'#skF_2',k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_87)),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4',B_87)))
      | ~ v3_yellow_6(B_87,'#skF_2')
      | ~ v7_waybel_0(B_87)
      | ~ v4_orders_2(B_87)
      | ~ l1_waybel_0(B_87,'#skF_2')
      | v2_struct_0(B_87) ) ),
    inference(splitRight,[status(thm)],[c_617])).

tff(c_639,plain,(
    ~ m1_subset_1(k4_waybel_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_637])).

tff(c_642,plain,(
    ~ m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_141,c_639])).

tff(c_646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_642])).

tff(c_648,plain,(
    m1_subset_1(k4_waybel_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_637])).

tff(c_174,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( k3_funct_2(A_88,B_89,C_90,D_91) = k1_funct_1(C_90,D_91)
      | ~ m1_subset_1(D_91,A_88)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ v1_funct_2(C_90,A_88,B_89)
      | ~ v1_funct_1(C_90)
      | v1_xboole_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_183,plain,(
    ! [B_89,C_90] :
      ( k3_funct_2(k2_struct_0('#skF_2'),B_89,C_90,'#skF_4') = k1_funct_1(C_90,'#skF_4')
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),B_89)))
      | ~ v1_funct_2(C_90,k2_struct_0('#skF_2'),B_89)
      | ~ v1_funct_1(C_90)
      | v1_xboole_0(k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_91,c_174])).

tff(c_231,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_14,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(k2_struct_0(A_13))
      | ~ l1_orders_2(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_234,plain,
    ( ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_231,c_14])).

tff(c_237,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_234])).

tff(c_239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_237])).

tff(c_241,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( k3_funct_2(A_1,B_2,C_3,D_4) = k1_funct_1(C_3,D_4)
      | ~ m1_subset_1(D_4,A_1)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_927,plain,(
    ! [A_204,B_205,C_206,B_207] :
      ( k3_funct_2(u1_struct_0(A_204),B_205,C_206,k11_yellow_6(A_204,B_207)) = k1_funct_1(C_206,k11_yellow_6(A_204,B_207))
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_204),B_205)))
      | ~ v1_funct_2(C_206,u1_struct_0(A_204),B_205)
      | ~ v1_funct_1(C_206)
      | v1_xboole_0(u1_struct_0(A_204))
      | ~ l1_waybel_0(B_207,A_204)
      | ~ v3_yellow_6(B_207,A_204)
      | ~ v7_waybel_0(B_207)
      | ~ v4_orders_2(B_207)
      | v2_struct_0(B_207)
      | ~ l1_pre_topc(A_204)
      | ~ v8_pre_topc(A_204)
      | ~ v2_pre_topc(A_204)
      | v2_struct_0(A_204) ) ),
    inference(resolution,[status(thm)],[c_193,c_2])).

tff(c_931,plain,(
    ! [B_205,C_206,B_207] :
      ( k3_funct_2(u1_struct_0('#skF_2'),B_205,C_206,k11_yellow_6('#skF_2',B_207)) = k1_funct_1(C_206,k11_yellow_6('#skF_2',B_207))
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),B_205)))
      | ~ v1_funct_2(C_206,u1_struct_0('#skF_2'),B_205)
      | ~ v1_funct_1(C_206)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_207,'#skF_2')
      | ~ v3_yellow_6(B_207,'#skF_2')
      | ~ v7_waybel_0(B_207)
      | ~ v4_orders_2(B_207)
      | v2_struct_0(B_207)
      | ~ l1_pre_topc('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_927])).

tff(c_934,plain,(
    ! [B_205,C_206,B_207] :
      ( k3_funct_2(k2_struct_0('#skF_2'),B_205,C_206,k11_yellow_6('#skF_2',B_207)) = k1_funct_1(C_206,k11_yellow_6('#skF_2',B_207))
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),B_205)))
      | ~ v1_funct_2(C_206,k2_struct_0('#skF_2'),B_205)
      | ~ v1_funct_1(C_206)
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_207,'#skF_2')
      | ~ v3_yellow_6(B_207,'#skF_2')
      | ~ v7_waybel_0(B_207)
      | ~ v4_orders_2(B_207)
      | v2_struct_0(B_207)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_73,c_90,c_90,c_90,c_931])).

tff(c_965,plain,(
    ! [B_210,C_211,B_212] :
      ( k3_funct_2(k2_struct_0('#skF_2'),B_210,C_211,k11_yellow_6('#skF_2',B_212)) = k1_funct_1(C_211,k11_yellow_6('#skF_2',B_212))
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),B_210)))
      | ~ v1_funct_2(C_211,k2_struct_0('#skF_2'),B_210)
      | ~ v1_funct_1(C_211)
      | ~ l1_waybel_0(B_212,'#skF_2')
      | ~ v3_yellow_6(B_212,'#skF_2')
      | ~ v7_waybel_0(B_212)
      | ~ v4_orders_2(B_212)
      | v2_struct_0(B_212) ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_241,c_934])).

tff(c_967,plain,(
    ! [B_212] :
      ( k3_funct_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_212)) = k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_212))
      | ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_4'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_4'))
      | ~ l1_waybel_0(B_212,'#skF_2')
      | ~ v3_yellow_6(B_212,'#skF_2')
      | ~ v7_waybel_0(B_212)
      | ~ v4_orders_2(B_212)
      | v2_struct_0(B_212) ) ),
    inference(resolution,[status(thm)],[c_648,c_965])).

tff(c_974,plain,(
    ! [B_213] :
      ( k3_funct_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_213)) = k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_213))
      | ~ l1_waybel_0(B_213,'#skF_2')
      | ~ v3_yellow_6(B_213,'#skF_2')
      | ~ v7_waybel_0(B_213)
      | ~ v4_orders_2(B_213)
      | v2_struct_0(B_213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_638,c_967])).

tff(c_26,plain,(
    ! [A_40,B_41] :
      ( v1_funct_2(k4_waybel_1(A_40,B_41),u1_struct_0(A_40),u1_struct_0(A_40))
      | ~ m1_subset_1(B_41,u1_struct_0(A_40))
      | ~ l1_orders_2(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_24,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(k4_waybel_1(A_40,B_41),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_40),u1_struct_0(A_40))))
      | ~ m1_subset_1(B_41,u1_struct_0(A_40))
      | ~ l1_orders_2(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_491,plain,(
    ! [A_159,B_160,D_161] :
      ( k3_funct_2(u1_struct_0(A_159),u1_struct_0(A_159),k4_waybel_1(A_159,B_160),D_161) = k11_lattice3(A_159,B_160,D_161)
      | ~ m1_subset_1(D_161,u1_struct_0(A_159))
      | ~ m1_subset_1(k4_waybel_1(A_159,B_160),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_159),u1_struct_0(A_159))))
      | ~ v1_funct_2(k4_waybel_1(A_159,B_160),u1_struct_0(A_159),u1_struct_0(A_159))
      | ~ v1_funct_1(k4_waybel_1(A_159,B_160))
      | ~ m1_subset_1(B_160,u1_struct_0(A_159))
      | ~ l1_orders_2(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_505,plain,(
    ! [A_162,B_163,D_164] :
      ( k3_funct_2(u1_struct_0(A_162),u1_struct_0(A_162),k4_waybel_1(A_162,B_163),D_164) = k11_lattice3(A_162,B_163,D_164)
      | ~ m1_subset_1(D_164,u1_struct_0(A_162))
      | ~ v1_funct_2(k4_waybel_1(A_162,B_163),u1_struct_0(A_162),u1_struct_0(A_162))
      | ~ v1_funct_1(k4_waybel_1(A_162,B_163))
      | ~ m1_subset_1(B_163,u1_struct_0(A_162))
      | ~ l1_orders_2(A_162)
      | v2_struct_0(A_162) ) ),
    inference(resolution,[status(thm)],[c_24,c_491])).

tff(c_519,plain,(
    ! [A_165,B_166,D_167] :
      ( k3_funct_2(u1_struct_0(A_165),u1_struct_0(A_165),k4_waybel_1(A_165,B_166),D_167) = k11_lattice3(A_165,B_166,D_167)
      | ~ m1_subset_1(D_167,u1_struct_0(A_165))
      | ~ v1_funct_1(k4_waybel_1(A_165,B_166))
      | ~ m1_subset_1(B_166,u1_struct_0(A_165))
      | ~ l1_orders_2(A_165)
      | v2_struct_0(A_165) ) ),
    inference(resolution,[status(thm)],[c_26,c_505])).

tff(c_531,plain,(
    ! [B_166,D_167] :
      ( k3_funct_2(k2_struct_0('#skF_2'),u1_struct_0('#skF_2'),k4_waybel_1('#skF_2',B_166),D_167) = k11_lattice3('#skF_2',B_166,D_167)
      | ~ m1_subset_1(D_167,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2',B_166))
      | ~ m1_subset_1(B_166,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_519])).

tff(c_538,plain,(
    ! [B_166,D_167] :
      ( k3_funct_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k4_waybel_1('#skF_2',B_166),D_167) = k11_lattice3('#skF_2',B_166,D_167)
      | ~ m1_subset_1(D_167,k2_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2',B_166))
      | ~ m1_subset_1(B_166,k2_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_90,c_90,c_90,c_531])).

tff(c_539,plain,(
    ! [B_166,D_167] :
      ( k3_funct_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k4_waybel_1('#skF_2',B_166),D_167) = k11_lattice3('#skF_2',B_166,D_167)
      | ~ m1_subset_1(D_167,k2_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2',B_166))
      | ~ m1_subset_1(B_166,k2_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_538])).

tff(c_980,plain,(
    ! [B_213] :
      ( k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_213)) = k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_213))
      | ~ m1_subset_1(k11_yellow_6('#skF_2',B_213),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_4'))
      | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_213,'#skF_2')
      | ~ v3_yellow_6(B_213,'#skF_2')
      | ~ v7_waybel_0(B_213)
      | ~ v4_orders_2(B_213)
      | v2_struct_0(B_213) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_539])).

tff(c_993,plain,(
    ! [B_214] :
      ( k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_214)) = k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_214))
      | ~ m1_subset_1(k11_yellow_6('#skF_2',B_214),k2_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_214,'#skF_2')
      | ~ v3_yellow_6(B_214,'#skF_2')
      | ~ v7_waybel_0(B_214)
      | ~ v4_orders_2(B_214)
      | v2_struct_0(B_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_117,c_980])).

tff(c_998,plain,(
    ! [B_215] :
      ( k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_215)) = k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_215))
      | ~ l1_waybel_0(B_215,'#skF_2')
      | ~ v3_yellow_6(B_215,'#skF_2')
      | ~ v7_waybel_0(B_215)
      | ~ v4_orders_2(B_215)
      | v2_struct_0(B_215) ) ),
    inference(resolution,[status(thm)],[c_212,c_993])).

tff(c_257,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( k2_yellow_6(A_100,B_101,C_102,D_103) = k1_funct_1(C_102,D_103)
      | ~ m1_subset_1(D_103,A_100)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,u1_struct_0(B_101))))
      | ~ v1_funct_2(C_102,A_100,u1_struct_0(B_101))
      | ~ v1_funct_1(C_102)
      | ~ l1_orders_2(B_101)
      | v2_struct_0(B_101)
      | v1_xboole_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_259,plain,(
    ! [B_101,C_102,B_94] :
      ( k2_yellow_6(k2_struct_0('#skF_2'),B_101,C_102,k11_yellow_6('#skF_2',B_94)) = k1_funct_1(C_102,k11_yellow_6('#skF_2',B_94))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_101))))
      | ~ v1_funct_2(C_102,k2_struct_0('#skF_2'),u1_struct_0(B_101))
      | ~ v1_funct_1(C_102)
      | ~ l1_orders_2(B_101)
      | v2_struct_0(B_101)
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_94,'#skF_2')
      | ~ v3_yellow_6(B_94,'#skF_2')
      | ~ v7_waybel_0(B_94)
      | ~ v4_orders_2(B_94)
      | v2_struct_0(B_94) ) ),
    inference(resolution,[status(thm)],[c_212,c_257])).

tff(c_358,plain,(
    ! [B_121,C_122,B_123] :
      ( k2_yellow_6(k2_struct_0('#skF_2'),B_121,C_122,k11_yellow_6('#skF_2',B_123)) = k1_funct_1(C_122,k11_yellow_6('#skF_2',B_123))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_121))))
      | ~ v1_funct_2(C_122,k2_struct_0('#skF_2'),u1_struct_0(B_121))
      | ~ v1_funct_1(C_122)
      | ~ l1_orders_2(B_121)
      | v2_struct_0(B_121)
      | ~ l1_waybel_0(B_123,'#skF_2')
      | ~ v3_yellow_6(B_123,'#skF_2')
      | ~ v7_waybel_0(B_123)
      | ~ v4_orders_2(B_123)
      | v2_struct_0(B_123) ) ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_259])).

tff(c_360,plain,(
    ! [C_122,B_123] :
      ( k2_yellow_6(k2_struct_0('#skF_2'),'#skF_2',C_122,k11_yellow_6('#skF_2',B_123)) = k1_funct_1(C_122,k11_yellow_6('#skF_2',B_123))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_122,k2_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_122)
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_waybel_0(B_123,'#skF_2')
      | ~ v3_yellow_6(B_123,'#skF_2')
      | ~ v7_waybel_0(B_123)
      | ~ v4_orders_2(B_123)
      | v2_struct_0(B_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_358])).

tff(c_362,plain,(
    ! [C_122,B_123] :
      ( k2_yellow_6(k2_struct_0('#skF_2'),'#skF_2',C_122,k11_yellow_6('#skF_2',B_123)) = k1_funct_1(C_122,k11_yellow_6('#skF_2',B_123))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_122,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_122)
      | v2_struct_0('#skF_2')
      | ~ l1_waybel_0(B_123,'#skF_2')
      | ~ v3_yellow_6(B_123,'#skF_2')
      | ~ v7_waybel_0(B_123)
      | ~ v4_orders_2(B_123)
      | v2_struct_0(B_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_90,c_360])).

tff(c_363,plain,(
    ! [C_122,B_123] :
      ( k2_yellow_6(k2_struct_0('#skF_2'),'#skF_2',C_122,k11_yellow_6('#skF_2',B_123)) = k1_funct_1(C_122,k11_yellow_6('#skF_2',B_123))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_122,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_122)
      | ~ l1_waybel_0(B_123,'#skF_2')
      | ~ v3_yellow_6(B_123,'#skF_2')
      | ~ v7_waybel_0(B_123)
      | ~ v4_orders_2(B_123)
      | v2_struct_0(B_123) ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_362])).

tff(c_662,plain,(
    ! [B_123] :
      ( k2_yellow_6(k2_struct_0('#skF_2'),'#skF_2',k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_123)) = k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_123))
      | ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_4'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_4'))
      | ~ l1_waybel_0(B_123,'#skF_2')
      | ~ v3_yellow_6(B_123,'#skF_2')
      | ~ v7_waybel_0(B_123)
      | ~ v4_orders_2(B_123)
      | v2_struct_0(B_123) ) ),
    inference(resolution,[status(thm)],[c_648,c_363])).

tff(c_833,plain,(
    ! [B_192] :
      ( k2_yellow_6(k2_struct_0('#skF_2'),'#skF_2',k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_192)) = k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_192))
      | ~ l1_waybel_0(B_192,'#skF_2')
      | ~ v3_yellow_6(B_192,'#skF_2')
      | ~ v7_waybel_0(B_192)
      | ~ v4_orders_2(B_192)
      | v2_struct_0(B_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_638,c_662])).

tff(c_613,plain,(
    ! [C_177,B_178] :
      ( r2_hidden(k2_yellow_6(k2_struct_0('#skF_2'),'#skF_2',C_177,k11_yellow_6('#skF_2',B_178)),k10_yellow_6('#skF_2',k6_waybel_9('#skF_2','#skF_2',C_177,B_178)))
      | ~ v5_pre_topc(C_177,'#skF_2','#skF_2')
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_177,u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_177)
      | ~ l1_waybel_0(B_178,'#skF_2')
      | ~ v3_yellow_6(B_178,'#skF_2')
      | ~ v7_waybel_0(B_178)
      | ~ v4_orders_2(B_178)
      | v2_struct_0(B_178)
      | ~ l1_waybel_9('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_604])).

tff(c_619,plain,(
    ! [C_177,B_178] :
      ( r2_hidden(k2_yellow_6(k2_struct_0('#skF_2'),'#skF_2',C_177,k11_yellow_6('#skF_2',B_178)),k10_yellow_6('#skF_2',k6_waybel_9('#skF_2','#skF_2',C_177,B_178)))
      | ~ v5_pre_topc(C_177,'#skF_2','#skF_2')
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_177,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_177)
      | ~ l1_waybel_0(B_178,'#skF_2')
      | ~ v3_yellow_6(B_178,'#skF_2')
      | ~ v7_waybel_0(B_178)
      | ~ v4_orders_2(B_178)
      | v2_struct_0(B_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_60,c_58,c_56,c_54,c_90,c_90,c_90,c_90,c_613])).

tff(c_842,plain,(
    ! [B_192] :
      ( r2_hidden(k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_192)),k10_yellow_6('#skF_2',k6_waybel_9('#skF_2','#skF_2',k4_waybel_1('#skF_2','#skF_4'),B_192)))
      | ~ v5_pre_topc(k4_waybel_1('#skF_2','#skF_4'),'#skF_2','#skF_2')
      | ~ m1_subset_1(k4_waybel_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_4'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_4'))
      | ~ l1_waybel_0(B_192,'#skF_2')
      | ~ v3_yellow_6(B_192,'#skF_2')
      | ~ v7_waybel_0(B_192)
      | ~ v4_orders_2(B_192)
      | v2_struct_0(B_192)
      | ~ l1_waybel_0(B_192,'#skF_2')
      | ~ v3_yellow_6(B_192,'#skF_2')
      | ~ v7_waybel_0(B_192)
      | ~ v4_orders_2(B_192)
      | v2_struct_0(B_192) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_833,c_619])).

tff(c_850,plain,(
    ! [B_193] :
      ( r2_hidden(k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_193)),k10_yellow_6('#skF_2',k6_waybel_9('#skF_2','#skF_2',k4_waybel_1('#skF_2','#skF_4'),B_193)))
      | ~ l1_waybel_0(B_193,'#skF_2')
      | ~ v3_yellow_6(B_193,'#skF_2')
      | ~ v7_waybel_0(B_193)
      | ~ v4_orders_2(B_193)
      | v2_struct_0(B_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_638,c_648,c_40,c_842])).

tff(c_853,plain,(
    ! [B_87] :
      ( r2_hidden(k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_87)),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4',B_87)))
      | ~ l1_waybel_0(B_87,'#skF_2')
      | ~ v3_yellow_6(B_87,'#skF_2')
      | ~ v7_waybel_0(B_87)
      | ~ v4_orders_2(B_87)
      | v2_struct_0(B_87)
      | ~ l1_waybel_0(B_87,'#skF_2')
      | v2_struct_0(B_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_850])).

tff(c_1048,plain,(
    ! [B_222] :
      ( r2_hidden(k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_222)),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4',B_222)))
      | ~ l1_waybel_0(B_222,'#skF_2')
      | ~ v3_yellow_6(B_222,'#skF_2')
      | ~ v7_waybel_0(B_222)
      | ~ v4_orders_2(B_222)
      | v2_struct_0(B_222)
      | ~ l1_waybel_0(B_222,'#skF_2')
      | v2_struct_0(B_222)
      | ~ l1_waybel_0(B_222,'#skF_2')
      | ~ v3_yellow_6(B_222,'#skF_2')
      | ~ v7_waybel_0(B_222)
      | ~ v4_orders_2(B_222)
      | v2_struct_0(B_222) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_998,c_853])).

tff(c_213,plain,(
    ! [B_95] :
      ( m1_subset_1(k11_yellow_6('#skF_2',B_95),k2_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_95,'#skF_2')
      | ~ v3_yellow_6(B_95,'#skF_2')
      | ~ v7_waybel_0(B_95)
      | ~ v4_orders_2(B_95)
      | v2_struct_0(B_95) ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_211])).

tff(c_146,plain,(
    ! [A_77,B_78,C_79] :
      ( k12_lattice3(A_77,B_78,C_79) = k11_lattice3(A_77,B_78,C_79)
      | ~ m1_subset_1(C_79,u1_struct_0(A_77))
      | ~ m1_subset_1(B_78,u1_struct_0(A_77))
      | ~ l1_orders_2(A_77)
      | ~ v2_lattice3(A_77)
      | ~ v5_orders_2(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_148,plain,(
    ! [B_78,C_79] :
      ( k12_lattice3('#skF_2',B_78,C_79) = k11_lattice3('#skF_2',B_78,C_79)
      | ~ m1_subset_1(C_79,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_146])).

tff(c_150,plain,(
    ! [B_78,C_79] :
      ( k12_lattice3('#skF_2',B_78,C_79) = k11_lattice3('#skF_2',B_78,C_79)
      | ~ m1_subset_1(C_79,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_78,k2_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_79,c_90,c_148])).

tff(c_278,plain,(
    ! [B_106,B_107] :
      ( k12_lattice3('#skF_2',B_106,k11_yellow_6('#skF_2',B_107)) = k11_lattice3('#skF_2',B_106,k11_yellow_6('#skF_2',B_107))
      | ~ m1_subset_1(B_106,k2_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_107,'#skF_2')
      | ~ v3_yellow_6(B_107,'#skF_2')
      | ~ v7_waybel_0(B_107)
      | ~ v4_orders_2(B_107)
      | v2_struct_0(B_107) ) ),
    inference(resolution,[status(thm)],[c_213,c_150])).

tff(c_285,plain,(
    ! [B_108] :
      ( k12_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_108)) = k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_108))
      | ~ l1_waybel_0(B_108,'#skF_2')
      | ~ v3_yellow_6(B_108,'#skF_2')
      | ~ v7_waybel_0(B_108)
      | ~ v4_orders_2(B_108)
      | v2_struct_0(B_108) ) ),
    inference(resolution,[status(thm)],[c_91,c_278])).

tff(c_38,plain,(
    ~ r2_hidden(k12_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2','#skF_3')),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_291,plain,
    ( ~ r2_hidden(k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2','#skF_3')),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4','#skF_3')))
    | ~ l1_waybel_0('#skF_3','#skF_2')
    | ~ v3_yellow_6('#skF_3','#skF_2')
    | ~ v7_waybel_0('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_38])).

tff(c_297,plain,
    ( ~ r2_hidden(k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2','#skF_3')),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4','#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_291])).

tff(c_298,plain,(
    ~ r2_hidden(k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2','#skF_3')),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_297])).

tff(c_1051,plain,
    ( ~ l1_waybel_0('#skF_3','#skF_2')
    | ~ v3_yellow_6('#skF_3','#skF_2')
    | ~ v7_waybel_0('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1048,c_298])).

tff(c_1054,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_1051])).

tff(c_1056,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1054])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.04/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.69  
% 4.04/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.69  %$ v5_pre_topc > v1_funct_2 > v3_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k6_waybel_9 > k3_funct_2 > k2_yellow_6 > k3_waybel_2 > k12_lattice3 > k11_lattice3 > k4_waybel_1 > k2_zfmisc_1 > k1_funct_1 > k11_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 4.04/1.69  
% 4.04/1.69  %Foreground sorts:
% 4.04/1.69  
% 4.04/1.69  
% 4.04/1.69  %Background operators:
% 4.04/1.69  
% 4.04/1.69  
% 4.04/1.69  %Foreground operators:
% 4.04/1.69  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.04/1.69  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 4.04/1.69  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.04/1.69  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.04/1.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.04/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.04/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.04/1.69  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 4.04/1.69  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 4.04/1.69  tff(k6_waybel_9, type, k6_waybel_9: ($i * $i * $i * $i) > $i).
% 4.04/1.69  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.04/1.69  tff(k3_waybel_2, type, k3_waybel_2: ($i * $i * $i) > $i).
% 4.04/1.69  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 4.04/1.69  tff(k2_yellow_6, type, k2_yellow_6: ($i * $i * $i * $i) > $i).
% 4.04/1.69  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 4.04/1.69  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 4.04/1.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.04/1.69  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 4.04/1.69  tff('#skF_2', type, '#skF_2': $i).
% 4.04/1.69  tff('#skF_3', type, '#skF_3': $i).
% 4.04/1.69  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.04/1.69  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.04/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.04/1.69  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.04/1.69  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.04/1.69  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.04/1.69  tff(k4_waybel_1, type, k4_waybel_1: ($i * $i) > $i).
% 4.04/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.04/1.69  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 4.04/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.04/1.69  tff('#skF_4', type, '#skF_4': $i).
% 4.04/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.04/1.69  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 4.04/1.69  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.04/1.69  tff(k11_yellow_6, type, k11_yellow_6: ($i * $i) > $i).
% 4.04/1.69  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 4.04/1.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.04/1.69  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.04/1.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.04/1.69  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.04/1.69  tff(l1_waybel_9, type, l1_waybel_9: $i > $o).
% 4.04/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.04/1.69  
% 4.04/1.72  tff(f_245, negated_conjecture, ~(![A]: ((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_waybel_9(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (v5_pre_topc(k4_waybel_1(A, C), A, A) => r2_hidden(k12_lattice3(A, C, k11_yellow_6(A, B)), k10_yellow_6(A, k3_waybel_2(A, C, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_waybel_9)).
% 4.04/1.72  tff(f_154, axiom, (![A]: (l1_waybel_9(A) => (l1_pre_topc(A) & l1_orders_2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 4.04/1.72  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.04/1.72  tff(f_42, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.04/1.72  tff(f_148, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => ((v1_funct_1(k4_waybel_1(A, B)) & v1_funct_2(k4_waybel_1(A, B), u1_struct_0(A), u1_struct_0(A))) & m1_subset_1(k4_waybel_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_waybel_1)).
% 4.04/1.72  tff(f_53, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 4.04/1.72  tff(f_87, axiom, (![A, B]: (((((((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A)) & l1_waybel_0(B, A)) => m1_subset_1(k11_yellow_6(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_yellow_6)).
% 4.04/1.72  tff(f_170, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k6_waybel_9(A, A, k4_waybel_1(A, C), B) = k3_waybel_2(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_waybel_9)).
% 4.04/1.72  tff(f_209, axiom, (![A]: ((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_waybel_9(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A)) & l1_waybel_0(B, A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))) => (v5_pre_topc(C, A, A) => r2_hidden(k2_yellow_6(u1_struct_0(A), A, C, k11_yellow_6(A, B)), k10_yellow_6(A, k6_waybel_9(A, A, C, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_waybel_9)).
% 4.04/1.72  tff(f_38, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.04/1.72  tff(f_95, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_yellow_0)).
% 4.04/1.72  tff(f_135, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))) => ((C = k4_waybel_1(A, B)) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (k3_funct_2(u1_struct_0(A), u1_struct_0(A), C, D) = k11_lattice3(A, B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_waybel_1)).
% 4.04/1.72  tff(f_113, axiom, (![A, B, C, D]: (((((((~v1_xboole_0(A) & ~v2_struct_0(B)) & l1_orders_2(B)) & v1_funct_1(C)) & v1_funct_2(C, A, u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, u1_struct_0(B))))) & m1_subset_1(D, A)) => (k2_yellow_6(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_yellow_6)).
% 4.04/1.72  tff(f_65, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 4.04/1.72  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_245])).
% 4.04/1.72  tff(c_50, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_245])).
% 4.04/1.72  tff(c_48, plain, (v7_waybel_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_245])).
% 4.04/1.72  tff(c_46, plain, (v3_yellow_6('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_245])).
% 4.04/1.72  tff(c_44, plain, (l1_waybel_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_245])).
% 4.04/1.72  tff(c_54, plain, (l1_waybel_9('#skF_2')), inference(cnfTransformation, [status(thm)], [f_245])).
% 4.04/1.72  tff(c_75, plain, (![A_63]: (l1_orders_2(A_63) | ~l1_waybel_9(A_63))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.04/1.72  tff(c_79, plain, (l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_54, c_75])).
% 4.04/1.72  tff(c_58, plain, (v1_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_245])).
% 4.04/1.72  tff(c_69, plain, (![A_61]: (l1_pre_topc(A_61) | ~l1_waybel_9(A_61))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.04/1.72  tff(c_73, plain, (l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_69])).
% 4.04/1.72  tff(c_6, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.04/1.72  tff(c_81, plain, (![A_65]: (u1_struct_0(A_65)=k2_struct_0(A_65) | ~l1_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.04/1.72  tff(c_86, plain, (![A_66]: (u1_struct_0(A_66)=k2_struct_0(A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_6, c_81])).
% 4.04/1.72  tff(c_90, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_73, c_86])).
% 4.04/1.72  tff(c_97, plain, (![A_68, B_69]: (v1_funct_1(k4_waybel_1(A_68, B_69)) | ~m1_subset_1(B_69, u1_struct_0(A_68)) | ~l1_orders_2(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.04/1.72  tff(c_100, plain, (![B_69]: (v1_funct_1(k4_waybel_1('#skF_2', B_69)) | ~m1_subset_1(B_69, k2_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_97])).
% 4.04/1.72  tff(c_102, plain, (![B_69]: (v1_funct_1(k4_waybel_1('#skF_2', B_69)) | ~m1_subset_1(B_69, k2_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_100])).
% 4.04/1.72  tff(c_103, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_102])).
% 4.04/1.72  tff(c_8, plain, (![A_7]: (~v2_struct_0(A_7) | ~v1_lattice3(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.04/1.72  tff(c_106, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_103, c_8])).
% 4.04/1.72  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_58, c_106])).
% 4.04/1.72  tff(c_112, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_102])).
% 4.04/1.72  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_245])).
% 4.04/1.72  tff(c_66, plain, (v8_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_245])).
% 4.04/1.72  tff(c_193, plain, (![A_93, B_94]: (m1_subset_1(k11_yellow_6(A_93, B_94), u1_struct_0(A_93)) | ~l1_waybel_0(B_94, A_93) | ~v3_yellow_6(B_94, A_93) | ~v7_waybel_0(B_94) | ~v4_orders_2(B_94) | v2_struct_0(B_94) | ~l1_pre_topc(A_93) | ~v8_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.04/1.72  tff(c_205, plain, (![B_94]: (m1_subset_1(k11_yellow_6('#skF_2', B_94), k2_struct_0('#skF_2')) | ~l1_waybel_0(B_94, '#skF_2') | ~v3_yellow_6(B_94, '#skF_2') | ~v7_waybel_0(B_94) | ~v4_orders_2(B_94) | v2_struct_0(B_94) | ~l1_pre_topc('#skF_2') | ~v8_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_193])).
% 4.04/1.72  tff(c_211, plain, (![B_94]: (m1_subset_1(k11_yellow_6('#skF_2', B_94), k2_struct_0('#skF_2')) | ~l1_waybel_0(B_94, '#skF_2') | ~v3_yellow_6(B_94, '#skF_2') | ~v7_waybel_0(B_94) | ~v4_orders_2(B_94) | v2_struct_0(B_94) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_73, c_205])).
% 4.04/1.72  tff(c_212, plain, (![B_94]: (m1_subset_1(k11_yellow_6('#skF_2', B_94), k2_struct_0('#skF_2')) | ~l1_waybel_0(B_94, '#skF_2') | ~v3_yellow_6(B_94, '#skF_2') | ~v7_waybel_0(B_94) | ~v4_orders_2(B_94) | v2_struct_0(B_94))), inference(negUnitSimplification, [status(thm)], [c_112, c_211])).
% 4.04/1.72  tff(c_42, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_245])).
% 4.04/1.72  tff(c_91, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_42])).
% 4.04/1.72  tff(c_113, plain, (![B_70]: (v1_funct_1(k4_waybel_1('#skF_2', B_70)) | ~m1_subset_1(B_70, k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_102])).
% 4.04/1.72  tff(c_117, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_91, c_113])).
% 4.04/1.72  tff(c_118, plain, (![A_71, B_72]: (v1_funct_2(k4_waybel_1(A_71, B_72), u1_struct_0(A_71), u1_struct_0(A_71)) | ~m1_subset_1(B_72, u1_struct_0(A_71)) | ~l1_orders_2(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.04/1.72  tff(c_121, plain, (![B_72]: (v1_funct_2(k4_waybel_1('#skF_2', B_72), k2_struct_0('#skF_2'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_72, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_118])).
% 4.04/1.72  tff(c_126, plain, (![B_72]: (v1_funct_2(k4_waybel_1('#skF_2', B_72), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~m1_subset_1(B_72, k2_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_90, c_90, c_121])).
% 4.04/1.72  tff(c_127, plain, (![B_72]: (v1_funct_2(k4_waybel_1('#skF_2', B_72), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~m1_subset_1(B_72, k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_112, c_126])).
% 4.04/1.72  tff(c_64, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_245])).
% 4.04/1.72  tff(c_62, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_245])).
% 4.04/1.72  tff(c_60, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_245])).
% 4.04/1.72  tff(c_56, plain, (v2_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_245])).
% 4.04/1.72  tff(c_40, plain, (v5_pre_topc(k4_waybel_1('#skF_2', '#skF_4'), '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_245])).
% 4.04/1.72  tff(c_164, plain, (![A_83, C_84, B_85]: (k6_waybel_9(A_83, A_83, k4_waybel_1(A_83, C_84), B_85)=k3_waybel_2(A_83, C_84, B_85) | ~m1_subset_1(C_84, u1_struct_0(A_83)) | ~l1_waybel_0(B_85, A_83) | v2_struct_0(B_85) | ~l1_orders_2(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.04/1.72  tff(c_166, plain, (![C_84, B_85]: (k6_waybel_9('#skF_2', '#skF_2', k4_waybel_1('#skF_2', C_84), B_85)=k3_waybel_2('#skF_2', C_84, B_85) | ~m1_subset_1(C_84, k2_struct_0('#skF_2')) | ~l1_waybel_0(B_85, '#skF_2') | v2_struct_0(B_85) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_164])).
% 4.04/1.72  tff(c_168, plain, (![C_84, B_85]: (k6_waybel_9('#skF_2', '#skF_2', k4_waybel_1('#skF_2', C_84), B_85)=k3_waybel_2('#skF_2', C_84, B_85) | ~m1_subset_1(C_84, k2_struct_0('#skF_2')) | ~l1_waybel_0(B_85, '#skF_2') | v2_struct_0(B_85) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_166])).
% 4.04/1.72  tff(c_170, plain, (![C_86, B_87]: (k6_waybel_9('#skF_2', '#skF_2', k4_waybel_1('#skF_2', C_86), B_87)=k3_waybel_2('#skF_2', C_86, B_87) | ~m1_subset_1(C_86, k2_struct_0('#skF_2')) | ~l1_waybel_0(B_87, '#skF_2') | v2_struct_0(B_87))), inference(negUnitSimplification, [status(thm)], [c_112, c_168])).
% 4.04/1.72  tff(c_173, plain, (![B_87]: (k6_waybel_9('#skF_2', '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), B_87)=k3_waybel_2('#skF_2', '#skF_4', B_87) | ~l1_waybel_0(B_87, '#skF_2') | v2_struct_0(B_87))), inference(resolution, [status(thm)], [c_91, c_170])).
% 4.04/1.72  tff(c_604, plain, (![A_176, C_177, B_178]: (r2_hidden(k2_yellow_6(u1_struct_0(A_176), A_176, C_177, k11_yellow_6(A_176, B_178)), k10_yellow_6(A_176, k6_waybel_9(A_176, A_176, C_177, B_178))) | ~v5_pre_topc(C_177, A_176, A_176) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_176), u1_struct_0(A_176)))) | ~v1_funct_2(C_177, u1_struct_0(A_176), u1_struct_0(A_176)) | ~v1_funct_1(C_177) | ~l1_waybel_0(B_178, A_176) | ~v3_yellow_6(B_178, A_176) | ~v7_waybel_0(B_178) | ~v4_orders_2(B_178) | v2_struct_0(B_178) | ~l1_waybel_9(A_176) | ~v2_lattice3(A_176) | ~v1_lattice3(A_176) | ~v5_orders_2(A_176) | ~v4_orders_2(A_176) | ~v3_orders_2(A_176) | ~v8_pre_topc(A_176) | ~v2_pre_topc(A_176))), inference(cnfTransformation, [status(thm)], [f_209])).
% 4.04/1.72  tff(c_610, plain, (![B_87]: (r2_hidden(k2_yellow_6(u1_struct_0('#skF_2'), '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_87)), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', B_87))) | ~v5_pre_topc(k4_waybel_1('#skF_2', '#skF_4'), '#skF_2', '#skF_2') | ~m1_subset_1(k4_waybel_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_waybel_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', '#skF_4')) | ~l1_waybel_0(B_87, '#skF_2') | ~v3_yellow_6(B_87, '#skF_2') | ~v7_waybel_0(B_87) | ~v4_orders_2(B_87) | v2_struct_0(B_87) | ~l1_waybel_9('#skF_2') | ~v2_lattice3('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | ~v8_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_waybel_0(B_87, '#skF_2') | v2_struct_0(B_87))), inference(superposition, [status(thm), theory('equality')], [c_173, c_604])).
% 4.04/1.72  tff(c_617, plain, (![B_87]: (r2_hidden(k2_yellow_6(k2_struct_0('#skF_2'), '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_87)), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', B_87))) | ~m1_subset_1(k4_waybel_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(k4_waybel_1('#skF_2', '#skF_4'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v3_yellow_6(B_87, '#skF_2') | ~v7_waybel_0(B_87) | ~v4_orders_2(B_87) | ~l1_waybel_0(B_87, '#skF_2') | v2_struct_0(B_87))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_60, c_58, c_56, c_54, c_117, c_90, c_90, c_90, c_90, c_40, c_90, c_610])).
% 4.04/1.72  tff(c_629, plain, (~v1_funct_2(k4_waybel_1('#skF_2', '#skF_4'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_617])).
% 4.04/1.72  tff(c_632, plain, (~m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_127, c_629])).
% 4.04/1.72  tff(c_636, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_632])).
% 4.04/1.72  tff(c_638, plain, (v1_funct_2(k4_waybel_1('#skF_2', '#skF_4'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_617])).
% 4.04/1.72  tff(c_132, plain, (![A_74, B_75]: (m1_subset_1(k4_waybel_1(A_74, B_75), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_74), u1_struct_0(A_74)))) | ~m1_subset_1(B_75, u1_struct_0(A_74)) | ~l1_orders_2(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.04/1.72  tff(c_135, plain, (![B_75]: (m1_subset_1(k4_waybel_1('#skF_2', B_75), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0('#skF_2')))) | ~m1_subset_1(B_75, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_132])).
% 4.04/1.72  tff(c_140, plain, (![B_75]: (m1_subset_1(k4_waybel_1('#skF_2', B_75), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~m1_subset_1(B_75, k2_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_90, c_90, c_135])).
% 4.04/1.72  tff(c_141, plain, (![B_75]: (m1_subset_1(k4_waybel_1('#skF_2', B_75), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~m1_subset_1(B_75, k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_112, c_140])).
% 4.04/1.72  tff(c_637, plain, (![B_87]: (~m1_subset_1(k4_waybel_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | r2_hidden(k2_yellow_6(k2_struct_0('#skF_2'), '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_87)), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', B_87))) | ~v3_yellow_6(B_87, '#skF_2') | ~v7_waybel_0(B_87) | ~v4_orders_2(B_87) | ~l1_waybel_0(B_87, '#skF_2') | v2_struct_0(B_87))), inference(splitRight, [status(thm)], [c_617])).
% 4.04/1.72  tff(c_639, plain, (~m1_subset_1(k4_waybel_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_637])).
% 4.04/1.72  tff(c_642, plain, (~m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_141, c_639])).
% 4.04/1.72  tff(c_646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_642])).
% 4.04/1.72  tff(c_648, plain, (m1_subset_1(k4_waybel_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_637])).
% 4.04/1.72  tff(c_174, plain, (![A_88, B_89, C_90, D_91]: (k3_funct_2(A_88, B_89, C_90, D_91)=k1_funct_1(C_90, D_91) | ~m1_subset_1(D_91, A_88) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~v1_funct_2(C_90, A_88, B_89) | ~v1_funct_1(C_90) | v1_xboole_0(A_88))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.04/1.72  tff(c_183, plain, (![B_89, C_90]: (k3_funct_2(k2_struct_0('#skF_2'), B_89, C_90, '#skF_4')=k1_funct_1(C_90, '#skF_4') | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), B_89))) | ~v1_funct_2(C_90, k2_struct_0('#skF_2'), B_89) | ~v1_funct_1(C_90) | v1_xboole_0(k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_91, c_174])).
% 4.04/1.72  tff(c_231, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_183])).
% 4.04/1.72  tff(c_14, plain, (![A_13]: (~v1_xboole_0(k2_struct_0(A_13)) | ~l1_orders_2(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.04/1.72  tff(c_234, plain, (~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_231, c_14])).
% 4.04/1.72  tff(c_237, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_234])).
% 4.04/1.72  tff(c_239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_237])).
% 4.04/1.72  tff(c_241, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_183])).
% 4.04/1.72  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k3_funct_2(A_1, B_2, C_3, D_4)=k1_funct_1(C_3, D_4) | ~m1_subset_1(D_4, A_1) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.04/1.72  tff(c_927, plain, (![A_204, B_205, C_206, B_207]: (k3_funct_2(u1_struct_0(A_204), B_205, C_206, k11_yellow_6(A_204, B_207))=k1_funct_1(C_206, k11_yellow_6(A_204, B_207)) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_204), B_205))) | ~v1_funct_2(C_206, u1_struct_0(A_204), B_205) | ~v1_funct_1(C_206) | v1_xboole_0(u1_struct_0(A_204)) | ~l1_waybel_0(B_207, A_204) | ~v3_yellow_6(B_207, A_204) | ~v7_waybel_0(B_207) | ~v4_orders_2(B_207) | v2_struct_0(B_207) | ~l1_pre_topc(A_204) | ~v8_pre_topc(A_204) | ~v2_pre_topc(A_204) | v2_struct_0(A_204))), inference(resolution, [status(thm)], [c_193, c_2])).
% 4.04/1.72  tff(c_931, plain, (![B_205, C_206, B_207]: (k3_funct_2(u1_struct_0('#skF_2'), B_205, C_206, k11_yellow_6('#skF_2', B_207))=k1_funct_1(C_206, k11_yellow_6('#skF_2', B_207)) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), B_205))) | ~v1_funct_2(C_206, u1_struct_0('#skF_2'), B_205) | ~v1_funct_1(C_206) | v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_waybel_0(B_207, '#skF_2') | ~v3_yellow_6(B_207, '#skF_2') | ~v7_waybel_0(B_207) | ~v4_orders_2(B_207) | v2_struct_0(B_207) | ~l1_pre_topc('#skF_2') | ~v8_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_927])).
% 4.04/1.72  tff(c_934, plain, (![B_205, C_206, B_207]: (k3_funct_2(k2_struct_0('#skF_2'), B_205, C_206, k11_yellow_6('#skF_2', B_207))=k1_funct_1(C_206, k11_yellow_6('#skF_2', B_207)) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), B_205))) | ~v1_funct_2(C_206, k2_struct_0('#skF_2'), B_205) | ~v1_funct_1(C_206) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_waybel_0(B_207, '#skF_2') | ~v3_yellow_6(B_207, '#skF_2') | ~v7_waybel_0(B_207) | ~v4_orders_2(B_207) | v2_struct_0(B_207) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_73, c_90, c_90, c_90, c_931])).
% 4.04/1.72  tff(c_965, plain, (![B_210, C_211, B_212]: (k3_funct_2(k2_struct_0('#skF_2'), B_210, C_211, k11_yellow_6('#skF_2', B_212))=k1_funct_1(C_211, k11_yellow_6('#skF_2', B_212)) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), B_210))) | ~v1_funct_2(C_211, k2_struct_0('#skF_2'), B_210) | ~v1_funct_1(C_211) | ~l1_waybel_0(B_212, '#skF_2') | ~v3_yellow_6(B_212, '#skF_2') | ~v7_waybel_0(B_212) | ~v4_orders_2(B_212) | v2_struct_0(B_212))), inference(negUnitSimplification, [status(thm)], [c_112, c_241, c_934])).
% 4.04/1.72  tff(c_967, plain, (![B_212]: (k3_funct_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_212))=k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_212)) | ~v1_funct_2(k4_waybel_1('#skF_2', '#skF_4'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', '#skF_4')) | ~l1_waybel_0(B_212, '#skF_2') | ~v3_yellow_6(B_212, '#skF_2') | ~v7_waybel_0(B_212) | ~v4_orders_2(B_212) | v2_struct_0(B_212))), inference(resolution, [status(thm)], [c_648, c_965])).
% 4.04/1.72  tff(c_974, plain, (![B_213]: (k3_funct_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_213))=k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_213)) | ~l1_waybel_0(B_213, '#skF_2') | ~v3_yellow_6(B_213, '#skF_2') | ~v7_waybel_0(B_213) | ~v4_orders_2(B_213) | v2_struct_0(B_213))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_638, c_967])).
% 4.04/1.72  tff(c_26, plain, (![A_40, B_41]: (v1_funct_2(k4_waybel_1(A_40, B_41), u1_struct_0(A_40), u1_struct_0(A_40)) | ~m1_subset_1(B_41, u1_struct_0(A_40)) | ~l1_orders_2(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.04/1.72  tff(c_24, plain, (![A_40, B_41]: (m1_subset_1(k4_waybel_1(A_40, B_41), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_40), u1_struct_0(A_40)))) | ~m1_subset_1(B_41, u1_struct_0(A_40)) | ~l1_orders_2(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.04/1.72  tff(c_491, plain, (![A_159, B_160, D_161]: (k3_funct_2(u1_struct_0(A_159), u1_struct_0(A_159), k4_waybel_1(A_159, B_160), D_161)=k11_lattice3(A_159, B_160, D_161) | ~m1_subset_1(D_161, u1_struct_0(A_159)) | ~m1_subset_1(k4_waybel_1(A_159, B_160), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_159), u1_struct_0(A_159)))) | ~v1_funct_2(k4_waybel_1(A_159, B_160), u1_struct_0(A_159), u1_struct_0(A_159)) | ~v1_funct_1(k4_waybel_1(A_159, B_160)) | ~m1_subset_1(B_160, u1_struct_0(A_159)) | ~l1_orders_2(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.04/1.72  tff(c_505, plain, (![A_162, B_163, D_164]: (k3_funct_2(u1_struct_0(A_162), u1_struct_0(A_162), k4_waybel_1(A_162, B_163), D_164)=k11_lattice3(A_162, B_163, D_164) | ~m1_subset_1(D_164, u1_struct_0(A_162)) | ~v1_funct_2(k4_waybel_1(A_162, B_163), u1_struct_0(A_162), u1_struct_0(A_162)) | ~v1_funct_1(k4_waybel_1(A_162, B_163)) | ~m1_subset_1(B_163, u1_struct_0(A_162)) | ~l1_orders_2(A_162) | v2_struct_0(A_162))), inference(resolution, [status(thm)], [c_24, c_491])).
% 4.04/1.72  tff(c_519, plain, (![A_165, B_166, D_167]: (k3_funct_2(u1_struct_0(A_165), u1_struct_0(A_165), k4_waybel_1(A_165, B_166), D_167)=k11_lattice3(A_165, B_166, D_167) | ~m1_subset_1(D_167, u1_struct_0(A_165)) | ~v1_funct_1(k4_waybel_1(A_165, B_166)) | ~m1_subset_1(B_166, u1_struct_0(A_165)) | ~l1_orders_2(A_165) | v2_struct_0(A_165))), inference(resolution, [status(thm)], [c_26, c_505])).
% 4.04/1.72  tff(c_531, plain, (![B_166, D_167]: (k3_funct_2(k2_struct_0('#skF_2'), u1_struct_0('#skF_2'), k4_waybel_1('#skF_2', B_166), D_167)=k11_lattice3('#skF_2', B_166, D_167) | ~m1_subset_1(D_167, u1_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', B_166)) | ~m1_subset_1(B_166, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_519])).
% 4.04/1.72  tff(c_538, plain, (![B_166, D_167]: (k3_funct_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k4_waybel_1('#skF_2', B_166), D_167)=k11_lattice3('#skF_2', B_166, D_167) | ~m1_subset_1(D_167, k2_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', B_166)) | ~m1_subset_1(B_166, k2_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_90, c_90, c_90, c_531])).
% 4.04/1.72  tff(c_539, plain, (![B_166, D_167]: (k3_funct_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k4_waybel_1('#skF_2', B_166), D_167)=k11_lattice3('#skF_2', B_166, D_167) | ~m1_subset_1(D_167, k2_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', B_166)) | ~m1_subset_1(B_166, k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_112, c_538])).
% 4.04/1.72  tff(c_980, plain, (![B_213]: (k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_213))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_213)) | ~m1_subset_1(k11_yellow_6('#skF_2', B_213), k2_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_4', k2_struct_0('#skF_2')) | ~l1_waybel_0(B_213, '#skF_2') | ~v3_yellow_6(B_213, '#skF_2') | ~v7_waybel_0(B_213) | ~v4_orders_2(B_213) | v2_struct_0(B_213))), inference(superposition, [status(thm), theory('equality')], [c_974, c_539])).
% 4.04/1.72  tff(c_993, plain, (![B_214]: (k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_214))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_214)) | ~m1_subset_1(k11_yellow_6('#skF_2', B_214), k2_struct_0('#skF_2')) | ~l1_waybel_0(B_214, '#skF_2') | ~v3_yellow_6(B_214, '#skF_2') | ~v7_waybel_0(B_214) | ~v4_orders_2(B_214) | v2_struct_0(B_214))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_117, c_980])).
% 4.04/1.72  tff(c_998, plain, (![B_215]: (k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_215))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_215)) | ~l1_waybel_0(B_215, '#skF_2') | ~v3_yellow_6(B_215, '#skF_2') | ~v7_waybel_0(B_215) | ~v4_orders_2(B_215) | v2_struct_0(B_215))), inference(resolution, [status(thm)], [c_212, c_993])).
% 4.04/1.72  tff(c_257, plain, (![A_100, B_101, C_102, D_103]: (k2_yellow_6(A_100, B_101, C_102, D_103)=k1_funct_1(C_102, D_103) | ~m1_subset_1(D_103, A_100) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, u1_struct_0(B_101)))) | ~v1_funct_2(C_102, A_100, u1_struct_0(B_101)) | ~v1_funct_1(C_102) | ~l1_orders_2(B_101) | v2_struct_0(B_101) | v1_xboole_0(A_100))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.04/1.72  tff(c_259, plain, (![B_101, C_102, B_94]: (k2_yellow_6(k2_struct_0('#skF_2'), B_101, C_102, k11_yellow_6('#skF_2', B_94))=k1_funct_1(C_102, k11_yellow_6('#skF_2', B_94)) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_101)))) | ~v1_funct_2(C_102, k2_struct_0('#skF_2'), u1_struct_0(B_101)) | ~v1_funct_1(C_102) | ~l1_orders_2(B_101) | v2_struct_0(B_101) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_waybel_0(B_94, '#skF_2') | ~v3_yellow_6(B_94, '#skF_2') | ~v7_waybel_0(B_94) | ~v4_orders_2(B_94) | v2_struct_0(B_94))), inference(resolution, [status(thm)], [c_212, c_257])).
% 4.04/1.72  tff(c_358, plain, (![B_121, C_122, B_123]: (k2_yellow_6(k2_struct_0('#skF_2'), B_121, C_122, k11_yellow_6('#skF_2', B_123))=k1_funct_1(C_122, k11_yellow_6('#skF_2', B_123)) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_121)))) | ~v1_funct_2(C_122, k2_struct_0('#skF_2'), u1_struct_0(B_121)) | ~v1_funct_1(C_122) | ~l1_orders_2(B_121) | v2_struct_0(B_121) | ~l1_waybel_0(B_123, '#skF_2') | ~v3_yellow_6(B_123, '#skF_2') | ~v7_waybel_0(B_123) | ~v4_orders_2(B_123) | v2_struct_0(B_123))), inference(negUnitSimplification, [status(thm)], [c_241, c_259])).
% 4.04/1.72  tff(c_360, plain, (![C_122, B_123]: (k2_yellow_6(k2_struct_0('#skF_2'), '#skF_2', C_122, k11_yellow_6('#skF_2', B_123))=k1_funct_1(C_122, k11_yellow_6('#skF_2', B_123)) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_122, k2_struct_0('#skF_2'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_122) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~l1_waybel_0(B_123, '#skF_2') | ~v3_yellow_6(B_123, '#skF_2') | ~v7_waybel_0(B_123) | ~v4_orders_2(B_123) | v2_struct_0(B_123))), inference(superposition, [status(thm), theory('equality')], [c_90, c_358])).
% 4.04/1.72  tff(c_362, plain, (![C_122, B_123]: (k2_yellow_6(k2_struct_0('#skF_2'), '#skF_2', C_122, k11_yellow_6('#skF_2', B_123))=k1_funct_1(C_122, k11_yellow_6('#skF_2', B_123)) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_122, k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_122) | v2_struct_0('#skF_2') | ~l1_waybel_0(B_123, '#skF_2') | ~v3_yellow_6(B_123, '#skF_2') | ~v7_waybel_0(B_123) | ~v4_orders_2(B_123) | v2_struct_0(B_123))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_90, c_360])).
% 4.04/1.72  tff(c_363, plain, (![C_122, B_123]: (k2_yellow_6(k2_struct_0('#skF_2'), '#skF_2', C_122, k11_yellow_6('#skF_2', B_123))=k1_funct_1(C_122, k11_yellow_6('#skF_2', B_123)) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_122, k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_122) | ~l1_waybel_0(B_123, '#skF_2') | ~v3_yellow_6(B_123, '#skF_2') | ~v7_waybel_0(B_123) | ~v4_orders_2(B_123) | v2_struct_0(B_123))), inference(negUnitSimplification, [status(thm)], [c_112, c_362])).
% 4.04/1.72  tff(c_662, plain, (![B_123]: (k2_yellow_6(k2_struct_0('#skF_2'), '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_123))=k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_123)) | ~v1_funct_2(k4_waybel_1('#skF_2', '#skF_4'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', '#skF_4')) | ~l1_waybel_0(B_123, '#skF_2') | ~v3_yellow_6(B_123, '#skF_2') | ~v7_waybel_0(B_123) | ~v4_orders_2(B_123) | v2_struct_0(B_123))), inference(resolution, [status(thm)], [c_648, c_363])).
% 4.04/1.72  tff(c_833, plain, (![B_192]: (k2_yellow_6(k2_struct_0('#skF_2'), '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_192))=k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_192)) | ~l1_waybel_0(B_192, '#skF_2') | ~v3_yellow_6(B_192, '#skF_2') | ~v7_waybel_0(B_192) | ~v4_orders_2(B_192) | v2_struct_0(B_192))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_638, c_662])).
% 4.04/1.72  tff(c_613, plain, (![C_177, B_178]: (r2_hidden(k2_yellow_6(k2_struct_0('#skF_2'), '#skF_2', C_177, k11_yellow_6('#skF_2', B_178)), k10_yellow_6('#skF_2', k6_waybel_9('#skF_2', '#skF_2', C_177, B_178))) | ~v5_pre_topc(C_177, '#skF_2', '#skF_2') | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_177, u1_struct_0('#skF_2'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_177) | ~l1_waybel_0(B_178, '#skF_2') | ~v3_yellow_6(B_178, '#skF_2') | ~v7_waybel_0(B_178) | ~v4_orders_2(B_178) | v2_struct_0(B_178) | ~l1_waybel_9('#skF_2') | ~v2_lattice3('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | ~v8_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_604])).
% 4.04/1.72  tff(c_619, plain, (![C_177, B_178]: (r2_hidden(k2_yellow_6(k2_struct_0('#skF_2'), '#skF_2', C_177, k11_yellow_6('#skF_2', B_178)), k10_yellow_6('#skF_2', k6_waybel_9('#skF_2', '#skF_2', C_177, B_178))) | ~v5_pre_topc(C_177, '#skF_2', '#skF_2') | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_177, k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_177) | ~l1_waybel_0(B_178, '#skF_2') | ~v3_yellow_6(B_178, '#skF_2') | ~v7_waybel_0(B_178) | ~v4_orders_2(B_178) | v2_struct_0(B_178))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_60, c_58, c_56, c_54, c_90, c_90, c_90, c_90, c_613])).
% 4.04/1.72  tff(c_842, plain, (![B_192]: (r2_hidden(k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_192)), k10_yellow_6('#skF_2', k6_waybel_9('#skF_2', '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), B_192))) | ~v5_pre_topc(k4_waybel_1('#skF_2', '#skF_4'), '#skF_2', '#skF_2') | ~m1_subset_1(k4_waybel_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(k4_waybel_1('#skF_2', '#skF_4'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', '#skF_4')) | ~l1_waybel_0(B_192, '#skF_2') | ~v3_yellow_6(B_192, '#skF_2') | ~v7_waybel_0(B_192) | ~v4_orders_2(B_192) | v2_struct_0(B_192) | ~l1_waybel_0(B_192, '#skF_2') | ~v3_yellow_6(B_192, '#skF_2') | ~v7_waybel_0(B_192) | ~v4_orders_2(B_192) | v2_struct_0(B_192))), inference(superposition, [status(thm), theory('equality')], [c_833, c_619])).
% 4.04/1.72  tff(c_850, plain, (![B_193]: (r2_hidden(k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_193)), k10_yellow_6('#skF_2', k6_waybel_9('#skF_2', '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), B_193))) | ~l1_waybel_0(B_193, '#skF_2') | ~v3_yellow_6(B_193, '#skF_2') | ~v7_waybel_0(B_193) | ~v4_orders_2(B_193) | v2_struct_0(B_193))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_638, c_648, c_40, c_842])).
% 4.04/1.72  tff(c_853, plain, (![B_87]: (r2_hidden(k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_87)), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', B_87))) | ~l1_waybel_0(B_87, '#skF_2') | ~v3_yellow_6(B_87, '#skF_2') | ~v7_waybel_0(B_87) | ~v4_orders_2(B_87) | v2_struct_0(B_87) | ~l1_waybel_0(B_87, '#skF_2') | v2_struct_0(B_87))), inference(superposition, [status(thm), theory('equality')], [c_173, c_850])).
% 4.04/1.72  tff(c_1048, plain, (![B_222]: (r2_hidden(k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_222)), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', B_222))) | ~l1_waybel_0(B_222, '#skF_2') | ~v3_yellow_6(B_222, '#skF_2') | ~v7_waybel_0(B_222) | ~v4_orders_2(B_222) | v2_struct_0(B_222) | ~l1_waybel_0(B_222, '#skF_2') | v2_struct_0(B_222) | ~l1_waybel_0(B_222, '#skF_2') | ~v3_yellow_6(B_222, '#skF_2') | ~v7_waybel_0(B_222) | ~v4_orders_2(B_222) | v2_struct_0(B_222))), inference(superposition, [status(thm), theory('equality')], [c_998, c_853])).
% 4.04/1.72  tff(c_213, plain, (![B_95]: (m1_subset_1(k11_yellow_6('#skF_2', B_95), k2_struct_0('#skF_2')) | ~l1_waybel_0(B_95, '#skF_2') | ~v3_yellow_6(B_95, '#skF_2') | ~v7_waybel_0(B_95) | ~v4_orders_2(B_95) | v2_struct_0(B_95))), inference(negUnitSimplification, [status(thm)], [c_112, c_211])).
% 4.04/1.72  tff(c_146, plain, (![A_77, B_78, C_79]: (k12_lattice3(A_77, B_78, C_79)=k11_lattice3(A_77, B_78, C_79) | ~m1_subset_1(C_79, u1_struct_0(A_77)) | ~m1_subset_1(B_78, u1_struct_0(A_77)) | ~l1_orders_2(A_77) | ~v2_lattice3(A_77) | ~v5_orders_2(A_77))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.04/1.72  tff(c_148, plain, (![B_78, C_79]: (k12_lattice3('#skF_2', B_78, C_79)=k11_lattice3('#skF_2', B_78, C_79) | ~m1_subset_1(C_79, k2_struct_0('#skF_2')) | ~m1_subset_1(B_78, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_146])).
% 4.04/1.72  tff(c_150, plain, (![B_78, C_79]: (k12_lattice3('#skF_2', B_78, C_79)=k11_lattice3('#skF_2', B_78, C_79) | ~m1_subset_1(C_79, k2_struct_0('#skF_2')) | ~m1_subset_1(B_78, k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_79, c_90, c_148])).
% 4.04/1.72  tff(c_278, plain, (![B_106, B_107]: (k12_lattice3('#skF_2', B_106, k11_yellow_6('#skF_2', B_107))=k11_lattice3('#skF_2', B_106, k11_yellow_6('#skF_2', B_107)) | ~m1_subset_1(B_106, k2_struct_0('#skF_2')) | ~l1_waybel_0(B_107, '#skF_2') | ~v3_yellow_6(B_107, '#skF_2') | ~v7_waybel_0(B_107) | ~v4_orders_2(B_107) | v2_struct_0(B_107))), inference(resolution, [status(thm)], [c_213, c_150])).
% 4.04/1.72  tff(c_285, plain, (![B_108]: (k12_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_108))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_108)) | ~l1_waybel_0(B_108, '#skF_2') | ~v3_yellow_6(B_108, '#skF_2') | ~v7_waybel_0(B_108) | ~v4_orders_2(B_108) | v2_struct_0(B_108))), inference(resolution, [status(thm)], [c_91, c_278])).
% 4.04/1.72  tff(c_38, plain, (~r2_hidden(k12_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', '#skF_3')), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_245])).
% 4.04/1.72  tff(c_291, plain, (~r2_hidden(k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', '#skF_3')), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', '#skF_3'))) | ~l1_waybel_0('#skF_3', '#skF_2') | ~v3_yellow_6('#skF_3', '#skF_2') | ~v7_waybel_0('#skF_3') | ~v4_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_285, c_38])).
% 4.04/1.72  tff(c_297, plain, (~r2_hidden(k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', '#skF_3')), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', '#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_291])).
% 4.04/1.72  tff(c_298, plain, (~r2_hidden(k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', '#skF_3')), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_297])).
% 4.04/1.72  tff(c_1051, plain, (~l1_waybel_0('#skF_3', '#skF_2') | ~v3_yellow_6('#skF_3', '#skF_2') | ~v7_waybel_0('#skF_3') | ~v4_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1048, c_298])).
% 4.04/1.72  tff(c_1054, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_1051])).
% 4.04/1.72  tff(c_1056, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1054])).
% 4.04/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.72  
% 4.04/1.72  Inference rules
% 4.04/1.72  ----------------------
% 4.04/1.72  #Ref     : 0
% 4.04/1.72  #Sup     : 208
% 4.04/1.72  #Fact    : 0
% 4.04/1.72  #Define  : 0
% 4.04/1.72  #Split   : 4
% 4.04/1.72  #Chain   : 0
% 4.04/1.72  #Close   : 0
% 4.04/1.72  
% 4.04/1.72  Ordering : KBO
% 4.04/1.72  
% 4.04/1.72  Simplification rules
% 4.04/1.72  ----------------------
% 4.04/1.72  #Subsume      : 29
% 4.04/1.72  #Demod        : 288
% 4.04/1.72  #Tautology    : 66
% 4.04/1.72  #SimpNegUnit  : 40
% 4.04/1.72  #BackRed      : 1
% 4.04/1.72  
% 4.04/1.72  #Partial instantiations: 0
% 4.04/1.72  #Strategies tried      : 1
% 4.04/1.72  
% 4.04/1.72  Timing (in seconds)
% 4.04/1.72  ----------------------
% 4.04/1.73  Preprocessing        : 0.38
% 4.04/1.73  Parsing              : 0.20
% 4.04/1.73  CNF conversion       : 0.03
% 4.04/1.73  Main loop            : 0.57
% 4.04/1.73  Inferencing          : 0.21
% 4.04/1.73  Reduction            : 0.17
% 4.04/1.73  Demodulation         : 0.12
% 4.04/1.73  BG Simplification    : 0.04
% 4.04/1.73  Subsumption          : 0.10
% 4.04/1.73  Abstraction          : 0.04
% 4.04/1.73  MUC search           : 0.00
% 4.04/1.73  Cooper               : 0.00
% 4.04/1.73  Total                : 1.00
% 4.04/1.73  Index Insertion      : 0.00
% 4.04/1.73  Index Deletion       : 0.00
% 4.04/1.73  Index Matching       : 0.00
% 4.04/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
