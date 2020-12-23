%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:18 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
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

tff(f_241,negated_conjecture,(
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

tff(f_150,axiom,(
    ! [A] :
      ( l1_waybel_9(A)
     => ( l1_pre_topc(A)
        & l1_orders_2(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

tff(f_144,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( v1_funct_1(k4_waybel_1(A,B))
        & v1_funct_2(k4_waybel_1(A,B),u1_struct_0(A),u1_struct_0(A))
        & m1_subset_1(k4_waybel_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_91,axiom,(
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

tff(f_50,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_166,axiom,(
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

tff(f_205,axiom,(
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

tff(f_131,axiom,(
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

tff(f_109,axiom,(
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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_48,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_46,plain,(
    v7_waybel_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_44,plain,(
    v3_yellow_6('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_42,plain,(
    l1_waybel_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_52,plain,(
    l1_waybel_9('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_67,plain,(
    ! [A_60] :
      ( l1_orders_2(A_60)
      | ~ l1_waybel_9(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_71,plain,(
    l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_67])).

tff(c_54,plain,(
    v2_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_80,plain,(
    ! [A_65,B_66] :
      ( v1_funct_1(k4_waybel_1(A_65,B_66))
      | ~ m1_subset_1(B_66,u1_struct_0(A_65))
      | ~ l1_orders_2(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_83,plain,
    ( v1_funct_1(k4_waybel_1('#skF_2','#skF_4'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_80])).

tff(c_86,plain,
    ( v1_funct_1(k4_waybel_1('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_83])).

tff(c_87,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ v2_struct_0(A_7)
      | ~ v2_lattice3(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_90,plain,
    ( ~ v2_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_87,c_8])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_54,c_90])).

tff(c_96,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_64,plain,(
    v8_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_73,plain,(
    ! [A_62] :
      ( l1_pre_topc(A_62)
      | ~ l1_waybel_9(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_77,plain,(
    l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_73])).

tff(c_12,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_95,plain,(
    v1_funct_1(k4_waybel_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_4,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_130,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( k3_funct_2(A_79,B_80,C_81,D_82) = k1_funct_1(C_81,D_82)
      | ~ m1_subset_1(D_82,A_79)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ v1_funct_2(C_81,A_79,B_80)
      | ~ v1_funct_1(C_81)
      | v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_136,plain,(
    ! [B_80,C_81] :
      ( k3_funct_2(u1_struct_0('#skF_2'),B_80,C_81,'#skF_4') = k1_funct_1(C_81,'#skF_4')
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),B_80)))
      | ~ v1_funct_2(C_81,u1_struct_0('#skF_2'),B_80)
      | ~ v1_funct_1(C_81)
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_40,c_130])).

tff(c_168,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_6,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_171,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_168,c_6])).

tff(c_174,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_171])).

tff(c_177,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_174])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_177])).

tff(c_183,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_24,plain,(
    ! [A_39,B_40] :
      ( v1_funct_2(k4_waybel_1(A_39,B_40),u1_struct_0(A_39),u1_struct_0(A_39))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_62,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_60,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_58,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_56,plain,(
    v1_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_38,plain,(
    v5_pre_topc(k4_waybel_1('#skF_2','#skF_4'),'#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_114,plain,(
    ! [A_75,C_76,B_77] :
      ( k6_waybel_9(A_75,A_75,k4_waybel_1(A_75,C_76),B_77) = k3_waybel_2(A_75,C_76,B_77)
      | ~ m1_subset_1(C_76,u1_struct_0(A_75))
      | ~ l1_waybel_0(B_77,A_75)
      | v2_struct_0(B_77)
      | ~ l1_orders_2(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_116,plain,(
    ! [B_77] :
      ( k6_waybel_9('#skF_2','#skF_2',k4_waybel_1('#skF_2','#skF_4'),B_77) = k3_waybel_2('#skF_2','#skF_4',B_77)
      | ~ l1_waybel_0(B_77,'#skF_2')
      | v2_struct_0(B_77)
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_114])).

tff(c_119,plain,(
    ! [B_77] :
      ( k6_waybel_9('#skF_2','#skF_2',k4_waybel_1('#skF_2','#skF_4'),B_77) = k3_waybel_2('#skF_2','#skF_4',B_77)
      | ~ l1_waybel_0(B_77,'#skF_2')
      | v2_struct_0(B_77)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_116])).

tff(c_120,plain,(
    ! [B_77] :
      ( k6_waybel_9('#skF_2','#skF_2',k4_waybel_1('#skF_2','#skF_4'),B_77) = k3_waybel_2('#skF_2','#skF_4',B_77)
      | ~ l1_waybel_0(B_77,'#skF_2')
      | v2_struct_0(B_77) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_119])).

tff(c_383,plain,(
    ! [A_131,C_132,B_133] :
      ( r2_hidden(k2_yellow_6(u1_struct_0(A_131),A_131,C_132,k11_yellow_6(A_131,B_133)),k10_yellow_6(A_131,k6_waybel_9(A_131,A_131,C_132,B_133)))
      | ~ v5_pre_topc(C_132,A_131,A_131)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_131),u1_struct_0(A_131))))
      | ~ v1_funct_2(C_132,u1_struct_0(A_131),u1_struct_0(A_131))
      | ~ v1_funct_1(C_132)
      | ~ l1_waybel_0(B_133,A_131)
      | ~ v3_yellow_6(B_133,A_131)
      | ~ v7_waybel_0(B_133)
      | ~ v4_orders_2(B_133)
      | v2_struct_0(B_133)
      | ~ l1_waybel_9(A_131)
      | ~ v2_lattice3(A_131)
      | ~ v1_lattice3(A_131)
      | ~ v5_orders_2(A_131)
      | ~ v4_orders_2(A_131)
      | ~ v3_orders_2(A_131)
      | ~ v8_pre_topc(A_131)
      | ~ v2_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_386,plain,(
    ! [B_77] :
      ( r2_hidden(k2_yellow_6(u1_struct_0('#skF_2'),'#skF_2',k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_77)),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4',B_77)))
      | ~ v5_pre_topc(k4_waybel_1('#skF_2','#skF_4'),'#skF_2','#skF_2')
      | ~ m1_subset_1(k4_waybel_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_4'))
      | ~ l1_waybel_0(B_77,'#skF_2')
      | ~ v3_yellow_6(B_77,'#skF_2')
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | v2_struct_0(B_77)
      | ~ l1_waybel_9('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_waybel_0(B_77,'#skF_2')
      | v2_struct_0(B_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_383])).

tff(c_388,plain,(
    ! [B_77] :
      ( r2_hidden(k2_yellow_6(u1_struct_0('#skF_2'),'#skF_2',k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_77)),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4',B_77)))
      | ~ m1_subset_1(k4_waybel_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v3_yellow_6(B_77,'#skF_2')
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | ~ l1_waybel_0(B_77,'#skF_2')
      | v2_struct_0(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_56,c_54,c_52,c_95,c_38,c_386])).

tff(c_437,plain,(
    ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_388])).

tff(c_440,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_437])).

tff(c_443,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_40,c_440])).

tff(c_445,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_443])).

tff(c_447,plain,(
    v1_funct_2(k4_waybel_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_22,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(k4_waybel_1(A_39,B_40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_39),u1_struct_0(A_39))))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_446,plain,(
    ! [B_77] :
      ( ~ m1_subset_1(k4_waybel_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))))
      | r2_hidden(k2_yellow_6(u1_struct_0('#skF_2'),'#skF_2',k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_77)),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4',B_77)))
      | ~ v3_yellow_6(B_77,'#skF_2')
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | ~ l1_waybel_0(B_77,'#skF_2')
      | v2_struct_0(B_77) ) ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_448,plain,(
    ~ m1_subset_1(k4_waybel_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_446])).

tff(c_455,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_448])).

tff(c_458,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_40,c_455])).

tff(c_460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_458])).

tff(c_462,plain,(
    m1_subset_1(k4_waybel_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_446])).

tff(c_137,plain,(
    ! [A_83,B_84] :
      ( m1_subset_1(k11_yellow_6(A_83,B_84),u1_struct_0(A_83))
      | ~ l1_waybel_0(B_84,A_83)
      | ~ v3_yellow_6(B_84,A_83)
      | ~ v7_waybel_0(B_84)
      | ~ v4_orders_2(B_84)
      | v2_struct_0(B_84)
      | ~ l1_pre_topc(A_83)
      | ~ v8_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( k3_funct_2(A_1,B_2,C_3,D_4) = k1_funct_1(C_3,D_4)
      | ~ m1_subset_1(D_4,A_1)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_606,plain,(
    ! [A_153,B_154,C_155,B_156] :
      ( k3_funct_2(u1_struct_0(A_153),B_154,C_155,k11_yellow_6(A_153,B_156)) = k1_funct_1(C_155,k11_yellow_6(A_153,B_156))
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_153),B_154)))
      | ~ v1_funct_2(C_155,u1_struct_0(A_153),B_154)
      | ~ v1_funct_1(C_155)
      | v1_xboole_0(u1_struct_0(A_153))
      | ~ l1_waybel_0(B_156,A_153)
      | ~ v3_yellow_6(B_156,A_153)
      | ~ v7_waybel_0(B_156)
      | ~ v4_orders_2(B_156)
      | v2_struct_0(B_156)
      | ~ l1_pre_topc(A_153)
      | ~ v8_pre_topc(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_137,c_2])).

tff(c_608,plain,(
    ! [B_156] :
      ( k3_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_156)) = k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_156))
      | ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_156,'#skF_2')
      | ~ v3_yellow_6(B_156,'#skF_2')
      | ~ v7_waybel_0(B_156)
      | ~ v4_orders_2(B_156)
      | v2_struct_0(B_156)
      | ~ l1_pre_topc('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_462,c_606])).

tff(c_613,plain,(
    ! [B_156] :
      ( k3_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_156)) = k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_156))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_156,'#skF_2')
      | ~ v3_yellow_6(B_156,'#skF_2')
      | ~ v7_waybel_0(B_156)
      | ~ v4_orders_2(B_156)
      | v2_struct_0(B_156)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_77,c_95,c_447,c_608])).

tff(c_616,plain,(
    ! [B_157] :
      ( k3_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_157)) = k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_157))
      | ~ l1_waybel_0(B_157,'#skF_2')
      | ~ v3_yellow_6(B_157,'#skF_2')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_183,c_613])).

tff(c_323,plain,(
    ! [A_121,B_122,D_123] :
      ( k3_funct_2(u1_struct_0(A_121),u1_struct_0(A_121),k4_waybel_1(A_121,B_122),D_123) = k11_lattice3(A_121,B_122,D_123)
      | ~ m1_subset_1(D_123,u1_struct_0(A_121))
      | ~ m1_subset_1(k4_waybel_1(A_121,B_122),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_121),u1_struct_0(A_121))))
      | ~ v1_funct_2(k4_waybel_1(A_121,B_122),u1_struct_0(A_121),u1_struct_0(A_121))
      | ~ v1_funct_1(k4_waybel_1(A_121,B_122))
      | ~ m1_subset_1(B_122,u1_struct_0(A_121))
      | ~ l1_orders_2(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_327,plain,(
    ! [A_124,B_125,D_126] :
      ( k3_funct_2(u1_struct_0(A_124),u1_struct_0(A_124),k4_waybel_1(A_124,B_125),D_126) = k11_lattice3(A_124,B_125,D_126)
      | ~ m1_subset_1(D_126,u1_struct_0(A_124))
      | ~ v1_funct_2(k4_waybel_1(A_124,B_125),u1_struct_0(A_124),u1_struct_0(A_124))
      | ~ v1_funct_1(k4_waybel_1(A_124,B_125))
      | ~ m1_subset_1(B_125,u1_struct_0(A_124))
      | ~ l1_orders_2(A_124)
      | v2_struct_0(A_124) ) ),
    inference(resolution,[status(thm)],[c_22,c_323])).

tff(c_330,plain,(
    ! [A_39,B_40,D_126] :
      ( k3_funct_2(u1_struct_0(A_39),u1_struct_0(A_39),k4_waybel_1(A_39,B_40),D_126) = k11_lattice3(A_39,B_40,D_126)
      | ~ m1_subset_1(D_126,u1_struct_0(A_39))
      | ~ v1_funct_1(k4_waybel_1(A_39,B_40))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39)
      | v2_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_24,c_327])).

tff(c_622,plain,(
    ! [B_157] :
      ( k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_157)) = k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_157))
      | ~ m1_subset_1(k11_yellow_6('#skF_2',B_157),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_4'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_waybel_0(B_157,'#skF_2')
      | ~ v3_yellow_6(B_157,'#skF_2')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_330])).

tff(c_631,plain,(
    ! [B_157] :
      ( k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_157)) = k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_157))
      | ~ m1_subset_1(k11_yellow_6('#skF_2',B_157),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ l1_waybel_0(B_157,'#skF_2')
      | ~ v3_yellow_6(B_157,'#skF_2')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_40,c_95,c_622])).

tff(c_637,plain,(
    ! [B_158] :
      ( k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_158)) = k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_158))
      | ~ m1_subset_1(k11_yellow_6('#skF_2',B_158),u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_158,'#skF_2')
      | ~ v3_yellow_6(B_158,'#skF_2')
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_631])).

tff(c_641,plain,(
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
    inference(resolution,[status(thm)],[c_12,c_637])).

tff(c_644,plain,(
    ! [B_12] :
      ( k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_12)) = k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_12))
      | ~ l1_waybel_0(B_12,'#skF_2')
      | ~ v3_yellow_6(B_12,'#skF_2')
      | ~ v7_waybel_0(B_12)
      | ~ v4_orders_2(B_12)
      | v2_struct_0(B_12)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_77,c_641])).

tff(c_645,plain,(
    ! [B_12] :
      ( k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_12)) = k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_12))
      | ~ l1_waybel_0(B_12,'#skF_2')
      | ~ v3_yellow_6(B_12,'#skF_2')
      | ~ v7_waybel_0(B_12)
      | ~ v4_orders_2(B_12)
      | v2_struct_0(B_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_644])).

tff(c_203,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( k2_yellow_6(A_91,B_92,C_93,D_94) = k1_funct_1(C_93,D_94)
      | ~ m1_subset_1(D_94,A_91)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,u1_struct_0(B_92))))
      | ~ v1_funct_2(C_93,A_91,u1_struct_0(B_92))
      | ~ v1_funct_1(C_93)
      | ~ l1_orders_2(B_92)
      | v2_struct_0(B_92)
      | v1_xboole_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_800,plain,(
    ! [A_180,B_181,C_182,B_183] :
      ( k2_yellow_6(u1_struct_0(A_180),B_181,C_182,k11_yellow_6(A_180,B_183)) = k1_funct_1(C_182,k11_yellow_6(A_180,B_183))
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_180),u1_struct_0(B_181))))
      | ~ v1_funct_2(C_182,u1_struct_0(A_180),u1_struct_0(B_181))
      | ~ v1_funct_1(C_182)
      | ~ l1_orders_2(B_181)
      | v2_struct_0(B_181)
      | v1_xboole_0(u1_struct_0(A_180))
      | ~ l1_waybel_0(B_183,A_180)
      | ~ v3_yellow_6(B_183,A_180)
      | ~ v7_waybel_0(B_183)
      | ~ v4_orders_2(B_183)
      | v2_struct_0(B_183)
      | ~ l1_pre_topc(A_180)
      | ~ v8_pre_topc(A_180)
      | ~ v2_pre_topc(A_180)
      | v2_struct_0(A_180) ) ),
    inference(resolution,[status(thm)],[c_12,c_203])).

tff(c_802,plain,(
    ! [B_183] :
      ( k2_yellow_6(u1_struct_0('#skF_2'),'#skF_2',k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_183)) = k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_183))
      | ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_4'))
      | ~ l1_orders_2('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_183,'#skF_2')
      | ~ v3_yellow_6(B_183,'#skF_2')
      | ~ v7_waybel_0(B_183)
      | ~ v4_orders_2(B_183)
      | v2_struct_0(B_183)
      | ~ l1_pre_topc('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_462,c_800])).

tff(c_807,plain,(
    ! [B_183] :
      ( k2_yellow_6(u1_struct_0('#skF_2'),'#skF_2',k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_183)) = k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_183))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_183,'#skF_2')
      | ~ v3_yellow_6(B_183,'#skF_2')
      | ~ v7_waybel_0(B_183)
      | ~ v4_orders_2(B_183)
      | v2_struct_0(B_183)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_77,c_71,c_95,c_447,c_802])).

tff(c_810,plain,(
    ! [B_184] :
      ( k2_yellow_6(u1_struct_0('#skF_2'),'#skF_2',k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_184)) = k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_184))
      | ~ l1_waybel_0(B_184,'#skF_2')
      | ~ v3_yellow_6(B_184,'#skF_2')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_183,c_807])).

tff(c_34,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_819,plain,(
    ! [B_184] :
      ( r2_hidden(k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_184)),k10_yellow_6('#skF_2',k6_waybel_9('#skF_2','#skF_2',k4_waybel_1('#skF_2','#skF_4'),B_184)))
      | ~ v5_pre_topc(k4_waybel_1('#skF_2','#skF_4'),'#skF_2','#skF_2')
      | ~ m1_subset_1(k4_waybel_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_4'))
      | ~ l1_waybel_0(B_184,'#skF_2')
      | ~ v3_yellow_6(B_184,'#skF_2')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184)
      | ~ l1_waybel_9('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_waybel_0(B_184,'#skF_2')
      | ~ v3_yellow_6(B_184,'#skF_2')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_810,c_34])).

tff(c_827,plain,(
    ! [B_185] :
      ( r2_hidden(k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_185)),k10_yellow_6('#skF_2',k6_waybel_9('#skF_2','#skF_2',k4_waybel_1('#skF_2','#skF_4'),B_185)))
      | ~ l1_waybel_0(B_185,'#skF_2')
      | ~ v3_yellow_6(B_185,'#skF_2')
      | ~ v7_waybel_0(B_185)
      | ~ v4_orders_2(B_185)
      | v2_struct_0(B_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_56,c_54,c_52,c_95,c_447,c_462,c_38,c_819])).

tff(c_834,plain,(
    ! [B_186] :
      ( r2_hidden(k1_funct_1(k4_waybel_1('#skF_2','#skF_4'),k11_yellow_6('#skF_2',B_186)),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4',B_186)))
      | ~ l1_waybel_0(B_186,'#skF_2')
      | ~ v3_yellow_6(B_186,'#skF_2')
      | ~ v7_waybel_0(B_186)
      | ~ v4_orders_2(B_186)
      | v2_struct_0(B_186)
      | ~ l1_waybel_0(B_186,'#skF_2')
      | v2_struct_0(B_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_827])).

tff(c_842,plain,(
    ! [B_188] :
      ( r2_hidden(k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_188)),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4',B_188)))
      | ~ l1_waybel_0(B_188,'#skF_2')
      | ~ v3_yellow_6(B_188,'#skF_2')
      | ~ v7_waybel_0(B_188)
      | ~ v4_orders_2(B_188)
      | v2_struct_0(B_188)
      | ~ l1_waybel_0(B_188,'#skF_2')
      | v2_struct_0(B_188)
      | ~ l1_waybel_0(B_188,'#skF_2')
      | ~ v3_yellow_6(B_188,'#skF_2')
      | ~ v7_waybel_0(B_188)
      | ~ v4_orders_2(B_188)
      | v2_struct_0(B_188) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_834])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( k12_lattice3(A_8,B_9,C_10) = k11_lattice3(A_8,B_9,C_10)
      | ~ m1_subset_1(C_10,u1_struct_0(A_8))
      | ~ m1_subset_1(B_9,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8)
      | ~ v2_lattice3(A_8)
      | ~ v5_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_295,plain,(
    ! [A_117,B_118,B_119] :
      ( k12_lattice3(A_117,B_118,k11_yellow_6(A_117,B_119)) = k11_lattice3(A_117,B_118,k11_yellow_6(A_117,B_119))
      | ~ m1_subset_1(B_118,u1_struct_0(A_117))
      | ~ l1_orders_2(A_117)
      | ~ v2_lattice3(A_117)
      | ~ v5_orders_2(A_117)
      | ~ l1_waybel_0(B_119,A_117)
      | ~ v3_yellow_6(B_119,A_117)
      | ~ v7_waybel_0(B_119)
      | ~ v4_orders_2(B_119)
      | v2_struct_0(B_119)
      | ~ l1_pre_topc(A_117)
      | ~ v8_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_137,c_10])).

tff(c_301,plain,(
    ! [B_119] :
      ( k12_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_119)) = k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_119))
      | ~ l1_orders_2('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ l1_waybel_0(B_119,'#skF_2')
      | ~ v3_yellow_6(B_119,'#skF_2')
      | ~ v7_waybel_0(B_119)
      | ~ v4_orders_2(B_119)
      | v2_struct_0(B_119)
      | ~ l1_pre_topc('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_295])).

tff(c_306,plain,(
    ! [B_119] :
      ( k12_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_119)) = k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_119))
      | ~ l1_waybel_0(B_119,'#skF_2')
      | ~ v3_yellow_6(B_119,'#skF_2')
      | ~ v7_waybel_0(B_119)
      | ~ v4_orders_2(B_119)
      | v2_struct_0(B_119)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_77,c_58,c_54,c_71,c_301])).

tff(c_308,plain,(
    ! [B_120] :
      ( k12_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_120)) = k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2',B_120))
      | ~ l1_waybel_0(B_120,'#skF_2')
      | ~ v3_yellow_6(B_120,'#skF_2')
      | ~ v7_waybel_0(B_120)
      | ~ v4_orders_2(B_120)
      | v2_struct_0(B_120) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_306])).

tff(c_36,plain,(
    ~ r2_hidden(k12_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2','#skF_3')),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_314,plain,
    ( ~ r2_hidden(k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2','#skF_3')),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4','#skF_3')))
    | ~ l1_waybel_0('#skF_3','#skF_2')
    | ~ v3_yellow_6('#skF_3','#skF_2')
    | ~ v7_waybel_0('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_36])).

tff(c_320,plain,
    ( ~ r2_hidden(k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2','#skF_3')),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4','#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_314])).

tff(c_321,plain,(
    ~ r2_hidden(k11_lattice3('#skF_2','#skF_4',k11_yellow_6('#skF_2','#skF_3')),k10_yellow_6('#skF_2',k3_waybel_2('#skF_2','#skF_4','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_320])).

tff(c_845,plain,
    ( ~ l1_waybel_0('#skF_3','#skF_2')
    | ~ v3_yellow_6('#skF_3','#skF_2')
    | ~ v7_waybel_0('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_842,c_321])).

tff(c_848,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_845])).

tff(c_850,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_848])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:05:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.73/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.60  
% 3.73/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.61  %$ v5_pre_topc > v1_funct_2 > v3_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k6_waybel_9 > k3_funct_2 > k2_yellow_6 > k3_waybel_2 > k12_lattice3 > k11_lattice3 > k4_waybel_1 > k2_zfmisc_1 > k1_funct_1 > k11_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.73/1.61  
% 3.73/1.61  %Foreground sorts:
% 3.73/1.61  
% 3.73/1.61  
% 3.73/1.61  %Background operators:
% 3.73/1.61  
% 3.73/1.61  
% 3.73/1.61  %Foreground operators:
% 3.73/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.73/1.61  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 3.73/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.73/1.61  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.73/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.73/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.73/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.73/1.61  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 3.73/1.61  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 3.73/1.61  tff(k6_waybel_9, type, k6_waybel_9: ($i * $i * $i * $i) > $i).
% 3.73/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.73/1.61  tff(k3_waybel_2, type, k3_waybel_2: ($i * $i * $i) > $i).
% 3.73/1.61  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.73/1.61  tff(k2_yellow_6, type, k2_yellow_6: ($i * $i * $i * $i) > $i).
% 3.73/1.61  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 3.73/1.61  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 3.73/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.73/1.61  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 3.73/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.73/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.73/1.61  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.73/1.61  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.73/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.73/1.61  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.73/1.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.73/1.61  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.73/1.61  tff(k4_waybel_1, type, k4_waybel_1: ($i * $i) > $i).
% 3.73/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.73/1.61  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.73/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.73/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.73/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.73/1.61  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.73/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.73/1.61  tff(k11_yellow_6, type, k11_yellow_6: ($i * $i) > $i).
% 3.73/1.61  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 3.73/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.73/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.73/1.61  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.73/1.61  tff(l1_waybel_9, type, l1_waybel_9: $i > $o).
% 3.73/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.73/1.61  
% 3.73/1.63  tff(f_241, negated_conjecture, ~(![A]: ((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_waybel_9(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (v5_pre_topc(k4_waybel_1(A, C), A, A) => r2_hidden(k12_lattice3(A, C, k11_yellow_6(A, B)), k10_yellow_6(A, k3_waybel_2(A, C, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_waybel_9)).
% 3.73/1.63  tff(f_150, axiom, (![A]: (l1_waybel_9(A) => (l1_pre_topc(A) & l1_orders_2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 3.73/1.63  tff(f_144, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => ((v1_funct_1(k4_waybel_1(A, B)) & v1_funct_2(k4_waybel_1(A, B), u1_struct_0(A), u1_struct_0(A))) & m1_subset_1(k4_waybel_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_waybel_1)).
% 3.73/1.63  tff(f_57, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_lattice3)).
% 3.73/1.63  tff(f_91, axiom, (![A, B]: (((((((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A)) & l1_waybel_0(B, A)) => m1_subset_1(k11_yellow_6(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_yellow_6)).
% 3.73/1.63  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.73/1.63  tff(f_38, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.73/1.63  tff(f_50, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.73/1.63  tff(f_166, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k6_waybel_9(A, A, k4_waybel_1(A, C), B) = k3_waybel_2(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_waybel_9)).
% 3.73/1.63  tff(f_205, axiom, (![A]: ((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_waybel_9(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A)) & l1_waybel_0(B, A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))) => (v5_pre_topc(C, A, A) => r2_hidden(k2_yellow_6(u1_struct_0(A), A, C, k11_yellow_6(A, B)), k10_yellow_6(A, k6_waybel_9(A, A, C, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_waybel_9)).
% 3.73/1.63  tff(f_131, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))) => ((C = k4_waybel_1(A, B)) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (k3_funct_2(u1_struct_0(A), u1_struct_0(A), C, D) = k11_lattice3(A, B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_waybel_1)).
% 3.73/1.63  tff(f_109, axiom, (![A, B, C, D]: (((((((~v1_xboole_0(A) & ~v2_struct_0(B)) & l1_orders_2(B)) & v1_funct_1(C)) & v1_funct_2(C, A, u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, u1_struct_0(B))))) & m1_subset_1(D, A)) => (k2_yellow_6(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_yellow_6)).
% 3.73/1.63  tff(f_69, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 3.73/1.63  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.73/1.63  tff(c_48, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.73/1.63  tff(c_46, plain, (v7_waybel_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.73/1.63  tff(c_44, plain, (v3_yellow_6('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.73/1.63  tff(c_42, plain, (l1_waybel_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.73/1.63  tff(c_52, plain, (l1_waybel_9('#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.73/1.63  tff(c_67, plain, (![A_60]: (l1_orders_2(A_60) | ~l1_waybel_9(A_60))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.73/1.63  tff(c_71, plain, (l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_52, c_67])).
% 3.73/1.63  tff(c_54, plain, (v2_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.73/1.63  tff(c_40, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.73/1.63  tff(c_80, plain, (![A_65, B_66]: (v1_funct_1(k4_waybel_1(A_65, B_66)) | ~m1_subset_1(B_66, u1_struct_0(A_65)) | ~l1_orders_2(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.73/1.63  tff(c_83, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_4')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_80])).
% 3.73/1.63  tff(c_86, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_83])).
% 3.73/1.63  tff(c_87, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_86])).
% 3.73/1.63  tff(c_8, plain, (![A_7]: (~v2_struct_0(A_7) | ~v2_lattice3(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.73/1.63  tff(c_90, plain, (~v2_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_87, c_8])).
% 3.73/1.63  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_54, c_90])).
% 3.73/1.63  tff(c_96, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_86])).
% 3.73/1.63  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.73/1.63  tff(c_64, plain, (v8_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.73/1.63  tff(c_73, plain, (![A_62]: (l1_pre_topc(A_62) | ~l1_waybel_9(A_62))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.73/1.63  tff(c_77, plain, (l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_73])).
% 3.73/1.63  tff(c_12, plain, (![A_11, B_12]: (m1_subset_1(k11_yellow_6(A_11, B_12), u1_struct_0(A_11)) | ~l1_waybel_0(B_12, A_11) | ~v3_yellow_6(B_12, A_11) | ~v7_waybel_0(B_12) | ~v4_orders_2(B_12) | v2_struct_0(B_12) | ~l1_pre_topc(A_11) | ~v8_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.73/1.63  tff(c_95, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_86])).
% 3.73/1.63  tff(c_4, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.73/1.63  tff(c_130, plain, (![A_79, B_80, C_81, D_82]: (k3_funct_2(A_79, B_80, C_81, D_82)=k1_funct_1(C_81, D_82) | ~m1_subset_1(D_82, A_79) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~v1_funct_2(C_81, A_79, B_80) | ~v1_funct_1(C_81) | v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.73/1.63  tff(c_136, plain, (![B_80, C_81]: (k3_funct_2(u1_struct_0('#skF_2'), B_80, C_81, '#skF_4')=k1_funct_1(C_81, '#skF_4') | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), B_80))) | ~v1_funct_2(C_81, u1_struct_0('#skF_2'), B_80) | ~v1_funct_1(C_81) | v1_xboole_0(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_40, c_130])).
% 3.73/1.63  tff(c_168, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_136])).
% 3.73/1.63  tff(c_6, plain, (![A_6]: (~v1_xboole_0(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.73/1.63  tff(c_171, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_168, c_6])).
% 3.73/1.63  tff(c_174, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_96, c_171])).
% 3.73/1.63  tff(c_177, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_174])).
% 3.73/1.63  tff(c_181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_177])).
% 3.73/1.63  tff(c_183, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_136])).
% 3.73/1.63  tff(c_24, plain, (![A_39, B_40]: (v1_funct_2(k4_waybel_1(A_39, B_40), u1_struct_0(A_39), u1_struct_0(A_39)) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_orders_2(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.73/1.63  tff(c_62, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.73/1.63  tff(c_60, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.73/1.63  tff(c_58, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.73/1.63  tff(c_56, plain, (v1_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.73/1.63  tff(c_38, plain, (v5_pre_topc(k4_waybel_1('#skF_2', '#skF_4'), '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.73/1.63  tff(c_114, plain, (![A_75, C_76, B_77]: (k6_waybel_9(A_75, A_75, k4_waybel_1(A_75, C_76), B_77)=k3_waybel_2(A_75, C_76, B_77) | ~m1_subset_1(C_76, u1_struct_0(A_75)) | ~l1_waybel_0(B_77, A_75) | v2_struct_0(B_77) | ~l1_orders_2(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.73/1.63  tff(c_116, plain, (![B_77]: (k6_waybel_9('#skF_2', '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), B_77)=k3_waybel_2('#skF_2', '#skF_4', B_77) | ~l1_waybel_0(B_77, '#skF_2') | v2_struct_0(B_77) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_114])).
% 3.73/1.63  tff(c_119, plain, (![B_77]: (k6_waybel_9('#skF_2', '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), B_77)=k3_waybel_2('#skF_2', '#skF_4', B_77) | ~l1_waybel_0(B_77, '#skF_2') | v2_struct_0(B_77) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_116])).
% 3.73/1.63  tff(c_120, plain, (![B_77]: (k6_waybel_9('#skF_2', '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), B_77)=k3_waybel_2('#skF_2', '#skF_4', B_77) | ~l1_waybel_0(B_77, '#skF_2') | v2_struct_0(B_77))), inference(negUnitSimplification, [status(thm)], [c_96, c_119])).
% 3.73/1.63  tff(c_383, plain, (![A_131, C_132, B_133]: (r2_hidden(k2_yellow_6(u1_struct_0(A_131), A_131, C_132, k11_yellow_6(A_131, B_133)), k10_yellow_6(A_131, k6_waybel_9(A_131, A_131, C_132, B_133))) | ~v5_pre_topc(C_132, A_131, A_131) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_131), u1_struct_0(A_131)))) | ~v1_funct_2(C_132, u1_struct_0(A_131), u1_struct_0(A_131)) | ~v1_funct_1(C_132) | ~l1_waybel_0(B_133, A_131) | ~v3_yellow_6(B_133, A_131) | ~v7_waybel_0(B_133) | ~v4_orders_2(B_133) | v2_struct_0(B_133) | ~l1_waybel_9(A_131) | ~v2_lattice3(A_131) | ~v1_lattice3(A_131) | ~v5_orders_2(A_131) | ~v4_orders_2(A_131) | ~v3_orders_2(A_131) | ~v8_pre_topc(A_131) | ~v2_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.73/1.63  tff(c_386, plain, (![B_77]: (r2_hidden(k2_yellow_6(u1_struct_0('#skF_2'), '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_77)), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', B_77))) | ~v5_pre_topc(k4_waybel_1('#skF_2', '#skF_4'), '#skF_2', '#skF_2') | ~m1_subset_1(k4_waybel_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_waybel_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', '#skF_4')) | ~l1_waybel_0(B_77, '#skF_2') | ~v3_yellow_6(B_77, '#skF_2') | ~v7_waybel_0(B_77) | ~v4_orders_2(B_77) | v2_struct_0(B_77) | ~l1_waybel_9('#skF_2') | ~v2_lattice3('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | ~v8_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_waybel_0(B_77, '#skF_2') | v2_struct_0(B_77))), inference(superposition, [status(thm), theory('equality')], [c_120, c_383])).
% 3.73/1.63  tff(c_388, plain, (![B_77]: (r2_hidden(k2_yellow_6(u1_struct_0('#skF_2'), '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_77)), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', B_77))) | ~m1_subset_1(k4_waybel_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_waybel_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2')) | ~v3_yellow_6(B_77, '#skF_2') | ~v7_waybel_0(B_77) | ~v4_orders_2(B_77) | ~l1_waybel_0(B_77, '#skF_2') | v2_struct_0(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_56, c_54, c_52, c_95, c_38, c_386])).
% 3.73/1.63  tff(c_437, plain, (~v1_funct_2(k4_waybel_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_388])).
% 3.73/1.63  tff(c_440, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_437])).
% 3.73/1.63  tff(c_443, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_40, c_440])).
% 3.73/1.63  tff(c_445, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_443])).
% 3.73/1.63  tff(c_447, plain, (v1_funct_2(k4_waybel_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_388])).
% 3.73/1.63  tff(c_22, plain, (![A_39, B_40]: (m1_subset_1(k4_waybel_1(A_39, B_40), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_39), u1_struct_0(A_39)))) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_orders_2(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.73/1.63  tff(c_446, plain, (![B_77]: (~m1_subset_1(k4_waybel_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2')))) | r2_hidden(k2_yellow_6(u1_struct_0('#skF_2'), '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_77)), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', B_77))) | ~v3_yellow_6(B_77, '#skF_2') | ~v7_waybel_0(B_77) | ~v4_orders_2(B_77) | ~l1_waybel_0(B_77, '#skF_2') | v2_struct_0(B_77))), inference(splitRight, [status(thm)], [c_388])).
% 3.73/1.63  tff(c_448, plain, (~m1_subset_1(k4_waybel_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_446])).
% 3.73/1.63  tff(c_455, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_448])).
% 3.73/1.63  tff(c_458, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_40, c_455])).
% 3.73/1.63  tff(c_460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_458])).
% 3.73/1.63  tff(c_462, plain, (m1_subset_1(k4_waybel_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_446])).
% 3.73/1.63  tff(c_137, plain, (![A_83, B_84]: (m1_subset_1(k11_yellow_6(A_83, B_84), u1_struct_0(A_83)) | ~l1_waybel_0(B_84, A_83) | ~v3_yellow_6(B_84, A_83) | ~v7_waybel_0(B_84) | ~v4_orders_2(B_84) | v2_struct_0(B_84) | ~l1_pre_topc(A_83) | ~v8_pre_topc(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.73/1.63  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k3_funct_2(A_1, B_2, C_3, D_4)=k1_funct_1(C_3, D_4) | ~m1_subset_1(D_4, A_1) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.73/1.63  tff(c_606, plain, (![A_153, B_154, C_155, B_156]: (k3_funct_2(u1_struct_0(A_153), B_154, C_155, k11_yellow_6(A_153, B_156))=k1_funct_1(C_155, k11_yellow_6(A_153, B_156)) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_153), B_154))) | ~v1_funct_2(C_155, u1_struct_0(A_153), B_154) | ~v1_funct_1(C_155) | v1_xboole_0(u1_struct_0(A_153)) | ~l1_waybel_0(B_156, A_153) | ~v3_yellow_6(B_156, A_153) | ~v7_waybel_0(B_156) | ~v4_orders_2(B_156) | v2_struct_0(B_156) | ~l1_pre_topc(A_153) | ~v8_pre_topc(A_153) | ~v2_pre_topc(A_153) | v2_struct_0(A_153))), inference(resolution, [status(thm)], [c_137, c_2])).
% 3.73/1.63  tff(c_608, plain, (![B_156]: (k3_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_156))=k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_156)) | ~v1_funct_2(k4_waybel_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', '#skF_4')) | v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_waybel_0(B_156, '#skF_2') | ~v3_yellow_6(B_156, '#skF_2') | ~v7_waybel_0(B_156) | ~v4_orders_2(B_156) | v2_struct_0(B_156) | ~l1_pre_topc('#skF_2') | ~v8_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_462, c_606])).
% 3.73/1.63  tff(c_613, plain, (![B_156]: (k3_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_156))=k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_156)) | v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_waybel_0(B_156, '#skF_2') | ~v3_yellow_6(B_156, '#skF_2') | ~v7_waybel_0(B_156) | ~v4_orders_2(B_156) | v2_struct_0(B_156) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_77, c_95, c_447, c_608])).
% 3.73/1.63  tff(c_616, plain, (![B_157]: (k3_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_157))=k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_157)) | ~l1_waybel_0(B_157, '#skF_2') | ~v3_yellow_6(B_157, '#skF_2') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(negUnitSimplification, [status(thm)], [c_96, c_183, c_613])).
% 3.73/1.63  tff(c_323, plain, (![A_121, B_122, D_123]: (k3_funct_2(u1_struct_0(A_121), u1_struct_0(A_121), k4_waybel_1(A_121, B_122), D_123)=k11_lattice3(A_121, B_122, D_123) | ~m1_subset_1(D_123, u1_struct_0(A_121)) | ~m1_subset_1(k4_waybel_1(A_121, B_122), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_121), u1_struct_0(A_121)))) | ~v1_funct_2(k4_waybel_1(A_121, B_122), u1_struct_0(A_121), u1_struct_0(A_121)) | ~v1_funct_1(k4_waybel_1(A_121, B_122)) | ~m1_subset_1(B_122, u1_struct_0(A_121)) | ~l1_orders_2(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.73/1.63  tff(c_327, plain, (![A_124, B_125, D_126]: (k3_funct_2(u1_struct_0(A_124), u1_struct_0(A_124), k4_waybel_1(A_124, B_125), D_126)=k11_lattice3(A_124, B_125, D_126) | ~m1_subset_1(D_126, u1_struct_0(A_124)) | ~v1_funct_2(k4_waybel_1(A_124, B_125), u1_struct_0(A_124), u1_struct_0(A_124)) | ~v1_funct_1(k4_waybel_1(A_124, B_125)) | ~m1_subset_1(B_125, u1_struct_0(A_124)) | ~l1_orders_2(A_124) | v2_struct_0(A_124))), inference(resolution, [status(thm)], [c_22, c_323])).
% 3.73/1.63  tff(c_330, plain, (![A_39, B_40, D_126]: (k3_funct_2(u1_struct_0(A_39), u1_struct_0(A_39), k4_waybel_1(A_39, B_40), D_126)=k11_lattice3(A_39, B_40, D_126) | ~m1_subset_1(D_126, u1_struct_0(A_39)) | ~v1_funct_1(k4_waybel_1(A_39, B_40)) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_orders_2(A_39) | v2_struct_0(A_39))), inference(resolution, [status(thm)], [c_24, c_327])).
% 3.73/1.63  tff(c_622, plain, (![B_157]: (k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_157))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_157)) | ~m1_subset_1(k11_yellow_6('#skF_2', B_157), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~l1_waybel_0(B_157, '#skF_2') | ~v3_yellow_6(B_157, '#skF_2') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(superposition, [status(thm), theory('equality')], [c_616, c_330])).
% 3.73/1.63  tff(c_631, plain, (![B_157]: (k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_157))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_157)) | ~m1_subset_1(k11_yellow_6('#skF_2', B_157), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~l1_waybel_0(B_157, '#skF_2') | ~v3_yellow_6(B_157, '#skF_2') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_40, c_95, c_622])).
% 3.73/1.63  tff(c_637, plain, (![B_158]: (k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_158))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_158)) | ~m1_subset_1(k11_yellow_6('#skF_2', B_158), u1_struct_0('#skF_2')) | ~l1_waybel_0(B_158, '#skF_2') | ~v3_yellow_6(B_158, '#skF_2') | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158))), inference(negUnitSimplification, [status(thm)], [c_96, c_631])).
% 3.73/1.63  tff(c_641, plain, (![B_12]: (k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_12))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_12)) | ~l1_waybel_0(B_12, '#skF_2') | ~v3_yellow_6(B_12, '#skF_2') | ~v7_waybel_0(B_12) | ~v4_orders_2(B_12) | v2_struct_0(B_12) | ~l1_pre_topc('#skF_2') | ~v8_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_637])).
% 3.73/1.63  tff(c_644, plain, (![B_12]: (k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_12))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_12)) | ~l1_waybel_0(B_12, '#skF_2') | ~v3_yellow_6(B_12, '#skF_2') | ~v7_waybel_0(B_12) | ~v4_orders_2(B_12) | v2_struct_0(B_12) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_77, c_641])).
% 3.73/1.63  tff(c_645, plain, (![B_12]: (k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_12))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_12)) | ~l1_waybel_0(B_12, '#skF_2') | ~v3_yellow_6(B_12, '#skF_2') | ~v7_waybel_0(B_12) | ~v4_orders_2(B_12) | v2_struct_0(B_12))), inference(negUnitSimplification, [status(thm)], [c_96, c_644])).
% 3.73/1.63  tff(c_203, plain, (![A_91, B_92, C_93, D_94]: (k2_yellow_6(A_91, B_92, C_93, D_94)=k1_funct_1(C_93, D_94) | ~m1_subset_1(D_94, A_91) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, u1_struct_0(B_92)))) | ~v1_funct_2(C_93, A_91, u1_struct_0(B_92)) | ~v1_funct_1(C_93) | ~l1_orders_2(B_92) | v2_struct_0(B_92) | v1_xboole_0(A_91))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.73/1.63  tff(c_800, plain, (![A_180, B_181, C_182, B_183]: (k2_yellow_6(u1_struct_0(A_180), B_181, C_182, k11_yellow_6(A_180, B_183))=k1_funct_1(C_182, k11_yellow_6(A_180, B_183)) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_180), u1_struct_0(B_181)))) | ~v1_funct_2(C_182, u1_struct_0(A_180), u1_struct_0(B_181)) | ~v1_funct_1(C_182) | ~l1_orders_2(B_181) | v2_struct_0(B_181) | v1_xboole_0(u1_struct_0(A_180)) | ~l1_waybel_0(B_183, A_180) | ~v3_yellow_6(B_183, A_180) | ~v7_waybel_0(B_183) | ~v4_orders_2(B_183) | v2_struct_0(B_183) | ~l1_pre_topc(A_180) | ~v8_pre_topc(A_180) | ~v2_pre_topc(A_180) | v2_struct_0(A_180))), inference(resolution, [status(thm)], [c_12, c_203])).
% 3.73/1.63  tff(c_802, plain, (![B_183]: (k2_yellow_6(u1_struct_0('#skF_2'), '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_183))=k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_183)) | ~v1_funct_2(k4_waybel_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', '#skF_4')) | ~l1_orders_2('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_waybel_0(B_183, '#skF_2') | ~v3_yellow_6(B_183, '#skF_2') | ~v7_waybel_0(B_183) | ~v4_orders_2(B_183) | v2_struct_0(B_183) | ~l1_pre_topc('#skF_2') | ~v8_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_462, c_800])).
% 3.73/1.63  tff(c_807, plain, (![B_183]: (k2_yellow_6(u1_struct_0('#skF_2'), '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_183))=k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_183)) | v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_waybel_0(B_183, '#skF_2') | ~v3_yellow_6(B_183, '#skF_2') | ~v7_waybel_0(B_183) | ~v4_orders_2(B_183) | v2_struct_0(B_183) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_77, c_71, c_95, c_447, c_802])).
% 3.73/1.63  tff(c_810, plain, (![B_184]: (k2_yellow_6(u1_struct_0('#skF_2'), '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_184))=k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_184)) | ~l1_waybel_0(B_184, '#skF_2') | ~v3_yellow_6(B_184, '#skF_2') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(negUnitSimplification, [status(thm)], [c_96, c_183, c_807])).
% 3.73/1.63  tff(c_34, plain, (![A_49, C_55, B_53]: (r2_hidden(k2_yellow_6(u1_struct_0(A_49), A_49, C_55, k11_yellow_6(A_49, B_53)), k10_yellow_6(A_49, k6_waybel_9(A_49, A_49, C_55, B_53))) | ~v5_pre_topc(C_55, A_49, A_49) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_49), u1_struct_0(A_49)))) | ~v1_funct_2(C_55, u1_struct_0(A_49), u1_struct_0(A_49)) | ~v1_funct_1(C_55) | ~l1_waybel_0(B_53, A_49) | ~v3_yellow_6(B_53, A_49) | ~v7_waybel_0(B_53) | ~v4_orders_2(B_53) | v2_struct_0(B_53) | ~l1_waybel_9(A_49) | ~v2_lattice3(A_49) | ~v1_lattice3(A_49) | ~v5_orders_2(A_49) | ~v4_orders_2(A_49) | ~v3_orders_2(A_49) | ~v8_pre_topc(A_49) | ~v2_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.73/1.63  tff(c_819, plain, (![B_184]: (r2_hidden(k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_184)), k10_yellow_6('#skF_2', k6_waybel_9('#skF_2', '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), B_184))) | ~v5_pre_topc(k4_waybel_1('#skF_2', '#skF_4'), '#skF_2', '#skF_2') | ~m1_subset_1(k4_waybel_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_waybel_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', '#skF_4')) | ~l1_waybel_0(B_184, '#skF_2') | ~v3_yellow_6(B_184, '#skF_2') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184) | ~l1_waybel_9('#skF_2') | ~v2_lattice3('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | ~v8_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_waybel_0(B_184, '#skF_2') | ~v3_yellow_6(B_184, '#skF_2') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(superposition, [status(thm), theory('equality')], [c_810, c_34])).
% 3.73/1.63  tff(c_827, plain, (![B_185]: (r2_hidden(k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_185)), k10_yellow_6('#skF_2', k6_waybel_9('#skF_2', '#skF_2', k4_waybel_1('#skF_2', '#skF_4'), B_185))) | ~l1_waybel_0(B_185, '#skF_2') | ~v3_yellow_6(B_185, '#skF_2') | ~v7_waybel_0(B_185) | ~v4_orders_2(B_185) | v2_struct_0(B_185))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_56, c_54, c_52, c_95, c_447, c_462, c_38, c_819])).
% 3.73/1.63  tff(c_834, plain, (![B_186]: (r2_hidden(k1_funct_1(k4_waybel_1('#skF_2', '#skF_4'), k11_yellow_6('#skF_2', B_186)), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', B_186))) | ~l1_waybel_0(B_186, '#skF_2') | ~v3_yellow_6(B_186, '#skF_2') | ~v7_waybel_0(B_186) | ~v4_orders_2(B_186) | v2_struct_0(B_186) | ~l1_waybel_0(B_186, '#skF_2') | v2_struct_0(B_186))), inference(superposition, [status(thm), theory('equality')], [c_120, c_827])).
% 3.73/1.63  tff(c_842, plain, (![B_188]: (r2_hidden(k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_188)), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', B_188))) | ~l1_waybel_0(B_188, '#skF_2') | ~v3_yellow_6(B_188, '#skF_2') | ~v7_waybel_0(B_188) | ~v4_orders_2(B_188) | v2_struct_0(B_188) | ~l1_waybel_0(B_188, '#skF_2') | v2_struct_0(B_188) | ~l1_waybel_0(B_188, '#skF_2') | ~v3_yellow_6(B_188, '#skF_2') | ~v7_waybel_0(B_188) | ~v4_orders_2(B_188) | v2_struct_0(B_188))), inference(superposition, [status(thm), theory('equality')], [c_645, c_834])).
% 3.73/1.63  tff(c_10, plain, (![A_8, B_9, C_10]: (k12_lattice3(A_8, B_9, C_10)=k11_lattice3(A_8, B_9, C_10) | ~m1_subset_1(C_10, u1_struct_0(A_8)) | ~m1_subset_1(B_9, u1_struct_0(A_8)) | ~l1_orders_2(A_8) | ~v2_lattice3(A_8) | ~v5_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.73/1.63  tff(c_295, plain, (![A_117, B_118, B_119]: (k12_lattice3(A_117, B_118, k11_yellow_6(A_117, B_119))=k11_lattice3(A_117, B_118, k11_yellow_6(A_117, B_119)) | ~m1_subset_1(B_118, u1_struct_0(A_117)) | ~l1_orders_2(A_117) | ~v2_lattice3(A_117) | ~v5_orders_2(A_117) | ~l1_waybel_0(B_119, A_117) | ~v3_yellow_6(B_119, A_117) | ~v7_waybel_0(B_119) | ~v4_orders_2(B_119) | v2_struct_0(B_119) | ~l1_pre_topc(A_117) | ~v8_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(resolution, [status(thm)], [c_137, c_10])).
% 3.73/1.63  tff(c_301, plain, (![B_119]: (k12_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_119))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_119)) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | ~l1_waybel_0(B_119, '#skF_2') | ~v3_yellow_6(B_119, '#skF_2') | ~v7_waybel_0(B_119) | ~v4_orders_2(B_119) | v2_struct_0(B_119) | ~l1_pre_topc('#skF_2') | ~v8_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_295])).
% 3.73/1.63  tff(c_306, plain, (![B_119]: (k12_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_119))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_119)) | ~l1_waybel_0(B_119, '#skF_2') | ~v3_yellow_6(B_119, '#skF_2') | ~v7_waybel_0(B_119) | ~v4_orders_2(B_119) | v2_struct_0(B_119) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_77, c_58, c_54, c_71, c_301])).
% 3.73/1.63  tff(c_308, plain, (![B_120]: (k12_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_120))=k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', B_120)) | ~l1_waybel_0(B_120, '#skF_2') | ~v3_yellow_6(B_120, '#skF_2') | ~v7_waybel_0(B_120) | ~v4_orders_2(B_120) | v2_struct_0(B_120))), inference(negUnitSimplification, [status(thm)], [c_96, c_306])).
% 3.73/1.63  tff(c_36, plain, (~r2_hidden(k12_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', '#skF_3')), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.73/1.63  tff(c_314, plain, (~r2_hidden(k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', '#skF_3')), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', '#skF_3'))) | ~l1_waybel_0('#skF_3', '#skF_2') | ~v3_yellow_6('#skF_3', '#skF_2') | ~v7_waybel_0('#skF_3') | ~v4_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_308, c_36])).
% 3.73/1.63  tff(c_320, plain, (~r2_hidden(k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', '#skF_3')), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', '#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_314])).
% 3.73/1.63  tff(c_321, plain, (~r2_hidden(k11_lattice3('#skF_2', '#skF_4', k11_yellow_6('#skF_2', '#skF_3')), k10_yellow_6('#skF_2', k3_waybel_2('#skF_2', '#skF_4', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_50, c_320])).
% 3.73/1.63  tff(c_845, plain, (~l1_waybel_0('#skF_3', '#skF_2') | ~v3_yellow_6('#skF_3', '#skF_2') | ~v7_waybel_0('#skF_3') | ~v4_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_842, c_321])).
% 3.73/1.63  tff(c_848, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_845])).
% 3.73/1.63  tff(c_850, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_848])).
% 3.73/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.63  
% 3.73/1.63  Inference rules
% 3.73/1.63  ----------------------
% 3.73/1.63  #Ref     : 1
% 3.73/1.63  #Sup     : 148
% 3.73/1.63  #Fact    : 0
% 3.73/1.63  #Define  : 0
% 3.73/1.63  #Split   : 4
% 3.73/1.63  #Chain   : 0
% 3.73/1.63  #Close   : 0
% 3.73/1.63  
% 3.73/1.63  Ordering : KBO
% 3.73/1.63  
% 3.73/1.63  Simplification rules
% 3.73/1.63  ----------------------
% 3.73/1.63  #Subsume      : 16
% 3.73/1.63  #Demod        : 172
% 3.73/1.63  #Tautology    : 59
% 3.73/1.63  #SimpNegUnit  : 42
% 3.73/1.63  #BackRed      : 0
% 3.73/1.63  
% 3.73/1.63  #Partial instantiations: 0
% 3.73/1.63  #Strategies tried      : 1
% 3.73/1.63  
% 3.73/1.63  Timing (in seconds)
% 3.73/1.63  ----------------------
% 3.73/1.63  Preprocessing        : 0.38
% 3.73/1.63  Parsing              : 0.20
% 3.73/1.63  CNF conversion       : 0.03
% 3.73/1.63  Main loop            : 0.48
% 3.73/1.63  Inferencing          : 0.19
% 3.73/1.63  Reduction            : 0.14
% 3.73/1.63  Demodulation         : 0.10
% 3.73/1.63  BG Simplification    : 0.03
% 3.73/1.63  Subsumption          : 0.08
% 3.73/1.63  Abstraction          : 0.04
% 3.73/1.63  MUC search           : 0.00
% 3.73/1.63  Cooper               : 0.00
% 3.73/1.63  Total                : 0.90
% 3.73/1.63  Index Insertion      : 0.00
% 3.73/1.63  Index Deletion       : 0.00
% 3.73/1.63  Index Matching       : 0.00
% 3.73/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
