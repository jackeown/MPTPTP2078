%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:08 EST 2020

% Result     : Theorem 12.33s
% Output     : CNFRefutation 12.55s
% Verified   : 
% Statistics : Number of formulae       :  181 (2710 expanded)
%              Number of leaves         :   30 ( 922 expanded)
%              Depth                    :   42
%              Number of atoms          :  747 (12150 expanded)
%              Number of equality atoms :   83 (1755 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_tarski > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v7_struct_0(B)
              & m1_pre_topc(B,A) )
           => ? [C] :
                ( m1_subset_1(C,u1_struct_0(A))
                & g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(k1_tex_2(A,C)),u1_pre_topc(k1_tex_2(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tex_2)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ( v7_struct_0(A)
      <=> ? [B] :
            ( m1_subset_1(B,u1_struct_0(A))
            & u1_struct_0(A) = k6_domain_1(u1_struct_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( u1_struct_0(B) = u1_struct_0(C)
               => g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tsep_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_111,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_tex_2(A,B)
              <=> u1_struct_0(C) = k6_domain_1(u1_struct_0(A),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_42,plain,(
    ! [B_41,A_42] :
      ( l1_pre_topc(B_41)
      | ~ m1_pre_topc(B_41,A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_45,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_42])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_45])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    v7_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_52,plain,(
    ! [A_47] :
      ( m1_subset_1('#skF_1'(A_47),u1_struct_0(A_47))
      | ~ v7_struct_0(A_47)
      | ~ l1_struct_0(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_10,plain,(
    ! [A_13,B_14] :
      ( k6_domain_1(A_13,B_14) = k1_tarski(B_14)
      | ~ m1_subset_1(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_97,plain,(
    ! [A_64] :
      ( k6_domain_1(u1_struct_0(A_64),'#skF_1'(A_64)) = k1_tarski('#skF_1'(A_64))
      | v1_xboole_0(u1_struct_0(A_64))
      | ~ v7_struct_0(A_64)
      | ~ l1_struct_0(A_64)
      | v2_struct_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_52,c_10])).

tff(c_16,plain,(
    ! [A_22] :
      ( k6_domain_1(u1_struct_0(A_22),'#skF_1'(A_22)) = u1_struct_0(A_22)
      | ~ v7_struct_0(A_22)
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_211,plain,(
    ! [A_84] :
      ( k1_tarski('#skF_1'(A_84)) = u1_struct_0(A_84)
      | ~ v7_struct_0(A_84)
      | ~ l1_struct_0(A_84)
      | v2_struct_0(A_84)
      | v1_xboole_0(u1_struct_0(A_84))
      | ~ v7_struct_0(A_84)
      | ~ l1_struct_0(A_84)
      | v2_struct_0(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_16])).

tff(c_6,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_215,plain,(
    ! [A_84] :
      ( k1_tarski('#skF_1'(A_84)) = u1_struct_0(A_84)
      | ~ v7_struct_0(A_84)
      | ~ l1_struct_0(A_84)
      | v2_struct_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_211,c_6])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_18,plain,(
    ! [A_22] :
      ( m1_subset_1('#skF_1'(A_22),u1_struct_0(A_22))
      | ~ v7_struct_0(A_22)
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_136,plain,(
    ! [C_69,B_70,A_71] :
      ( g1_pre_topc(u1_struct_0(C_69),u1_pre_topc(C_69)) = g1_pre_topc(u1_struct_0(B_70),u1_pre_topc(B_70))
      | u1_struct_0(C_69) != u1_struct_0(B_70)
      | ~ m1_pre_topc(C_69,A_71)
      | ~ m1_pre_topc(B_70,A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_140,plain,(
    ! [B_70] :
      ( g1_pre_topc(u1_struct_0(B_70),u1_pre_topc(B_70)) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | u1_struct_0(B_70) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_70,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_136])).

tff(c_145,plain,(
    ! [B_72] :
      ( g1_pre_topc(u1_struct_0(B_72),u1_pre_topc(B_72)) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | u1_struct_0(B_72) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_72,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_140])).

tff(c_30,plain,(
    ! [C_39] :
      ( g1_pre_topc(u1_struct_0(k1_tex_2('#skF_2',C_39)),u1_pre_topc(k1_tex_2('#skF_2',C_39))) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(C_39,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_160,plain,(
    ! [C_73] :
      ( ~ m1_subset_1(C_73,u1_struct_0('#skF_2'))
      | u1_struct_0(k1_tex_2('#skF_2',C_73)) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(k1_tex_2('#skF_2',C_73),'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_30])).

tff(c_168,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_2'))) != u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_2')),'#skF_2')
    | ~ v7_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_160])).

tff(c_175,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_2'))) != u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_2')),'#skF_2')
    | ~ v7_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_168])).

tff(c_176,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_188,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_176])).

tff(c_192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_188])).

tff(c_194,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_93,plain,(
    ! [C_61,A_62,B_63] :
      ( m1_subset_1(C_61,u1_struct_0(A_62))
      | ~ m1_subset_1(C_61,u1_struct_0(B_63))
      | ~ m1_pre_topc(B_63,A_62)
      | v2_struct_0(B_63)
      | ~ l1_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_112,plain,(
    ! [A_65,A_66] :
      ( m1_subset_1('#skF_1'(A_65),u1_struct_0(A_66))
      | ~ m1_pre_topc(A_65,A_66)
      | ~ l1_pre_topc(A_66)
      | v2_struct_0(A_66)
      | ~ v7_struct_0(A_65)
      | ~ l1_struct_0(A_65)
      | v2_struct_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_18,c_93])).

tff(c_8,plain,(
    ! [C_12,A_6,B_10] :
      ( m1_subset_1(C_12,u1_struct_0(A_6))
      | ~ m1_subset_1(C_12,u1_struct_0(B_10))
      | ~ m1_pre_topc(B_10,A_6)
      | v2_struct_0(B_10)
      | ~ l1_pre_topc(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_355,plain,(
    ! [A_96,A_97,A_98] :
      ( m1_subset_1('#skF_1'(A_96),u1_struct_0(A_97))
      | ~ m1_pre_topc(A_98,A_97)
      | ~ l1_pre_topc(A_97)
      | v2_struct_0(A_97)
      | ~ m1_pre_topc(A_96,A_98)
      | ~ l1_pre_topc(A_98)
      | v2_struct_0(A_98)
      | ~ v7_struct_0(A_96)
      | ~ l1_struct_0(A_96)
      | v2_struct_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_112,c_8])).

tff(c_361,plain,(
    ! [A_96] :
      ( m1_subset_1('#skF_1'(A_96),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(A_96,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v7_struct_0(A_96)
      | ~ l1_struct_0(A_96)
      | v2_struct_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_32,c_355])).

tff(c_366,plain,(
    ! [A_96] :
      ( m1_subset_1('#skF_1'(A_96),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(A_96,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v7_struct_0(A_96)
      | ~ l1_struct_0(A_96)
      | v2_struct_0(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38,c_361])).

tff(c_368,plain,(
    ! [A_99] :
      ( m1_subset_1('#skF_1'(A_99),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(A_99,'#skF_3')
      | ~ v7_struct_0(A_99)
      | ~ l1_struct_0(A_99)
      | v2_struct_0(A_99) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_40,c_366])).

tff(c_408,plain,(
    ! [A_99] :
      ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'(A_99)) = k1_tarski('#skF_1'(A_99))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(A_99,'#skF_3')
      | ~ v7_struct_0(A_99)
      | ~ l1_struct_0(A_99)
      | v2_struct_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_368,c_10])).

tff(c_15302,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_408])).

tff(c_15305,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_15302,c_6])).

tff(c_15308,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_15305])).

tff(c_15310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_15308])).

tff(c_15312,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_408])).

tff(c_134,plain,(
    ! [A_66,A_65] :
      ( k6_domain_1(u1_struct_0(A_66),'#skF_1'(A_65)) = k1_tarski('#skF_1'(A_65))
      | v1_xboole_0(u1_struct_0(A_66))
      | ~ m1_pre_topc(A_65,A_66)
      | ~ l1_pre_topc(A_66)
      | v2_struct_0(A_66)
      | ~ v7_struct_0(A_65)
      | ~ l1_struct_0(A_65)
      | v2_struct_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_112,c_10])).

tff(c_14,plain,(
    ! [A_22,B_25] :
      ( v7_struct_0(A_22)
      | k6_domain_1(u1_struct_0(A_22),B_25) != u1_struct_0(A_22)
      | ~ m1_subset_1(B_25,u1_struct_0(A_22))
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_376,plain,(
    ! [A_99] :
      ( v7_struct_0('#skF_2')
      | k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'(A_99)) != u1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(A_99,'#skF_3')
      | ~ v7_struct_0(A_99)
      | ~ l1_struct_0(A_99)
      | v2_struct_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_368,c_14])).

tff(c_394,plain,(
    ! [A_99] :
      ( v7_struct_0('#skF_2')
      | k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'(A_99)) != u1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(A_99,'#skF_3')
      | ~ v7_struct_0(A_99)
      | ~ l1_struct_0(A_99)
      | v2_struct_0(A_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_376])).

tff(c_395,plain,(
    ! [A_99] :
      ( v7_struct_0('#skF_2')
      | k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'(A_99)) != u1_struct_0('#skF_2')
      | ~ m1_pre_topc(A_99,'#skF_3')
      | ~ v7_struct_0(A_99)
      | ~ l1_struct_0(A_99)
      | v2_struct_0(A_99) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_394])).

tff(c_436,plain,(
    v7_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_395])).

tff(c_197,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_tex_2(A_77,B_78) = C_79
      | u1_struct_0(C_79) != k6_domain_1(u1_struct_0(A_77),B_78)
      | ~ m1_pre_topc(C_79,A_77)
      | ~ v1_pre_topc(C_79)
      | v2_struct_0(C_79)
      | ~ m1_subset_1(B_78,u1_struct_0(A_77))
      | ~ l1_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_437,plain,(
    ! [A_104,C_105] :
      ( k1_tex_2(A_104,'#skF_1'(A_104)) = C_105
      | u1_struct_0(C_105) != u1_struct_0(A_104)
      | ~ m1_pre_topc(C_105,A_104)
      | ~ v1_pre_topc(C_105)
      | v2_struct_0(C_105)
      | ~ m1_subset_1('#skF_1'(A_104),u1_struct_0(A_104))
      | ~ l1_pre_topc(A_104)
      | v2_struct_0(A_104)
      | ~ v7_struct_0(A_104)
      | ~ l1_struct_0(A_104)
      | v2_struct_0(A_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_197])).

tff(c_445,plain,
    ( k1_tex_2('#skF_2','#skF_1'('#skF_2')) = '#skF_3'
    | u1_struct_0('#skF_2') != u1_struct_0('#skF_3')
    | ~ v1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2'),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_437])).

tff(c_455,plain,
    ( k1_tex_2('#skF_2','#skF_1'('#skF_2')) = '#skF_3'
    | u1_struct_0('#skF_2') != u1_struct_0('#skF_3')
    | ~ v1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_38,c_445])).

tff(c_456,plain,
    ( k1_tex_2('#skF_2','#skF_1'('#skF_2')) = '#skF_3'
    | u1_struct_0('#skF_2') != u1_struct_0('#skF_3')
    | ~ v1_pre_topc('#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v7_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_36,c_455])).

tff(c_458,plain,
    ( k1_tex_2('#skF_2','#skF_1'('#skF_2')) = '#skF_3'
    | u1_struct_0('#skF_2') != u1_struct_0('#skF_3')
    | ~ v1_pre_topc('#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_456])).

tff(c_459,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_458])).

tff(c_468,plain,
    ( ~ v7_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_459])).

tff(c_479,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_436,c_468])).

tff(c_481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_479])).

tff(c_483,plain,(
    m1_subset_1('#skF_1'('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_458])).

tff(c_24,plain,(
    ! [A_33,B_34] :
      ( m1_pre_topc(k1_tex_2(A_33,B_34),A_33)
      | ~ m1_subset_1(B_34,u1_struct_0(A_33))
      | ~ l1_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_524,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_2')),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_483,c_24])).

tff(c_544,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_2')),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_524])).

tff(c_545,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_2')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_544])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( l1_pre_topc(B_4)
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_565,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_545,c_4])).

tff(c_584,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_565])).

tff(c_28,plain,(
    ! [A_33,B_34] :
      ( ~ v2_struct_0(k1_tex_2(A_33,B_34))
      | ~ m1_subset_1(B_34,u1_struct_0(A_33))
      | ~ l1_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_530,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_483,c_28])).

tff(c_552,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_530])).

tff(c_553,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_552])).

tff(c_26,plain,(
    ! [A_33,B_34] :
      ( v1_pre_topc(k1_tex_2(A_33,B_34))
      | ~ m1_subset_1(B_34,u1_struct_0(A_33))
      | ~ l1_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_527,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_483,c_26])).

tff(c_548,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_527])).

tff(c_549,plain,(
    v1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_548])).

tff(c_76,plain,(
    ! [A_53,B_54] :
      ( m1_pre_topc(k1_tex_2(A_53,B_54),A_53)
      | ~ m1_subset_1(B_54,u1_struct_0(A_53))
      | ~ l1_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_79,plain,(
    ! [A_22] :
      ( m1_pre_topc(k1_tex_2(A_22,'#skF_1'(A_22)),A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v7_struct_0(A_22)
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(resolution,[status(thm)],[c_18,c_76])).

tff(c_318,plain,(
    ! [A_92,B_93] :
      ( k6_domain_1(u1_struct_0(A_92),B_93) = u1_struct_0(k1_tex_2(A_92,B_93))
      | ~ m1_pre_topc(k1_tex_2(A_92,B_93),A_92)
      | ~ v1_pre_topc(k1_tex_2(A_92,B_93))
      | v2_struct_0(k1_tex_2(A_92,B_93))
      | ~ m1_subset_1(B_93,u1_struct_0(A_92))
      | ~ l1_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_585,plain,(
    ! [A_108] :
      ( k6_domain_1(u1_struct_0(A_108),'#skF_1'(A_108)) = u1_struct_0(k1_tex_2(A_108,'#skF_1'(A_108)))
      | ~ v1_pre_topc(k1_tex_2(A_108,'#skF_1'(A_108)))
      | v2_struct_0(k1_tex_2(A_108,'#skF_1'(A_108)))
      | ~ m1_subset_1('#skF_1'(A_108),u1_struct_0(A_108))
      | ~ l1_pre_topc(A_108)
      | ~ v7_struct_0(A_108)
      | ~ l1_struct_0(A_108)
      | v2_struct_0(A_108) ) ),
    inference(resolution,[status(thm)],[c_79,c_318])).

tff(c_588,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2')) = u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_2')))
    | ~ v1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_2')))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_483,c_585])).

tff(c_606,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2')) = u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_2')))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_436,c_38,c_549,c_588])).

tff(c_607,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2')) = u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_553,c_606])).

tff(c_629,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_2'))) = u1_struct_0('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_16])).

tff(c_654,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_2'))) = u1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_436,c_629])).

tff(c_655,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_2'))) = u1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_654])).

tff(c_727,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_2')))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_655,c_6])).

tff(c_779,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_553,c_727])).

tff(c_836,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_779])).

tff(c_839,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_2,c_836])).

tff(c_843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_839])).

tff(c_844,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_779])).

tff(c_96,plain,(
    ! [A_22,A_62] :
      ( m1_subset_1('#skF_1'(A_22),u1_struct_0(A_62))
      | ~ m1_pre_topc(A_22,A_62)
      | ~ l1_pre_topc(A_62)
      | v2_struct_0(A_62)
      | ~ v7_struct_0(A_22)
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(resolution,[status(thm)],[c_18,c_93])).

tff(c_704,plain,(
    ! [C_12,A_6] :
      ( m1_subset_1(C_12,u1_struct_0(A_6))
      | ~ m1_subset_1(C_12,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_2')),A_6)
      | v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_2')))
      | ~ l1_pre_topc(A_6)
      | v2_struct_0(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_655,c_8])).

tff(c_1398,plain,(
    ! [C_131,A_132] :
      ( m1_subset_1(C_131,u1_struct_0(A_132))
      | ~ m1_subset_1(C_131,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_2')),A_132)
      | ~ l1_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(negUnitSimplification,[status(thm)],[c_553,c_704])).

tff(c_1413,plain,(
    ! [A_22,A_132] :
      ( m1_subset_1('#skF_1'(A_22),u1_struct_0(A_132))
      | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_2')),A_132)
      | ~ l1_pre_topc(A_132)
      | v2_struct_0(A_132)
      | ~ m1_pre_topc(A_22,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v7_struct_0(A_22)
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(resolution,[status(thm)],[c_96,c_1398])).

tff(c_1430,plain,(
    ! [A_22,A_132] :
      ( m1_subset_1('#skF_1'(A_22),u1_struct_0(A_132))
      | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_2')),A_132)
      | ~ l1_pre_topc(A_132)
      | v2_struct_0(A_132)
      | ~ m1_pre_topc(A_22,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v7_struct_0(A_22)
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1413])).

tff(c_4109,plain,(
    ! [A_198,A_199] :
      ( m1_subset_1('#skF_1'(A_198),u1_struct_0(A_199))
      | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_2')),A_199)
      | ~ l1_pre_topc(A_199)
      | v2_struct_0(A_199)
      | ~ m1_pre_topc(A_198,'#skF_2')
      | ~ v7_struct_0(A_198)
      | ~ l1_struct_0(A_198)
      | v2_struct_0(A_198) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1430])).

tff(c_4672,plain,(
    ! [A_215,A_216] :
      ( v1_pre_topc(k1_tex_2(A_215,'#skF_1'(A_216)))
      | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_2')),A_215)
      | ~ l1_pre_topc(A_215)
      | v2_struct_0(A_215)
      | ~ m1_pre_topc(A_216,'#skF_2')
      | ~ v7_struct_0(A_216)
      | ~ l1_struct_0(A_216)
      | v2_struct_0(A_216) ) ),
    inference(resolution,[status(thm)],[c_4109,c_26])).

tff(c_4683,plain,(
    ! [A_216] :
      ( v1_pre_topc(k1_tex_2('#skF_2','#skF_1'(A_216)))
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(A_216,'#skF_2')
      | ~ v7_struct_0(A_216)
      | ~ l1_struct_0(A_216)
      | v2_struct_0(A_216) ) ),
    inference(resolution,[status(thm)],[c_545,c_4672])).

tff(c_4707,plain,(
    ! [A_216] :
      ( v1_pre_topc(k1_tex_2('#skF_2','#skF_1'(A_216)))
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(A_216,'#skF_2')
      | ~ v7_struct_0(A_216)
      | ~ l1_struct_0(A_216)
      | v2_struct_0(A_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4683])).

tff(c_4708,plain,(
    ! [A_216] :
      ( v1_pre_topc(k1_tex_2('#skF_2','#skF_1'(A_216)))
      | ~ m1_pre_topc(A_216,'#skF_2')
      | ~ v7_struct_0(A_216)
      | ~ l1_struct_0(A_216)
      | v2_struct_0(A_216) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_4707])).

tff(c_131,plain,(
    ! [A_66,A_65] :
      ( m1_pre_topc(k1_tex_2(A_66,'#skF_1'(A_65)),A_66)
      | ~ m1_pre_topc(A_65,A_66)
      | ~ l1_pre_topc(A_66)
      | v2_struct_0(A_66)
      | ~ v7_struct_0(A_65)
      | ~ l1_struct_0(A_65)
      | v2_struct_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_112,c_24])).

tff(c_1939,plain,(
    ! [A_147,A_148] :
      ( k6_domain_1(u1_struct_0(A_147),'#skF_1'(A_148)) = u1_struct_0(k1_tex_2(A_147,'#skF_1'(A_148)))
      | ~ v1_pre_topc(k1_tex_2(A_147,'#skF_1'(A_148)))
      | v2_struct_0(k1_tex_2(A_147,'#skF_1'(A_148)))
      | ~ m1_subset_1('#skF_1'(A_148),u1_struct_0(A_147))
      | ~ m1_pre_topc(A_148,A_147)
      | ~ l1_pre_topc(A_147)
      | v2_struct_0(A_147)
      | ~ v7_struct_0(A_148)
      | ~ l1_struct_0(A_148)
      | v2_struct_0(A_148) ) ),
    inference(resolution,[status(thm)],[c_131,c_318])).

tff(c_4777,plain,(
    ! [A_220,A_221] :
      ( k6_domain_1(u1_struct_0(A_220),'#skF_1'(A_221)) = u1_struct_0(k1_tex_2(A_220,'#skF_1'(A_221)))
      | ~ v1_pre_topc(k1_tex_2(A_220,'#skF_1'(A_221)))
      | v2_struct_0(k1_tex_2(A_220,'#skF_1'(A_221)))
      | ~ m1_pre_topc(A_221,A_220)
      | ~ l1_pre_topc(A_220)
      | v2_struct_0(A_220)
      | ~ v7_struct_0(A_221)
      | ~ l1_struct_0(A_221)
      | v2_struct_0(A_221) ) ),
    inference(resolution,[status(thm)],[c_96,c_1939])).

tff(c_133,plain,(
    ! [A_66,A_65] :
      ( ~ v2_struct_0(k1_tex_2(A_66,'#skF_1'(A_65)))
      | ~ m1_pre_topc(A_65,A_66)
      | ~ l1_pre_topc(A_66)
      | v2_struct_0(A_66)
      | ~ v7_struct_0(A_65)
      | ~ l1_struct_0(A_65)
      | v2_struct_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_112,c_28])).

tff(c_12703,plain,(
    ! [A_325,A_326] :
      ( k6_domain_1(u1_struct_0(A_325),'#skF_1'(A_326)) = u1_struct_0(k1_tex_2(A_325,'#skF_1'(A_326)))
      | ~ v1_pre_topc(k1_tex_2(A_325,'#skF_1'(A_326)))
      | ~ m1_pre_topc(A_326,A_325)
      | ~ l1_pre_topc(A_325)
      | v2_struct_0(A_325)
      | ~ v7_struct_0(A_326)
      | ~ l1_struct_0(A_326)
      | v2_struct_0(A_326) ) ),
    inference(resolution,[status(thm)],[c_4777,c_133])).

tff(c_12728,plain,(
    ! [A_216] :
      ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'(A_216)) = u1_struct_0(k1_tex_2('#skF_2','#skF_1'(A_216)))
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(A_216,'#skF_2')
      | ~ v7_struct_0(A_216)
      | ~ l1_struct_0(A_216)
      | v2_struct_0(A_216) ) ),
    inference(resolution,[status(thm)],[c_4708,c_12703])).

tff(c_12776,plain,(
    ! [A_216] :
      ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'(A_216)) = u1_struct_0(k1_tex_2('#skF_2','#skF_1'(A_216)))
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(A_216,'#skF_2')
      | ~ v7_struct_0(A_216)
      | ~ l1_struct_0(A_216)
      | v2_struct_0(A_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_12728])).

tff(c_12808,plain,(
    ! [A_327] :
      ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'(A_327)) = u1_struct_0(k1_tex_2('#skF_2','#skF_1'(A_327)))
      | ~ m1_pre_topc(A_327,'#skF_2')
      | ~ v7_struct_0(A_327)
      | ~ l1_struct_0(A_327)
      | v2_struct_0(A_327) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_12776])).

tff(c_12872,plain,(
    ! [A_327] :
      ( u1_struct_0(k1_tex_2('#skF_2','#skF_1'(A_327))) = k1_tarski('#skF_1'(A_327))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(A_327,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v7_struct_0(A_327)
      | ~ l1_struct_0(A_327)
      | v2_struct_0(A_327)
      | ~ m1_pre_topc(A_327,'#skF_2')
      | ~ v7_struct_0(A_327)
      | ~ l1_struct_0(A_327)
      | v2_struct_0(A_327) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12808,c_134])).

tff(c_12975,plain,(
    ! [A_327] :
      ( u1_struct_0(k1_tex_2('#skF_2','#skF_1'(A_327))) = k1_tarski('#skF_1'(A_327))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(A_327,'#skF_2')
      | ~ v7_struct_0(A_327)
      | ~ l1_struct_0(A_327)
      | v2_struct_0(A_327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_12872])).

tff(c_13023,plain,(
    ! [A_328] :
      ( u1_struct_0(k1_tex_2('#skF_2','#skF_1'(A_328))) = k1_tarski('#skF_1'(A_328))
      | ~ m1_pre_topc(A_328,'#skF_2')
      | ~ v7_struct_0(A_328)
      | ~ l1_struct_0(A_328)
      | v2_struct_0(A_328) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_844,c_12975])).

tff(c_164,plain,(
    ! [A_22] :
      ( u1_struct_0(k1_tex_2('#skF_2','#skF_1'(A_22))) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_1'(A_22)),'#skF_2')
      | ~ m1_pre_topc(A_22,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v7_struct_0(A_22)
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(resolution,[status(thm)],[c_96,c_160])).

tff(c_171,plain,(
    ! [A_22] :
      ( u1_struct_0(k1_tex_2('#skF_2','#skF_1'(A_22))) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_1'(A_22)),'#skF_2')
      | ~ m1_pre_topc(A_22,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v7_struct_0(A_22)
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_164])).

tff(c_216,plain,(
    ! [A_85] :
      ( u1_struct_0(k1_tex_2('#skF_2','#skF_1'(A_85))) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_1'(A_85)),'#skF_2')
      | ~ m1_pre_topc(A_85,'#skF_2')
      | ~ v7_struct_0(A_85)
      | ~ l1_struct_0(A_85)
      | v2_struct_0(A_85) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_171])).

tff(c_220,plain,(
    ! [A_65] :
      ( u1_struct_0(k1_tex_2('#skF_2','#skF_1'(A_65))) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(A_65,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v7_struct_0(A_65)
      | ~ l1_struct_0(A_65)
      | v2_struct_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_131,c_216])).

tff(c_227,plain,(
    ! [A_65] :
      ( u1_struct_0(k1_tex_2('#skF_2','#skF_1'(A_65))) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(A_65,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v7_struct_0(A_65)
      | ~ l1_struct_0(A_65)
      | v2_struct_0(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_220])).

tff(c_228,plain,(
    ! [A_65] :
      ( u1_struct_0(k1_tex_2('#skF_2','#skF_1'(A_65))) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(A_65,'#skF_2')
      | ~ v7_struct_0(A_65)
      | ~ l1_struct_0(A_65)
      | v2_struct_0(A_65) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_227])).

tff(c_14121,plain,(
    ! [A_336] :
      ( k1_tarski('#skF_1'(A_336)) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(A_336,'#skF_2')
      | ~ v7_struct_0(A_336)
      | ~ l1_struct_0(A_336)
      | v2_struct_0(A_336)
      | ~ m1_pre_topc(A_336,'#skF_2')
      | ~ v7_struct_0(A_336)
      | ~ l1_struct_0(A_336)
      | v2_struct_0(A_336) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13023,c_228])).

tff(c_15176,plain,(
    ! [A_347] :
      ( u1_struct_0(A_347) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(A_347,'#skF_2')
      | ~ v7_struct_0(A_347)
      | ~ l1_struct_0(A_347)
      | v2_struct_0(A_347)
      | ~ m1_pre_topc(A_347,'#skF_2')
      | ~ v7_struct_0(A_347)
      | ~ l1_struct_0(A_347)
      | v2_struct_0(A_347)
      | ~ v7_struct_0(A_347)
      | ~ l1_struct_0(A_347)
      | v2_struct_0(A_347) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_14121])).

tff(c_15209,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_15176])).

tff(c_15248,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_15209])).

tff(c_15249,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_15248])).

tff(c_15252,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_15249])).

tff(c_15256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_15252])).

tff(c_15279,plain,(
    ! [A_350] :
      ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'(A_350)) != u1_struct_0('#skF_2')
      | ~ m1_pre_topc(A_350,'#skF_3')
      | ~ v7_struct_0(A_350)
      | ~ l1_struct_0(A_350)
      | v2_struct_0(A_350) ) ),
    inference(splitRight,[status(thm)],[c_395])).

tff(c_15283,plain,(
    ! [A_65] :
      ( k1_tarski('#skF_1'(A_65)) != u1_struct_0('#skF_2')
      | ~ m1_pre_topc(A_65,'#skF_3')
      | ~ v7_struct_0(A_65)
      | ~ l1_struct_0(A_65)
      | v2_struct_0(A_65)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(A_65,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v7_struct_0(A_65)
      | ~ l1_struct_0(A_65)
      | v2_struct_0(A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_15279])).

tff(c_15293,plain,(
    ! [A_65] :
      ( k1_tarski('#skF_1'(A_65)) != u1_struct_0('#skF_2')
      | ~ m1_pre_topc(A_65,'#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(A_65,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v7_struct_0(A_65)
      | ~ l1_struct_0(A_65)
      | v2_struct_0(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_15283])).

tff(c_15294,plain,(
    ! [A_65] :
      ( k1_tarski('#skF_1'(A_65)) != u1_struct_0('#skF_2')
      | ~ m1_pre_topc(A_65,'#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(A_65,'#skF_2')
      | ~ v7_struct_0(A_65)
      | ~ l1_struct_0(A_65)
      | v2_struct_0(A_65) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_15293])).

tff(c_15313,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_15294])).

tff(c_15314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15312,c_15313])).

tff(c_15401,plain,(
    ! [A_353] :
      ( k1_tarski('#skF_1'(A_353)) != u1_struct_0('#skF_2')
      | ~ m1_pre_topc(A_353,'#skF_3')
      | ~ m1_pre_topc(A_353,'#skF_2')
      | ~ v7_struct_0(A_353)
      | ~ l1_struct_0(A_353)
      | v2_struct_0(A_353) ) ),
    inference(splitRight,[status(thm)],[c_15294])).

tff(c_15507,plain,(
    ! [A_368] :
      ( u1_struct_0(A_368) != u1_struct_0('#skF_2')
      | ~ m1_pre_topc(A_368,'#skF_3')
      | ~ m1_pre_topc(A_368,'#skF_2')
      | ~ v7_struct_0(A_368)
      | ~ l1_struct_0(A_368)
      | v2_struct_0(A_368)
      | ~ v7_struct_0(A_368)
      | ~ l1_struct_0(A_368)
      | v2_struct_0(A_368) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_15401])).

tff(c_15525,plain,
    ( u1_struct_0('#skF_2') != u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_15507])).

tff(c_15541,plain,
    ( u1_struct_0('#skF_2') != u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_15525])).

tff(c_15542,plain,
    ( u1_struct_0('#skF_2') != u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_15541])).

tff(c_15543,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_15542])).

tff(c_15546,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_15543])).

tff(c_15550,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_15546])).

tff(c_15552,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_15542])).

tff(c_132,plain,(
    ! [A_66,A_65] :
      ( v1_pre_topc(k1_tex_2(A_66,'#skF_1'(A_65)))
      | ~ m1_pre_topc(A_65,A_66)
      | ~ l1_pre_topc(A_66)
      | v2_struct_0(A_66)
      | ~ v7_struct_0(A_65)
      | ~ l1_struct_0(A_65)
      | v2_struct_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_112,c_26])).

tff(c_16434,plain,(
    ! [A_401,A_402] :
      ( k6_domain_1(u1_struct_0(A_401),'#skF_1'(A_402)) = u1_struct_0(k1_tex_2(A_401,'#skF_1'(A_402)))
      | ~ v1_pre_topc(k1_tex_2(A_401,'#skF_1'(A_402)))
      | v2_struct_0(k1_tex_2(A_401,'#skF_1'(A_402)))
      | ~ m1_subset_1('#skF_1'(A_402),u1_struct_0(A_401))
      | ~ m1_pre_topc(A_402,A_401)
      | ~ l1_pre_topc(A_401)
      | v2_struct_0(A_401)
      | ~ v7_struct_0(A_402)
      | ~ l1_struct_0(A_402)
      | v2_struct_0(A_402) ) ),
    inference(resolution,[status(thm)],[c_131,c_318])).

tff(c_16978,plain,(
    ! [A_425,A_426] :
      ( k6_domain_1(u1_struct_0(A_425),'#skF_1'(A_426)) = u1_struct_0(k1_tex_2(A_425,'#skF_1'(A_426)))
      | ~ v1_pre_topc(k1_tex_2(A_425,'#skF_1'(A_426)))
      | v2_struct_0(k1_tex_2(A_425,'#skF_1'(A_426)))
      | ~ m1_pre_topc(A_426,A_425)
      | ~ l1_pre_topc(A_425)
      | v2_struct_0(A_425)
      | ~ v7_struct_0(A_426)
      | ~ l1_struct_0(A_426)
      | v2_struct_0(A_426) ) ),
    inference(resolution,[status(thm)],[c_96,c_16434])).

tff(c_17013,plain,(
    ! [A_430,A_431] :
      ( k6_domain_1(u1_struct_0(A_430),'#skF_1'(A_431)) = u1_struct_0(k1_tex_2(A_430,'#skF_1'(A_431)))
      | ~ v1_pre_topc(k1_tex_2(A_430,'#skF_1'(A_431)))
      | ~ m1_pre_topc(A_431,A_430)
      | ~ l1_pre_topc(A_430)
      | v2_struct_0(A_430)
      | ~ v7_struct_0(A_431)
      | ~ l1_struct_0(A_431)
      | v2_struct_0(A_431) ) ),
    inference(resolution,[status(thm)],[c_16978,c_133])).

tff(c_17033,plain,(
    ! [A_432,A_433] :
      ( k6_domain_1(u1_struct_0(A_432),'#skF_1'(A_433)) = u1_struct_0(k1_tex_2(A_432,'#skF_1'(A_433)))
      | ~ m1_pre_topc(A_433,A_432)
      | ~ l1_pre_topc(A_432)
      | v2_struct_0(A_432)
      | ~ v7_struct_0(A_433)
      | ~ l1_struct_0(A_433)
      | v2_struct_0(A_433) ) ),
    inference(resolution,[status(thm)],[c_132,c_17013])).

tff(c_18398,plain,(
    ! [A_487,A_488] :
      ( u1_struct_0(k1_tex_2(A_487,'#skF_1'(A_488))) = k1_tarski('#skF_1'(A_488))
      | v1_xboole_0(u1_struct_0(A_487))
      | ~ m1_pre_topc(A_488,A_487)
      | ~ l1_pre_topc(A_487)
      | v2_struct_0(A_487)
      | ~ v7_struct_0(A_488)
      | ~ l1_struct_0(A_488)
      | v2_struct_0(A_488)
      | ~ m1_pre_topc(A_488,A_487)
      | ~ l1_pre_topc(A_487)
      | v2_struct_0(A_487)
      | ~ v7_struct_0(A_488)
      | ~ l1_struct_0(A_488)
      | v2_struct_0(A_488) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17033,c_134])).

tff(c_18524,plain,(
    ! [A_488] :
      ( k1_tarski('#skF_1'(A_488)) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(A_488,'#skF_2')
      | ~ v7_struct_0(A_488)
      | ~ l1_struct_0(A_488)
      | v2_struct_0(A_488)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(A_488,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v7_struct_0(A_488)
      | ~ l1_struct_0(A_488)
      | v2_struct_0(A_488)
      | ~ m1_pre_topc(A_488,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v7_struct_0(A_488)
      | ~ l1_struct_0(A_488)
      | v2_struct_0(A_488) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18398,c_228])).

tff(c_18620,plain,(
    ! [A_488] :
      ( k1_tarski('#skF_1'(A_488)) != u1_struct_0('#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(A_488,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v7_struct_0(A_488)
      | ~ l1_struct_0(A_488)
      | v2_struct_0(A_488) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_18524])).

tff(c_18641,plain,(
    ! [A_489] :
      ( k1_tarski('#skF_1'(A_489)) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(A_489,'#skF_2')
      | ~ v7_struct_0(A_489)
      | ~ l1_struct_0(A_489)
      | v2_struct_0(A_489) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_15312,c_18620])).

tff(c_18645,plain,(
    ! [A_490] :
      ( u1_struct_0(A_490) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(A_490,'#skF_2')
      | ~ v7_struct_0(A_490)
      | ~ l1_struct_0(A_490)
      | v2_struct_0(A_490)
      | ~ v7_struct_0(A_490)
      | ~ l1_struct_0(A_490)
      | v2_struct_0(A_490) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_18641])).

tff(c_18663,plain,
    ( ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_18645])).

tff(c_18679,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15552,c_34,c_18663])).

tff(c_18681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_18679])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:49:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.33/4.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.33/4.82  
% 12.33/4.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.33/4.83  %$ m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_tarski > #skF_1 > #skF_2 > #skF_3
% 12.33/4.83  
% 12.33/4.83  %Foreground sorts:
% 12.33/4.83  
% 12.33/4.83  
% 12.33/4.83  %Background operators:
% 12.33/4.83  
% 12.33/4.83  
% 12.33/4.83  %Foreground operators:
% 12.33/4.83  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.33/4.83  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 12.33/4.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.33/4.83  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 12.33/4.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.33/4.83  tff('#skF_1', type, '#skF_1': $i > $i).
% 12.33/4.83  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 12.33/4.83  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.33/4.83  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 12.33/4.83  tff('#skF_2', type, '#skF_2': $i).
% 12.33/4.83  tff('#skF_3', type, '#skF_3': $i).
% 12.33/4.83  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 12.33/4.83  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 12.33/4.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.33/4.83  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 12.33/4.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.33/4.83  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 12.33/4.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.33/4.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.33/4.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.33/4.83  
% 12.55/4.85  tff(f_144, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v7_struct_0(B)) & m1_pre_topc(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & (g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(k1_tex_2(A, C)), u1_pre_topc(k1_tex_2(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tex_2)).
% 12.55/4.85  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 12.55/4.85  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 12.55/4.85  tff(f_91, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (v7_struct_0(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & (u1_struct_0(A) = k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_1)).
% 12.55/4.85  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 12.55/4.85  tff(f_44, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 12.55/4.85  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => ((u1_struct_0(B) = u1_struct_0(C)) => (g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tsep_1)).
% 12.55/4.85  tff(f_60, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 12.55/4.85  tff(f_111, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tex_2)).
% 12.55/4.85  tff(f_125, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 12.55/4.85  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.55/4.85  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.55/4.85  tff(c_32, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.55/4.85  tff(c_42, plain, (![B_41, A_42]: (l1_pre_topc(B_41) | ~m1_pre_topc(B_41, A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_36])).
% 12.55/4.85  tff(c_45, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_42])).
% 12.55/4.85  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_45])).
% 12.55/4.85  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.55/4.85  tff(c_34, plain, (v7_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.55/4.85  tff(c_52, plain, (![A_47]: (m1_subset_1('#skF_1'(A_47), u1_struct_0(A_47)) | ~v7_struct_0(A_47) | ~l1_struct_0(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.55/4.85  tff(c_10, plain, (![A_13, B_14]: (k6_domain_1(A_13, B_14)=k1_tarski(B_14) | ~m1_subset_1(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.55/4.85  tff(c_97, plain, (![A_64]: (k6_domain_1(u1_struct_0(A_64), '#skF_1'(A_64))=k1_tarski('#skF_1'(A_64)) | v1_xboole_0(u1_struct_0(A_64)) | ~v7_struct_0(A_64) | ~l1_struct_0(A_64) | v2_struct_0(A_64))), inference(resolution, [status(thm)], [c_52, c_10])).
% 12.55/4.85  tff(c_16, plain, (![A_22]: (k6_domain_1(u1_struct_0(A_22), '#skF_1'(A_22))=u1_struct_0(A_22) | ~v7_struct_0(A_22) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.55/4.85  tff(c_211, plain, (![A_84]: (k1_tarski('#skF_1'(A_84))=u1_struct_0(A_84) | ~v7_struct_0(A_84) | ~l1_struct_0(A_84) | v2_struct_0(A_84) | v1_xboole_0(u1_struct_0(A_84)) | ~v7_struct_0(A_84) | ~l1_struct_0(A_84) | v2_struct_0(A_84))), inference(superposition, [status(thm), theory('equality')], [c_97, c_16])).
% 12.55/4.85  tff(c_6, plain, (![A_5]: (~v1_xboole_0(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.55/4.85  tff(c_215, plain, (![A_84]: (k1_tarski('#skF_1'(A_84))=u1_struct_0(A_84) | ~v7_struct_0(A_84) | ~l1_struct_0(A_84) | v2_struct_0(A_84))), inference(resolution, [status(thm)], [c_211, c_6])).
% 12.55/4.85  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.55/4.85  tff(c_18, plain, (![A_22]: (m1_subset_1('#skF_1'(A_22), u1_struct_0(A_22)) | ~v7_struct_0(A_22) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.55/4.85  tff(c_136, plain, (![C_69, B_70, A_71]: (g1_pre_topc(u1_struct_0(C_69), u1_pre_topc(C_69))=g1_pre_topc(u1_struct_0(B_70), u1_pre_topc(B_70)) | u1_struct_0(C_69)!=u1_struct_0(B_70) | ~m1_pre_topc(C_69, A_71) | ~m1_pre_topc(B_70, A_71) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.55/4.85  tff(c_140, plain, (![B_70]: (g1_pre_topc(u1_struct_0(B_70), u1_pre_topc(B_70))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | u1_struct_0(B_70)!=u1_struct_0('#skF_3') | ~m1_pre_topc(B_70, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_136])).
% 12.55/4.85  tff(c_145, plain, (![B_72]: (g1_pre_topc(u1_struct_0(B_72), u1_pre_topc(B_72))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | u1_struct_0(B_72)!=u1_struct_0('#skF_3') | ~m1_pre_topc(B_72, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_140])).
% 12.55/4.85  tff(c_30, plain, (![C_39]: (g1_pre_topc(u1_struct_0(k1_tex_2('#skF_2', C_39)), u1_pre_topc(k1_tex_2('#skF_2', C_39)))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_subset_1(C_39, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.55/4.85  tff(c_160, plain, (![C_73]: (~m1_subset_1(C_73, u1_struct_0('#skF_2')) | u1_struct_0(k1_tex_2('#skF_2', C_73))!=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_2', C_73), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_30])).
% 12.55/4.85  tff(c_168, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_2')))!=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_2')), '#skF_2') | ~v7_struct_0('#skF_2') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_160])).
% 12.55/4.85  tff(c_175, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_2')))!=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_2')), '#skF_2') | ~v7_struct_0('#skF_2') | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_168])).
% 12.55/4.85  tff(c_176, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_175])).
% 12.55/4.85  tff(c_188, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_176])).
% 12.55/4.85  tff(c_192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_188])).
% 12.55/4.85  tff(c_194, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_175])).
% 12.55/4.85  tff(c_93, plain, (![C_61, A_62, B_63]: (m1_subset_1(C_61, u1_struct_0(A_62)) | ~m1_subset_1(C_61, u1_struct_0(B_63)) | ~m1_pre_topc(B_63, A_62) | v2_struct_0(B_63) | ~l1_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.55/4.85  tff(c_112, plain, (![A_65, A_66]: (m1_subset_1('#skF_1'(A_65), u1_struct_0(A_66)) | ~m1_pre_topc(A_65, A_66) | ~l1_pre_topc(A_66) | v2_struct_0(A_66) | ~v7_struct_0(A_65) | ~l1_struct_0(A_65) | v2_struct_0(A_65))), inference(resolution, [status(thm)], [c_18, c_93])).
% 12.55/4.85  tff(c_8, plain, (![C_12, A_6, B_10]: (m1_subset_1(C_12, u1_struct_0(A_6)) | ~m1_subset_1(C_12, u1_struct_0(B_10)) | ~m1_pre_topc(B_10, A_6) | v2_struct_0(B_10) | ~l1_pre_topc(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.55/4.85  tff(c_355, plain, (![A_96, A_97, A_98]: (m1_subset_1('#skF_1'(A_96), u1_struct_0(A_97)) | ~m1_pre_topc(A_98, A_97) | ~l1_pre_topc(A_97) | v2_struct_0(A_97) | ~m1_pre_topc(A_96, A_98) | ~l1_pre_topc(A_98) | v2_struct_0(A_98) | ~v7_struct_0(A_96) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(resolution, [status(thm)], [c_112, c_8])).
% 12.55/4.85  tff(c_361, plain, (![A_96]: (m1_subset_1('#skF_1'(A_96), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(A_96, '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~v7_struct_0(A_96) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(resolution, [status(thm)], [c_32, c_355])).
% 12.55/4.85  tff(c_366, plain, (![A_96]: (m1_subset_1('#skF_1'(A_96), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_pre_topc(A_96, '#skF_3') | v2_struct_0('#skF_3') | ~v7_struct_0(A_96) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_38, c_361])).
% 12.55/4.85  tff(c_368, plain, (![A_99]: (m1_subset_1('#skF_1'(A_99), u1_struct_0('#skF_2')) | ~m1_pre_topc(A_99, '#skF_3') | ~v7_struct_0(A_99) | ~l1_struct_0(A_99) | v2_struct_0(A_99))), inference(negUnitSimplification, [status(thm)], [c_36, c_40, c_366])).
% 12.55/4.85  tff(c_408, plain, (![A_99]: (k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'(A_99))=k1_tarski('#skF_1'(A_99)) | v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_pre_topc(A_99, '#skF_3') | ~v7_struct_0(A_99) | ~l1_struct_0(A_99) | v2_struct_0(A_99))), inference(resolution, [status(thm)], [c_368, c_10])).
% 12.55/4.85  tff(c_15302, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_408])).
% 12.55/4.85  tff(c_15305, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_15302, c_6])).
% 12.55/4.85  tff(c_15308, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_15305])).
% 12.55/4.85  tff(c_15310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_15308])).
% 12.55/4.85  tff(c_15312, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_408])).
% 12.55/4.85  tff(c_134, plain, (![A_66, A_65]: (k6_domain_1(u1_struct_0(A_66), '#skF_1'(A_65))=k1_tarski('#skF_1'(A_65)) | v1_xboole_0(u1_struct_0(A_66)) | ~m1_pre_topc(A_65, A_66) | ~l1_pre_topc(A_66) | v2_struct_0(A_66) | ~v7_struct_0(A_65) | ~l1_struct_0(A_65) | v2_struct_0(A_65))), inference(resolution, [status(thm)], [c_112, c_10])).
% 12.55/4.85  tff(c_14, plain, (![A_22, B_25]: (v7_struct_0(A_22) | k6_domain_1(u1_struct_0(A_22), B_25)!=u1_struct_0(A_22) | ~m1_subset_1(B_25, u1_struct_0(A_22)) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.55/4.85  tff(c_376, plain, (![A_99]: (v7_struct_0('#skF_2') | k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'(A_99))!=u1_struct_0('#skF_2') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(A_99, '#skF_3') | ~v7_struct_0(A_99) | ~l1_struct_0(A_99) | v2_struct_0(A_99))), inference(resolution, [status(thm)], [c_368, c_14])).
% 12.55/4.85  tff(c_394, plain, (![A_99]: (v7_struct_0('#skF_2') | k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'(A_99))!=u1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(A_99, '#skF_3') | ~v7_struct_0(A_99) | ~l1_struct_0(A_99) | v2_struct_0(A_99))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_376])).
% 12.55/4.85  tff(c_395, plain, (![A_99]: (v7_struct_0('#skF_2') | k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'(A_99))!=u1_struct_0('#skF_2') | ~m1_pre_topc(A_99, '#skF_3') | ~v7_struct_0(A_99) | ~l1_struct_0(A_99) | v2_struct_0(A_99))), inference(negUnitSimplification, [status(thm)], [c_40, c_394])).
% 12.55/4.85  tff(c_436, plain, (v7_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_395])).
% 12.55/4.85  tff(c_197, plain, (![A_77, B_78, C_79]: (k1_tex_2(A_77, B_78)=C_79 | u1_struct_0(C_79)!=k6_domain_1(u1_struct_0(A_77), B_78) | ~m1_pre_topc(C_79, A_77) | ~v1_pre_topc(C_79) | v2_struct_0(C_79) | ~m1_subset_1(B_78, u1_struct_0(A_77)) | ~l1_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.55/4.86  tff(c_437, plain, (![A_104, C_105]: (k1_tex_2(A_104, '#skF_1'(A_104))=C_105 | u1_struct_0(C_105)!=u1_struct_0(A_104) | ~m1_pre_topc(C_105, A_104) | ~v1_pre_topc(C_105) | v2_struct_0(C_105) | ~m1_subset_1('#skF_1'(A_104), u1_struct_0(A_104)) | ~l1_pre_topc(A_104) | v2_struct_0(A_104) | ~v7_struct_0(A_104) | ~l1_struct_0(A_104) | v2_struct_0(A_104))), inference(superposition, [status(thm), theory('equality')], [c_16, c_197])).
% 12.55/4.86  tff(c_445, plain, (k1_tex_2('#skF_2', '#skF_1'('#skF_2'))='#skF_3' | u1_struct_0('#skF_2')!=u1_struct_0('#skF_3') | ~v1_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_1'('#skF_2'), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v7_struct_0('#skF_2') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_437])).
% 12.55/4.86  tff(c_455, plain, (k1_tex_2('#skF_2', '#skF_1'('#skF_2'))='#skF_3' | u1_struct_0('#skF_2')!=u1_struct_0('#skF_3') | ~v1_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_1'('#skF_2'), u1_struct_0('#skF_2')) | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_38, c_445])).
% 12.55/4.86  tff(c_456, plain, (k1_tex_2('#skF_2', '#skF_1'('#skF_2'))='#skF_3' | u1_struct_0('#skF_2')!=u1_struct_0('#skF_3') | ~v1_pre_topc('#skF_3') | ~m1_subset_1('#skF_1'('#skF_2'), u1_struct_0('#skF_2')) | ~v7_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_36, c_455])).
% 12.55/4.86  tff(c_458, plain, (k1_tex_2('#skF_2', '#skF_1'('#skF_2'))='#skF_3' | u1_struct_0('#skF_2')!=u1_struct_0('#skF_3') | ~v1_pre_topc('#skF_3') | ~m1_subset_1('#skF_1'('#skF_2'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_436, c_456])).
% 12.55/4.86  tff(c_459, plain, (~m1_subset_1('#skF_1'('#skF_2'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_458])).
% 12.55/4.86  tff(c_468, plain, (~v7_struct_0('#skF_2') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_459])).
% 12.55/4.86  tff(c_479, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_436, c_468])).
% 12.55/4.86  tff(c_481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_479])).
% 12.55/4.86  tff(c_483, plain, (m1_subset_1('#skF_1'('#skF_2'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_458])).
% 12.55/4.86  tff(c_24, plain, (![A_33, B_34]: (m1_pre_topc(k1_tex_2(A_33, B_34), A_33) | ~m1_subset_1(B_34, u1_struct_0(A_33)) | ~l1_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_125])).
% 12.55/4.86  tff(c_524, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_2')), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_483, c_24])).
% 12.55/4.86  tff(c_544, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_2')), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_524])).
% 12.55/4.86  tff(c_545, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_2')), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_544])).
% 12.55/4.86  tff(c_4, plain, (![B_4, A_2]: (l1_pre_topc(B_4) | ~m1_pre_topc(B_4, A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 12.55/4.86  tff(c_565, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_545, c_4])).
% 12.55/4.86  tff(c_584, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_565])).
% 12.55/4.86  tff(c_28, plain, (![A_33, B_34]: (~v2_struct_0(k1_tex_2(A_33, B_34)) | ~m1_subset_1(B_34, u1_struct_0(A_33)) | ~l1_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_125])).
% 12.55/4.86  tff(c_530, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_2'))) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_483, c_28])).
% 12.55/4.86  tff(c_552, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_530])).
% 12.55/4.86  tff(c_553, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_552])).
% 12.55/4.86  tff(c_26, plain, (![A_33, B_34]: (v1_pre_topc(k1_tex_2(A_33, B_34)) | ~m1_subset_1(B_34, u1_struct_0(A_33)) | ~l1_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_125])).
% 12.55/4.86  tff(c_527, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_2'))) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_483, c_26])).
% 12.55/4.86  tff(c_548, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_527])).
% 12.55/4.86  tff(c_549, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_548])).
% 12.55/4.86  tff(c_76, plain, (![A_53, B_54]: (m1_pre_topc(k1_tex_2(A_53, B_54), A_53) | ~m1_subset_1(B_54, u1_struct_0(A_53)) | ~l1_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_125])).
% 12.55/4.86  tff(c_79, plain, (![A_22]: (m1_pre_topc(k1_tex_2(A_22, '#skF_1'(A_22)), A_22) | ~l1_pre_topc(A_22) | ~v7_struct_0(A_22) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(resolution, [status(thm)], [c_18, c_76])).
% 12.55/4.86  tff(c_318, plain, (![A_92, B_93]: (k6_domain_1(u1_struct_0(A_92), B_93)=u1_struct_0(k1_tex_2(A_92, B_93)) | ~m1_pre_topc(k1_tex_2(A_92, B_93), A_92) | ~v1_pre_topc(k1_tex_2(A_92, B_93)) | v2_struct_0(k1_tex_2(A_92, B_93)) | ~m1_subset_1(B_93, u1_struct_0(A_92)) | ~l1_pre_topc(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.55/4.86  tff(c_585, plain, (![A_108]: (k6_domain_1(u1_struct_0(A_108), '#skF_1'(A_108))=u1_struct_0(k1_tex_2(A_108, '#skF_1'(A_108))) | ~v1_pre_topc(k1_tex_2(A_108, '#skF_1'(A_108))) | v2_struct_0(k1_tex_2(A_108, '#skF_1'(A_108))) | ~m1_subset_1('#skF_1'(A_108), u1_struct_0(A_108)) | ~l1_pre_topc(A_108) | ~v7_struct_0(A_108) | ~l1_struct_0(A_108) | v2_struct_0(A_108))), inference(resolution, [status(thm)], [c_79, c_318])).
% 12.55/4.86  tff(c_588, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2'))=u1_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_2'))) | ~v1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_2'))) | v2_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v7_struct_0('#skF_2') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_483, c_585])).
% 12.55/4.86  tff(c_606, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2'))=u1_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_2'))) | v2_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_436, c_38, c_549, c_588])).
% 12.55/4.86  tff(c_607, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2'))=u1_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_553, c_606])).
% 12.55/4.86  tff(c_629, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_2')))=u1_struct_0('#skF_2') | ~v7_struct_0('#skF_2') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_607, c_16])).
% 12.55/4.86  tff(c_654, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_2')))=u1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_436, c_629])).
% 12.55/4.86  tff(c_655, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_2')))=u1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_654])).
% 12.55/4.86  tff(c_727, plain, (~v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_2'))) | v2_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_655, c_6])).
% 12.55/4.86  tff(c_779, plain, (~v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_553, c_727])).
% 12.55/4.86  tff(c_836, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_2')))), inference(splitLeft, [status(thm)], [c_779])).
% 12.55/4.86  tff(c_839, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_2')))), inference(resolution, [status(thm)], [c_2, c_836])).
% 12.55/4.86  tff(c_843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_584, c_839])).
% 12.55/4.86  tff(c_844, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_779])).
% 12.55/4.86  tff(c_96, plain, (![A_22, A_62]: (m1_subset_1('#skF_1'(A_22), u1_struct_0(A_62)) | ~m1_pre_topc(A_22, A_62) | ~l1_pre_topc(A_62) | v2_struct_0(A_62) | ~v7_struct_0(A_22) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(resolution, [status(thm)], [c_18, c_93])).
% 12.55/4.86  tff(c_704, plain, (![C_12, A_6]: (m1_subset_1(C_12, u1_struct_0(A_6)) | ~m1_subset_1(C_12, u1_struct_0('#skF_2')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_2')), A_6) | v2_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_2'))) | ~l1_pre_topc(A_6) | v2_struct_0(A_6))), inference(superposition, [status(thm), theory('equality')], [c_655, c_8])).
% 12.55/4.86  tff(c_1398, plain, (![C_131, A_132]: (m1_subset_1(C_131, u1_struct_0(A_132)) | ~m1_subset_1(C_131, u1_struct_0('#skF_2')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_2')), A_132) | ~l1_pre_topc(A_132) | v2_struct_0(A_132))), inference(negUnitSimplification, [status(thm)], [c_553, c_704])).
% 12.55/4.86  tff(c_1413, plain, (![A_22, A_132]: (m1_subset_1('#skF_1'(A_22), u1_struct_0(A_132)) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_2')), A_132) | ~l1_pre_topc(A_132) | v2_struct_0(A_132) | ~m1_pre_topc(A_22, '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v7_struct_0(A_22) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(resolution, [status(thm)], [c_96, c_1398])).
% 12.55/4.86  tff(c_1430, plain, (![A_22, A_132]: (m1_subset_1('#skF_1'(A_22), u1_struct_0(A_132)) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_2')), A_132) | ~l1_pre_topc(A_132) | v2_struct_0(A_132) | ~m1_pre_topc(A_22, '#skF_2') | v2_struct_0('#skF_2') | ~v7_struct_0(A_22) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1413])).
% 12.55/4.86  tff(c_4109, plain, (![A_198, A_199]: (m1_subset_1('#skF_1'(A_198), u1_struct_0(A_199)) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_2')), A_199) | ~l1_pre_topc(A_199) | v2_struct_0(A_199) | ~m1_pre_topc(A_198, '#skF_2') | ~v7_struct_0(A_198) | ~l1_struct_0(A_198) | v2_struct_0(A_198))), inference(negUnitSimplification, [status(thm)], [c_40, c_1430])).
% 12.55/4.86  tff(c_4672, plain, (![A_215, A_216]: (v1_pre_topc(k1_tex_2(A_215, '#skF_1'(A_216))) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_2')), A_215) | ~l1_pre_topc(A_215) | v2_struct_0(A_215) | ~m1_pre_topc(A_216, '#skF_2') | ~v7_struct_0(A_216) | ~l1_struct_0(A_216) | v2_struct_0(A_216))), inference(resolution, [status(thm)], [c_4109, c_26])).
% 12.55/4.86  tff(c_4683, plain, (![A_216]: (v1_pre_topc(k1_tex_2('#skF_2', '#skF_1'(A_216))) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(A_216, '#skF_2') | ~v7_struct_0(A_216) | ~l1_struct_0(A_216) | v2_struct_0(A_216))), inference(resolution, [status(thm)], [c_545, c_4672])).
% 12.55/4.86  tff(c_4707, plain, (![A_216]: (v1_pre_topc(k1_tex_2('#skF_2', '#skF_1'(A_216))) | v2_struct_0('#skF_2') | ~m1_pre_topc(A_216, '#skF_2') | ~v7_struct_0(A_216) | ~l1_struct_0(A_216) | v2_struct_0(A_216))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4683])).
% 12.55/4.86  tff(c_4708, plain, (![A_216]: (v1_pre_topc(k1_tex_2('#skF_2', '#skF_1'(A_216))) | ~m1_pre_topc(A_216, '#skF_2') | ~v7_struct_0(A_216) | ~l1_struct_0(A_216) | v2_struct_0(A_216))), inference(negUnitSimplification, [status(thm)], [c_40, c_4707])).
% 12.55/4.86  tff(c_131, plain, (![A_66, A_65]: (m1_pre_topc(k1_tex_2(A_66, '#skF_1'(A_65)), A_66) | ~m1_pre_topc(A_65, A_66) | ~l1_pre_topc(A_66) | v2_struct_0(A_66) | ~v7_struct_0(A_65) | ~l1_struct_0(A_65) | v2_struct_0(A_65))), inference(resolution, [status(thm)], [c_112, c_24])).
% 12.55/4.86  tff(c_1939, plain, (![A_147, A_148]: (k6_domain_1(u1_struct_0(A_147), '#skF_1'(A_148))=u1_struct_0(k1_tex_2(A_147, '#skF_1'(A_148))) | ~v1_pre_topc(k1_tex_2(A_147, '#skF_1'(A_148))) | v2_struct_0(k1_tex_2(A_147, '#skF_1'(A_148))) | ~m1_subset_1('#skF_1'(A_148), u1_struct_0(A_147)) | ~m1_pre_topc(A_148, A_147) | ~l1_pre_topc(A_147) | v2_struct_0(A_147) | ~v7_struct_0(A_148) | ~l1_struct_0(A_148) | v2_struct_0(A_148))), inference(resolution, [status(thm)], [c_131, c_318])).
% 12.55/4.86  tff(c_4777, plain, (![A_220, A_221]: (k6_domain_1(u1_struct_0(A_220), '#skF_1'(A_221))=u1_struct_0(k1_tex_2(A_220, '#skF_1'(A_221))) | ~v1_pre_topc(k1_tex_2(A_220, '#skF_1'(A_221))) | v2_struct_0(k1_tex_2(A_220, '#skF_1'(A_221))) | ~m1_pre_topc(A_221, A_220) | ~l1_pre_topc(A_220) | v2_struct_0(A_220) | ~v7_struct_0(A_221) | ~l1_struct_0(A_221) | v2_struct_0(A_221))), inference(resolution, [status(thm)], [c_96, c_1939])).
% 12.55/4.86  tff(c_133, plain, (![A_66, A_65]: (~v2_struct_0(k1_tex_2(A_66, '#skF_1'(A_65))) | ~m1_pre_topc(A_65, A_66) | ~l1_pre_topc(A_66) | v2_struct_0(A_66) | ~v7_struct_0(A_65) | ~l1_struct_0(A_65) | v2_struct_0(A_65))), inference(resolution, [status(thm)], [c_112, c_28])).
% 12.55/4.86  tff(c_12703, plain, (![A_325, A_326]: (k6_domain_1(u1_struct_0(A_325), '#skF_1'(A_326))=u1_struct_0(k1_tex_2(A_325, '#skF_1'(A_326))) | ~v1_pre_topc(k1_tex_2(A_325, '#skF_1'(A_326))) | ~m1_pre_topc(A_326, A_325) | ~l1_pre_topc(A_325) | v2_struct_0(A_325) | ~v7_struct_0(A_326) | ~l1_struct_0(A_326) | v2_struct_0(A_326))), inference(resolution, [status(thm)], [c_4777, c_133])).
% 12.55/4.86  tff(c_12728, plain, (![A_216]: (k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'(A_216))=u1_struct_0(k1_tex_2('#skF_2', '#skF_1'(A_216))) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(A_216, '#skF_2') | ~v7_struct_0(A_216) | ~l1_struct_0(A_216) | v2_struct_0(A_216))), inference(resolution, [status(thm)], [c_4708, c_12703])).
% 12.55/4.86  tff(c_12776, plain, (![A_216]: (k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'(A_216))=u1_struct_0(k1_tex_2('#skF_2', '#skF_1'(A_216))) | v2_struct_0('#skF_2') | ~m1_pre_topc(A_216, '#skF_2') | ~v7_struct_0(A_216) | ~l1_struct_0(A_216) | v2_struct_0(A_216))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_12728])).
% 12.55/4.86  tff(c_12808, plain, (![A_327]: (k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'(A_327))=u1_struct_0(k1_tex_2('#skF_2', '#skF_1'(A_327))) | ~m1_pre_topc(A_327, '#skF_2') | ~v7_struct_0(A_327) | ~l1_struct_0(A_327) | v2_struct_0(A_327))), inference(negUnitSimplification, [status(thm)], [c_40, c_12776])).
% 12.55/4.86  tff(c_12872, plain, (![A_327]: (u1_struct_0(k1_tex_2('#skF_2', '#skF_1'(A_327)))=k1_tarski('#skF_1'(A_327)) | v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_pre_topc(A_327, '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v7_struct_0(A_327) | ~l1_struct_0(A_327) | v2_struct_0(A_327) | ~m1_pre_topc(A_327, '#skF_2') | ~v7_struct_0(A_327) | ~l1_struct_0(A_327) | v2_struct_0(A_327))), inference(superposition, [status(thm), theory('equality')], [c_12808, c_134])).
% 12.55/4.86  tff(c_12975, plain, (![A_327]: (u1_struct_0(k1_tex_2('#skF_2', '#skF_1'(A_327)))=k1_tarski('#skF_1'(A_327)) | v1_xboole_0(u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_pre_topc(A_327, '#skF_2') | ~v7_struct_0(A_327) | ~l1_struct_0(A_327) | v2_struct_0(A_327))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_12872])).
% 12.55/4.86  tff(c_13023, plain, (![A_328]: (u1_struct_0(k1_tex_2('#skF_2', '#skF_1'(A_328)))=k1_tarski('#skF_1'(A_328)) | ~m1_pre_topc(A_328, '#skF_2') | ~v7_struct_0(A_328) | ~l1_struct_0(A_328) | v2_struct_0(A_328))), inference(negUnitSimplification, [status(thm)], [c_40, c_844, c_12975])).
% 12.55/4.86  tff(c_164, plain, (![A_22]: (u1_struct_0(k1_tex_2('#skF_2', '#skF_1'(A_22)))!=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_1'(A_22)), '#skF_2') | ~m1_pre_topc(A_22, '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v7_struct_0(A_22) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(resolution, [status(thm)], [c_96, c_160])).
% 12.55/4.86  tff(c_171, plain, (![A_22]: (u1_struct_0(k1_tex_2('#skF_2', '#skF_1'(A_22)))!=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_1'(A_22)), '#skF_2') | ~m1_pre_topc(A_22, '#skF_2') | v2_struct_0('#skF_2') | ~v7_struct_0(A_22) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_164])).
% 12.55/4.86  tff(c_216, plain, (![A_85]: (u1_struct_0(k1_tex_2('#skF_2', '#skF_1'(A_85)))!=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_1'(A_85)), '#skF_2') | ~m1_pre_topc(A_85, '#skF_2') | ~v7_struct_0(A_85) | ~l1_struct_0(A_85) | v2_struct_0(A_85))), inference(negUnitSimplification, [status(thm)], [c_40, c_171])).
% 12.55/4.86  tff(c_220, plain, (![A_65]: (u1_struct_0(k1_tex_2('#skF_2', '#skF_1'(A_65)))!=u1_struct_0('#skF_3') | ~m1_pre_topc(A_65, '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v7_struct_0(A_65) | ~l1_struct_0(A_65) | v2_struct_0(A_65))), inference(resolution, [status(thm)], [c_131, c_216])).
% 12.55/4.86  tff(c_227, plain, (![A_65]: (u1_struct_0(k1_tex_2('#skF_2', '#skF_1'(A_65)))!=u1_struct_0('#skF_3') | ~m1_pre_topc(A_65, '#skF_2') | v2_struct_0('#skF_2') | ~v7_struct_0(A_65) | ~l1_struct_0(A_65) | v2_struct_0(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_220])).
% 12.55/4.86  tff(c_228, plain, (![A_65]: (u1_struct_0(k1_tex_2('#skF_2', '#skF_1'(A_65)))!=u1_struct_0('#skF_3') | ~m1_pre_topc(A_65, '#skF_2') | ~v7_struct_0(A_65) | ~l1_struct_0(A_65) | v2_struct_0(A_65))), inference(negUnitSimplification, [status(thm)], [c_40, c_227])).
% 12.55/4.86  tff(c_14121, plain, (![A_336]: (k1_tarski('#skF_1'(A_336))!=u1_struct_0('#skF_3') | ~m1_pre_topc(A_336, '#skF_2') | ~v7_struct_0(A_336) | ~l1_struct_0(A_336) | v2_struct_0(A_336) | ~m1_pre_topc(A_336, '#skF_2') | ~v7_struct_0(A_336) | ~l1_struct_0(A_336) | v2_struct_0(A_336))), inference(superposition, [status(thm), theory('equality')], [c_13023, c_228])).
% 12.55/4.86  tff(c_15176, plain, (![A_347]: (u1_struct_0(A_347)!=u1_struct_0('#skF_3') | ~m1_pre_topc(A_347, '#skF_2') | ~v7_struct_0(A_347) | ~l1_struct_0(A_347) | v2_struct_0(A_347) | ~m1_pre_topc(A_347, '#skF_2') | ~v7_struct_0(A_347) | ~l1_struct_0(A_347) | v2_struct_0(A_347) | ~v7_struct_0(A_347) | ~l1_struct_0(A_347) | v2_struct_0(A_347))), inference(superposition, [status(thm), theory('equality')], [c_215, c_14121])).
% 12.55/4.86  tff(c_15209, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_15176])).
% 12.55/4.86  tff(c_15248, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_15209])).
% 12.55/4.86  tff(c_15249, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_36, c_15248])).
% 12.55/4.86  tff(c_15252, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_15249])).
% 12.55/4.86  tff(c_15256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_15252])).
% 12.55/4.86  tff(c_15279, plain, (![A_350]: (k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'(A_350))!=u1_struct_0('#skF_2') | ~m1_pre_topc(A_350, '#skF_3') | ~v7_struct_0(A_350) | ~l1_struct_0(A_350) | v2_struct_0(A_350))), inference(splitRight, [status(thm)], [c_395])).
% 12.55/4.86  tff(c_15283, plain, (![A_65]: (k1_tarski('#skF_1'(A_65))!=u1_struct_0('#skF_2') | ~m1_pre_topc(A_65, '#skF_3') | ~v7_struct_0(A_65) | ~l1_struct_0(A_65) | v2_struct_0(A_65) | v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_pre_topc(A_65, '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v7_struct_0(A_65) | ~l1_struct_0(A_65) | v2_struct_0(A_65))), inference(superposition, [status(thm), theory('equality')], [c_134, c_15279])).
% 12.55/4.86  tff(c_15293, plain, (![A_65]: (k1_tarski('#skF_1'(A_65))!=u1_struct_0('#skF_2') | ~m1_pre_topc(A_65, '#skF_3') | v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_pre_topc(A_65, '#skF_2') | v2_struct_0('#skF_2') | ~v7_struct_0(A_65) | ~l1_struct_0(A_65) | v2_struct_0(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_15283])).
% 12.55/4.86  tff(c_15294, plain, (![A_65]: (k1_tarski('#skF_1'(A_65))!=u1_struct_0('#skF_2') | ~m1_pre_topc(A_65, '#skF_3') | v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_pre_topc(A_65, '#skF_2') | ~v7_struct_0(A_65) | ~l1_struct_0(A_65) | v2_struct_0(A_65))), inference(negUnitSimplification, [status(thm)], [c_40, c_15293])).
% 12.55/4.86  tff(c_15313, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_15294])).
% 12.55/4.86  tff(c_15314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15312, c_15313])).
% 12.55/4.86  tff(c_15401, plain, (![A_353]: (k1_tarski('#skF_1'(A_353))!=u1_struct_0('#skF_2') | ~m1_pre_topc(A_353, '#skF_3') | ~m1_pre_topc(A_353, '#skF_2') | ~v7_struct_0(A_353) | ~l1_struct_0(A_353) | v2_struct_0(A_353))), inference(splitRight, [status(thm)], [c_15294])).
% 12.55/4.86  tff(c_15507, plain, (![A_368]: (u1_struct_0(A_368)!=u1_struct_0('#skF_2') | ~m1_pre_topc(A_368, '#skF_3') | ~m1_pre_topc(A_368, '#skF_2') | ~v7_struct_0(A_368) | ~l1_struct_0(A_368) | v2_struct_0(A_368) | ~v7_struct_0(A_368) | ~l1_struct_0(A_368) | v2_struct_0(A_368))), inference(superposition, [status(thm), theory('equality')], [c_215, c_15401])).
% 12.55/4.86  tff(c_15525, plain, (u1_struct_0('#skF_2')!=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_15507])).
% 12.55/4.86  tff(c_15541, plain, (u1_struct_0('#skF_2')!=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_15525])).
% 12.55/4.86  tff(c_15542, plain, (u1_struct_0('#skF_2')!=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_36, c_15541])).
% 12.55/4.86  tff(c_15543, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_15542])).
% 12.55/4.86  tff(c_15546, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_15543])).
% 12.55/4.86  tff(c_15550, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_15546])).
% 12.55/4.86  tff(c_15552, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_15542])).
% 12.55/4.86  tff(c_132, plain, (![A_66, A_65]: (v1_pre_topc(k1_tex_2(A_66, '#skF_1'(A_65))) | ~m1_pre_topc(A_65, A_66) | ~l1_pre_topc(A_66) | v2_struct_0(A_66) | ~v7_struct_0(A_65) | ~l1_struct_0(A_65) | v2_struct_0(A_65))), inference(resolution, [status(thm)], [c_112, c_26])).
% 12.55/4.86  tff(c_16434, plain, (![A_401, A_402]: (k6_domain_1(u1_struct_0(A_401), '#skF_1'(A_402))=u1_struct_0(k1_tex_2(A_401, '#skF_1'(A_402))) | ~v1_pre_topc(k1_tex_2(A_401, '#skF_1'(A_402))) | v2_struct_0(k1_tex_2(A_401, '#skF_1'(A_402))) | ~m1_subset_1('#skF_1'(A_402), u1_struct_0(A_401)) | ~m1_pre_topc(A_402, A_401) | ~l1_pre_topc(A_401) | v2_struct_0(A_401) | ~v7_struct_0(A_402) | ~l1_struct_0(A_402) | v2_struct_0(A_402))), inference(resolution, [status(thm)], [c_131, c_318])).
% 12.55/4.86  tff(c_16978, plain, (![A_425, A_426]: (k6_domain_1(u1_struct_0(A_425), '#skF_1'(A_426))=u1_struct_0(k1_tex_2(A_425, '#skF_1'(A_426))) | ~v1_pre_topc(k1_tex_2(A_425, '#skF_1'(A_426))) | v2_struct_0(k1_tex_2(A_425, '#skF_1'(A_426))) | ~m1_pre_topc(A_426, A_425) | ~l1_pre_topc(A_425) | v2_struct_0(A_425) | ~v7_struct_0(A_426) | ~l1_struct_0(A_426) | v2_struct_0(A_426))), inference(resolution, [status(thm)], [c_96, c_16434])).
% 12.55/4.86  tff(c_17013, plain, (![A_430, A_431]: (k6_domain_1(u1_struct_0(A_430), '#skF_1'(A_431))=u1_struct_0(k1_tex_2(A_430, '#skF_1'(A_431))) | ~v1_pre_topc(k1_tex_2(A_430, '#skF_1'(A_431))) | ~m1_pre_topc(A_431, A_430) | ~l1_pre_topc(A_430) | v2_struct_0(A_430) | ~v7_struct_0(A_431) | ~l1_struct_0(A_431) | v2_struct_0(A_431))), inference(resolution, [status(thm)], [c_16978, c_133])).
% 12.55/4.86  tff(c_17033, plain, (![A_432, A_433]: (k6_domain_1(u1_struct_0(A_432), '#skF_1'(A_433))=u1_struct_0(k1_tex_2(A_432, '#skF_1'(A_433))) | ~m1_pre_topc(A_433, A_432) | ~l1_pre_topc(A_432) | v2_struct_0(A_432) | ~v7_struct_0(A_433) | ~l1_struct_0(A_433) | v2_struct_0(A_433))), inference(resolution, [status(thm)], [c_132, c_17013])).
% 12.55/4.86  tff(c_18398, plain, (![A_487, A_488]: (u1_struct_0(k1_tex_2(A_487, '#skF_1'(A_488)))=k1_tarski('#skF_1'(A_488)) | v1_xboole_0(u1_struct_0(A_487)) | ~m1_pre_topc(A_488, A_487) | ~l1_pre_topc(A_487) | v2_struct_0(A_487) | ~v7_struct_0(A_488) | ~l1_struct_0(A_488) | v2_struct_0(A_488) | ~m1_pre_topc(A_488, A_487) | ~l1_pre_topc(A_487) | v2_struct_0(A_487) | ~v7_struct_0(A_488) | ~l1_struct_0(A_488) | v2_struct_0(A_488))), inference(superposition, [status(thm), theory('equality')], [c_17033, c_134])).
% 12.55/4.86  tff(c_18524, plain, (![A_488]: (k1_tarski('#skF_1'(A_488))!=u1_struct_0('#skF_3') | ~m1_pre_topc(A_488, '#skF_2') | ~v7_struct_0(A_488) | ~l1_struct_0(A_488) | v2_struct_0(A_488) | v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_pre_topc(A_488, '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v7_struct_0(A_488) | ~l1_struct_0(A_488) | v2_struct_0(A_488) | ~m1_pre_topc(A_488, '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v7_struct_0(A_488) | ~l1_struct_0(A_488) | v2_struct_0(A_488))), inference(superposition, [status(thm), theory('equality')], [c_18398, c_228])).
% 12.55/4.86  tff(c_18620, plain, (![A_488]: (k1_tarski('#skF_1'(A_488))!=u1_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_pre_topc(A_488, '#skF_2') | v2_struct_0('#skF_2') | ~v7_struct_0(A_488) | ~l1_struct_0(A_488) | v2_struct_0(A_488))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_18524])).
% 12.55/4.86  tff(c_18641, plain, (![A_489]: (k1_tarski('#skF_1'(A_489))!=u1_struct_0('#skF_3') | ~m1_pre_topc(A_489, '#skF_2') | ~v7_struct_0(A_489) | ~l1_struct_0(A_489) | v2_struct_0(A_489))), inference(negUnitSimplification, [status(thm)], [c_40, c_15312, c_18620])).
% 12.55/4.86  tff(c_18645, plain, (![A_490]: (u1_struct_0(A_490)!=u1_struct_0('#skF_3') | ~m1_pre_topc(A_490, '#skF_2') | ~v7_struct_0(A_490) | ~l1_struct_0(A_490) | v2_struct_0(A_490) | ~v7_struct_0(A_490) | ~l1_struct_0(A_490) | v2_struct_0(A_490))), inference(superposition, [status(thm), theory('equality')], [c_215, c_18641])).
% 12.55/4.86  tff(c_18663, plain, (~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_18645])).
% 12.55/4.86  tff(c_18679, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15552, c_34, c_18663])).
% 12.55/4.86  tff(c_18681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_18679])).
% 12.55/4.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.55/4.86  
% 12.55/4.86  Inference rules
% 12.55/4.86  ----------------------
% 12.55/4.86  #Ref     : 9
% 12.55/4.86  #Sup     : 3829
% 12.55/4.86  #Fact    : 0
% 12.55/4.86  #Define  : 0
% 12.55/4.86  #Split   : 21
% 12.55/4.86  #Chain   : 0
% 12.55/4.86  #Close   : 0
% 12.55/4.86  
% 12.55/4.86  Ordering : KBO
% 12.55/4.86  
% 12.55/4.86  Simplification rules
% 12.55/4.86  ----------------------
% 12.55/4.86  #Subsume      : 1670
% 12.55/4.86  #Demod        : 5888
% 12.55/4.86  #Tautology    : 568
% 12.55/4.86  #SimpNegUnit  : 1676
% 12.55/4.86  #BackRed      : 15
% 12.55/4.86  
% 12.55/4.86  #Partial instantiations: 0
% 12.55/4.86  #Strategies tried      : 1
% 12.55/4.86  
% 12.55/4.86  Timing (in seconds)
% 12.55/4.86  ----------------------
% 12.55/4.86  Preprocessing        : 0.34
% 12.55/4.86  Parsing              : 0.18
% 12.55/4.86  CNF conversion       : 0.02
% 12.55/4.86  Main loop            : 3.73
% 12.55/4.86  Inferencing          : 0.86
% 12.55/4.86  Reduction            : 1.04
% 12.55/4.86  Demodulation         : 0.72
% 12.55/4.86  BG Simplification    : 0.10
% 12.55/4.86  Subsumption          : 1.57
% 12.55/4.86  Abstraction          : 0.21
% 12.55/4.86  MUC search           : 0.00
% 12.55/4.86  Cooper               : 0.00
% 12.55/4.86  Total                : 4.13
% 12.55/4.86  Index Insertion      : 0.00
% 12.55/4.86  Index Deletion       : 0.00
% 12.55/4.86  Index Matching       : 0.00
% 12.55/4.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
