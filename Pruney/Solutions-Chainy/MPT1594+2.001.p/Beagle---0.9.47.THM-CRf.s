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
% DateTime   : Thu Dec  3 10:25:20 EST 2020

% Result     : Theorem 17.90s
% Output     : CNFRefutation 17.90s
% Verified   : 
% Statistics : Number of formulae       :  225 (7416 expanded)
%              Number of leaves         :   52 (2729 expanded)
%              Depth                    :   36
%              Number of atoms          :  663 (22226 expanded)
%              Number of equality atoms :  101 (5060 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r3_lattices > r1_lattices > v1_partfun1 > r1_tarski > m1_subset_1 > v9_lattices > v8_relat_2 > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_relat_2 > v4_lattices > v3_lattices > v2_struct_0 > v1_relat_2 > v1_orders_2 > v10_lattices > l3_lattices > l1_orders_2 > k4_lattice3 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_1 > k3_lattice3 > k2_lattice3 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(k4_lattice3,type,(
    k4_lattice3: ( $i * $i ) > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_lattices,type,(
    v3_lattices: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_lattice3,type,(
    k2_lattice3: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_176,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
       => ! [C] :
            ( m1_subset_1(C,u1_struct_0(k3_yellow_1(A)))
           => ( r3_orders_2(k3_yellow_1(A),B,C)
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow_1)).

tff(f_134,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k1_lattice3(A))
      & v3_lattices(k1_lattice3(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_lattice3)).

tff(f_138,axiom,(
    ! [A] :
      ( v3_lattices(k1_lattice3(A))
      & v10_lattices(k1_lattice3(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_lattice3)).

tff(f_112,axiom,(
    ! [A] :
      ( v3_lattices(k1_lattice3(A))
      & l3_lattices(k1_lattice3(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattice3)).

tff(f_166,axiom,(
    ! [A] : k3_yellow_1(A) = k3_lattice3(k1_lattice3(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ( v1_partfun1(k2_lattice3(A),u1_struct_0(A))
        & v1_relat_2(k2_lattice3(A))
        & v4_relat_2(k2_lattice3(A))
        & v8_relat_2(k2_lattice3(A))
        & m1_subset_1(k2_lattice3(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_lattice3)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => k3_lattice3(A) = g1_orders_2(u1_struct_0(A),k2_lattice3(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_lattice3)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ( v1_orders_2(g1_orders_2(A,B))
        & l1_orders_2(g1_orders_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k4_lattice3(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattice3)).

tff(f_164,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r3_lattices(A,B,C)
              <=> r3_orders_2(k3_lattice3(A),k4_lattice3(A,B),k4_lattice3(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_lattice3)).

tff(f_147,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,u1_struct_0(k1_lattice3(A)))
     => ! [C] :
          ( m1_subset_1(C,u1_struct_0(k1_lattice3(A)))
         => ( r1_lattices(k1_lattice3(A),B,C)
          <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_lattice3)).

tff(f_68,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v4_lattices(A)
          & v5_lattices(A)
          & v6_lattices(A)
          & v7_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_lattices(A,B,C)
      <=> r1_lattices(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

tff(c_76,plain,
    ( r3_orders_2(k3_yellow_1('#skF_1'),'#skF_2','#skF_3')
    | r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_94,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_70,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ r3_orders_2(k3_yellow_1('#skF_1'),'#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_100,plain,(
    ~ r3_orders_2(k3_yellow_1('#skF_1'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_70])).

tff(c_48,plain,(
    ! [A_20] : ~ v2_struct_0(k1_lattice3(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_54,plain,(
    ! [A_21] : v10_lattices(k1_lattice3(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_36,plain,(
    ! [A_18] : l3_lattices(k1_lattice3(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_64,plain,(
    ! [A_33] : k3_lattice3(k1_lattice3(A_33)) = k3_yellow_1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_38,plain,(
    ! [A_19] :
      ( m1_subset_1(k2_lattice3(A_19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19),u1_struct_0(A_19))))
      | ~ l3_lattices(A_19)
      | ~ v10_lattices(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_30,plain,(
    ! [A_14] :
      ( g1_orders_2(u1_struct_0(A_14),k2_lattice3(A_14)) = k3_lattice3(A_14)
      | ~ l3_lattices(A_14)
      | ~ v10_lattices(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_151,plain,(
    ! [C_62,A_63,D_64,B_65] :
      ( C_62 = A_63
      | g1_orders_2(C_62,D_64) != g1_orders_2(A_63,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k2_zfmisc_1(A_63,A_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_228,plain,(
    ! [A_89,A_90,B_91] :
      ( u1_struct_0(A_89) = A_90
      | k3_lattice3(A_89) != g1_orders_2(A_90,B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k2_zfmisc_1(A_90,A_90)))
      | ~ l3_lattices(A_89)
      | ~ v10_lattices(A_89)
      | v2_struct_0(A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_151])).

tff(c_234,plain,(
    ! [A_33,A_90,B_91] :
      ( u1_struct_0(k1_lattice3(A_33)) = A_90
      | k3_yellow_1(A_33) != g1_orders_2(A_90,B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k2_zfmisc_1(A_90,A_90)))
      | ~ l3_lattices(k1_lattice3(A_33))
      | ~ v10_lattices(k1_lattice3(A_33))
      | v2_struct_0(k1_lattice3(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_228])).

tff(c_236,plain,(
    ! [A_33,A_90,B_91] :
      ( u1_struct_0(k1_lattice3(A_33)) = A_90
      | k3_yellow_1(A_33) != g1_orders_2(A_90,B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k2_zfmisc_1(A_90,A_90)))
      | v2_struct_0(k1_lattice3(A_33)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36,c_234])).

tff(c_238,plain,(
    ! [A_92,A_93,B_94] :
      ( u1_struct_0(k1_lattice3(A_92)) = A_93
      | k3_yellow_1(A_92) != g1_orders_2(A_93,B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(k2_zfmisc_1(A_93,A_93))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_236])).

tff(c_723,plain,(
    ! [A_192,A_193] :
      ( u1_struct_0(k1_lattice3(A_192)) = u1_struct_0(A_193)
      | k3_yellow_1(A_192) != k3_lattice3(A_193)
      | ~ m1_subset_1(k2_lattice3(A_193),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_193),u1_struct_0(A_193))))
      | ~ l3_lattices(A_193)
      | ~ v10_lattices(A_193)
      | v2_struct_0(A_193) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_238])).

tff(c_1055,plain,(
    ! [A_204,A_205] :
      ( u1_struct_0(k1_lattice3(A_204)) = u1_struct_0(A_205)
      | k3_yellow_1(A_204) != k3_lattice3(A_205)
      | ~ l3_lattices(A_205)
      | ~ v10_lattices(A_205)
      | v2_struct_0(A_205) ) ),
    inference(resolution,[status(thm)],[c_38,c_723])).

tff(c_1187,plain,(
    ! [A_205,A_204] :
      ( g1_orders_2(u1_struct_0(A_205),k2_lattice3(k1_lattice3(A_204))) = k3_lattice3(k1_lattice3(A_204))
      | ~ l3_lattices(k1_lattice3(A_204))
      | ~ v10_lattices(k1_lattice3(A_204))
      | v2_struct_0(k1_lattice3(A_204))
      | k3_yellow_1(A_204) != k3_lattice3(A_205)
      | ~ l3_lattices(A_205)
      | ~ v10_lattices(A_205)
      | v2_struct_0(A_205) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1055,c_30])).

tff(c_1291,plain,(
    ! [A_205,A_204] :
      ( g1_orders_2(u1_struct_0(A_205),k2_lattice3(k1_lattice3(A_204))) = k3_yellow_1(A_204)
      | v2_struct_0(k1_lattice3(A_204))
      | k3_yellow_1(A_204) != k3_lattice3(A_205)
      | ~ l3_lattices(A_205)
      | ~ v10_lattices(A_205)
      | v2_struct_0(A_205) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36,c_64,c_1187])).

tff(c_1292,plain,(
    ! [A_205,A_204] :
      ( g1_orders_2(u1_struct_0(A_205),k2_lattice3(k1_lattice3(A_204))) = k3_yellow_1(A_204)
      | k3_yellow_1(A_204) != k3_lattice3(A_205)
      | ~ l3_lattices(A_205)
      | ~ v10_lattices(A_205)
      | v2_struct_0(A_205) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1291])).

tff(c_161,plain,(
    ! [A_66] :
      ( m1_subset_1(k2_lattice3(A_66),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_66),u1_struct_0(A_66))))
      | ~ l3_lattices(A_66)
      | ~ v10_lattices(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( l1_orders_2(g1_orders_2(A_2,B_3))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k2_zfmisc_1(A_2,A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_170,plain,(
    ! [A_67] :
      ( l1_orders_2(g1_orders_2(u1_struct_0(A_67),k2_lattice3(A_67)))
      | ~ l3_lattices(A_67)
      | ~ v10_lattices(A_67)
      | v2_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_161,c_4])).

tff(c_178,plain,(
    ! [A_69] :
      ( l1_orders_2(k3_lattice3(A_69))
      | ~ l3_lattices(A_69)
      | ~ v10_lattices(A_69)
      | v2_struct_0(A_69)
      | ~ l3_lattices(A_69)
      | ~ v10_lattices(A_69)
      | v2_struct_0(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_170])).

tff(c_181,plain,(
    ! [A_33] :
      ( l1_orders_2(k3_yellow_1(A_33))
      | ~ l3_lattices(k1_lattice3(A_33))
      | ~ v10_lattices(k1_lattice3(A_33))
      | v2_struct_0(k1_lattice3(A_33))
      | ~ l3_lattices(k1_lattice3(A_33))
      | ~ v10_lattices(k1_lattice3(A_33))
      | v2_struct_0(k1_lattice3(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_178])).

tff(c_183,plain,(
    ! [A_33] :
      ( l1_orders_2(k3_yellow_1(A_33))
      | v2_struct_0(k1_lattice3(A_33)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36,c_54,c_36,c_181])).

tff(c_184,plain,(
    ! [A_33] : l1_orders_2(k3_yellow_1(A_33)) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_183])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( v1_orders_2(g1_orders_2(A_2,B_3))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k2_zfmisc_1(A_2,A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_169,plain,(
    ! [A_66] :
      ( v1_orders_2(g1_orders_2(u1_struct_0(A_66),k2_lattice3(A_66)))
      | ~ l3_lattices(A_66)
      | ~ v10_lattices(A_66)
      | v2_struct_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_161,c_6])).

tff(c_1157,plain,(
    ! [A_205,A_204] :
      ( v1_orders_2(g1_orders_2(u1_struct_0(A_205),k2_lattice3(k1_lattice3(A_204))))
      | ~ l3_lattices(k1_lattice3(A_204))
      | ~ v10_lattices(k1_lattice3(A_204))
      | v2_struct_0(k1_lattice3(A_204))
      | k3_yellow_1(A_204) != k3_lattice3(A_205)
      | ~ l3_lattices(A_205)
      | ~ v10_lattices(A_205)
      | v2_struct_0(A_205) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1055,c_169])).

tff(c_1276,plain,(
    ! [A_205,A_204] :
      ( v1_orders_2(g1_orders_2(u1_struct_0(A_205),k2_lattice3(k1_lattice3(A_204))))
      | v2_struct_0(k1_lattice3(A_204))
      | k3_yellow_1(A_204) != k3_lattice3(A_205)
      | ~ l3_lattices(A_205)
      | ~ v10_lattices(A_205)
      | v2_struct_0(A_205) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36,c_1157])).

tff(c_1277,plain,(
    ! [A_205,A_204] :
      ( v1_orders_2(g1_orders_2(u1_struct_0(A_205),k2_lattice3(k1_lattice3(A_204))))
      | k3_yellow_1(A_204) != k3_lattice3(A_205)
      | ~ l3_lattices(A_205)
      | ~ v10_lattices(A_205)
      | v2_struct_0(A_205) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1276])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) = A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_157,plain,(
    ! [A_1,A_63,B_65] :
      ( u1_struct_0(A_1) = A_63
      | g1_orders_2(A_63,B_65) != A_1
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k2_zfmisc_1(A_63,A_63)))
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_151])).

tff(c_218,plain,(
    ! [A_85,B_86] :
      ( u1_struct_0(g1_orders_2(A_85,B_86)) = A_85
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k2_zfmisc_1(A_85,A_85)))
      | ~ v1_orders_2(g1_orders_2(A_85,B_86))
      | ~ l1_orders_2(g1_orders_2(A_85,B_86)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_157])).

tff(c_5726,plain,(
    ! [A_378] :
      ( u1_struct_0(g1_orders_2(u1_struct_0(A_378),k2_lattice3(A_378))) = u1_struct_0(A_378)
      | ~ v1_orders_2(g1_orders_2(u1_struct_0(A_378),k2_lattice3(A_378)))
      | ~ l1_orders_2(g1_orders_2(u1_struct_0(A_378),k2_lattice3(A_378)))
      | ~ l3_lattices(A_378)
      | ~ v10_lattices(A_378)
      | v2_struct_0(A_378) ) ),
    inference(resolution,[status(thm)],[c_38,c_218])).

tff(c_5743,plain,(
    ! [A_204] :
      ( u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_204)),k2_lattice3(k1_lattice3(A_204)))) = u1_struct_0(k1_lattice3(A_204))
      | ~ l1_orders_2(g1_orders_2(u1_struct_0(k1_lattice3(A_204)),k2_lattice3(k1_lattice3(A_204))))
      | k3_lattice3(k1_lattice3(A_204)) != k3_yellow_1(A_204)
      | ~ l3_lattices(k1_lattice3(A_204))
      | ~ v10_lattices(k1_lattice3(A_204))
      | v2_struct_0(k1_lattice3(A_204)) ) ),
    inference(resolution,[status(thm)],[c_1277,c_5726])).

tff(c_5806,plain,(
    ! [A_204] :
      ( u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_204)),k2_lattice3(k1_lattice3(A_204)))) = u1_struct_0(k1_lattice3(A_204))
      | ~ l1_orders_2(g1_orders_2(u1_struct_0(k1_lattice3(A_204)),k2_lattice3(k1_lattice3(A_204))))
      | v2_struct_0(k1_lattice3(A_204)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36,c_64,c_5743])).

tff(c_7917,plain,(
    ! [A_469] :
      ( u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_469)),k2_lattice3(k1_lattice3(A_469)))) = u1_struct_0(k1_lattice3(A_469))
      | ~ l1_orders_2(g1_orders_2(u1_struct_0(k1_lattice3(A_469)),k2_lattice3(k1_lattice3(A_469)))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_5806])).

tff(c_7924,plain,(
    ! [A_204] :
      ( u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_204)),k2_lattice3(k1_lattice3(A_204)))) = u1_struct_0(k1_lattice3(A_204))
      | ~ l1_orders_2(k3_yellow_1(A_204))
      | k3_lattice3(k1_lattice3(A_204)) != k3_yellow_1(A_204)
      | ~ l3_lattices(k1_lattice3(A_204))
      | ~ v10_lattices(k1_lattice3(A_204))
      | v2_struct_0(k1_lattice3(A_204)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1292,c_7917])).

tff(c_7978,plain,(
    ! [A_204] :
      ( u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_204)),k2_lattice3(k1_lattice3(A_204)))) = u1_struct_0(k1_lattice3(A_204))
      | v2_struct_0(k1_lattice3(A_204)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36,c_64,c_184,c_7924])).

tff(c_8011,plain,(
    ! [A_470] : u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_470)),k2_lattice3(k1_lattice3(A_470)))) = u1_struct_0(k1_lattice3(A_470)) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_7978])).

tff(c_8143,plain,(
    ! [A_204] :
      ( u1_struct_0(k3_yellow_1(A_204)) = u1_struct_0(k1_lattice3(A_204))
      | k3_lattice3(k1_lattice3(A_204)) != k3_yellow_1(A_204)
      | ~ l3_lattices(k1_lattice3(A_204))
      | ~ v10_lattices(k1_lattice3(A_204))
      | v2_struct_0(k1_lattice3(A_204)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1292,c_8011])).

tff(c_8222,plain,(
    ! [A_204] :
      ( u1_struct_0(k3_yellow_1(A_204)) = u1_struct_0(k1_lattice3(A_204))
      | v2_struct_0(k1_lattice3(A_204)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36,c_64,c_8143])).

tff(c_8223,plain,(
    ! [A_204] : u1_struct_0(k3_yellow_1(A_204)) = u1_struct_0(k1_lattice3(A_204)) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_8222])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k3_yellow_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_8273,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k1_lattice3('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8223,c_66])).

tff(c_32,plain,(
    ! [A_15,B_17] :
      ( k4_lattice3(A_15,B_17) = B_17
      | ~ m1_subset_1(B_17,u1_struct_0(A_15))
      | ~ l3_lattices(A_15)
      | ~ v10_lattices(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_8456,plain,
    ( k4_lattice3(k1_lattice3('#skF_1'),'#skF_3') = '#skF_3'
    | ~ l3_lattices(k1_lattice3('#skF_1'))
    | ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8273,c_32])).

tff(c_8500,plain,
    ( k4_lattice3(k1_lattice3('#skF_1'),'#skF_3') = '#skF_3'
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36,c_8456])).

tff(c_8501,plain,(
    k4_lattice3(k1_lattice3('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_8500])).

tff(c_68,plain,(
    m1_subset_1('#skF_2',u1_struct_0(k3_yellow_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_8274,plain,(
    m1_subset_1('#skF_2',u1_struct_0(k1_lattice3('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8223,c_68])).

tff(c_8656,plain,
    ( k4_lattice3(k1_lattice3('#skF_1'),'#skF_2') = '#skF_2'
    | ~ l3_lattices(k1_lattice3('#skF_1'))
    | ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8274,c_32])).

tff(c_8704,plain,
    ( k4_lattice3(k1_lattice3('#skF_1'),'#skF_2') = '#skF_2'
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36,c_8656])).

tff(c_8705,plain,(
    k4_lattice3(k1_lattice3('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_8704])).

tff(c_481,plain,(
    ! [A_141,B_142,C_143] :
      ( r3_orders_2(k3_lattice3(A_141),k4_lattice3(A_141,B_142),k4_lattice3(A_141,C_143))
      | ~ r3_lattices(A_141,B_142,C_143)
      | ~ m1_subset_1(C_143,u1_struct_0(A_141))
      | ~ m1_subset_1(B_142,u1_struct_0(A_141))
      | ~ l3_lattices(A_141)
      | ~ v10_lattices(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_487,plain,(
    ! [A_33,B_142,C_143] :
      ( r3_orders_2(k3_yellow_1(A_33),k4_lattice3(k1_lattice3(A_33),B_142),k4_lattice3(k1_lattice3(A_33),C_143))
      | ~ r3_lattices(k1_lattice3(A_33),B_142,C_143)
      | ~ m1_subset_1(C_143,u1_struct_0(k1_lattice3(A_33)))
      | ~ m1_subset_1(B_142,u1_struct_0(k1_lattice3(A_33)))
      | ~ l3_lattices(k1_lattice3(A_33))
      | ~ v10_lattices(k1_lattice3(A_33))
      | v2_struct_0(k1_lattice3(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_481])).

tff(c_490,plain,(
    ! [A_33,B_142,C_143] :
      ( r3_orders_2(k3_yellow_1(A_33),k4_lattice3(k1_lattice3(A_33),B_142),k4_lattice3(k1_lattice3(A_33),C_143))
      | ~ r3_lattices(k1_lattice3(A_33),B_142,C_143)
      | ~ m1_subset_1(C_143,u1_struct_0(k1_lattice3(A_33)))
      | ~ m1_subset_1(B_142,u1_struct_0(k1_lattice3(A_33)))
      | v2_struct_0(k1_lattice3(A_33)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36,c_487])).

tff(c_491,plain,(
    ! [A_33,B_142,C_143] :
      ( r3_orders_2(k3_yellow_1(A_33),k4_lattice3(k1_lattice3(A_33),B_142),k4_lattice3(k1_lattice3(A_33),C_143))
      | ~ r3_lattices(k1_lattice3(A_33),B_142,C_143)
      | ~ m1_subset_1(C_143,u1_struct_0(k1_lattice3(A_33)))
      | ~ m1_subset_1(B_142,u1_struct_0(k1_lattice3(A_33))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_490])).

tff(c_8785,plain,(
    ! [C_143] :
      ( r3_orders_2(k3_yellow_1('#skF_1'),'#skF_2',k4_lattice3(k1_lattice3('#skF_1'),C_143))
      | ~ r3_lattices(k1_lattice3('#skF_1'),'#skF_2',C_143)
      | ~ m1_subset_1(C_143,u1_struct_0(k1_lattice3('#skF_1')))
      | ~ m1_subset_1('#skF_2',u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8705,c_491])).

tff(c_10022,plain,(
    ! [C_494] :
      ( r3_orders_2(k3_yellow_1('#skF_1'),'#skF_2',k4_lattice3(k1_lattice3('#skF_1'),C_494))
      | ~ r3_lattices(k1_lattice3('#skF_1'),'#skF_2',C_494)
      | ~ m1_subset_1(C_494,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8274,c_8785])).

tff(c_10028,plain,
    ( r3_orders_2(k3_yellow_1('#skF_1'),'#skF_2','#skF_3')
    | ~ r3_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0(k1_lattice3('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8501,c_10022])).

tff(c_10040,plain,
    ( r3_orders_2(k3_yellow_1('#skF_1'),'#skF_2','#skF_3')
    | ~ r3_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8273,c_10028])).

tff(c_10041,plain,(
    ~ r3_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_10040])).

tff(c_56,plain,(
    ! [A_22,B_23,C_25] :
      ( r1_lattices(k1_lattice3(A_22),B_23,C_25)
      | ~ r1_tarski(B_23,C_25)
      | ~ m1_subset_1(C_25,u1_struct_0(k1_lattice3(A_22)))
      | ~ m1_subset_1(B_23,u1_struct_0(k1_lattice3(A_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_8831,plain,(
    ! [B_473] :
      ( r1_lattices(k1_lattice3('#skF_1'),B_473,'#skF_3')
      | ~ r1_tarski(B_473,'#skF_3')
      | ~ m1_subset_1(B_473,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_8273,c_56])).

tff(c_8834,plain,
    ( r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_8274,c_8831])).

tff(c_8874,plain,(
    r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_8834])).

tff(c_14,plain,(
    ! [A_10] :
      ( v8_lattices(A_10)
      | ~ v10_lattices(A_10)
      | v2_struct_0(A_10)
      | ~ l3_lattices(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    ! [A_10] :
      ( v6_lattices(A_10)
      | ~ v10_lattices(A_10)
      | v2_struct_0(A_10)
      | ~ l3_lattices(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [A_11,B_12,C_13] :
      ( r3_lattices(A_11,B_12,C_13)
      | ~ r1_lattices(A_11,B_12,C_13)
      | ~ m1_subset_1(C_13,u1_struct_0(A_11))
      | ~ m1_subset_1(B_12,u1_struct_0(A_11))
      | ~ l3_lattices(A_11)
      | ~ v9_lattices(A_11)
      | ~ v8_lattices(A_11)
      | ~ v6_lattices(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8451,plain,(
    ! [B_12] :
      ( r3_lattices(k1_lattice3('#skF_1'),B_12,'#skF_3')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_12,'#skF_3')
      | ~ m1_subset_1(B_12,u1_struct_0(k1_lattice3('#skF_1')))
      | ~ l3_lattices(k1_lattice3('#skF_1'))
      | ~ v9_lattices(k1_lattice3('#skF_1'))
      | ~ v8_lattices(k1_lattice3('#skF_1'))
      | ~ v6_lattices(k1_lattice3('#skF_1'))
      | v2_struct_0(k1_lattice3('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_8273,c_26])).

tff(c_8495,plain,(
    ! [B_12] :
      ( r3_lattices(k1_lattice3('#skF_1'),B_12,'#skF_3')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_12,'#skF_3')
      | ~ m1_subset_1(B_12,u1_struct_0(k1_lattice3('#skF_1')))
      | ~ v9_lattices(k1_lattice3('#skF_1'))
      | ~ v8_lattices(k1_lattice3('#skF_1'))
      | ~ v6_lattices(k1_lattice3('#skF_1'))
      | v2_struct_0(k1_lattice3('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8451])).

tff(c_8496,plain,(
    ! [B_12] :
      ( r3_lattices(k1_lattice3('#skF_1'),B_12,'#skF_3')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_12,'#skF_3')
      | ~ m1_subset_1(B_12,u1_struct_0(k1_lattice3('#skF_1')))
      | ~ v9_lattices(k1_lattice3('#skF_1'))
      | ~ v8_lattices(k1_lattice3('#skF_1'))
      | ~ v6_lattices(k1_lattice3('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_8495])).

tff(c_21913,plain,(
    ~ v6_lattices(k1_lattice3('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_8496])).

tff(c_21916,plain,
    ( ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1'))
    | ~ l3_lattices(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_21913])).

tff(c_21919,plain,(
    v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_21916])).

tff(c_21921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_21919])).

tff(c_21923,plain,(
    v6_lattices(k1_lattice3('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_8496])).

tff(c_8651,plain,(
    ! [B_12] :
      ( r3_lattices(k1_lattice3('#skF_1'),B_12,'#skF_2')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_12,'#skF_2')
      | ~ m1_subset_1(B_12,u1_struct_0(k1_lattice3('#skF_1')))
      | ~ l3_lattices(k1_lattice3('#skF_1'))
      | ~ v9_lattices(k1_lattice3('#skF_1'))
      | ~ v8_lattices(k1_lattice3('#skF_1'))
      | ~ v6_lattices(k1_lattice3('#skF_1'))
      | v2_struct_0(k1_lattice3('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_8274,c_26])).

tff(c_8699,plain,(
    ! [B_12] :
      ( r3_lattices(k1_lattice3('#skF_1'),B_12,'#skF_2')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_12,'#skF_2')
      | ~ m1_subset_1(B_12,u1_struct_0(k1_lattice3('#skF_1')))
      | ~ v9_lattices(k1_lattice3('#skF_1'))
      | ~ v8_lattices(k1_lattice3('#skF_1'))
      | ~ v6_lattices(k1_lattice3('#skF_1'))
      | v2_struct_0(k1_lattice3('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8651])).

tff(c_8700,plain,(
    ! [B_12] :
      ( r3_lattices(k1_lattice3('#skF_1'),B_12,'#skF_2')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_12,'#skF_2')
      | ~ m1_subset_1(B_12,u1_struct_0(k1_lattice3('#skF_1')))
      | ~ v9_lattices(k1_lattice3('#skF_1'))
      | ~ v8_lattices(k1_lattice3('#skF_1'))
      | ~ v6_lattices(k1_lattice3('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_8699])).

tff(c_22161,plain,(
    ! [B_12] :
      ( r3_lattices(k1_lattice3('#skF_1'),B_12,'#skF_2')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_12,'#skF_2')
      | ~ m1_subset_1(B_12,u1_struct_0(k1_lattice3('#skF_1')))
      | ~ v9_lattices(k1_lattice3('#skF_1'))
      | ~ v8_lattices(k1_lattice3('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21923,c_8700])).

tff(c_22162,plain,(
    ~ v8_lattices(k1_lattice3('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_22161])).

tff(c_22165,plain,
    ( ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1'))
    | ~ l3_lattices(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_14,c_22162])).

tff(c_22168,plain,(
    v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_22165])).

tff(c_22170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_22168])).

tff(c_22172,plain,(
    v8_lattices(k1_lattice3('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_22161])).

tff(c_12,plain,(
    ! [A_10] :
      ( v9_lattices(A_10)
      | ~ v10_lattices(A_10)
      | v2_struct_0(A_10)
      | ~ l3_lattices(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_21922,plain,(
    ! [B_12] :
      ( ~ v8_lattices(k1_lattice3('#skF_1'))
      | ~ v9_lattices(k1_lattice3('#skF_1'))
      | r3_lattices(k1_lattice3('#skF_1'),B_12,'#skF_3')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_12,'#skF_3')
      | ~ m1_subset_1(B_12,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_8496])).

tff(c_22149,plain,(
    ~ v9_lattices(k1_lattice3('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_21922])).

tff(c_22152,plain,
    ( ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1'))
    | ~ l3_lattices(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_22149])).

tff(c_22155,plain,(
    v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_22152])).

tff(c_22157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_22155])).

tff(c_22158,plain,(
    ! [B_12] :
      ( ~ v8_lattices(k1_lattice3('#skF_1'))
      | r3_lattices(k1_lattice3('#skF_1'),B_12,'#skF_3')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_12,'#skF_3')
      | ~ m1_subset_1(B_12,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_21922])).

tff(c_22175,plain,(
    ! [B_766] :
      ( r3_lattices(k1_lattice3('#skF_1'),B_766,'#skF_3')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_766,'#skF_3')
      | ~ m1_subset_1(B_766,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22172,c_22158])).

tff(c_22190,plain,
    ( r3_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3')
    | ~ r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_8274,c_22175])).

tff(c_22236,plain,(
    r3_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8874,c_22190])).

tff(c_22238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10041,c_22236])).

tff(c_22240,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_22284,plain,(
    ! [C_783,A_784,D_785,B_786] :
      ( C_783 = A_784
      | g1_orders_2(C_783,D_785) != g1_orders_2(A_784,B_786)
      | ~ m1_subset_1(B_786,k1_zfmisc_1(k2_zfmisc_1(A_784,A_784))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22418,plain,(
    ! [A_829,A_830,B_831] :
      ( u1_struct_0(A_829) = A_830
      | k3_lattice3(A_829) != g1_orders_2(A_830,B_831)
      | ~ m1_subset_1(B_831,k1_zfmisc_1(k2_zfmisc_1(A_830,A_830)))
      | ~ l3_lattices(A_829)
      | ~ v10_lattices(A_829)
      | v2_struct_0(A_829) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_22284])).

tff(c_22424,plain,(
    ! [A_33,A_830,B_831] :
      ( u1_struct_0(k1_lattice3(A_33)) = A_830
      | k3_yellow_1(A_33) != g1_orders_2(A_830,B_831)
      | ~ m1_subset_1(B_831,k1_zfmisc_1(k2_zfmisc_1(A_830,A_830)))
      | ~ l3_lattices(k1_lattice3(A_33))
      | ~ v10_lattices(k1_lattice3(A_33))
      | v2_struct_0(k1_lattice3(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_22418])).

tff(c_22426,plain,(
    ! [A_33,A_830,B_831] :
      ( u1_struct_0(k1_lattice3(A_33)) = A_830
      | k3_yellow_1(A_33) != g1_orders_2(A_830,B_831)
      | ~ m1_subset_1(B_831,k1_zfmisc_1(k2_zfmisc_1(A_830,A_830)))
      | v2_struct_0(k1_lattice3(A_33)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36,c_22424])).

tff(c_22429,plain,(
    ! [A_835,A_836,B_837] :
      ( u1_struct_0(k1_lattice3(A_835)) = A_836
      | k3_yellow_1(A_835) != g1_orders_2(A_836,B_837)
      | ~ m1_subset_1(B_837,k1_zfmisc_1(k2_zfmisc_1(A_836,A_836))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_22426])).

tff(c_22480,plain,(
    ! [A_857,A_858] :
      ( u1_struct_0(k1_lattice3(A_857)) = u1_struct_0(A_858)
      | k3_yellow_1(A_857) != k3_lattice3(A_858)
      | ~ m1_subset_1(k2_lattice3(A_858),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_858),u1_struct_0(A_858))))
      | ~ l3_lattices(A_858)
      | ~ v10_lattices(A_858)
      | v2_struct_0(A_858) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_22429])).

tff(c_22484,plain,(
    ! [A_859,A_860] :
      ( u1_struct_0(k1_lattice3(A_859)) = u1_struct_0(A_860)
      | k3_yellow_1(A_859) != k3_lattice3(A_860)
      | ~ l3_lattices(A_860)
      | ~ v10_lattices(A_860)
      | v2_struct_0(A_860) ) ),
    inference(resolution,[status(thm)],[c_38,c_22480])).

tff(c_22557,plain,(
    ! [A_860,A_859] :
      ( g1_orders_2(u1_struct_0(A_860),k2_lattice3(k1_lattice3(A_859))) = k3_lattice3(k1_lattice3(A_859))
      | ~ l3_lattices(k1_lattice3(A_859))
      | ~ v10_lattices(k1_lattice3(A_859))
      | v2_struct_0(k1_lattice3(A_859))
      | k3_yellow_1(A_859) != k3_lattice3(A_860)
      | ~ l3_lattices(A_860)
      | ~ v10_lattices(A_860)
      | v2_struct_0(A_860) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22484,c_30])).

tff(c_22619,plain,(
    ! [A_860,A_859] :
      ( g1_orders_2(u1_struct_0(A_860),k2_lattice3(k1_lattice3(A_859))) = k3_yellow_1(A_859)
      | v2_struct_0(k1_lattice3(A_859))
      | k3_yellow_1(A_859) != k3_lattice3(A_860)
      | ~ l3_lattices(A_860)
      | ~ v10_lattices(A_860)
      | v2_struct_0(A_860) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36,c_64,c_22557])).

tff(c_22620,plain,(
    ! [A_860,A_859] :
      ( g1_orders_2(u1_struct_0(A_860),k2_lattice3(k1_lattice3(A_859))) = k3_yellow_1(A_859)
      | k3_yellow_1(A_859) != k3_lattice3(A_860)
      | ~ l3_lattices(A_860)
      | ~ v10_lattices(A_860)
      | v2_struct_0(A_860) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_22619])).

tff(c_22307,plain,(
    ! [A_791] :
      ( m1_subset_1(k2_lattice3(A_791),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_791),u1_struct_0(A_791))))
      | ~ l3_lattices(A_791)
      | ~ v10_lattices(A_791)
      | v2_struct_0(A_791) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_22316,plain,(
    ! [A_792] :
      ( l1_orders_2(g1_orders_2(u1_struct_0(A_792),k2_lattice3(A_792)))
      | ~ l3_lattices(A_792)
      | ~ v10_lattices(A_792)
      | v2_struct_0(A_792) ) ),
    inference(resolution,[status(thm)],[c_22307,c_4])).

tff(c_22325,plain,(
    ! [A_797] :
      ( l1_orders_2(k3_lattice3(A_797))
      | ~ l3_lattices(A_797)
      | ~ v10_lattices(A_797)
      | v2_struct_0(A_797)
      | ~ l3_lattices(A_797)
      | ~ v10_lattices(A_797)
      | v2_struct_0(A_797) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_22316])).

tff(c_22328,plain,(
    ! [A_33] :
      ( l1_orders_2(k3_yellow_1(A_33))
      | ~ l3_lattices(k1_lattice3(A_33))
      | ~ v10_lattices(k1_lattice3(A_33))
      | v2_struct_0(k1_lattice3(A_33))
      | ~ l3_lattices(k1_lattice3(A_33))
      | ~ v10_lattices(k1_lattice3(A_33))
      | v2_struct_0(k1_lattice3(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_22325])).

tff(c_22330,plain,(
    ! [A_33] :
      ( l1_orders_2(k3_yellow_1(A_33))
      | v2_struct_0(k1_lattice3(A_33)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36,c_54,c_36,c_22328])).

tff(c_22331,plain,(
    ! [A_33] : l1_orders_2(k3_yellow_1(A_33)) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_22330])).

tff(c_22315,plain,(
    ! [A_791] :
      ( v1_orders_2(g1_orders_2(u1_struct_0(A_791),k2_lattice3(A_791)))
      | ~ l3_lattices(A_791)
      | ~ v10_lattices(A_791)
      | v2_struct_0(A_791) ) ),
    inference(resolution,[status(thm)],[c_22307,c_6])).

tff(c_22527,plain,(
    ! [A_860,A_859] :
      ( v1_orders_2(g1_orders_2(u1_struct_0(A_860),k2_lattice3(k1_lattice3(A_859))))
      | ~ l3_lattices(k1_lattice3(A_859))
      | ~ v10_lattices(k1_lattice3(A_859))
      | v2_struct_0(k1_lattice3(A_859))
      | k3_yellow_1(A_859) != k3_lattice3(A_860)
      | ~ l3_lattices(A_860)
      | ~ v10_lattices(A_860)
      | v2_struct_0(A_860) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22484,c_22315])).

tff(c_22604,plain,(
    ! [A_860,A_859] :
      ( v1_orders_2(g1_orders_2(u1_struct_0(A_860),k2_lattice3(k1_lattice3(A_859))))
      | v2_struct_0(k1_lattice3(A_859))
      | k3_yellow_1(A_859) != k3_lattice3(A_860)
      | ~ l3_lattices(A_860)
      | ~ v10_lattices(A_860)
      | v2_struct_0(A_860) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36,c_22527])).

tff(c_22605,plain,(
    ! [A_860,A_859] :
      ( v1_orders_2(g1_orders_2(u1_struct_0(A_860),k2_lattice3(k1_lattice3(A_859))))
      | k3_yellow_1(A_859) != k3_lattice3(A_860)
      | ~ l3_lattices(A_860)
      | ~ v10_lattices(A_860)
      | v2_struct_0(A_860) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_22604])).

tff(c_22290,plain,(
    ! [A_1,A_784,B_786] :
      ( u1_struct_0(A_1) = A_784
      | g1_orders_2(A_784,B_786) != A_1
      | ~ m1_subset_1(B_786,k1_zfmisc_1(k2_zfmisc_1(A_784,A_784)))
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_22284])).

tff(c_22369,plain,(
    ! [A_812,B_813] :
      ( u1_struct_0(g1_orders_2(A_812,B_813)) = A_812
      | ~ m1_subset_1(B_813,k1_zfmisc_1(k2_zfmisc_1(A_812,A_812)))
      | ~ v1_orders_2(g1_orders_2(A_812,B_813))
      | ~ l1_orders_2(g1_orders_2(A_812,B_813)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_22290])).

tff(c_27964,plain,(
    ! [A_1121] :
      ( u1_struct_0(g1_orders_2(u1_struct_0(A_1121),k2_lattice3(A_1121))) = u1_struct_0(A_1121)
      | ~ v1_orders_2(g1_orders_2(u1_struct_0(A_1121),k2_lattice3(A_1121)))
      | ~ l1_orders_2(g1_orders_2(u1_struct_0(A_1121),k2_lattice3(A_1121)))
      | ~ l3_lattices(A_1121)
      | ~ v10_lattices(A_1121)
      | v2_struct_0(A_1121) ) ),
    inference(resolution,[status(thm)],[c_38,c_22369])).

tff(c_28009,plain,(
    ! [A_859] :
      ( u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_859)),k2_lattice3(k1_lattice3(A_859)))) = u1_struct_0(k1_lattice3(A_859))
      | ~ l1_orders_2(g1_orders_2(u1_struct_0(k1_lattice3(A_859)),k2_lattice3(k1_lattice3(A_859))))
      | k3_lattice3(k1_lattice3(A_859)) != k3_yellow_1(A_859)
      | ~ l3_lattices(k1_lattice3(A_859))
      | ~ v10_lattices(k1_lattice3(A_859))
      | v2_struct_0(k1_lattice3(A_859)) ) ),
    inference(resolution,[status(thm)],[c_22605,c_27964])).

tff(c_28057,plain,(
    ! [A_859] :
      ( u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_859)),k2_lattice3(k1_lattice3(A_859)))) = u1_struct_0(k1_lattice3(A_859))
      | ~ l1_orders_2(g1_orders_2(u1_struct_0(k1_lattice3(A_859)),k2_lattice3(k1_lattice3(A_859))))
      | v2_struct_0(k1_lattice3(A_859)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36,c_64,c_28009])).

tff(c_30958,plain,(
    ! [A_1208] :
      ( u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_1208)),k2_lattice3(k1_lattice3(A_1208)))) = u1_struct_0(k1_lattice3(A_1208))
      | ~ l1_orders_2(g1_orders_2(u1_struct_0(k1_lattice3(A_1208)),k2_lattice3(k1_lattice3(A_1208)))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_28057])).

tff(c_30987,plain,(
    ! [A_859] :
      ( u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_859)),k2_lattice3(k1_lattice3(A_859)))) = u1_struct_0(k1_lattice3(A_859))
      | ~ l1_orders_2(k3_yellow_1(A_859))
      | k3_lattice3(k1_lattice3(A_859)) != k3_yellow_1(A_859)
      | ~ l3_lattices(k1_lattice3(A_859))
      | ~ v10_lattices(k1_lattice3(A_859))
      | v2_struct_0(k1_lattice3(A_859)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22620,c_30958])).

tff(c_31031,plain,(
    ! [A_859] :
      ( u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_859)),k2_lattice3(k1_lattice3(A_859)))) = u1_struct_0(k1_lattice3(A_859))
      | v2_struct_0(k1_lattice3(A_859)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36,c_64,c_22331,c_30987])).

tff(c_31052,plain,(
    ! [A_1209] : u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_1209)),k2_lattice3(k1_lattice3(A_1209)))) = u1_struct_0(k1_lattice3(A_1209)) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_31031])).

tff(c_31223,plain,(
    ! [A_859] :
      ( u1_struct_0(k3_yellow_1(A_859)) = u1_struct_0(k1_lattice3(A_859))
      | k3_lattice3(k1_lattice3(A_859)) != k3_yellow_1(A_859)
      | ~ l3_lattices(k1_lattice3(A_859))
      | ~ v10_lattices(k1_lattice3(A_859))
      | v2_struct_0(k1_lattice3(A_859)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22620,c_31052])).

tff(c_31285,plain,(
    ! [A_859] :
      ( u1_struct_0(k3_yellow_1(A_859)) = u1_struct_0(k1_lattice3(A_859))
      | v2_struct_0(k1_lattice3(A_859)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36,c_64,c_31223])).

tff(c_31286,plain,(
    ! [A_859] : u1_struct_0(k3_yellow_1(A_859)) = u1_struct_0(k1_lattice3(A_859)) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_31285])).

tff(c_31333,plain,(
    m1_subset_1('#skF_2',u1_struct_0(k1_lattice3('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31286,c_68])).

tff(c_31332,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k1_lattice3('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31286,c_66])).

tff(c_22239,plain,(
    r3_orders_2(k3_yellow_1('#skF_1'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_31594,plain,
    ( k4_lattice3(k1_lattice3('#skF_1'),'#skF_2') = '#skF_2'
    | ~ l3_lattices(k1_lattice3('#skF_1'))
    | ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_31333,c_32])).

tff(c_31632,plain,
    ( k4_lattice3(k1_lattice3('#skF_1'),'#skF_2') = '#skF_2'
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36,c_31594])).

tff(c_31633,plain,(
    k4_lattice3(k1_lattice3('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_31632])).

tff(c_31524,plain,
    ( k4_lattice3(k1_lattice3('#skF_1'),'#skF_3') = '#skF_3'
    | ~ l3_lattices(k1_lattice3('#skF_1'))
    | ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_31332,c_32])).

tff(c_31562,plain,
    ( k4_lattice3(k1_lattice3('#skF_1'),'#skF_3') = '#skF_3'
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36,c_31524])).

tff(c_31563,plain,(
    k4_lattice3(k1_lattice3('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_31562])).

tff(c_22473,plain,(
    ! [A_854,B_855,C_856] :
      ( r3_lattices(A_854,B_855,C_856)
      | ~ r3_orders_2(k3_lattice3(A_854),k4_lattice3(A_854,B_855),k4_lattice3(A_854,C_856))
      | ~ m1_subset_1(C_856,u1_struct_0(A_854))
      | ~ m1_subset_1(B_855,u1_struct_0(A_854))
      | ~ l3_lattices(A_854)
      | ~ v10_lattices(A_854)
      | v2_struct_0(A_854) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_22476,plain,(
    ! [A_33,B_855,C_856] :
      ( r3_lattices(k1_lattice3(A_33),B_855,C_856)
      | ~ r3_orders_2(k3_yellow_1(A_33),k4_lattice3(k1_lattice3(A_33),B_855),k4_lattice3(k1_lattice3(A_33),C_856))
      | ~ m1_subset_1(C_856,u1_struct_0(k1_lattice3(A_33)))
      | ~ m1_subset_1(B_855,u1_struct_0(k1_lattice3(A_33)))
      | ~ l3_lattices(k1_lattice3(A_33))
      | ~ v10_lattices(k1_lattice3(A_33))
      | v2_struct_0(k1_lattice3(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_22473])).

tff(c_22478,plain,(
    ! [A_33,B_855,C_856] :
      ( r3_lattices(k1_lattice3(A_33),B_855,C_856)
      | ~ r3_orders_2(k3_yellow_1(A_33),k4_lattice3(k1_lattice3(A_33),B_855),k4_lattice3(k1_lattice3(A_33),C_856))
      | ~ m1_subset_1(C_856,u1_struct_0(k1_lattice3(A_33)))
      | ~ m1_subset_1(B_855,u1_struct_0(k1_lattice3(A_33)))
      | v2_struct_0(k1_lattice3(A_33)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36,c_22476])).

tff(c_22479,plain,(
    ! [A_33,B_855,C_856] :
      ( r3_lattices(k1_lattice3(A_33),B_855,C_856)
      | ~ r3_orders_2(k3_yellow_1(A_33),k4_lattice3(k1_lattice3(A_33),B_855),k4_lattice3(k1_lattice3(A_33),C_856))
      | ~ m1_subset_1(C_856,u1_struct_0(k1_lattice3(A_33)))
      | ~ m1_subset_1(B_855,u1_struct_0(k1_lattice3(A_33))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_22478])).

tff(c_31652,plain,(
    ! [B_855] :
      ( r3_lattices(k1_lattice3('#skF_1'),B_855,'#skF_3')
      | ~ r3_orders_2(k3_yellow_1('#skF_1'),k4_lattice3(k1_lattice3('#skF_1'),B_855),'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0(k1_lattice3('#skF_1')))
      | ~ m1_subset_1(B_855,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31563,c_22479])).

tff(c_32916,plain,(
    ! [B_1229] :
      ( r3_lattices(k1_lattice3('#skF_1'),B_1229,'#skF_3')
      | ~ r3_orders_2(k3_yellow_1('#skF_1'),k4_lattice3(k1_lattice3('#skF_1'),B_1229),'#skF_3')
      | ~ m1_subset_1(B_1229,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31332,c_31652])).

tff(c_32919,plain,
    ( r3_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3')
    | ~ r3_orders_2(k3_yellow_1('#skF_1'),'#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_2',u1_struct_0(k1_lattice3('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_31633,c_32916])).

tff(c_32932,plain,(
    r3_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31333,c_22239,c_32919])).

tff(c_28,plain,(
    ! [A_11,B_12,C_13] :
      ( r1_lattices(A_11,B_12,C_13)
      | ~ r3_lattices(A_11,B_12,C_13)
      | ~ m1_subset_1(C_13,u1_struct_0(A_11))
      | ~ m1_subset_1(B_12,u1_struct_0(A_11))
      | ~ l3_lattices(A_11)
      | ~ v9_lattices(A_11)
      | ~ v8_lattices(A_11)
      | ~ v6_lattices(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32948,plain,
    ( r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0(k1_lattice3('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0(k1_lattice3('#skF_1')))
    | ~ l3_lattices(k1_lattice3('#skF_1'))
    | ~ v9_lattices(k1_lattice3('#skF_1'))
    | ~ v8_lattices(k1_lattice3('#skF_1'))
    | ~ v6_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32932,c_28])).

tff(c_32951,plain,
    ( r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3')
    | ~ v9_lattices(k1_lattice3('#skF_1'))
    | ~ v8_lattices(k1_lattice3('#skF_1'))
    | ~ v6_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_31333,c_31332,c_32948])).

tff(c_32952,plain,
    ( r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3')
    | ~ v9_lattices(k1_lattice3('#skF_1'))
    | ~ v8_lattices(k1_lattice3('#skF_1'))
    | ~ v6_lattices(k1_lattice3('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_32951])).

tff(c_32955,plain,(
    ~ v6_lattices(k1_lattice3('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_32952])).

tff(c_32958,plain,
    ( ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1'))
    | ~ l3_lattices(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_32955])).

tff(c_32961,plain,(
    v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_32958])).

tff(c_32963,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_32961])).

tff(c_32964,plain,
    ( ~ v8_lattices(k1_lattice3('#skF_1'))
    | ~ v9_lattices(k1_lattice3('#skF_1'))
    | r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32952])).

tff(c_33053,plain,(
    ~ v9_lattices(k1_lattice3('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_32964])).

tff(c_33056,plain,
    ( ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1'))
    | ~ l3_lattices(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_33053])).

tff(c_33059,plain,(
    v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_33056])).

tff(c_33061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_33059])).

tff(c_33062,plain,
    ( ~ v8_lattices(k1_lattice3('#skF_1'))
    | r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32964])).

tff(c_33064,plain,(
    ~ v8_lattices(k1_lattice3('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_33062])).

tff(c_33067,plain,
    ( ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1'))
    | ~ l3_lattices(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_14,c_33064])).

tff(c_33070,plain,(
    v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_33067])).

tff(c_33072,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_33070])).

tff(c_33073,plain,(
    r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_33062])).

tff(c_58,plain,(
    ! [B_23,C_25,A_22] :
      ( r1_tarski(B_23,C_25)
      | ~ r1_lattices(k1_lattice3(A_22),B_23,C_25)
      | ~ m1_subset_1(C_25,u1_struct_0(k1_lattice3(A_22)))
      | ~ m1_subset_1(B_23,u1_struct_0(k1_lattice3(A_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_33184,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0(k1_lattice3('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0(k1_lattice3('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_33073,c_58])).

tff(c_33187,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31333,c_31332,c_33184])).

tff(c_33189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22240,c_33187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:16:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.90/7.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.90/7.31  
% 17.90/7.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.90/7.31  %$ r3_orders_2 > r3_lattices > r1_lattices > v1_partfun1 > r1_tarski > m1_subset_1 > v9_lattices > v8_relat_2 > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_relat_2 > v4_lattices > v3_lattices > v2_struct_0 > v1_relat_2 > v1_orders_2 > v10_lattices > l3_lattices > l1_orders_2 > k4_lattice3 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_1 > k3_lattice3 > k2_lattice3 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1
% 17.90/7.31  
% 17.90/7.31  %Foreground sorts:
% 17.90/7.31  
% 17.90/7.31  
% 17.90/7.31  %Background operators:
% 17.90/7.31  
% 17.90/7.31  
% 17.90/7.31  %Foreground operators:
% 17.90/7.31  tff(l3_lattices, type, l3_lattices: $i > $o).
% 17.90/7.31  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 17.90/7.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 17.90/7.31  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 17.90/7.31  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 17.90/7.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.90/7.31  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 17.90/7.31  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 17.90/7.31  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 17.90/7.31  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 17.90/7.31  tff(k4_lattice3, type, k4_lattice3: ($i * $i) > $i).
% 17.90/7.31  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 17.90/7.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.90/7.31  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 17.90/7.31  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 17.90/7.31  tff(v4_lattices, type, v4_lattices: $i > $o).
% 17.90/7.31  tff(v6_lattices, type, v6_lattices: $i > $o).
% 17.90/7.31  tff('#skF_2', type, '#skF_2': $i).
% 17.90/7.31  tff(v9_lattices, type, v9_lattices: $i > $o).
% 17.90/7.31  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 17.90/7.31  tff('#skF_3', type, '#skF_3': $i).
% 17.90/7.31  tff('#skF_1', type, '#skF_1': $i).
% 17.90/7.31  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 17.90/7.31  tff(v5_lattices, type, v5_lattices: $i > $o).
% 17.90/7.31  tff(v10_lattices, type, v10_lattices: $i > $o).
% 17.90/7.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.90/7.31  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 17.90/7.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.90/7.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 17.90/7.31  tff(v8_lattices, type, v8_lattices: $i > $o).
% 17.90/7.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.90/7.31  tff(v3_lattices, type, v3_lattices: $i > $o).
% 17.90/7.31  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 17.90/7.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 17.90/7.31  tff(k2_lattice3, type, k2_lattice3: $i > $i).
% 17.90/7.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.90/7.31  tff(v7_lattices, type, v7_lattices: $i > $o).
% 17.90/7.31  
% 17.90/7.34  tff(f_176, negated_conjecture, ~(![A, B]: (m1_subset_1(B, u1_struct_0(k3_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k3_yellow_1(A))) => (r3_orders_2(k3_yellow_1(A), B, C) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow_1)).
% 17.90/7.34  tff(f_134, axiom, (![A]: (~v2_struct_0(k1_lattice3(A)) & v3_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_lattice3)).
% 17.90/7.34  tff(f_138, axiom, (![A]: (v3_lattices(k1_lattice3(A)) & v10_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_lattice3)).
% 17.90/7.34  tff(f_112, axiom, (![A]: (v3_lattices(k1_lattice3(A)) & l3_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_lattice3)).
% 17.90/7.34  tff(f_166, axiom, (![A]: (k3_yellow_1(A) = k3_lattice3(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_yellow_1)).
% 17.90/7.34  tff(f_129, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => ((((v1_partfun1(k2_lattice3(A), u1_struct_0(A)) & v1_relat_2(k2_lattice3(A))) & v4_relat_2(k2_lattice3(A))) & v8_relat_2(k2_lattice3(A))) & m1_subset_1(k2_lattice3(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_lattice3)).
% 17.90/7.34  tff(f_96, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (k3_lattice3(A) = g1_orders_2(u1_struct_0(A), k2_lattice3(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_lattice3)).
% 17.90/7.34  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C, D]: ((g1_orders_2(A, B) = g1_orders_2(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_orders_2)).
% 17.90/7.34  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (v1_orders_2(g1_orders_2(A, B)) & l1_orders_2(g1_orders_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_orders_2)).
% 17.90/7.34  tff(f_31, axiom, (![A]: (l1_orders_2(A) => (v1_orders_2(A) => (A = g1_orders_2(u1_struct_0(A), u1_orders_2(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_orders_2)).
% 17.90/7.34  tff(f_108, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattice3(A, B) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattice3)).
% 17.90/7.34  tff(f_164, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_lattices(A, B, C) <=> r3_orders_2(k3_lattice3(A), k4_lattice3(A, B), k4_lattice3(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_lattice3)).
% 17.90/7.34  tff(f_147, axiom, (![A, B]: (m1_subset_1(B, u1_struct_0(k1_lattice3(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k1_lattice3(A))) => (r1_lattices(k1_lattice3(A), B, C) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_lattice3)).
% 17.90/7.34  tff(f_68, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 17.90/7.34  tff(f_87, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 17.90/7.34  tff(c_76, plain, (r3_orders_2(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3') | r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 17.90/7.34  tff(c_94, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_76])).
% 17.90/7.34  tff(c_70, plain, (~r1_tarski('#skF_2', '#skF_3') | ~r3_orders_2(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 17.90/7.34  tff(c_100, plain, (~r3_orders_2(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_70])).
% 17.90/7.34  tff(c_48, plain, (![A_20]: (~v2_struct_0(k1_lattice3(A_20)))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.90/7.34  tff(c_54, plain, (![A_21]: (v10_lattices(k1_lattice3(A_21)))), inference(cnfTransformation, [status(thm)], [f_138])).
% 17.90/7.34  tff(c_36, plain, (![A_18]: (l3_lattices(k1_lattice3(A_18)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 17.90/7.34  tff(c_64, plain, (![A_33]: (k3_lattice3(k1_lattice3(A_33))=k3_yellow_1(A_33))), inference(cnfTransformation, [status(thm)], [f_166])).
% 17.90/7.34  tff(c_38, plain, (![A_19]: (m1_subset_1(k2_lattice3(A_19), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19), u1_struct_0(A_19)))) | ~l3_lattices(A_19) | ~v10_lattices(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_129])).
% 17.90/7.34  tff(c_30, plain, (![A_14]: (g1_orders_2(u1_struct_0(A_14), k2_lattice3(A_14))=k3_lattice3(A_14) | ~l3_lattices(A_14) | ~v10_lattices(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_96])).
% 17.90/7.34  tff(c_151, plain, (![C_62, A_63, D_64, B_65]: (C_62=A_63 | g1_orders_2(C_62, D_64)!=g1_orders_2(A_63, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(k2_zfmisc_1(A_63, A_63))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 17.90/7.34  tff(c_228, plain, (![A_89, A_90, B_91]: (u1_struct_0(A_89)=A_90 | k3_lattice3(A_89)!=g1_orders_2(A_90, B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(k2_zfmisc_1(A_90, A_90))) | ~l3_lattices(A_89) | ~v10_lattices(A_89) | v2_struct_0(A_89))), inference(superposition, [status(thm), theory('equality')], [c_30, c_151])).
% 17.90/7.34  tff(c_234, plain, (![A_33, A_90, B_91]: (u1_struct_0(k1_lattice3(A_33))=A_90 | k3_yellow_1(A_33)!=g1_orders_2(A_90, B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(k2_zfmisc_1(A_90, A_90))) | ~l3_lattices(k1_lattice3(A_33)) | ~v10_lattices(k1_lattice3(A_33)) | v2_struct_0(k1_lattice3(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_228])).
% 17.90/7.34  tff(c_236, plain, (![A_33, A_90, B_91]: (u1_struct_0(k1_lattice3(A_33))=A_90 | k3_yellow_1(A_33)!=g1_orders_2(A_90, B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(k2_zfmisc_1(A_90, A_90))) | v2_struct_0(k1_lattice3(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36, c_234])).
% 17.90/7.34  tff(c_238, plain, (![A_92, A_93, B_94]: (u1_struct_0(k1_lattice3(A_92))=A_93 | k3_yellow_1(A_92)!=g1_orders_2(A_93, B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(k2_zfmisc_1(A_93, A_93))))), inference(negUnitSimplification, [status(thm)], [c_48, c_236])).
% 17.90/7.34  tff(c_723, plain, (![A_192, A_193]: (u1_struct_0(k1_lattice3(A_192))=u1_struct_0(A_193) | k3_yellow_1(A_192)!=k3_lattice3(A_193) | ~m1_subset_1(k2_lattice3(A_193), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_193), u1_struct_0(A_193)))) | ~l3_lattices(A_193) | ~v10_lattices(A_193) | v2_struct_0(A_193))), inference(superposition, [status(thm), theory('equality')], [c_30, c_238])).
% 17.90/7.34  tff(c_1055, plain, (![A_204, A_205]: (u1_struct_0(k1_lattice3(A_204))=u1_struct_0(A_205) | k3_yellow_1(A_204)!=k3_lattice3(A_205) | ~l3_lattices(A_205) | ~v10_lattices(A_205) | v2_struct_0(A_205))), inference(resolution, [status(thm)], [c_38, c_723])).
% 17.90/7.34  tff(c_1187, plain, (![A_205, A_204]: (g1_orders_2(u1_struct_0(A_205), k2_lattice3(k1_lattice3(A_204)))=k3_lattice3(k1_lattice3(A_204)) | ~l3_lattices(k1_lattice3(A_204)) | ~v10_lattices(k1_lattice3(A_204)) | v2_struct_0(k1_lattice3(A_204)) | k3_yellow_1(A_204)!=k3_lattice3(A_205) | ~l3_lattices(A_205) | ~v10_lattices(A_205) | v2_struct_0(A_205))), inference(superposition, [status(thm), theory('equality')], [c_1055, c_30])).
% 17.90/7.34  tff(c_1291, plain, (![A_205, A_204]: (g1_orders_2(u1_struct_0(A_205), k2_lattice3(k1_lattice3(A_204)))=k3_yellow_1(A_204) | v2_struct_0(k1_lattice3(A_204)) | k3_yellow_1(A_204)!=k3_lattice3(A_205) | ~l3_lattices(A_205) | ~v10_lattices(A_205) | v2_struct_0(A_205))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36, c_64, c_1187])).
% 17.90/7.34  tff(c_1292, plain, (![A_205, A_204]: (g1_orders_2(u1_struct_0(A_205), k2_lattice3(k1_lattice3(A_204)))=k3_yellow_1(A_204) | k3_yellow_1(A_204)!=k3_lattice3(A_205) | ~l3_lattices(A_205) | ~v10_lattices(A_205) | v2_struct_0(A_205))), inference(negUnitSimplification, [status(thm)], [c_48, c_1291])).
% 17.90/7.34  tff(c_161, plain, (![A_66]: (m1_subset_1(k2_lattice3(A_66), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_66), u1_struct_0(A_66)))) | ~l3_lattices(A_66) | ~v10_lattices(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_129])).
% 17.90/7.34  tff(c_4, plain, (![A_2, B_3]: (l1_orders_2(g1_orders_2(A_2, B_3)) | ~m1_subset_1(B_3, k1_zfmisc_1(k2_zfmisc_1(A_2, A_2))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.90/7.34  tff(c_170, plain, (![A_67]: (l1_orders_2(g1_orders_2(u1_struct_0(A_67), k2_lattice3(A_67))) | ~l3_lattices(A_67) | ~v10_lattices(A_67) | v2_struct_0(A_67))), inference(resolution, [status(thm)], [c_161, c_4])).
% 17.90/7.34  tff(c_178, plain, (![A_69]: (l1_orders_2(k3_lattice3(A_69)) | ~l3_lattices(A_69) | ~v10_lattices(A_69) | v2_struct_0(A_69) | ~l3_lattices(A_69) | ~v10_lattices(A_69) | v2_struct_0(A_69))), inference(superposition, [status(thm), theory('equality')], [c_30, c_170])).
% 17.90/7.34  tff(c_181, plain, (![A_33]: (l1_orders_2(k3_yellow_1(A_33)) | ~l3_lattices(k1_lattice3(A_33)) | ~v10_lattices(k1_lattice3(A_33)) | v2_struct_0(k1_lattice3(A_33)) | ~l3_lattices(k1_lattice3(A_33)) | ~v10_lattices(k1_lattice3(A_33)) | v2_struct_0(k1_lattice3(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_178])).
% 17.90/7.34  tff(c_183, plain, (![A_33]: (l1_orders_2(k3_yellow_1(A_33)) | v2_struct_0(k1_lattice3(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36, c_54, c_36, c_181])).
% 17.90/7.34  tff(c_184, plain, (![A_33]: (l1_orders_2(k3_yellow_1(A_33)))), inference(negUnitSimplification, [status(thm)], [c_48, c_183])).
% 17.90/7.34  tff(c_6, plain, (![A_2, B_3]: (v1_orders_2(g1_orders_2(A_2, B_3)) | ~m1_subset_1(B_3, k1_zfmisc_1(k2_zfmisc_1(A_2, A_2))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.90/7.34  tff(c_169, plain, (![A_66]: (v1_orders_2(g1_orders_2(u1_struct_0(A_66), k2_lattice3(A_66))) | ~l3_lattices(A_66) | ~v10_lattices(A_66) | v2_struct_0(A_66))), inference(resolution, [status(thm)], [c_161, c_6])).
% 17.90/7.34  tff(c_1157, plain, (![A_205, A_204]: (v1_orders_2(g1_orders_2(u1_struct_0(A_205), k2_lattice3(k1_lattice3(A_204)))) | ~l3_lattices(k1_lattice3(A_204)) | ~v10_lattices(k1_lattice3(A_204)) | v2_struct_0(k1_lattice3(A_204)) | k3_yellow_1(A_204)!=k3_lattice3(A_205) | ~l3_lattices(A_205) | ~v10_lattices(A_205) | v2_struct_0(A_205))), inference(superposition, [status(thm), theory('equality')], [c_1055, c_169])).
% 17.90/7.34  tff(c_1276, plain, (![A_205, A_204]: (v1_orders_2(g1_orders_2(u1_struct_0(A_205), k2_lattice3(k1_lattice3(A_204)))) | v2_struct_0(k1_lattice3(A_204)) | k3_yellow_1(A_204)!=k3_lattice3(A_205) | ~l3_lattices(A_205) | ~v10_lattices(A_205) | v2_struct_0(A_205))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36, c_1157])).
% 17.90/7.34  tff(c_1277, plain, (![A_205, A_204]: (v1_orders_2(g1_orders_2(u1_struct_0(A_205), k2_lattice3(k1_lattice3(A_204)))) | k3_yellow_1(A_204)!=k3_lattice3(A_205) | ~l3_lattices(A_205) | ~v10_lattices(A_205) | v2_struct_0(A_205))), inference(negUnitSimplification, [status(thm)], [c_48, c_1276])).
% 17.90/7.34  tff(c_2, plain, (![A_1]: (g1_orders_2(u1_struct_0(A_1), u1_orders_2(A_1))=A_1 | ~v1_orders_2(A_1) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.90/7.34  tff(c_157, plain, (![A_1, A_63, B_65]: (u1_struct_0(A_1)=A_63 | g1_orders_2(A_63, B_65)!=A_1 | ~m1_subset_1(B_65, k1_zfmisc_1(k2_zfmisc_1(A_63, A_63))) | ~v1_orders_2(A_1) | ~l1_orders_2(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_151])).
% 17.90/7.34  tff(c_218, plain, (![A_85, B_86]: (u1_struct_0(g1_orders_2(A_85, B_86))=A_85 | ~m1_subset_1(B_86, k1_zfmisc_1(k2_zfmisc_1(A_85, A_85))) | ~v1_orders_2(g1_orders_2(A_85, B_86)) | ~l1_orders_2(g1_orders_2(A_85, B_86)))), inference(reflexivity, [status(thm), theory('equality')], [c_157])).
% 17.90/7.34  tff(c_5726, plain, (![A_378]: (u1_struct_0(g1_orders_2(u1_struct_0(A_378), k2_lattice3(A_378)))=u1_struct_0(A_378) | ~v1_orders_2(g1_orders_2(u1_struct_0(A_378), k2_lattice3(A_378))) | ~l1_orders_2(g1_orders_2(u1_struct_0(A_378), k2_lattice3(A_378))) | ~l3_lattices(A_378) | ~v10_lattices(A_378) | v2_struct_0(A_378))), inference(resolution, [status(thm)], [c_38, c_218])).
% 17.90/7.34  tff(c_5743, plain, (![A_204]: (u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_204)), k2_lattice3(k1_lattice3(A_204))))=u1_struct_0(k1_lattice3(A_204)) | ~l1_orders_2(g1_orders_2(u1_struct_0(k1_lattice3(A_204)), k2_lattice3(k1_lattice3(A_204)))) | k3_lattice3(k1_lattice3(A_204))!=k3_yellow_1(A_204) | ~l3_lattices(k1_lattice3(A_204)) | ~v10_lattices(k1_lattice3(A_204)) | v2_struct_0(k1_lattice3(A_204)))), inference(resolution, [status(thm)], [c_1277, c_5726])).
% 17.90/7.34  tff(c_5806, plain, (![A_204]: (u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_204)), k2_lattice3(k1_lattice3(A_204))))=u1_struct_0(k1_lattice3(A_204)) | ~l1_orders_2(g1_orders_2(u1_struct_0(k1_lattice3(A_204)), k2_lattice3(k1_lattice3(A_204)))) | v2_struct_0(k1_lattice3(A_204)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36, c_64, c_5743])).
% 17.90/7.34  tff(c_7917, plain, (![A_469]: (u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_469)), k2_lattice3(k1_lattice3(A_469))))=u1_struct_0(k1_lattice3(A_469)) | ~l1_orders_2(g1_orders_2(u1_struct_0(k1_lattice3(A_469)), k2_lattice3(k1_lattice3(A_469)))))), inference(negUnitSimplification, [status(thm)], [c_48, c_5806])).
% 17.90/7.34  tff(c_7924, plain, (![A_204]: (u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_204)), k2_lattice3(k1_lattice3(A_204))))=u1_struct_0(k1_lattice3(A_204)) | ~l1_orders_2(k3_yellow_1(A_204)) | k3_lattice3(k1_lattice3(A_204))!=k3_yellow_1(A_204) | ~l3_lattices(k1_lattice3(A_204)) | ~v10_lattices(k1_lattice3(A_204)) | v2_struct_0(k1_lattice3(A_204)))), inference(superposition, [status(thm), theory('equality')], [c_1292, c_7917])).
% 17.90/7.34  tff(c_7978, plain, (![A_204]: (u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_204)), k2_lattice3(k1_lattice3(A_204))))=u1_struct_0(k1_lattice3(A_204)) | v2_struct_0(k1_lattice3(A_204)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36, c_64, c_184, c_7924])).
% 17.90/7.34  tff(c_8011, plain, (![A_470]: (u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_470)), k2_lattice3(k1_lattice3(A_470))))=u1_struct_0(k1_lattice3(A_470)))), inference(negUnitSimplification, [status(thm)], [c_48, c_7978])).
% 17.90/7.34  tff(c_8143, plain, (![A_204]: (u1_struct_0(k3_yellow_1(A_204))=u1_struct_0(k1_lattice3(A_204)) | k3_lattice3(k1_lattice3(A_204))!=k3_yellow_1(A_204) | ~l3_lattices(k1_lattice3(A_204)) | ~v10_lattices(k1_lattice3(A_204)) | v2_struct_0(k1_lattice3(A_204)))), inference(superposition, [status(thm), theory('equality')], [c_1292, c_8011])).
% 17.90/7.34  tff(c_8222, plain, (![A_204]: (u1_struct_0(k3_yellow_1(A_204))=u1_struct_0(k1_lattice3(A_204)) | v2_struct_0(k1_lattice3(A_204)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36, c_64, c_8143])).
% 17.90/7.34  tff(c_8223, plain, (![A_204]: (u1_struct_0(k3_yellow_1(A_204))=u1_struct_0(k1_lattice3(A_204)))), inference(negUnitSimplification, [status(thm)], [c_48, c_8222])).
% 17.90/7.34  tff(c_66, plain, (m1_subset_1('#skF_3', u1_struct_0(k3_yellow_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 17.90/7.34  tff(c_8273, plain, (m1_subset_1('#skF_3', u1_struct_0(k1_lattice3('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8223, c_66])).
% 17.90/7.34  tff(c_32, plain, (![A_15, B_17]: (k4_lattice3(A_15, B_17)=B_17 | ~m1_subset_1(B_17, u1_struct_0(A_15)) | ~l3_lattices(A_15) | ~v10_lattices(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_108])).
% 17.90/7.34  tff(c_8456, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_3')='#skF_3' | ~l3_lattices(k1_lattice3('#skF_1')) | ~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_8273, c_32])).
% 17.90/7.34  tff(c_8500, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_3')='#skF_3' | v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36, c_8456])).
% 17.90/7.34  tff(c_8501, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_48, c_8500])).
% 17.90/7.34  tff(c_68, plain, (m1_subset_1('#skF_2', u1_struct_0(k3_yellow_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 17.90/7.34  tff(c_8274, plain, (m1_subset_1('#skF_2', u1_struct_0(k1_lattice3('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8223, c_68])).
% 17.90/7.34  tff(c_8656, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_2')='#skF_2' | ~l3_lattices(k1_lattice3('#skF_1')) | ~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_8274, c_32])).
% 17.90/7.34  tff(c_8704, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_2')='#skF_2' | v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36, c_8656])).
% 17.90/7.34  tff(c_8705, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_48, c_8704])).
% 17.90/7.34  tff(c_481, plain, (![A_141, B_142, C_143]: (r3_orders_2(k3_lattice3(A_141), k4_lattice3(A_141, B_142), k4_lattice3(A_141, C_143)) | ~r3_lattices(A_141, B_142, C_143) | ~m1_subset_1(C_143, u1_struct_0(A_141)) | ~m1_subset_1(B_142, u1_struct_0(A_141)) | ~l3_lattices(A_141) | ~v10_lattices(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_164])).
% 17.90/7.34  tff(c_487, plain, (![A_33, B_142, C_143]: (r3_orders_2(k3_yellow_1(A_33), k4_lattice3(k1_lattice3(A_33), B_142), k4_lattice3(k1_lattice3(A_33), C_143)) | ~r3_lattices(k1_lattice3(A_33), B_142, C_143) | ~m1_subset_1(C_143, u1_struct_0(k1_lattice3(A_33))) | ~m1_subset_1(B_142, u1_struct_0(k1_lattice3(A_33))) | ~l3_lattices(k1_lattice3(A_33)) | ~v10_lattices(k1_lattice3(A_33)) | v2_struct_0(k1_lattice3(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_481])).
% 17.90/7.34  tff(c_490, plain, (![A_33, B_142, C_143]: (r3_orders_2(k3_yellow_1(A_33), k4_lattice3(k1_lattice3(A_33), B_142), k4_lattice3(k1_lattice3(A_33), C_143)) | ~r3_lattices(k1_lattice3(A_33), B_142, C_143) | ~m1_subset_1(C_143, u1_struct_0(k1_lattice3(A_33))) | ~m1_subset_1(B_142, u1_struct_0(k1_lattice3(A_33))) | v2_struct_0(k1_lattice3(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36, c_487])).
% 17.90/7.34  tff(c_491, plain, (![A_33, B_142, C_143]: (r3_orders_2(k3_yellow_1(A_33), k4_lattice3(k1_lattice3(A_33), B_142), k4_lattice3(k1_lattice3(A_33), C_143)) | ~r3_lattices(k1_lattice3(A_33), B_142, C_143) | ~m1_subset_1(C_143, u1_struct_0(k1_lattice3(A_33))) | ~m1_subset_1(B_142, u1_struct_0(k1_lattice3(A_33))))), inference(negUnitSimplification, [status(thm)], [c_48, c_490])).
% 17.90/7.34  tff(c_8785, plain, (![C_143]: (r3_orders_2(k3_yellow_1('#skF_1'), '#skF_2', k4_lattice3(k1_lattice3('#skF_1'), C_143)) | ~r3_lattices(k1_lattice3('#skF_1'), '#skF_2', C_143) | ~m1_subset_1(C_143, u1_struct_0(k1_lattice3('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0(k1_lattice3('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_8705, c_491])).
% 17.90/7.34  tff(c_10022, plain, (![C_494]: (r3_orders_2(k3_yellow_1('#skF_1'), '#skF_2', k4_lattice3(k1_lattice3('#skF_1'), C_494)) | ~r3_lattices(k1_lattice3('#skF_1'), '#skF_2', C_494) | ~m1_subset_1(C_494, u1_struct_0(k1_lattice3('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_8274, c_8785])).
% 17.90/7.34  tff(c_10028, plain, (r3_orders_2(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3') | ~r3_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0(k1_lattice3('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_8501, c_10022])).
% 17.90/7.34  tff(c_10040, plain, (r3_orders_2(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3') | ~r3_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8273, c_10028])).
% 17.90/7.34  tff(c_10041, plain, (~r3_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_100, c_10040])).
% 17.90/7.34  tff(c_56, plain, (![A_22, B_23, C_25]: (r1_lattices(k1_lattice3(A_22), B_23, C_25) | ~r1_tarski(B_23, C_25) | ~m1_subset_1(C_25, u1_struct_0(k1_lattice3(A_22))) | ~m1_subset_1(B_23, u1_struct_0(k1_lattice3(A_22))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 17.90/7.34  tff(c_8831, plain, (![B_473]: (r1_lattices(k1_lattice3('#skF_1'), B_473, '#skF_3') | ~r1_tarski(B_473, '#skF_3') | ~m1_subset_1(B_473, u1_struct_0(k1_lattice3('#skF_1'))))), inference(resolution, [status(thm)], [c_8273, c_56])).
% 17.90/7.34  tff(c_8834, plain, (r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3') | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_8274, c_8831])).
% 17.90/7.34  tff(c_8874, plain, (r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_8834])).
% 17.90/7.34  tff(c_14, plain, (![A_10]: (v8_lattices(A_10) | ~v10_lattices(A_10) | v2_struct_0(A_10) | ~l3_lattices(A_10))), inference(cnfTransformation, [status(thm)], [f_68])).
% 17.90/7.34  tff(c_18, plain, (![A_10]: (v6_lattices(A_10) | ~v10_lattices(A_10) | v2_struct_0(A_10) | ~l3_lattices(A_10))), inference(cnfTransformation, [status(thm)], [f_68])).
% 17.90/7.34  tff(c_26, plain, (![A_11, B_12, C_13]: (r3_lattices(A_11, B_12, C_13) | ~r1_lattices(A_11, B_12, C_13) | ~m1_subset_1(C_13, u1_struct_0(A_11)) | ~m1_subset_1(B_12, u1_struct_0(A_11)) | ~l3_lattices(A_11) | ~v9_lattices(A_11) | ~v8_lattices(A_11) | ~v6_lattices(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_87])).
% 17.90/7.34  tff(c_8451, plain, (![B_12]: (r3_lattices(k1_lattice3('#skF_1'), B_12, '#skF_3') | ~r1_lattices(k1_lattice3('#skF_1'), B_12, '#skF_3') | ~m1_subset_1(B_12, u1_struct_0(k1_lattice3('#skF_1'))) | ~l3_lattices(k1_lattice3('#skF_1')) | ~v9_lattices(k1_lattice3('#skF_1')) | ~v8_lattices(k1_lattice3('#skF_1')) | ~v6_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')))), inference(resolution, [status(thm)], [c_8273, c_26])).
% 17.90/7.34  tff(c_8495, plain, (![B_12]: (r3_lattices(k1_lattice3('#skF_1'), B_12, '#skF_3') | ~r1_lattices(k1_lattice3('#skF_1'), B_12, '#skF_3') | ~m1_subset_1(B_12, u1_struct_0(k1_lattice3('#skF_1'))) | ~v9_lattices(k1_lattice3('#skF_1')) | ~v8_lattices(k1_lattice3('#skF_1')) | ~v6_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8451])).
% 17.90/7.34  tff(c_8496, plain, (![B_12]: (r3_lattices(k1_lattice3('#skF_1'), B_12, '#skF_3') | ~r1_lattices(k1_lattice3('#skF_1'), B_12, '#skF_3') | ~m1_subset_1(B_12, u1_struct_0(k1_lattice3('#skF_1'))) | ~v9_lattices(k1_lattice3('#skF_1')) | ~v8_lattices(k1_lattice3('#skF_1')) | ~v6_lattices(k1_lattice3('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_48, c_8495])).
% 17.90/7.34  tff(c_21913, plain, (~v6_lattices(k1_lattice3('#skF_1'))), inference(splitLeft, [status(thm)], [c_8496])).
% 17.90/7.34  tff(c_21916, plain, (~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')) | ~l3_lattices(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_21913])).
% 17.90/7.34  tff(c_21919, plain, (v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_21916])).
% 17.90/7.34  tff(c_21921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_21919])).
% 17.90/7.34  tff(c_21923, plain, (v6_lattices(k1_lattice3('#skF_1'))), inference(splitRight, [status(thm)], [c_8496])).
% 17.90/7.34  tff(c_8651, plain, (![B_12]: (r3_lattices(k1_lattice3('#skF_1'), B_12, '#skF_2') | ~r1_lattices(k1_lattice3('#skF_1'), B_12, '#skF_2') | ~m1_subset_1(B_12, u1_struct_0(k1_lattice3('#skF_1'))) | ~l3_lattices(k1_lattice3('#skF_1')) | ~v9_lattices(k1_lattice3('#skF_1')) | ~v8_lattices(k1_lattice3('#skF_1')) | ~v6_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')))), inference(resolution, [status(thm)], [c_8274, c_26])).
% 17.90/7.34  tff(c_8699, plain, (![B_12]: (r3_lattices(k1_lattice3('#skF_1'), B_12, '#skF_2') | ~r1_lattices(k1_lattice3('#skF_1'), B_12, '#skF_2') | ~m1_subset_1(B_12, u1_struct_0(k1_lattice3('#skF_1'))) | ~v9_lattices(k1_lattice3('#skF_1')) | ~v8_lattices(k1_lattice3('#skF_1')) | ~v6_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8651])).
% 17.90/7.34  tff(c_8700, plain, (![B_12]: (r3_lattices(k1_lattice3('#skF_1'), B_12, '#skF_2') | ~r1_lattices(k1_lattice3('#skF_1'), B_12, '#skF_2') | ~m1_subset_1(B_12, u1_struct_0(k1_lattice3('#skF_1'))) | ~v9_lattices(k1_lattice3('#skF_1')) | ~v8_lattices(k1_lattice3('#skF_1')) | ~v6_lattices(k1_lattice3('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_48, c_8699])).
% 17.90/7.34  tff(c_22161, plain, (![B_12]: (r3_lattices(k1_lattice3('#skF_1'), B_12, '#skF_2') | ~r1_lattices(k1_lattice3('#skF_1'), B_12, '#skF_2') | ~m1_subset_1(B_12, u1_struct_0(k1_lattice3('#skF_1'))) | ~v9_lattices(k1_lattice3('#skF_1')) | ~v8_lattices(k1_lattice3('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_21923, c_8700])).
% 17.90/7.34  tff(c_22162, plain, (~v8_lattices(k1_lattice3('#skF_1'))), inference(splitLeft, [status(thm)], [c_22161])).
% 17.90/7.34  tff(c_22165, plain, (~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')) | ~l3_lattices(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_22162])).
% 17.90/7.34  tff(c_22168, plain, (v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_22165])).
% 17.90/7.34  tff(c_22170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_22168])).
% 17.90/7.34  tff(c_22172, plain, (v8_lattices(k1_lattice3('#skF_1'))), inference(splitRight, [status(thm)], [c_22161])).
% 17.90/7.34  tff(c_12, plain, (![A_10]: (v9_lattices(A_10) | ~v10_lattices(A_10) | v2_struct_0(A_10) | ~l3_lattices(A_10))), inference(cnfTransformation, [status(thm)], [f_68])).
% 17.90/7.34  tff(c_21922, plain, (![B_12]: (~v8_lattices(k1_lattice3('#skF_1')) | ~v9_lattices(k1_lattice3('#skF_1')) | r3_lattices(k1_lattice3('#skF_1'), B_12, '#skF_3') | ~r1_lattices(k1_lattice3('#skF_1'), B_12, '#skF_3') | ~m1_subset_1(B_12, u1_struct_0(k1_lattice3('#skF_1'))))), inference(splitRight, [status(thm)], [c_8496])).
% 17.90/7.34  tff(c_22149, plain, (~v9_lattices(k1_lattice3('#skF_1'))), inference(splitLeft, [status(thm)], [c_21922])).
% 17.90/7.34  tff(c_22152, plain, (~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')) | ~l3_lattices(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_22149])).
% 17.90/7.34  tff(c_22155, plain, (v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_22152])).
% 17.90/7.34  tff(c_22157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_22155])).
% 17.90/7.34  tff(c_22158, plain, (![B_12]: (~v8_lattices(k1_lattice3('#skF_1')) | r3_lattices(k1_lattice3('#skF_1'), B_12, '#skF_3') | ~r1_lattices(k1_lattice3('#skF_1'), B_12, '#skF_3') | ~m1_subset_1(B_12, u1_struct_0(k1_lattice3('#skF_1'))))), inference(splitRight, [status(thm)], [c_21922])).
% 17.90/7.34  tff(c_22175, plain, (![B_766]: (r3_lattices(k1_lattice3('#skF_1'), B_766, '#skF_3') | ~r1_lattices(k1_lattice3('#skF_1'), B_766, '#skF_3') | ~m1_subset_1(B_766, u1_struct_0(k1_lattice3('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_22172, c_22158])).
% 17.90/7.34  tff(c_22190, plain, (r3_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3') | ~r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_8274, c_22175])).
% 17.90/7.34  tff(c_22236, plain, (r3_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8874, c_22190])).
% 17.90/7.34  tff(c_22238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10041, c_22236])).
% 17.90/7.34  tff(c_22240, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_76])).
% 17.90/7.34  tff(c_22284, plain, (![C_783, A_784, D_785, B_786]: (C_783=A_784 | g1_orders_2(C_783, D_785)!=g1_orders_2(A_784, B_786) | ~m1_subset_1(B_786, k1_zfmisc_1(k2_zfmisc_1(A_784, A_784))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 17.90/7.34  tff(c_22418, plain, (![A_829, A_830, B_831]: (u1_struct_0(A_829)=A_830 | k3_lattice3(A_829)!=g1_orders_2(A_830, B_831) | ~m1_subset_1(B_831, k1_zfmisc_1(k2_zfmisc_1(A_830, A_830))) | ~l3_lattices(A_829) | ~v10_lattices(A_829) | v2_struct_0(A_829))), inference(superposition, [status(thm), theory('equality')], [c_30, c_22284])).
% 17.90/7.34  tff(c_22424, plain, (![A_33, A_830, B_831]: (u1_struct_0(k1_lattice3(A_33))=A_830 | k3_yellow_1(A_33)!=g1_orders_2(A_830, B_831) | ~m1_subset_1(B_831, k1_zfmisc_1(k2_zfmisc_1(A_830, A_830))) | ~l3_lattices(k1_lattice3(A_33)) | ~v10_lattices(k1_lattice3(A_33)) | v2_struct_0(k1_lattice3(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_22418])).
% 17.90/7.34  tff(c_22426, plain, (![A_33, A_830, B_831]: (u1_struct_0(k1_lattice3(A_33))=A_830 | k3_yellow_1(A_33)!=g1_orders_2(A_830, B_831) | ~m1_subset_1(B_831, k1_zfmisc_1(k2_zfmisc_1(A_830, A_830))) | v2_struct_0(k1_lattice3(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36, c_22424])).
% 17.90/7.34  tff(c_22429, plain, (![A_835, A_836, B_837]: (u1_struct_0(k1_lattice3(A_835))=A_836 | k3_yellow_1(A_835)!=g1_orders_2(A_836, B_837) | ~m1_subset_1(B_837, k1_zfmisc_1(k2_zfmisc_1(A_836, A_836))))), inference(negUnitSimplification, [status(thm)], [c_48, c_22426])).
% 17.90/7.34  tff(c_22480, plain, (![A_857, A_858]: (u1_struct_0(k1_lattice3(A_857))=u1_struct_0(A_858) | k3_yellow_1(A_857)!=k3_lattice3(A_858) | ~m1_subset_1(k2_lattice3(A_858), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_858), u1_struct_0(A_858)))) | ~l3_lattices(A_858) | ~v10_lattices(A_858) | v2_struct_0(A_858))), inference(superposition, [status(thm), theory('equality')], [c_30, c_22429])).
% 17.90/7.34  tff(c_22484, plain, (![A_859, A_860]: (u1_struct_0(k1_lattice3(A_859))=u1_struct_0(A_860) | k3_yellow_1(A_859)!=k3_lattice3(A_860) | ~l3_lattices(A_860) | ~v10_lattices(A_860) | v2_struct_0(A_860))), inference(resolution, [status(thm)], [c_38, c_22480])).
% 17.90/7.34  tff(c_22557, plain, (![A_860, A_859]: (g1_orders_2(u1_struct_0(A_860), k2_lattice3(k1_lattice3(A_859)))=k3_lattice3(k1_lattice3(A_859)) | ~l3_lattices(k1_lattice3(A_859)) | ~v10_lattices(k1_lattice3(A_859)) | v2_struct_0(k1_lattice3(A_859)) | k3_yellow_1(A_859)!=k3_lattice3(A_860) | ~l3_lattices(A_860) | ~v10_lattices(A_860) | v2_struct_0(A_860))), inference(superposition, [status(thm), theory('equality')], [c_22484, c_30])).
% 17.90/7.34  tff(c_22619, plain, (![A_860, A_859]: (g1_orders_2(u1_struct_0(A_860), k2_lattice3(k1_lattice3(A_859)))=k3_yellow_1(A_859) | v2_struct_0(k1_lattice3(A_859)) | k3_yellow_1(A_859)!=k3_lattice3(A_860) | ~l3_lattices(A_860) | ~v10_lattices(A_860) | v2_struct_0(A_860))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36, c_64, c_22557])).
% 17.90/7.34  tff(c_22620, plain, (![A_860, A_859]: (g1_orders_2(u1_struct_0(A_860), k2_lattice3(k1_lattice3(A_859)))=k3_yellow_1(A_859) | k3_yellow_1(A_859)!=k3_lattice3(A_860) | ~l3_lattices(A_860) | ~v10_lattices(A_860) | v2_struct_0(A_860))), inference(negUnitSimplification, [status(thm)], [c_48, c_22619])).
% 17.90/7.34  tff(c_22307, plain, (![A_791]: (m1_subset_1(k2_lattice3(A_791), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_791), u1_struct_0(A_791)))) | ~l3_lattices(A_791) | ~v10_lattices(A_791) | v2_struct_0(A_791))), inference(cnfTransformation, [status(thm)], [f_129])).
% 17.90/7.34  tff(c_22316, plain, (![A_792]: (l1_orders_2(g1_orders_2(u1_struct_0(A_792), k2_lattice3(A_792))) | ~l3_lattices(A_792) | ~v10_lattices(A_792) | v2_struct_0(A_792))), inference(resolution, [status(thm)], [c_22307, c_4])).
% 17.90/7.34  tff(c_22325, plain, (![A_797]: (l1_orders_2(k3_lattice3(A_797)) | ~l3_lattices(A_797) | ~v10_lattices(A_797) | v2_struct_0(A_797) | ~l3_lattices(A_797) | ~v10_lattices(A_797) | v2_struct_0(A_797))), inference(superposition, [status(thm), theory('equality')], [c_30, c_22316])).
% 17.90/7.34  tff(c_22328, plain, (![A_33]: (l1_orders_2(k3_yellow_1(A_33)) | ~l3_lattices(k1_lattice3(A_33)) | ~v10_lattices(k1_lattice3(A_33)) | v2_struct_0(k1_lattice3(A_33)) | ~l3_lattices(k1_lattice3(A_33)) | ~v10_lattices(k1_lattice3(A_33)) | v2_struct_0(k1_lattice3(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_22325])).
% 17.90/7.34  tff(c_22330, plain, (![A_33]: (l1_orders_2(k3_yellow_1(A_33)) | v2_struct_0(k1_lattice3(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36, c_54, c_36, c_22328])).
% 17.90/7.34  tff(c_22331, plain, (![A_33]: (l1_orders_2(k3_yellow_1(A_33)))), inference(negUnitSimplification, [status(thm)], [c_48, c_22330])).
% 17.90/7.34  tff(c_22315, plain, (![A_791]: (v1_orders_2(g1_orders_2(u1_struct_0(A_791), k2_lattice3(A_791))) | ~l3_lattices(A_791) | ~v10_lattices(A_791) | v2_struct_0(A_791))), inference(resolution, [status(thm)], [c_22307, c_6])).
% 17.90/7.34  tff(c_22527, plain, (![A_860, A_859]: (v1_orders_2(g1_orders_2(u1_struct_0(A_860), k2_lattice3(k1_lattice3(A_859)))) | ~l3_lattices(k1_lattice3(A_859)) | ~v10_lattices(k1_lattice3(A_859)) | v2_struct_0(k1_lattice3(A_859)) | k3_yellow_1(A_859)!=k3_lattice3(A_860) | ~l3_lattices(A_860) | ~v10_lattices(A_860) | v2_struct_0(A_860))), inference(superposition, [status(thm), theory('equality')], [c_22484, c_22315])).
% 17.90/7.34  tff(c_22604, plain, (![A_860, A_859]: (v1_orders_2(g1_orders_2(u1_struct_0(A_860), k2_lattice3(k1_lattice3(A_859)))) | v2_struct_0(k1_lattice3(A_859)) | k3_yellow_1(A_859)!=k3_lattice3(A_860) | ~l3_lattices(A_860) | ~v10_lattices(A_860) | v2_struct_0(A_860))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36, c_22527])).
% 17.90/7.34  tff(c_22605, plain, (![A_860, A_859]: (v1_orders_2(g1_orders_2(u1_struct_0(A_860), k2_lattice3(k1_lattice3(A_859)))) | k3_yellow_1(A_859)!=k3_lattice3(A_860) | ~l3_lattices(A_860) | ~v10_lattices(A_860) | v2_struct_0(A_860))), inference(negUnitSimplification, [status(thm)], [c_48, c_22604])).
% 17.90/7.34  tff(c_22290, plain, (![A_1, A_784, B_786]: (u1_struct_0(A_1)=A_784 | g1_orders_2(A_784, B_786)!=A_1 | ~m1_subset_1(B_786, k1_zfmisc_1(k2_zfmisc_1(A_784, A_784))) | ~v1_orders_2(A_1) | ~l1_orders_2(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_22284])).
% 17.90/7.34  tff(c_22369, plain, (![A_812, B_813]: (u1_struct_0(g1_orders_2(A_812, B_813))=A_812 | ~m1_subset_1(B_813, k1_zfmisc_1(k2_zfmisc_1(A_812, A_812))) | ~v1_orders_2(g1_orders_2(A_812, B_813)) | ~l1_orders_2(g1_orders_2(A_812, B_813)))), inference(reflexivity, [status(thm), theory('equality')], [c_22290])).
% 17.90/7.34  tff(c_27964, plain, (![A_1121]: (u1_struct_0(g1_orders_2(u1_struct_0(A_1121), k2_lattice3(A_1121)))=u1_struct_0(A_1121) | ~v1_orders_2(g1_orders_2(u1_struct_0(A_1121), k2_lattice3(A_1121))) | ~l1_orders_2(g1_orders_2(u1_struct_0(A_1121), k2_lattice3(A_1121))) | ~l3_lattices(A_1121) | ~v10_lattices(A_1121) | v2_struct_0(A_1121))), inference(resolution, [status(thm)], [c_38, c_22369])).
% 17.90/7.34  tff(c_28009, plain, (![A_859]: (u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_859)), k2_lattice3(k1_lattice3(A_859))))=u1_struct_0(k1_lattice3(A_859)) | ~l1_orders_2(g1_orders_2(u1_struct_0(k1_lattice3(A_859)), k2_lattice3(k1_lattice3(A_859)))) | k3_lattice3(k1_lattice3(A_859))!=k3_yellow_1(A_859) | ~l3_lattices(k1_lattice3(A_859)) | ~v10_lattices(k1_lattice3(A_859)) | v2_struct_0(k1_lattice3(A_859)))), inference(resolution, [status(thm)], [c_22605, c_27964])).
% 17.90/7.34  tff(c_28057, plain, (![A_859]: (u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_859)), k2_lattice3(k1_lattice3(A_859))))=u1_struct_0(k1_lattice3(A_859)) | ~l1_orders_2(g1_orders_2(u1_struct_0(k1_lattice3(A_859)), k2_lattice3(k1_lattice3(A_859)))) | v2_struct_0(k1_lattice3(A_859)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36, c_64, c_28009])).
% 17.90/7.34  tff(c_30958, plain, (![A_1208]: (u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_1208)), k2_lattice3(k1_lattice3(A_1208))))=u1_struct_0(k1_lattice3(A_1208)) | ~l1_orders_2(g1_orders_2(u1_struct_0(k1_lattice3(A_1208)), k2_lattice3(k1_lattice3(A_1208)))))), inference(negUnitSimplification, [status(thm)], [c_48, c_28057])).
% 17.90/7.34  tff(c_30987, plain, (![A_859]: (u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_859)), k2_lattice3(k1_lattice3(A_859))))=u1_struct_0(k1_lattice3(A_859)) | ~l1_orders_2(k3_yellow_1(A_859)) | k3_lattice3(k1_lattice3(A_859))!=k3_yellow_1(A_859) | ~l3_lattices(k1_lattice3(A_859)) | ~v10_lattices(k1_lattice3(A_859)) | v2_struct_0(k1_lattice3(A_859)))), inference(superposition, [status(thm), theory('equality')], [c_22620, c_30958])).
% 17.90/7.34  tff(c_31031, plain, (![A_859]: (u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_859)), k2_lattice3(k1_lattice3(A_859))))=u1_struct_0(k1_lattice3(A_859)) | v2_struct_0(k1_lattice3(A_859)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36, c_64, c_22331, c_30987])).
% 17.90/7.34  tff(c_31052, plain, (![A_1209]: (u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(A_1209)), k2_lattice3(k1_lattice3(A_1209))))=u1_struct_0(k1_lattice3(A_1209)))), inference(negUnitSimplification, [status(thm)], [c_48, c_31031])).
% 17.90/7.34  tff(c_31223, plain, (![A_859]: (u1_struct_0(k3_yellow_1(A_859))=u1_struct_0(k1_lattice3(A_859)) | k3_lattice3(k1_lattice3(A_859))!=k3_yellow_1(A_859) | ~l3_lattices(k1_lattice3(A_859)) | ~v10_lattices(k1_lattice3(A_859)) | v2_struct_0(k1_lattice3(A_859)))), inference(superposition, [status(thm), theory('equality')], [c_22620, c_31052])).
% 17.90/7.34  tff(c_31285, plain, (![A_859]: (u1_struct_0(k3_yellow_1(A_859))=u1_struct_0(k1_lattice3(A_859)) | v2_struct_0(k1_lattice3(A_859)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36, c_64, c_31223])).
% 17.90/7.34  tff(c_31286, plain, (![A_859]: (u1_struct_0(k3_yellow_1(A_859))=u1_struct_0(k1_lattice3(A_859)))), inference(negUnitSimplification, [status(thm)], [c_48, c_31285])).
% 17.90/7.34  tff(c_31333, plain, (m1_subset_1('#skF_2', u1_struct_0(k1_lattice3('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_31286, c_68])).
% 17.90/7.34  tff(c_31332, plain, (m1_subset_1('#skF_3', u1_struct_0(k1_lattice3('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_31286, c_66])).
% 17.90/7.34  tff(c_22239, plain, (r3_orders_2(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_76])).
% 17.90/7.34  tff(c_31594, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_2')='#skF_2' | ~l3_lattices(k1_lattice3('#skF_1')) | ~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_31333, c_32])).
% 17.90/7.34  tff(c_31632, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_2')='#skF_2' | v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36, c_31594])).
% 17.90/7.34  tff(c_31633, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_48, c_31632])).
% 17.90/7.34  tff(c_31524, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_3')='#skF_3' | ~l3_lattices(k1_lattice3('#skF_1')) | ~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_31332, c_32])).
% 17.90/7.34  tff(c_31562, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_3')='#skF_3' | v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36, c_31524])).
% 17.90/7.34  tff(c_31563, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_48, c_31562])).
% 17.90/7.34  tff(c_22473, plain, (![A_854, B_855, C_856]: (r3_lattices(A_854, B_855, C_856) | ~r3_orders_2(k3_lattice3(A_854), k4_lattice3(A_854, B_855), k4_lattice3(A_854, C_856)) | ~m1_subset_1(C_856, u1_struct_0(A_854)) | ~m1_subset_1(B_855, u1_struct_0(A_854)) | ~l3_lattices(A_854) | ~v10_lattices(A_854) | v2_struct_0(A_854))), inference(cnfTransformation, [status(thm)], [f_164])).
% 17.90/7.34  tff(c_22476, plain, (![A_33, B_855, C_856]: (r3_lattices(k1_lattice3(A_33), B_855, C_856) | ~r3_orders_2(k3_yellow_1(A_33), k4_lattice3(k1_lattice3(A_33), B_855), k4_lattice3(k1_lattice3(A_33), C_856)) | ~m1_subset_1(C_856, u1_struct_0(k1_lattice3(A_33))) | ~m1_subset_1(B_855, u1_struct_0(k1_lattice3(A_33))) | ~l3_lattices(k1_lattice3(A_33)) | ~v10_lattices(k1_lattice3(A_33)) | v2_struct_0(k1_lattice3(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_22473])).
% 17.90/7.34  tff(c_22478, plain, (![A_33, B_855, C_856]: (r3_lattices(k1_lattice3(A_33), B_855, C_856) | ~r3_orders_2(k3_yellow_1(A_33), k4_lattice3(k1_lattice3(A_33), B_855), k4_lattice3(k1_lattice3(A_33), C_856)) | ~m1_subset_1(C_856, u1_struct_0(k1_lattice3(A_33))) | ~m1_subset_1(B_855, u1_struct_0(k1_lattice3(A_33))) | v2_struct_0(k1_lattice3(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36, c_22476])).
% 17.90/7.34  tff(c_22479, plain, (![A_33, B_855, C_856]: (r3_lattices(k1_lattice3(A_33), B_855, C_856) | ~r3_orders_2(k3_yellow_1(A_33), k4_lattice3(k1_lattice3(A_33), B_855), k4_lattice3(k1_lattice3(A_33), C_856)) | ~m1_subset_1(C_856, u1_struct_0(k1_lattice3(A_33))) | ~m1_subset_1(B_855, u1_struct_0(k1_lattice3(A_33))))), inference(negUnitSimplification, [status(thm)], [c_48, c_22478])).
% 17.90/7.34  tff(c_31652, plain, (![B_855]: (r3_lattices(k1_lattice3('#skF_1'), B_855, '#skF_3') | ~r3_orders_2(k3_yellow_1('#skF_1'), k4_lattice3(k1_lattice3('#skF_1'), B_855), '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0(k1_lattice3('#skF_1'))) | ~m1_subset_1(B_855, u1_struct_0(k1_lattice3('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_31563, c_22479])).
% 17.90/7.34  tff(c_32916, plain, (![B_1229]: (r3_lattices(k1_lattice3('#skF_1'), B_1229, '#skF_3') | ~r3_orders_2(k3_yellow_1('#skF_1'), k4_lattice3(k1_lattice3('#skF_1'), B_1229), '#skF_3') | ~m1_subset_1(B_1229, u1_struct_0(k1_lattice3('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_31332, c_31652])).
% 17.90/7.34  tff(c_32919, plain, (r3_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3') | ~r3_orders_2(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3') | ~m1_subset_1('#skF_2', u1_struct_0(k1_lattice3('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_31633, c_32916])).
% 17.90/7.34  tff(c_32932, plain, (r3_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31333, c_22239, c_32919])).
% 17.90/7.34  tff(c_28, plain, (![A_11, B_12, C_13]: (r1_lattices(A_11, B_12, C_13) | ~r3_lattices(A_11, B_12, C_13) | ~m1_subset_1(C_13, u1_struct_0(A_11)) | ~m1_subset_1(B_12, u1_struct_0(A_11)) | ~l3_lattices(A_11) | ~v9_lattices(A_11) | ~v8_lattices(A_11) | ~v6_lattices(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_87])).
% 17.90/7.34  tff(c_32948, plain, (r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0(k1_lattice3('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0(k1_lattice3('#skF_1'))) | ~l3_lattices(k1_lattice3('#skF_1')) | ~v9_lattices(k1_lattice3('#skF_1')) | ~v8_lattices(k1_lattice3('#skF_1')) | ~v6_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_32932, c_28])).
% 17.90/7.34  tff(c_32951, plain, (r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3') | ~v9_lattices(k1_lattice3('#skF_1')) | ~v8_lattices(k1_lattice3('#skF_1')) | ~v6_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_31333, c_31332, c_32948])).
% 17.90/7.34  tff(c_32952, plain, (r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3') | ~v9_lattices(k1_lattice3('#skF_1')) | ~v8_lattices(k1_lattice3('#skF_1')) | ~v6_lattices(k1_lattice3('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_48, c_32951])).
% 17.90/7.34  tff(c_32955, plain, (~v6_lattices(k1_lattice3('#skF_1'))), inference(splitLeft, [status(thm)], [c_32952])).
% 17.90/7.34  tff(c_32958, plain, (~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')) | ~l3_lattices(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_32955])).
% 17.90/7.34  tff(c_32961, plain, (v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_32958])).
% 17.90/7.34  tff(c_32963, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_32961])).
% 17.90/7.34  tff(c_32964, plain, (~v8_lattices(k1_lattice3('#skF_1')) | ~v9_lattices(k1_lattice3('#skF_1')) | r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_32952])).
% 17.90/7.34  tff(c_33053, plain, (~v9_lattices(k1_lattice3('#skF_1'))), inference(splitLeft, [status(thm)], [c_32964])).
% 17.90/7.34  tff(c_33056, plain, (~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')) | ~l3_lattices(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_33053])).
% 17.90/7.34  tff(c_33059, plain, (v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_33056])).
% 17.90/7.34  tff(c_33061, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_33059])).
% 17.90/7.34  tff(c_33062, plain, (~v8_lattices(k1_lattice3('#skF_1')) | r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_32964])).
% 17.90/7.34  tff(c_33064, plain, (~v8_lattices(k1_lattice3('#skF_1'))), inference(splitLeft, [status(thm)], [c_33062])).
% 17.90/7.34  tff(c_33067, plain, (~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')) | ~l3_lattices(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_33064])).
% 17.90/7.34  tff(c_33070, plain, (v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_33067])).
% 17.90/7.34  tff(c_33072, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_33070])).
% 17.90/7.34  tff(c_33073, plain, (r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_33062])).
% 17.90/7.34  tff(c_58, plain, (![B_23, C_25, A_22]: (r1_tarski(B_23, C_25) | ~r1_lattices(k1_lattice3(A_22), B_23, C_25) | ~m1_subset_1(C_25, u1_struct_0(k1_lattice3(A_22))) | ~m1_subset_1(B_23, u1_struct_0(k1_lattice3(A_22))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 17.90/7.34  tff(c_33184, plain, (r1_tarski('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0(k1_lattice3('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0(k1_lattice3('#skF_1')))), inference(resolution, [status(thm)], [c_33073, c_58])).
% 17.90/7.34  tff(c_33187, plain, (r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31333, c_31332, c_33184])).
% 17.90/7.34  tff(c_33189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22240, c_33187])).
% 17.90/7.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.90/7.34  
% 17.90/7.34  Inference rules
% 17.90/7.34  ----------------------
% 17.90/7.34  #Ref     : 136
% 17.90/7.34  #Sup     : 8326
% 17.90/7.34  #Fact    : 4
% 17.90/7.34  #Define  : 0
% 17.90/7.34  #Split   : 21
% 17.90/7.34  #Chain   : 0
% 17.90/7.34  #Close   : 0
% 17.90/7.34  
% 17.90/7.34  Ordering : KBO
% 17.90/7.34  
% 17.90/7.34  Simplification rules
% 17.90/7.34  ----------------------
% 17.90/7.34  #Subsume      : 2105
% 17.90/7.34  #Demod        : 10608
% 17.90/7.34  #Tautology    : 938
% 17.90/7.34  #SimpNegUnit  : 1941
% 17.90/7.34  #BackRed      : 112
% 17.90/7.34  
% 17.90/7.34  #Partial instantiations: 0
% 17.90/7.34  #Strategies tried      : 1
% 17.90/7.34  
% 17.90/7.34  Timing (in seconds)
% 17.90/7.34  ----------------------
% 18.17/7.34  Preprocessing        : 0.35
% 18.17/7.34  Parsing              : 0.19
% 18.17/7.34  CNF conversion       : 0.03
% 18.17/7.34  Main loop            : 6.19
% 18.17/7.34  Inferencing          : 1.45
% 18.17/7.34  Reduction            : 1.94
% 18.17/7.34  Demodulation         : 1.35
% 18.17/7.34  BG Simplification    : 0.26
% 18.17/7.34  Subsumption          : 2.13
% 18.17/7.34  Abstraction          : 0.34
% 18.17/7.34  MUC search           : 0.00
% 18.17/7.34  Cooper               : 0.00
% 18.17/7.34  Total                : 6.61
% 18.17/7.34  Index Insertion      : 0.00
% 18.17/7.34  Index Deletion       : 0.00
% 18.17/7.34  Index Matching       : 0.00
% 18.17/7.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
