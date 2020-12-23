%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:28 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 365 expanded)
%              Number of leaves         :   53 ( 151 expanded)
%              Depth                    :   10
%              Number of atoms          :  225 ( 596 expanded)
%              Number of equality atoms :   45 ( 276 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v3_lattices > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > v10_lattices > l3_lattices > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k3_yellow_1 > k3_lattice3 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > k1_lattice3 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k13_lattice3,type,(
    k13_lattice3: ( $i * $i * $i ) > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k10_lattice3,type,(
    k10_lattice3: ( $i * $i * $i ) > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_lattices,type,(
    v3_lattices: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_154,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
       => ! [C] :
            ( m1_subset_1(C,u1_struct_0(k3_yellow_1(A)))
           => ( k13_lattice3(k3_yellow_1(A),B,C) = k2_xboole_0(B,C)
              & k12_lattice3(k3_yellow_1(A),B,C) = k3_xboole_0(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_1)).

tff(f_118,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_116,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
     => ! [C] :
          ( m1_subset_1(C,u1_struct_0(k3_yellow_1(A)))
         => ( r2_hidden(k3_xboole_0(B,C),k9_setfam_1(A))
            & r2_hidden(k2_xboole_0(B,C),k9_setfam_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l19_yellow_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_131,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r2_hidden(k2_xboole_0(B,C),A)
               => k10_lattice3(k2_yellow_1(A),B,C) = k2_xboole_0(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_yellow_1)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k1_lattice3(A))
      & v3_lattices(k1_lattice3(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_lattice3)).

tff(f_46,axiom,(
    ! [A] :
      ( v3_lattices(k1_lattice3(A))
      & v10_lattices(k1_lattice3(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_lattice3)).

tff(f_37,axiom,(
    ! [A] :
      ( v3_lattices(k1_lattice3(A))
      & l3_lattices(k1_lattice3(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattice3)).

tff(f_72,axiom,(
    ! [A] : k3_yellow_1(A) = k3_lattice3(k1_lattice3(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ( v1_orders_2(k3_lattice3(A))
        & v3_orders_2(k3_lattice3(A))
        & v4_orders_2(k3_lattice3(A))
        & v5_orders_2(k3_lattice3(A))
        & v1_lattice3(k3_lattice3(A))
        & v2_lattice3(k3_lattice3(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_yellow_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_144,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r2_hidden(k3_xboole_0(B,C),A)
               => k11_lattice3(k2_yellow_1(A),B,C) = k3_xboole_0(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(c_64,plain,
    ( k12_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') != k3_xboole_0('#skF_3','#skF_4')
    | k13_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') != k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_139,plain,(
    k13_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') != k2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_102,plain,(
    ! [A_54] : k2_yellow_1(k9_setfam_1(A_54)) = k3_yellow_1(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_54,plain,(
    ! [A_24] : u1_struct_0(k2_yellow_1(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_108,plain,(
    ! [A_54] : u1_struct_0(k3_yellow_1(A_54)) = k9_setfam_1(A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_54])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k3_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_142,plain,(
    m1_subset_1('#skF_3',k9_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_68])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k3_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_143,plain,(
    m1_subset_1('#skF_4',k9_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_66])).

tff(c_50,plain,(
    ! [B_21,C_23,A_20] :
      ( r2_hidden(k2_xboole_0(B_21,C_23),k9_setfam_1(A_20))
      | ~ m1_subset_1(C_23,u1_struct_0(k3_yellow_1(A_20)))
      | ~ m1_subset_1(B_21,u1_struct_0(k3_yellow_1(A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_221,plain,(
    ! [B_74,C_75,A_76] :
      ( r2_hidden(k2_xboole_0(B_74,C_75),k9_setfam_1(A_76))
      | ~ m1_subset_1(C_75,k9_setfam_1(A_76))
      | ~ m1_subset_1(B_74,k9_setfam_1(A_76)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_108,c_50])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_226,plain,(
    ! [A_77,C_78,B_79] :
      ( ~ v1_xboole_0(k9_setfam_1(A_77))
      | ~ m1_subset_1(C_78,k9_setfam_1(A_77))
      | ~ m1_subset_1(B_79,k9_setfam_1(A_77)) ) ),
    inference(resolution,[status(thm)],[c_221,c_2])).

tff(c_231,plain,(
    ! [B_79] :
      ( ~ v1_xboole_0(k9_setfam_1('#skF_2'))
      | ~ m1_subset_1(B_79,k9_setfam_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_143,c_226])).

tff(c_233,plain,(
    ~ v1_xboole_0(k9_setfam_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_58,plain,(
    ! [A_25] : k2_yellow_1(k9_setfam_1(A_25)) = k3_yellow_1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_220,plain,(
    ! [B_21,C_23,A_20] :
      ( r2_hidden(k2_xboole_0(B_21,C_23),k9_setfam_1(A_20))
      | ~ m1_subset_1(C_23,k9_setfam_1(A_20))
      | ~ m1_subset_1(B_21,k9_setfam_1(A_20)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_108,c_50])).

tff(c_60,plain,(
    ! [A_26,B_30,C_32] :
      ( k10_lattice3(k2_yellow_1(A_26),B_30,C_32) = k2_xboole_0(B_30,C_32)
      | ~ r2_hidden(k2_xboole_0(B_30,C_32),A_26)
      | ~ m1_subset_1(C_32,u1_struct_0(k2_yellow_1(A_26)))
      | ~ m1_subset_1(B_30,u1_struct_0(k2_yellow_1(A_26)))
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_257,plain,(
    ! [A_89,B_90,C_91] :
      ( k10_lattice3(k2_yellow_1(A_89),B_90,C_91) = k2_xboole_0(B_90,C_91)
      | ~ r2_hidden(k2_xboole_0(B_90,C_91),A_89)
      | ~ m1_subset_1(C_91,A_89)
      | ~ m1_subset_1(B_90,A_89)
      | v1_xboole_0(A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_60])).

tff(c_260,plain,(
    ! [A_20,B_21,C_23] :
      ( k10_lattice3(k2_yellow_1(k9_setfam_1(A_20)),B_21,C_23) = k2_xboole_0(B_21,C_23)
      | v1_xboole_0(k9_setfam_1(A_20))
      | ~ m1_subset_1(C_23,k9_setfam_1(A_20))
      | ~ m1_subset_1(B_21,k9_setfam_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_220,c_257])).

tff(c_297,plain,(
    ! [A_94,B_95,C_96] :
      ( k10_lattice3(k3_yellow_1(A_94),B_95,C_96) = k2_xboole_0(B_95,C_96)
      | v1_xboole_0(k9_setfam_1(A_94))
      | ~ m1_subset_1(C_96,k9_setfam_1(A_94))
      | ~ m1_subset_1(B_95,k9_setfam_1(A_94)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_260])).

tff(c_299,plain,(
    ! [B_95] :
      ( k10_lattice3(k3_yellow_1('#skF_2'),B_95,'#skF_4') = k2_xboole_0(B_95,'#skF_4')
      | v1_xboole_0(k9_setfam_1('#skF_2'))
      | ~ m1_subset_1(B_95,k9_setfam_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_143,c_297])).

tff(c_308,plain,(
    ! [B_97] :
      ( k10_lattice3(k3_yellow_1('#skF_2'),B_97,'#skF_4') = k2_xboole_0(B_97,'#skF_4')
      | ~ m1_subset_1(B_97,k9_setfam_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_299])).

tff(c_316,plain,(
    k10_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_142,c_308])).

tff(c_48,plain,(
    ! [A_19] : v5_orders_2(k2_yellow_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_118,plain,(
    ! [A_54] : v5_orders_2(k3_yellow_1(A_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_48])).

tff(c_12,plain,(
    ! [A_8] : ~ v2_struct_0(k1_lattice3(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18,plain,(
    ! [A_9] : v10_lattices(k1_lattice3(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_7] : l3_lattices(k1_lattice3(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [A_16] : k3_lattice3(k1_lattice3(A_16)) = k3_yellow_1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_176,plain,(
    ! [A_66] :
      ( v1_lattice3(k3_lattice3(A_66))
      | ~ l3_lattices(A_66)
      | ~ v10_lattices(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_179,plain,(
    ! [A_16] :
      ( v1_lattice3(k3_yellow_1(A_16))
      | ~ l3_lattices(k1_lattice3(A_16))
      | ~ v10_lattices(k1_lattice3(A_16))
      | v2_struct_0(k1_lattice3(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_176])).

tff(c_181,plain,(
    ! [A_16] :
      ( v1_lattice3(k3_yellow_1(A_16))
      | v2_struct_0(k1_lattice3(A_16)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_10,c_179])).

tff(c_182,plain,(
    ! [A_16] : v1_lattice3(k3_yellow_1(A_16)) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_181])).

tff(c_28,plain,(
    ! [A_17] : l1_orders_2(k2_yellow_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_116,plain,(
    ! [A_54] : l1_orders_2(k3_yellow_1(A_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_28])).

tff(c_388,plain,(
    ! [A_107,B_108,C_109] :
      ( k13_lattice3(A_107,B_108,C_109) = k10_lattice3(A_107,B_108,C_109)
      | ~ m1_subset_1(C_109,u1_struct_0(A_107))
      | ~ m1_subset_1(B_108,u1_struct_0(A_107))
      | ~ l1_orders_2(A_107)
      | ~ v1_lattice3(A_107)
      | ~ v5_orders_2(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_390,plain,(
    ! [A_54,B_108,C_109] :
      ( k13_lattice3(k3_yellow_1(A_54),B_108,C_109) = k10_lattice3(k3_yellow_1(A_54),B_108,C_109)
      | ~ m1_subset_1(C_109,k9_setfam_1(A_54))
      | ~ m1_subset_1(B_108,u1_struct_0(k3_yellow_1(A_54)))
      | ~ l1_orders_2(k3_yellow_1(A_54))
      | ~ v1_lattice3(k3_yellow_1(A_54))
      | ~ v5_orders_2(k3_yellow_1(A_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_388])).

tff(c_405,plain,(
    ! [A_110,B_111,C_112] :
      ( k13_lattice3(k3_yellow_1(A_110),B_111,C_112) = k10_lattice3(k3_yellow_1(A_110),B_111,C_112)
      | ~ m1_subset_1(C_112,k9_setfam_1(A_110))
      | ~ m1_subset_1(B_111,k9_setfam_1(A_110)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_182,c_116,c_108,c_390])).

tff(c_412,plain,(
    ! [B_113] :
      ( k13_lattice3(k3_yellow_1('#skF_2'),B_113,'#skF_4') = k10_lattice3(k3_yellow_1('#skF_2'),B_113,'#skF_4')
      | ~ m1_subset_1(B_113,k9_setfam_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_143,c_405])).

tff(c_418,plain,(
    k13_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') = k10_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_142,c_412])).

tff(c_422,plain,(
    k13_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_418])).

tff(c_424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_422])).

tff(c_425,plain,(
    ! [B_79] : ~ m1_subset_1(B_79,k9_setfam_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_425,c_143])).

tff(c_430,plain,(
    k12_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') != k3_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_434,plain,(
    m1_subset_1('#skF_3',k9_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_68])).

tff(c_435,plain,(
    m1_subset_1('#skF_4',k9_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_66])).

tff(c_516,plain,(
    ! [B_128,C_129,A_130] :
      ( r2_hidden(k2_xboole_0(B_128,C_129),k9_setfam_1(A_130))
      | ~ m1_subset_1(C_129,k9_setfam_1(A_130))
      | ~ m1_subset_1(B_128,k9_setfam_1(A_130)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_108,c_50])).

tff(c_522,plain,(
    ! [A_132,C_133,B_134] :
      ( ~ v1_xboole_0(k9_setfam_1(A_132))
      | ~ m1_subset_1(C_133,k9_setfam_1(A_132))
      | ~ m1_subset_1(B_134,k9_setfam_1(A_132)) ) ),
    inference(resolution,[status(thm)],[c_516,c_2])).

tff(c_527,plain,(
    ! [B_134] :
      ( ~ v1_xboole_0(k9_setfam_1('#skF_2'))
      | ~ m1_subset_1(B_134,k9_setfam_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_435,c_522])).

tff(c_529,plain,(
    ~ v1_xboole_0(k9_setfam_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_527])).

tff(c_52,plain,(
    ! [B_21,C_23,A_20] :
      ( r2_hidden(k3_xboole_0(B_21,C_23),k9_setfam_1(A_20))
      | ~ m1_subset_1(C_23,u1_struct_0(k3_yellow_1(A_20)))
      | ~ m1_subset_1(B_21,u1_struct_0(k3_yellow_1(A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_530,plain,(
    ! [B_21,C_23,A_20] :
      ( r2_hidden(k3_xboole_0(B_21,C_23),k9_setfam_1(A_20))
      | ~ m1_subset_1(C_23,k9_setfam_1(A_20))
      | ~ m1_subset_1(B_21,k9_setfam_1(A_20)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_108,c_52])).

tff(c_62,plain,(
    ! [A_33,B_37,C_39] :
      ( k11_lattice3(k2_yellow_1(A_33),B_37,C_39) = k3_xboole_0(B_37,C_39)
      | ~ r2_hidden(k3_xboole_0(B_37,C_39),A_33)
      | ~ m1_subset_1(C_39,u1_struct_0(k2_yellow_1(A_33)))
      | ~ m1_subset_1(B_37,u1_struct_0(k2_yellow_1(A_33)))
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_536,plain,(
    ! [A_138,B_139,C_140] :
      ( k11_lattice3(k2_yellow_1(A_138),B_139,C_140) = k3_xboole_0(B_139,C_140)
      | ~ r2_hidden(k3_xboole_0(B_139,C_140),A_138)
      | ~ m1_subset_1(C_140,A_138)
      | ~ m1_subset_1(B_139,A_138)
      | v1_xboole_0(A_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_62])).

tff(c_539,plain,(
    ! [A_20,B_21,C_23] :
      ( k11_lattice3(k2_yellow_1(k9_setfam_1(A_20)),B_21,C_23) = k3_xboole_0(B_21,C_23)
      | v1_xboole_0(k9_setfam_1(A_20))
      | ~ m1_subset_1(C_23,k9_setfam_1(A_20))
      | ~ m1_subset_1(B_21,k9_setfam_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_530,c_536])).

tff(c_542,plain,(
    ! [A_141,B_142,C_143] :
      ( k11_lattice3(k3_yellow_1(A_141),B_142,C_143) = k3_xboole_0(B_142,C_143)
      | v1_xboole_0(k9_setfam_1(A_141))
      | ~ m1_subset_1(C_143,k9_setfam_1(A_141))
      | ~ m1_subset_1(B_142,k9_setfam_1(A_141)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_539])).

tff(c_544,plain,(
    ! [B_142] :
      ( k11_lattice3(k3_yellow_1('#skF_2'),B_142,'#skF_4') = k3_xboole_0(B_142,'#skF_4')
      | v1_xboole_0(k9_setfam_1('#skF_2'))
      | ~ m1_subset_1(B_142,k9_setfam_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_435,c_542])).

tff(c_553,plain,(
    ! [B_144] :
      ( k11_lattice3(k3_yellow_1('#skF_2'),B_144,'#skF_4') = k3_xboole_0(B_144,'#skF_4')
      | ~ m1_subset_1(B_144,k9_setfam_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_529,c_544])).

tff(c_561,plain,(
    k11_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_434,c_553])).

tff(c_508,plain,(
    ! [A_127] :
      ( v2_lattice3(k3_lattice3(A_127))
      | ~ l3_lattices(A_127)
      | ~ v10_lattices(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_511,plain,(
    ! [A_16] :
      ( v2_lattice3(k3_yellow_1(A_16))
      | ~ l3_lattices(k1_lattice3(A_16))
      | ~ v10_lattices(k1_lattice3(A_16))
      | v2_struct_0(k1_lattice3(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_508])).

tff(c_513,plain,(
    ! [A_16] :
      ( v2_lattice3(k3_yellow_1(A_16))
      | v2_struct_0(k1_lattice3(A_16)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_10,c_511])).

tff(c_514,plain,(
    ! [A_16] : v2_lattice3(k3_yellow_1(A_16)) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_513])).

tff(c_660,plain,(
    ! [A_163,B_164,C_165] :
      ( k12_lattice3(A_163,B_164,C_165) = k11_lattice3(A_163,B_164,C_165)
      | ~ m1_subset_1(C_165,u1_struct_0(A_163))
      | ~ m1_subset_1(B_164,u1_struct_0(A_163))
      | ~ l1_orders_2(A_163)
      | ~ v2_lattice3(A_163)
      | ~ v5_orders_2(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_662,plain,(
    ! [A_54,B_164,C_165] :
      ( k12_lattice3(k3_yellow_1(A_54),B_164,C_165) = k11_lattice3(k3_yellow_1(A_54),B_164,C_165)
      | ~ m1_subset_1(C_165,k9_setfam_1(A_54))
      | ~ m1_subset_1(B_164,u1_struct_0(k3_yellow_1(A_54)))
      | ~ l1_orders_2(k3_yellow_1(A_54))
      | ~ v2_lattice3(k3_yellow_1(A_54))
      | ~ v5_orders_2(k3_yellow_1(A_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_660])).

tff(c_715,plain,(
    ! [A_168,B_169,C_170] :
      ( k12_lattice3(k3_yellow_1(A_168),B_169,C_170) = k11_lattice3(k3_yellow_1(A_168),B_169,C_170)
      | ~ m1_subset_1(C_170,k9_setfam_1(A_168))
      | ~ m1_subset_1(B_169,k9_setfam_1(A_168)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_514,c_116,c_108,c_662])).

tff(c_727,plain,(
    ! [B_174] :
      ( k12_lattice3(k3_yellow_1('#skF_2'),B_174,'#skF_4') = k11_lattice3(k3_yellow_1('#skF_2'),B_174,'#skF_4')
      | ~ m1_subset_1(B_174,k9_setfam_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_435,c_715])).

tff(c_733,plain,(
    k12_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') = k11_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_434,c_727])).

tff(c_737,plain,(
    k12_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_561,c_733])).

tff(c_739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_430,c_737])).

tff(c_740,plain,(
    ! [B_134] : ~ m1_subset_1(B_134,k9_setfam_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_527])).

tff(c_744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_740,c_435])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:20:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.60  
% 3.38/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.60  %$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v3_lattices > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > v10_lattices > l3_lattices > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k3_yellow_1 > k3_lattice3 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > k1_lattice3 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.38/1.60  
% 3.38/1.60  %Foreground sorts:
% 3.38/1.60  
% 3.38/1.60  
% 3.38/1.60  %Background operators:
% 3.38/1.60  
% 3.38/1.60  
% 3.38/1.60  %Foreground operators:
% 3.38/1.60  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.38/1.60  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.38/1.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.38/1.60  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.38/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.60  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.38/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.60  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 3.38/1.60  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.38/1.60  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.38/1.60  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 3.38/1.60  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.38/1.60  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 3.38/1.60  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 3.38/1.60  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 3.38/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.38/1.60  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 3.38/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.38/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.38/1.60  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.38/1.60  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.38/1.60  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.38/1.60  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.38/1.60  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.38/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.38/1.60  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.38/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.60  tff(v3_lattices, type, v3_lattices: $i > $o).
% 3.38/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.38/1.60  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 3.38/1.60  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.38/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.38/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.38/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.38/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.38/1.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.38/1.60  
% 3.38/1.62  tff(f_154, negated_conjecture, ~(![A, B]: (m1_subset_1(B, u1_struct_0(k3_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k3_yellow_1(A))) => ((k13_lattice3(k3_yellow_1(A), B, C) = k2_xboole_0(B, C)) & (k12_lattice3(k3_yellow_1(A), B, C) = k3_xboole_0(B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_yellow_1)).
% 3.38/1.62  tff(f_118, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 3.38/1.62  tff(f_116, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.38/1.62  tff(f_112, axiom, (![A, B]: (m1_subset_1(B, u1_struct_0(k3_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k3_yellow_1(A))) => (r2_hidden(k3_xboole_0(B, C), k9_setfam_1(A)) & r2_hidden(k2_xboole_0(B, C), k9_setfam_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l19_yellow_1)).
% 3.38/1.62  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.38/1.62  tff(f_131, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r2_hidden(k2_xboole_0(B, C), A) => (k10_lattice3(k2_yellow_1(A), B, C) = k2_xboole_0(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_yellow_1)).
% 3.38/1.62  tff(f_103, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.38/1.62  tff(f_42, axiom, (![A]: (~v2_struct_0(k1_lattice3(A)) & v3_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_lattice3)).
% 3.38/1.62  tff(f_46, axiom, (![A]: (v3_lattices(k1_lattice3(A)) & v10_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_lattice3)).
% 3.38/1.62  tff(f_37, axiom, (![A]: (v3_lattices(k1_lattice3(A)) & l3_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_lattice3)).
% 3.38/1.62  tff(f_72, axiom, (![A]: (k3_yellow_1(A) = k3_lattice3(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_yellow_1)).
% 3.38/1.62  tff(f_95, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (((((v1_orders_2(k3_lattice3(A)) & v3_orders_2(k3_lattice3(A))) & v4_orders_2(k3_lattice3(A))) & v5_orders_2(k3_lattice3(A))) & v1_lattice3(k3_lattice3(A))) & v2_lattice3(k3_lattice3(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_yellow_1)).
% 3.38/1.62  tff(f_76, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.38/1.62  tff(f_70, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 3.38/1.62  tff(f_144, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r2_hidden(k3_xboole_0(B, C), A) => (k11_lattice3(k2_yellow_1(A), B, C) = k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_yellow_1)).
% 3.38/1.62  tff(f_58, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 3.38/1.62  tff(c_64, plain, (k12_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')!=k3_xboole_0('#skF_3', '#skF_4') | k13_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')!=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.38/1.62  tff(c_139, plain, (k13_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')!=k2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_64])).
% 3.38/1.62  tff(c_102, plain, (![A_54]: (k2_yellow_1(k9_setfam_1(A_54))=k3_yellow_1(A_54))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.38/1.62  tff(c_54, plain, (![A_24]: (u1_struct_0(k2_yellow_1(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.38/1.62  tff(c_108, plain, (![A_54]: (u1_struct_0(k3_yellow_1(A_54))=k9_setfam_1(A_54))), inference(superposition, [status(thm), theory('equality')], [c_102, c_54])).
% 3.38/1.62  tff(c_68, plain, (m1_subset_1('#skF_3', u1_struct_0(k3_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.38/1.62  tff(c_142, plain, (m1_subset_1('#skF_3', k9_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_68])).
% 3.38/1.62  tff(c_66, plain, (m1_subset_1('#skF_4', u1_struct_0(k3_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.38/1.62  tff(c_143, plain, (m1_subset_1('#skF_4', k9_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_66])).
% 3.38/1.62  tff(c_50, plain, (![B_21, C_23, A_20]: (r2_hidden(k2_xboole_0(B_21, C_23), k9_setfam_1(A_20)) | ~m1_subset_1(C_23, u1_struct_0(k3_yellow_1(A_20))) | ~m1_subset_1(B_21, u1_struct_0(k3_yellow_1(A_20))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.38/1.62  tff(c_221, plain, (![B_74, C_75, A_76]: (r2_hidden(k2_xboole_0(B_74, C_75), k9_setfam_1(A_76)) | ~m1_subset_1(C_75, k9_setfam_1(A_76)) | ~m1_subset_1(B_74, k9_setfam_1(A_76)))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_108, c_50])).
% 3.38/1.62  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.38/1.62  tff(c_226, plain, (![A_77, C_78, B_79]: (~v1_xboole_0(k9_setfam_1(A_77)) | ~m1_subset_1(C_78, k9_setfam_1(A_77)) | ~m1_subset_1(B_79, k9_setfam_1(A_77)))), inference(resolution, [status(thm)], [c_221, c_2])).
% 3.38/1.62  tff(c_231, plain, (![B_79]: (~v1_xboole_0(k9_setfam_1('#skF_2')) | ~m1_subset_1(B_79, k9_setfam_1('#skF_2')))), inference(resolution, [status(thm)], [c_143, c_226])).
% 3.38/1.62  tff(c_233, plain, (~v1_xboole_0(k9_setfam_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_231])).
% 3.38/1.62  tff(c_58, plain, (![A_25]: (k2_yellow_1(k9_setfam_1(A_25))=k3_yellow_1(A_25))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.38/1.62  tff(c_220, plain, (![B_21, C_23, A_20]: (r2_hidden(k2_xboole_0(B_21, C_23), k9_setfam_1(A_20)) | ~m1_subset_1(C_23, k9_setfam_1(A_20)) | ~m1_subset_1(B_21, k9_setfam_1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_108, c_50])).
% 3.38/1.62  tff(c_60, plain, (![A_26, B_30, C_32]: (k10_lattice3(k2_yellow_1(A_26), B_30, C_32)=k2_xboole_0(B_30, C_32) | ~r2_hidden(k2_xboole_0(B_30, C_32), A_26) | ~m1_subset_1(C_32, u1_struct_0(k2_yellow_1(A_26))) | ~m1_subset_1(B_30, u1_struct_0(k2_yellow_1(A_26))) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.38/1.62  tff(c_257, plain, (![A_89, B_90, C_91]: (k10_lattice3(k2_yellow_1(A_89), B_90, C_91)=k2_xboole_0(B_90, C_91) | ~r2_hidden(k2_xboole_0(B_90, C_91), A_89) | ~m1_subset_1(C_91, A_89) | ~m1_subset_1(B_90, A_89) | v1_xboole_0(A_89))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_60])).
% 3.38/1.62  tff(c_260, plain, (![A_20, B_21, C_23]: (k10_lattice3(k2_yellow_1(k9_setfam_1(A_20)), B_21, C_23)=k2_xboole_0(B_21, C_23) | v1_xboole_0(k9_setfam_1(A_20)) | ~m1_subset_1(C_23, k9_setfam_1(A_20)) | ~m1_subset_1(B_21, k9_setfam_1(A_20)))), inference(resolution, [status(thm)], [c_220, c_257])).
% 3.38/1.62  tff(c_297, plain, (![A_94, B_95, C_96]: (k10_lattice3(k3_yellow_1(A_94), B_95, C_96)=k2_xboole_0(B_95, C_96) | v1_xboole_0(k9_setfam_1(A_94)) | ~m1_subset_1(C_96, k9_setfam_1(A_94)) | ~m1_subset_1(B_95, k9_setfam_1(A_94)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_260])).
% 3.38/1.62  tff(c_299, plain, (![B_95]: (k10_lattice3(k3_yellow_1('#skF_2'), B_95, '#skF_4')=k2_xboole_0(B_95, '#skF_4') | v1_xboole_0(k9_setfam_1('#skF_2')) | ~m1_subset_1(B_95, k9_setfam_1('#skF_2')))), inference(resolution, [status(thm)], [c_143, c_297])).
% 3.38/1.62  tff(c_308, plain, (![B_97]: (k10_lattice3(k3_yellow_1('#skF_2'), B_97, '#skF_4')=k2_xboole_0(B_97, '#skF_4') | ~m1_subset_1(B_97, k9_setfam_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_233, c_299])).
% 3.38/1.62  tff(c_316, plain, (k10_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_142, c_308])).
% 3.38/1.62  tff(c_48, plain, (![A_19]: (v5_orders_2(k2_yellow_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.38/1.62  tff(c_118, plain, (![A_54]: (v5_orders_2(k3_yellow_1(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_48])).
% 3.38/1.62  tff(c_12, plain, (![A_8]: (~v2_struct_0(k1_lattice3(A_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.38/1.62  tff(c_18, plain, (![A_9]: (v10_lattices(k1_lattice3(A_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.38/1.62  tff(c_10, plain, (![A_7]: (l3_lattices(k1_lattice3(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.38/1.62  tff(c_24, plain, (![A_16]: (k3_lattice3(k1_lattice3(A_16))=k3_yellow_1(A_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.38/1.62  tff(c_176, plain, (![A_66]: (v1_lattice3(k3_lattice3(A_66)) | ~l3_lattices(A_66) | ~v10_lattices(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.38/1.62  tff(c_179, plain, (![A_16]: (v1_lattice3(k3_yellow_1(A_16)) | ~l3_lattices(k1_lattice3(A_16)) | ~v10_lattices(k1_lattice3(A_16)) | v2_struct_0(k1_lattice3(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_176])).
% 3.38/1.62  tff(c_181, plain, (![A_16]: (v1_lattice3(k3_yellow_1(A_16)) | v2_struct_0(k1_lattice3(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_10, c_179])).
% 3.38/1.62  tff(c_182, plain, (![A_16]: (v1_lattice3(k3_yellow_1(A_16)))), inference(negUnitSimplification, [status(thm)], [c_12, c_181])).
% 3.38/1.62  tff(c_28, plain, (![A_17]: (l1_orders_2(k2_yellow_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.38/1.62  tff(c_116, plain, (![A_54]: (l1_orders_2(k3_yellow_1(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_28])).
% 3.38/1.62  tff(c_388, plain, (![A_107, B_108, C_109]: (k13_lattice3(A_107, B_108, C_109)=k10_lattice3(A_107, B_108, C_109) | ~m1_subset_1(C_109, u1_struct_0(A_107)) | ~m1_subset_1(B_108, u1_struct_0(A_107)) | ~l1_orders_2(A_107) | ~v1_lattice3(A_107) | ~v5_orders_2(A_107))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.38/1.62  tff(c_390, plain, (![A_54, B_108, C_109]: (k13_lattice3(k3_yellow_1(A_54), B_108, C_109)=k10_lattice3(k3_yellow_1(A_54), B_108, C_109) | ~m1_subset_1(C_109, k9_setfam_1(A_54)) | ~m1_subset_1(B_108, u1_struct_0(k3_yellow_1(A_54))) | ~l1_orders_2(k3_yellow_1(A_54)) | ~v1_lattice3(k3_yellow_1(A_54)) | ~v5_orders_2(k3_yellow_1(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_388])).
% 3.38/1.62  tff(c_405, plain, (![A_110, B_111, C_112]: (k13_lattice3(k3_yellow_1(A_110), B_111, C_112)=k10_lattice3(k3_yellow_1(A_110), B_111, C_112) | ~m1_subset_1(C_112, k9_setfam_1(A_110)) | ~m1_subset_1(B_111, k9_setfam_1(A_110)))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_182, c_116, c_108, c_390])).
% 3.38/1.62  tff(c_412, plain, (![B_113]: (k13_lattice3(k3_yellow_1('#skF_2'), B_113, '#skF_4')=k10_lattice3(k3_yellow_1('#skF_2'), B_113, '#skF_4') | ~m1_subset_1(B_113, k9_setfam_1('#skF_2')))), inference(resolution, [status(thm)], [c_143, c_405])).
% 3.38/1.62  tff(c_418, plain, (k13_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k10_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_142, c_412])).
% 3.38/1.62  tff(c_422, plain, (k13_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_418])).
% 3.38/1.62  tff(c_424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_422])).
% 3.38/1.62  tff(c_425, plain, (![B_79]: (~m1_subset_1(B_79, k9_setfam_1('#skF_2')))), inference(splitRight, [status(thm)], [c_231])).
% 3.38/1.62  tff(c_429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_425, c_143])).
% 3.38/1.62  tff(c_430, plain, (k12_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')!=k3_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_64])).
% 3.38/1.62  tff(c_434, plain, (m1_subset_1('#skF_3', k9_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_68])).
% 3.38/1.62  tff(c_435, plain, (m1_subset_1('#skF_4', k9_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_66])).
% 3.38/1.62  tff(c_516, plain, (![B_128, C_129, A_130]: (r2_hidden(k2_xboole_0(B_128, C_129), k9_setfam_1(A_130)) | ~m1_subset_1(C_129, k9_setfam_1(A_130)) | ~m1_subset_1(B_128, k9_setfam_1(A_130)))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_108, c_50])).
% 3.38/1.62  tff(c_522, plain, (![A_132, C_133, B_134]: (~v1_xboole_0(k9_setfam_1(A_132)) | ~m1_subset_1(C_133, k9_setfam_1(A_132)) | ~m1_subset_1(B_134, k9_setfam_1(A_132)))), inference(resolution, [status(thm)], [c_516, c_2])).
% 3.38/1.62  tff(c_527, plain, (![B_134]: (~v1_xboole_0(k9_setfam_1('#skF_2')) | ~m1_subset_1(B_134, k9_setfam_1('#skF_2')))), inference(resolution, [status(thm)], [c_435, c_522])).
% 3.38/1.62  tff(c_529, plain, (~v1_xboole_0(k9_setfam_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_527])).
% 3.38/1.62  tff(c_52, plain, (![B_21, C_23, A_20]: (r2_hidden(k3_xboole_0(B_21, C_23), k9_setfam_1(A_20)) | ~m1_subset_1(C_23, u1_struct_0(k3_yellow_1(A_20))) | ~m1_subset_1(B_21, u1_struct_0(k3_yellow_1(A_20))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.38/1.62  tff(c_530, plain, (![B_21, C_23, A_20]: (r2_hidden(k3_xboole_0(B_21, C_23), k9_setfam_1(A_20)) | ~m1_subset_1(C_23, k9_setfam_1(A_20)) | ~m1_subset_1(B_21, k9_setfam_1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_108, c_52])).
% 3.38/1.62  tff(c_62, plain, (![A_33, B_37, C_39]: (k11_lattice3(k2_yellow_1(A_33), B_37, C_39)=k3_xboole_0(B_37, C_39) | ~r2_hidden(k3_xboole_0(B_37, C_39), A_33) | ~m1_subset_1(C_39, u1_struct_0(k2_yellow_1(A_33))) | ~m1_subset_1(B_37, u1_struct_0(k2_yellow_1(A_33))) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.38/1.62  tff(c_536, plain, (![A_138, B_139, C_140]: (k11_lattice3(k2_yellow_1(A_138), B_139, C_140)=k3_xboole_0(B_139, C_140) | ~r2_hidden(k3_xboole_0(B_139, C_140), A_138) | ~m1_subset_1(C_140, A_138) | ~m1_subset_1(B_139, A_138) | v1_xboole_0(A_138))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_62])).
% 3.38/1.62  tff(c_539, plain, (![A_20, B_21, C_23]: (k11_lattice3(k2_yellow_1(k9_setfam_1(A_20)), B_21, C_23)=k3_xboole_0(B_21, C_23) | v1_xboole_0(k9_setfam_1(A_20)) | ~m1_subset_1(C_23, k9_setfam_1(A_20)) | ~m1_subset_1(B_21, k9_setfam_1(A_20)))), inference(resolution, [status(thm)], [c_530, c_536])).
% 3.38/1.62  tff(c_542, plain, (![A_141, B_142, C_143]: (k11_lattice3(k3_yellow_1(A_141), B_142, C_143)=k3_xboole_0(B_142, C_143) | v1_xboole_0(k9_setfam_1(A_141)) | ~m1_subset_1(C_143, k9_setfam_1(A_141)) | ~m1_subset_1(B_142, k9_setfam_1(A_141)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_539])).
% 3.38/1.62  tff(c_544, plain, (![B_142]: (k11_lattice3(k3_yellow_1('#skF_2'), B_142, '#skF_4')=k3_xboole_0(B_142, '#skF_4') | v1_xboole_0(k9_setfam_1('#skF_2')) | ~m1_subset_1(B_142, k9_setfam_1('#skF_2')))), inference(resolution, [status(thm)], [c_435, c_542])).
% 3.38/1.62  tff(c_553, plain, (![B_144]: (k11_lattice3(k3_yellow_1('#skF_2'), B_144, '#skF_4')=k3_xboole_0(B_144, '#skF_4') | ~m1_subset_1(B_144, k9_setfam_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_529, c_544])).
% 3.38/1.62  tff(c_561, plain, (k11_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k3_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_434, c_553])).
% 3.38/1.62  tff(c_508, plain, (![A_127]: (v2_lattice3(k3_lattice3(A_127)) | ~l3_lattices(A_127) | ~v10_lattices(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.38/1.62  tff(c_511, plain, (![A_16]: (v2_lattice3(k3_yellow_1(A_16)) | ~l3_lattices(k1_lattice3(A_16)) | ~v10_lattices(k1_lattice3(A_16)) | v2_struct_0(k1_lattice3(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_508])).
% 3.38/1.62  tff(c_513, plain, (![A_16]: (v2_lattice3(k3_yellow_1(A_16)) | v2_struct_0(k1_lattice3(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_10, c_511])).
% 3.38/1.62  tff(c_514, plain, (![A_16]: (v2_lattice3(k3_yellow_1(A_16)))), inference(negUnitSimplification, [status(thm)], [c_12, c_513])).
% 3.38/1.62  tff(c_660, plain, (![A_163, B_164, C_165]: (k12_lattice3(A_163, B_164, C_165)=k11_lattice3(A_163, B_164, C_165) | ~m1_subset_1(C_165, u1_struct_0(A_163)) | ~m1_subset_1(B_164, u1_struct_0(A_163)) | ~l1_orders_2(A_163) | ~v2_lattice3(A_163) | ~v5_orders_2(A_163))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.38/1.62  tff(c_662, plain, (![A_54, B_164, C_165]: (k12_lattice3(k3_yellow_1(A_54), B_164, C_165)=k11_lattice3(k3_yellow_1(A_54), B_164, C_165) | ~m1_subset_1(C_165, k9_setfam_1(A_54)) | ~m1_subset_1(B_164, u1_struct_0(k3_yellow_1(A_54))) | ~l1_orders_2(k3_yellow_1(A_54)) | ~v2_lattice3(k3_yellow_1(A_54)) | ~v5_orders_2(k3_yellow_1(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_660])).
% 3.38/1.62  tff(c_715, plain, (![A_168, B_169, C_170]: (k12_lattice3(k3_yellow_1(A_168), B_169, C_170)=k11_lattice3(k3_yellow_1(A_168), B_169, C_170) | ~m1_subset_1(C_170, k9_setfam_1(A_168)) | ~m1_subset_1(B_169, k9_setfam_1(A_168)))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_514, c_116, c_108, c_662])).
% 3.38/1.62  tff(c_727, plain, (![B_174]: (k12_lattice3(k3_yellow_1('#skF_2'), B_174, '#skF_4')=k11_lattice3(k3_yellow_1('#skF_2'), B_174, '#skF_4') | ~m1_subset_1(B_174, k9_setfam_1('#skF_2')))), inference(resolution, [status(thm)], [c_435, c_715])).
% 3.38/1.62  tff(c_733, plain, (k12_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k11_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_434, c_727])).
% 3.38/1.62  tff(c_737, plain, (k12_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k3_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_561, c_733])).
% 3.38/1.62  tff(c_739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_430, c_737])).
% 3.38/1.62  tff(c_740, plain, (![B_134]: (~m1_subset_1(B_134, k9_setfam_1('#skF_2')))), inference(splitRight, [status(thm)], [c_527])).
% 3.38/1.62  tff(c_744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_740, c_435])).
% 3.38/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.62  
% 3.38/1.62  Inference rules
% 3.38/1.62  ----------------------
% 3.38/1.62  #Ref     : 0
% 3.38/1.62  #Sup     : 161
% 3.38/1.62  #Fact    : 0
% 3.38/1.62  #Define  : 0
% 3.38/1.62  #Split   : 3
% 3.38/1.62  #Chain   : 0
% 3.38/1.62  #Close   : 0
% 3.38/1.62  
% 3.38/1.62  Ordering : KBO
% 3.38/1.62  
% 3.38/1.62  Simplification rules
% 3.38/1.62  ----------------------
% 3.38/1.62  #Subsume      : 6
% 3.38/1.62  #Demod        : 102
% 3.38/1.62  #Tautology    : 88
% 3.38/1.62  #SimpNegUnit  : 26
% 3.38/1.62  #BackRed      : 11
% 3.38/1.62  
% 3.38/1.62  #Partial instantiations: 0
% 3.38/1.62  #Strategies tried      : 1
% 3.38/1.62  
% 3.38/1.62  Timing (in seconds)
% 3.38/1.62  ----------------------
% 3.38/1.63  Preprocessing        : 0.45
% 3.38/1.63  Parsing              : 0.27
% 3.38/1.63  CNF conversion       : 0.03
% 3.38/1.63  Main loop            : 0.39
% 3.38/1.63  Inferencing          : 0.14
% 3.38/1.63  Reduction            : 0.13
% 3.38/1.63  Demodulation         : 0.09
% 3.38/1.63  BG Simplification    : 0.02
% 3.38/1.63  Subsumption          : 0.05
% 3.38/1.63  Abstraction          : 0.02
% 3.38/1.63  MUC search           : 0.00
% 3.38/1.63  Cooper               : 0.00
% 3.38/1.63  Total                : 0.88
% 3.38/1.63  Index Insertion      : 0.00
% 3.38/1.63  Index Deletion       : 0.00
% 3.38/1.63  Index Matching       : 0.00
% 3.38/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
