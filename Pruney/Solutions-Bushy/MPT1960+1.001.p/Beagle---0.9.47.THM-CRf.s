%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1960+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:43 EST 2020

% Result     : Theorem 4.24s
% Output     : CNFRefutation 4.49s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 301 expanded)
%              Number of leaves         :   58 ( 135 expanded)
%              Depth                    :   14
%              Number of atoms          :  260 ( 539 expanded)
%              Number of equality atoms :   72 ( 165 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r6_waybel_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_yellow_0 > v3_orders_2 > v2_waybel_1 > v2_struct_0 > v2_lattice3 > v1_orders_2 > v1_lattice3 > v11_waybel_1 > v10_waybel_1 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > k7_waybel_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v11_waybel_1,type,(
    v11_waybel_1: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v3_yellow_0,type,(
    v3_yellow_0: $i > $o )).

tff(k13_lattice3,type,(
    k13_lattice3: ( $i * $i * $i ) > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k10_lattice3,type,(
    k10_lattice3: ( $i * $i * $i ) > $i )).

tff(v10_waybel_1,type,(
    v10_waybel_1: $i > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(v2_waybel_1,type,(
    v2_waybel_1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(k7_waybel_1,type,(
    k7_waybel_1: ( $i * $i ) > $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(r6_waybel_1,type,(
    r6_waybel_1: ( $i * $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_171,axiom,(
    ! [A] : u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_waybel_7)).

tff(f_178,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
       => k7_waybel_1(k3_yellow_1(A),B) = k6_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_waybel_7)).

tff(f_165,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_169,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_118,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_173,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_124,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_157,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
     => ! [C] :
          ( m1_subset_1(C,u1_struct_0(k3_yellow_1(A)))
         => ( k13_lattice3(k3_yellow_1(A),B,C) = k2_xboole_0(B,C)
            & k12_lattice3(k3_yellow_1(A),B,C) = k3_xboole_0(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_1)).

tff(f_92,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k3_yellow_1(A))
      & v1_orders_2(k3_yellow_1(A))
      & v3_orders_2(k3_yellow_1(A))
      & v4_orders_2(k3_yellow_1(A))
      & v5_orders_2(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & l1_orders_2(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & v11_waybel_1(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_waybel_7)).

tff(f_50,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc8_waybel_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_161,axiom,(
    ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_1)).

tff(f_159,axiom,(
    ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r6_waybel_1(A,B,C)
              <=> ( k10_lattice3(A,B,C) = k4_yellow_0(A)
                  & k11_lattice3(A,B,C) = k3_yellow_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d23_waybel_1)).

tff(f_148,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & v11_waybel_1(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r6_waybel_1(A,B,C)
              <=> C = k7_waybel_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_yellow_5)).

tff(c_56,plain,(
    ! [A_24] : k9_setfam_1(A_24) = k1_zfmisc_1(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_78,plain,(
    ! [A_44] : u1_struct_0(k3_yellow_1(A_44)) = k9_setfam_1(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_84,plain,(
    m1_subset_1('#skF_2',u1_struct_0(k3_yellow_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_85,plain,(
    m1_subset_1('#skF_2',k9_setfam_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_84])).

tff(c_88,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_85])).

tff(c_181,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(A_76,B_77)
      | ~ m1_subset_1(A_76,k1_zfmisc_1(B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_193,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_181])).

tff(c_76,plain,(
    ! [A_42,B_43] :
      ( k2_xboole_0(A_42,k4_xboole_0(B_43,A_42)) = B_43
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_54,plain,(
    ! [A_22,B_23] : k6_subset_1(A_22,B_23) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_82,plain,(
    k7_waybel_1(k3_yellow_1('#skF_1'),'#skF_2') != k6_subset_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_92,plain,(
    k7_waybel_1(k3_yellow_1('#skF_1'),'#skF_2') != k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_82])).

tff(c_80,plain,(
    ! [A_45,B_46] : r1_xboole_0(k4_xboole_0(A_45,B_46),B_46) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_148,plain,(
    ! [B_64,A_65] :
      ( r1_xboole_0(B_64,A_65)
      | ~ r1_xboole_0(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_151,plain,(
    ! [B_46,A_45] : r1_xboole_0(B_46,k4_xboole_0(A_45,B_46)) ),
    inference(resolution,[status(thm)],[c_80,c_148])).

tff(c_157,plain,(
    ! [A_68,B_69] :
      ( k3_xboole_0(A_68,B_69) = k1_xboole_0
      | ~ r1_xboole_0(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_164,plain,(
    ! [B_46,A_45] : k3_xboole_0(B_46,k4_xboole_0(A_45,B_46)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_151,c_157])).

tff(c_34,plain,(
    ! [A_12,B_13] : m1_subset_1(k6_subset_1(A_12,B_13),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_94,plain,(
    ! [A_12,B_13] : m1_subset_1(k4_xboole_0(A_12,B_13),k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_34])).

tff(c_192,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(resolution,[status(thm)],[c_94,c_181])).

tff(c_66,plain,(
    ! [A_34,B_35,C_37] :
      ( k13_lattice3(k3_yellow_1(A_34),B_35,C_37) = k2_xboole_0(B_35,C_37)
      | ~ m1_subset_1(C_37,u1_struct_0(k3_yellow_1(A_34)))
      | ~ m1_subset_1(B_35,u1_struct_0(k3_yellow_1(A_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_86,plain,(
    ! [A_34,B_35,C_37] :
      ( k13_lattice3(k3_yellow_1(A_34),B_35,C_37) = k2_xboole_0(B_35,C_37)
      | ~ m1_subset_1(C_37,k9_setfam_1(A_34))
      | ~ m1_subset_1(B_35,k9_setfam_1(A_34)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_78,c_66])).

tff(c_329,plain,(
    ! [A_105,B_106,C_107] :
      ( k13_lattice3(k3_yellow_1(A_105),B_106,C_107) = k2_xboole_0(B_106,C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(A_105))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_86])).

tff(c_337,plain,(
    ! [A_12,B_106,B_13] :
      ( k13_lattice3(k3_yellow_1(A_12),B_106,k4_xboole_0(A_12,B_13)) = k2_xboole_0(B_106,k4_xboole_0(A_12,B_13))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_12)) ) ),
    inference(resolution,[status(thm)],[c_94,c_329])).

tff(c_74,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(A_40,k1_zfmisc_1(B_41))
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_48,plain,(
    ! [A_15] : v5_orders_2(k3_yellow_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32,plain,(
    ! [A_11] : l1_orders_2(k3_yellow_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    ! [A_14] : v11_waybel_1(k3_yellow_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_219,plain,(
    ! [A_86] :
      ( v1_lattice3(A_86)
      | ~ v11_waybel_1(A_86)
      | v2_struct_0(A_86)
      | ~ l1_orders_2(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    ! [A_15] : ~ v2_struct_0(k3_yellow_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_222,plain,(
    ! [A_15] :
      ( v1_lattice3(k3_yellow_1(A_15))
      | ~ v11_waybel_1(k3_yellow_1(A_15))
      | ~ l1_orders_2(k3_yellow_1(A_15)) ) ),
    inference(resolution,[status(thm)],[c_219,c_40])).

tff(c_225,plain,(
    ! [A_15] : v1_lattice3(k3_yellow_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_38,c_222])).

tff(c_89,plain,(
    ! [A_44] : u1_struct_0(k3_yellow_1(A_44)) = k1_zfmisc_1(A_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_78])).

tff(c_549,plain,(
    ! [A_122,B_123,C_124] :
      ( k13_lattice3(A_122,B_123,C_124) = k10_lattice3(A_122,B_123,C_124)
      | ~ m1_subset_1(C_124,u1_struct_0(A_122))
      | ~ m1_subset_1(B_123,u1_struct_0(A_122))
      | ~ l1_orders_2(A_122)
      | ~ v1_lattice3(A_122)
      | ~ v5_orders_2(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_551,plain,(
    ! [A_44,B_123,C_124] :
      ( k13_lattice3(k3_yellow_1(A_44),B_123,C_124) = k10_lattice3(k3_yellow_1(A_44),B_123,C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(A_44))
      | ~ m1_subset_1(B_123,u1_struct_0(k3_yellow_1(A_44)))
      | ~ l1_orders_2(k3_yellow_1(A_44))
      | ~ v1_lattice3(k3_yellow_1(A_44))
      | ~ v5_orders_2(k3_yellow_1(A_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_549])).

tff(c_812,plain,(
    ! [A_143,B_144,C_145] :
      ( k13_lattice3(k3_yellow_1(A_143),B_144,C_145) = k10_lattice3(k3_yellow_1(A_143),B_144,C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(A_143))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(A_143)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_225,c_32,c_89,c_551])).

tff(c_960,plain,(
    ! [B_153,B_154,A_155] :
      ( k13_lattice3(k3_yellow_1(B_153),B_154,A_155) = k10_lattice3(k3_yellow_1(B_153),B_154,A_155)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(B_153))
      | ~ r1_tarski(A_155,B_153) ) ),
    inference(resolution,[status(thm)],[c_74,c_812])).

tff(c_970,plain,(
    ! [A_156] :
      ( k13_lattice3(k3_yellow_1('#skF_1'),'#skF_2',A_156) = k10_lattice3(k3_yellow_1('#skF_1'),'#skF_2',A_156)
      | ~ r1_tarski(A_156,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_88,c_960])).

tff(c_1005,plain,(
    ! [B_13] :
      ( k10_lattice3(k3_yellow_1('#skF_1'),'#skF_2',k4_xboole_0('#skF_1',B_13)) = k2_xboole_0('#skF_2',k4_xboole_0('#skF_1',B_13))
      | ~ r1_tarski(k4_xboole_0('#skF_1',B_13),'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_970])).

tff(c_1035,plain,(
    ! [B_13] : k10_lattice3(k3_yellow_1('#skF_1'),'#skF_2',k4_xboole_0('#skF_1',B_13)) = k2_xboole_0('#skF_2',k4_xboole_0('#skF_1',B_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_192,c_1005])).

tff(c_212,plain,(
    ! [A_85] :
      ( v2_lattice3(A_85)
      | ~ v11_waybel_1(A_85)
      | v2_struct_0(A_85)
      | ~ l1_orders_2(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_215,plain,(
    ! [A_15] :
      ( v2_lattice3(k3_yellow_1(A_15))
      | ~ v11_waybel_1(k3_yellow_1(A_15))
      | ~ l1_orders_2(k3_yellow_1(A_15)) ) ),
    inference(resolution,[status(thm)],[c_212,c_40])).

tff(c_218,plain,(
    ! [A_15] : v2_lattice3(k3_yellow_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_38,c_215])).

tff(c_843,plain,(
    ! [A_147,B_148,C_149] :
      ( k12_lattice3(A_147,B_148,C_149) = k11_lattice3(A_147,B_148,C_149)
      | ~ m1_subset_1(C_149,u1_struct_0(A_147))
      | ~ m1_subset_1(B_148,u1_struct_0(A_147))
      | ~ l1_orders_2(A_147)
      | ~ v2_lattice3(A_147)
      | ~ v5_orders_2(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_845,plain,(
    ! [A_44,B_148,C_149] :
      ( k12_lattice3(k3_yellow_1(A_44),B_148,C_149) = k11_lattice3(k3_yellow_1(A_44),B_148,C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(A_44))
      | ~ m1_subset_1(B_148,u1_struct_0(k3_yellow_1(A_44)))
      | ~ l1_orders_2(k3_yellow_1(A_44))
      | ~ v2_lattice3(k3_yellow_1(A_44))
      | ~ v5_orders_2(k3_yellow_1(A_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_843])).

tff(c_1356,plain,(
    ! [A_177,B_178,C_179] :
      ( k12_lattice3(k3_yellow_1(A_177),B_178,C_179) = k11_lattice3(k3_yellow_1(A_177),B_178,C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(A_177))
      | ~ m1_subset_1(B_178,k1_zfmisc_1(A_177)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_218,c_32,c_89,c_845])).

tff(c_1500,plain,(
    ! [B_187,B_188,A_189] :
      ( k12_lattice3(k3_yellow_1(B_187),B_188,A_189) = k11_lattice3(k3_yellow_1(B_187),B_188,A_189)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(B_187))
      | ~ r1_tarski(A_189,B_187) ) ),
    inference(resolution,[status(thm)],[c_74,c_1356])).

tff(c_1510,plain,(
    ! [A_190] :
      ( k12_lattice3(k3_yellow_1('#skF_1'),'#skF_2',A_190) = k11_lattice3(k3_yellow_1('#skF_1'),'#skF_2',A_190)
      | ~ r1_tarski(A_190,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_88,c_1500])).

tff(c_64,plain,(
    ! [A_34,B_35,C_37] :
      ( k12_lattice3(k3_yellow_1(A_34),B_35,C_37) = k3_xboole_0(B_35,C_37)
      | ~ m1_subset_1(C_37,u1_struct_0(k3_yellow_1(A_34)))
      | ~ m1_subset_1(B_35,u1_struct_0(k3_yellow_1(A_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_87,plain,(
    ! [A_34,B_35,C_37] :
      ( k12_lattice3(k3_yellow_1(A_34),B_35,C_37) = k3_xboole_0(B_35,C_37)
      | ~ m1_subset_1(C_37,k9_setfam_1(A_34))
      | ~ m1_subset_1(B_35,k9_setfam_1(A_34)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_78,c_64])).

tff(c_258,plain,(
    ! [A_99,B_100,C_101] :
      ( k12_lattice3(k3_yellow_1(A_99),B_100,C_101) = k3_xboole_0(B_100,C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(A_99))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_87])).

tff(c_266,plain,(
    ! [A_12,B_100,B_13] :
      ( k12_lattice3(k3_yellow_1(A_12),B_100,k4_xboole_0(A_12,B_13)) = k3_xboole_0(B_100,k4_xboole_0(A_12,B_13))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_12)) ) ),
    inference(resolution,[status(thm)],[c_94,c_258])).

tff(c_1521,plain,(
    ! [B_13] :
      ( k11_lattice3(k3_yellow_1('#skF_1'),'#skF_2',k4_xboole_0('#skF_1',B_13)) = k3_xboole_0('#skF_2',k4_xboole_0('#skF_1',B_13))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski(k4_xboole_0('#skF_1',B_13),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1510,c_266])).

tff(c_1564,plain,(
    ! [B_13] : k11_lattice3(k3_yellow_1('#skF_1'),'#skF_2',k4_xboole_0('#skF_1',B_13)) = k3_xboole_0('#skF_2',k4_xboole_0('#skF_1',B_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_88,c_1521])).

tff(c_44,plain,(
    ! [A_15] : v3_orders_2(k3_yellow_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_46,plain,(
    ! [A_15] : v4_orders_2(k3_yellow_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_70,plain,(
    ! [A_39] : k4_yellow_0(k3_yellow_1(A_39)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_68,plain,(
    ! [A_38] : k3_yellow_0(k3_yellow_1(A_38)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1327,plain,(
    ! [A_171,B_172,C_173] :
      ( r6_waybel_1(A_171,B_172,C_173)
      | k11_lattice3(A_171,B_172,C_173) != k3_yellow_0(A_171)
      | k10_lattice3(A_171,B_172,C_173) != k4_yellow_0(A_171)
      | ~ m1_subset_1(C_173,u1_struct_0(A_171))
      | ~ m1_subset_1(B_172,u1_struct_0(A_171))
      | ~ l1_orders_2(A_171)
      | v2_struct_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1329,plain,(
    ! [A_44,B_172,C_173] :
      ( r6_waybel_1(k3_yellow_1(A_44),B_172,C_173)
      | k11_lattice3(k3_yellow_1(A_44),B_172,C_173) != k3_yellow_0(k3_yellow_1(A_44))
      | k10_lattice3(k3_yellow_1(A_44),B_172,C_173) != k4_yellow_0(k3_yellow_1(A_44))
      | ~ m1_subset_1(C_173,k1_zfmisc_1(A_44))
      | ~ m1_subset_1(B_172,u1_struct_0(k3_yellow_1(A_44)))
      | ~ l1_orders_2(k3_yellow_1(A_44))
      | v2_struct_0(k3_yellow_1(A_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_1327])).

tff(c_1331,plain,(
    ! [A_44,B_172,C_173] :
      ( r6_waybel_1(k3_yellow_1(A_44),B_172,C_173)
      | k11_lattice3(k3_yellow_1(A_44),B_172,C_173) != k1_xboole_0
      | k10_lattice3(k3_yellow_1(A_44),B_172,C_173) != A_44
      | ~ m1_subset_1(C_173,k1_zfmisc_1(A_44))
      | ~ m1_subset_1(B_172,k1_zfmisc_1(A_44))
      | v2_struct_0(k3_yellow_1(A_44)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_89,c_70,c_68,c_1329])).

tff(c_1785,plain,(
    ! [A_201,B_202,C_203] :
      ( r6_waybel_1(k3_yellow_1(A_201),B_202,C_203)
      | k11_lattice3(k3_yellow_1(A_201),B_202,C_203) != k1_xboole_0
      | k10_lattice3(k3_yellow_1(A_201),B_202,C_203) != A_201
      | ~ m1_subset_1(C_203,k1_zfmisc_1(A_201))
      | ~ m1_subset_1(B_202,k1_zfmisc_1(A_201)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1331])).

tff(c_62,plain,(
    ! [A_27,B_31,C_33] :
      ( k7_waybel_1(A_27,B_31) = C_33
      | ~ r6_waybel_1(A_27,B_31,C_33)
      | ~ m1_subset_1(C_33,u1_struct_0(A_27))
      | ~ m1_subset_1(B_31,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27)
      | ~ v11_waybel_1(A_27)
      | ~ v2_lattice3(A_27)
      | ~ v1_lattice3(A_27)
      | ~ v5_orders_2(A_27)
      | ~ v4_orders_2(A_27)
      | ~ v3_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1787,plain,(
    ! [A_201,B_202,C_203] :
      ( k7_waybel_1(k3_yellow_1(A_201),B_202) = C_203
      | ~ m1_subset_1(C_203,u1_struct_0(k3_yellow_1(A_201)))
      | ~ m1_subset_1(B_202,u1_struct_0(k3_yellow_1(A_201)))
      | ~ l1_orders_2(k3_yellow_1(A_201))
      | ~ v11_waybel_1(k3_yellow_1(A_201))
      | ~ v2_lattice3(k3_yellow_1(A_201))
      | ~ v1_lattice3(k3_yellow_1(A_201))
      | ~ v5_orders_2(k3_yellow_1(A_201))
      | ~ v4_orders_2(k3_yellow_1(A_201))
      | ~ v3_orders_2(k3_yellow_1(A_201))
      | k11_lattice3(k3_yellow_1(A_201),B_202,C_203) != k1_xboole_0
      | k10_lattice3(k3_yellow_1(A_201),B_202,C_203) != A_201
      | ~ m1_subset_1(C_203,k1_zfmisc_1(A_201))
      | ~ m1_subset_1(B_202,k1_zfmisc_1(A_201)) ) ),
    inference(resolution,[status(thm)],[c_1785,c_62])).

tff(c_2446,plain,(
    ! [A_239,B_240,C_241] :
      ( k7_waybel_1(k3_yellow_1(A_239),B_240) = C_241
      | k11_lattice3(k3_yellow_1(A_239),B_240,C_241) != k1_xboole_0
      | k10_lattice3(k3_yellow_1(A_239),B_240,C_241) != A_239
      | ~ m1_subset_1(C_241,k1_zfmisc_1(A_239))
      | ~ m1_subset_1(B_240,k1_zfmisc_1(A_239)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_48,c_225,c_218,c_38,c_32,c_89,c_89,c_1787])).

tff(c_2458,plain,(
    ! [B_13] :
      ( k7_waybel_1(k3_yellow_1('#skF_1'),'#skF_2') = k4_xboole_0('#skF_1',B_13)
      | k3_xboole_0('#skF_2',k4_xboole_0('#skF_1',B_13)) != k1_xboole_0
      | k10_lattice3(k3_yellow_1('#skF_1'),'#skF_2',k4_xboole_0('#skF_1',B_13)) != '#skF_1'
      | ~ m1_subset_1(k4_xboole_0('#skF_1',B_13),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1564,c_2446])).

tff(c_2528,plain,(
    ! [B_243] :
      ( k7_waybel_1(k3_yellow_1('#skF_1'),'#skF_2') = k4_xboole_0('#skF_1',B_243)
      | k3_xboole_0('#skF_2',k4_xboole_0('#skF_1',B_243)) != k1_xboole_0
      | k2_xboole_0('#skF_2',k4_xboole_0('#skF_1',B_243)) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_94,c_1035,c_2458])).

tff(c_2531,plain,
    ( k7_waybel_1(k3_yellow_1('#skF_1'),'#skF_2') = k4_xboole_0('#skF_1','#skF_2')
    | k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2')) != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_2528])).

tff(c_2534,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2')) != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_2531])).

tff(c_2537,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_2534])).

tff(c_2541,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_2537])).

%------------------------------------------------------------------------------
