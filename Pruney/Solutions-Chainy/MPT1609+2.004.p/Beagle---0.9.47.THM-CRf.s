%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:29 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 360 expanded)
%              Number of leaves         :   49 ( 148 expanded)
%              Depth                    :    9
%              Number of atoms          :  210 ( 590 expanded)
%              Number of equality atoms :   43 ( 272 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v3_lattice3 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > l1_orders_2 > k2_enumset1 > k1_enumset1 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(v3_lattice3,type,(
    v3_lattice3: $i > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_116,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_114,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_152,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
       => ! [C] :
            ( m1_subset_1(C,u1_struct_0(k3_yellow_1(A)))
           => ( k13_lattice3(k3_yellow_1(A),B,C) = k2_xboole_0(B,C)
              & k12_lattice3(k3_yellow_1(A),B,C) = k3_xboole_0(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k3_yellow_1(A))
      & v1_orders_2(k3_yellow_1(A))
      & v3_orders_2(k3_yellow_1(A))
      & v4_orders_2(k3_yellow_1(A))
      & v5_orders_2(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & v3_lattice3(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_yellow_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ( v3_lattice3(A)
       => ( v1_lattice3(A)
          & v2_lattice3(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_lattice3)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_110,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
     => ! [C] :
          ( m1_subset_1(C,u1_struct_0(k3_yellow_1(A)))
         => ( r2_hidden(k3_xboole_0(B,C),k9_setfam_1(A))
            & r2_hidden(k2_xboole_0(B,C),k9_setfam_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l19_yellow_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_129,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r2_hidden(k2_xboole_0(B,C),A)
               => k10_lattice3(k2_yellow_1(A),B,C) = k2_xboole_0(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_1)).

tff(f_142,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r2_hidden(k3_xboole_0(B,C),A)
               => k11_lattice3(k2_yellow_1(A),B,C) = k3_xboole_0(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_1)).

tff(c_91,plain,(
    ! [A_58] : k2_yellow_1(k9_setfam_1(A_58)) = k3_yellow_1(A_58) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_52,plain,(
    ! [A_29] : u1_struct_0(k2_yellow_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_97,plain,(
    ! [A_58] : u1_struct_0(k3_yellow_1(A_58)) = k9_setfam_1(A_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_52])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k3_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_131,plain,(
    m1_subset_1('#skF_3',k9_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_66])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k3_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_132,plain,(
    m1_subset_1('#skF_4',k9_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_64])).

tff(c_42,plain,(
    ! [A_23] : v5_orders_2(k3_yellow_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_34,plain,(
    ! [A_23] : ~ v2_struct_0(k3_yellow_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    ! [A_21] : l1_orders_2(k2_yellow_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_99,plain,(
    ! [A_58] : l1_orders_2(k3_yellow_1(A_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_24])).

tff(c_46,plain,(
    ! [A_24] : v3_lattice3(k3_yellow_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_522,plain,(
    ! [A_136] :
      ( v2_lattice3(A_136)
      | ~ v3_lattice3(A_136)
      | ~ l1_orders_2(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_525,plain,(
    ! [A_24] :
      ( v2_lattice3(k3_yellow_1(A_24))
      | ~ l1_orders_2(k3_yellow_1(A_24))
      | v2_struct_0(k3_yellow_1(A_24)) ) ),
    inference(resolution,[status(thm)],[c_46,c_522])).

tff(c_528,plain,(
    ! [A_24] :
      ( v2_lattice3(k3_yellow_1(A_24))
      | v2_struct_0(k3_yellow_1(A_24)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_525])).

tff(c_529,plain,(
    ! [A_24] : v2_lattice3(k3_yellow_1(A_24)) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_528])).

tff(c_566,plain,(
    ! [A_153,B_154,C_155] :
      ( k12_lattice3(A_153,B_154,C_155) = k11_lattice3(A_153,B_154,C_155)
      | ~ m1_subset_1(C_155,u1_struct_0(A_153))
      | ~ m1_subset_1(B_154,u1_struct_0(A_153))
      | ~ l1_orders_2(A_153)
      | ~ v2_lattice3(A_153)
      | ~ v5_orders_2(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_568,plain,(
    ! [A_58,B_154,C_155] :
      ( k12_lattice3(k3_yellow_1(A_58),B_154,C_155) = k11_lattice3(k3_yellow_1(A_58),B_154,C_155)
      | ~ m1_subset_1(C_155,k9_setfam_1(A_58))
      | ~ m1_subset_1(B_154,u1_struct_0(k3_yellow_1(A_58)))
      | ~ l1_orders_2(k3_yellow_1(A_58))
      | ~ v2_lattice3(k3_yellow_1(A_58))
      | ~ v5_orders_2(k3_yellow_1(A_58)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_566])).

tff(c_575,plain,(
    ! [A_156,B_157,C_158] :
      ( k12_lattice3(k3_yellow_1(A_156),B_157,C_158) = k11_lattice3(k3_yellow_1(A_156),B_157,C_158)
      | ~ m1_subset_1(C_158,k9_setfam_1(A_156))
      | ~ m1_subset_1(B_157,k9_setfam_1(A_156)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_529,c_99,c_97,c_568])).

tff(c_582,plain,(
    ! [B_159] :
      ( k12_lattice3(k3_yellow_1('#skF_2'),B_159,'#skF_4') = k11_lattice3(k3_yellow_1('#skF_2'),B_159,'#skF_4')
      | ~ m1_subset_1(B_159,k9_setfam_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_132,c_575])).

tff(c_590,plain,(
    k12_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') = k11_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_131,c_582])).

tff(c_193,plain,(
    ! [A_74] :
      ( v1_lattice3(A_74)
      | ~ v3_lattice3(A_74)
      | ~ l1_orders_2(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_196,plain,(
    ! [A_24] :
      ( v1_lattice3(k3_yellow_1(A_24))
      | ~ l1_orders_2(k3_yellow_1(A_24))
      | v2_struct_0(k3_yellow_1(A_24)) ) ),
    inference(resolution,[status(thm)],[c_46,c_193])).

tff(c_199,plain,(
    ! [A_24] :
      ( v1_lattice3(k3_yellow_1(A_24))
      | v2_struct_0(k3_yellow_1(A_24)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_196])).

tff(c_200,plain,(
    ! [A_24] : v1_lattice3(k3_yellow_1(A_24)) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_199])).

tff(c_292,plain,(
    ! [A_102,B_103,C_104] :
      ( k13_lattice3(A_102,B_103,C_104) = k10_lattice3(A_102,B_103,C_104)
      | ~ m1_subset_1(C_104,u1_struct_0(A_102))
      | ~ m1_subset_1(B_103,u1_struct_0(A_102))
      | ~ l1_orders_2(A_102)
      | ~ v1_lattice3(A_102)
      | ~ v5_orders_2(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_294,plain,(
    ! [A_58,B_103,C_104] :
      ( k13_lattice3(k3_yellow_1(A_58),B_103,C_104) = k10_lattice3(k3_yellow_1(A_58),B_103,C_104)
      | ~ m1_subset_1(C_104,k9_setfam_1(A_58))
      | ~ m1_subset_1(B_103,u1_struct_0(k3_yellow_1(A_58)))
      | ~ l1_orders_2(k3_yellow_1(A_58))
      | ~ v1_lattice3(k3_yellow_1(A_58))
      | ~ v5_orders_2(k3_yellow_1(A_58)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_292])).

tff(c_301,plain,(
    ! [A_105,B_106,C_107] :
      ( k13_lattice3(k3_yellow_1(A_105),B_106,C_107) = k10_lattice3(k3_yellow_1(A_105),B_106,C_107)
      | ~ m1_subset_1(C_107,k9_setfam_1(A_105))
      | ~ m1_subset_1(B_106,k9_setfam_1(A_105)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_200,c_99,c_97,c_294])).

tff(c_308,plain,(
    ! [B_108] :
      ( k13_lattice3(k3_yellow_1('#skF_2'),B_108,'#skF_4') = k10_lattice3(k3_yellow_1('#skF_2'),B_108,'#skF_4')
      | ~ m1_subset_1(B_108,k9_setfam_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_132,c_301])).

tff(c_316,plain,(
    k13_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') = k10_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_131,c_308])).

tff(c_62,plain,
    ( k12_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') != k3_xboole_0('#skF_3','#skF_4')
    | k13_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') != k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_142,plain,(
    k13_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') != k2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_321,plain,(
    k10_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') != k2_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_142])).

tff(c_50,plain,(
    ! [B_26,C_28,A_25] :
      ( r2_hidden(k3_xboole_0(B_26,C_28),k9_setfam_1(A_25))
      | ~ m1_subset_1(C_28,u1_struct_0(k3_yellow_1(A_25)))
      | ~ m1_subset_1(B_26,u1_struct_0(k3_yellow_1(A_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_212,plain,(
    ! [B_79,C_80,A_81] :
      ( r2_hidden(k3_xboole_0(B_79,C_80),k9_setfam_1(A_81))
      | ~ m1_subset_1(C_80,k9_setfam_1(A_81))
      | ~ m1_subset_1(B_79,k9_setfam_1(A_81)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_97,c_50])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_217,plain,(
    ! [A_82,C_83,B_84] :
      ( ~ v1_xboole_0(k9_setfam_1(A_82))
      | ~ m1_subset_1(C_83,k9_setfam_1(A_82))
      | ~ m1_subset_1(B_84,k9_setfam_1(A_82)) ) ),
    inference(resolution,[status(thm)],[c_212,c_2])).

tff(c_222,plain,(
    ! [B_84] :
      ( ~ v1_xboole_0(k9_setfam_1('#skF_2'))
      | ~ m1_subset_1(B_84,k9_setfam_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_132,c_217])).

tff(c_230,plain,(
    ~ v1_xboole_0(k9_setfam_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_56,plain,(
    ! [A_30] : k2_yellow_1(k9_setfam_1(A_30)) = k3_yellow_1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_48,plain,(
    ! [B_26,C_28,A_25] :
      ( r2_hidden(k2_xboole_0(B_26,C_28),k9_setfam_1(A_25))
      | ~ m1_subset_1(C_28,u1_struct_0(k3_yellow_1(A_25)))
      | ~ m1_subset_1(B_26,u1_struct_0(k3_yellow_1(A_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_224,plain,(
    ! [B_26,C_28,A_25] :
      ( r2_hidden(k2_xboole_0(B_26,C_28),k9_setfam_1(A_25))
      | ~ m1_subset_1(C_28,k9_setfam_1(A_25))
      | ~ m1_subset_1(B_26,k9_setfam_1(A_25)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_97,c_48])).

tff(c_58,plain,(
    ! [A_31,B_35,C_37] :
      ( k10_lattice3(k2_yellow_1(A_31),B_35,C_37) = k2_xboole_0(B_35,C_37)
      | ~ r2_hidden(k2_xboole_0(B_35,C_37),A_31)
      | ~ m1_subset_1(C_37,u1_struct_0(k2_yellow_1(A_31)))
      | ~ m1_subset_1(B_35,u1_struct_0(k2_yellow_1(A_31)))
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_326,plain,(
    ! [A_109,B_110,C_111] :
      ( k10_lattice3(k2_yellow_1(A_109),B_110,C_111) = k2_xboole_0(B_110,C_111)
      | ~ r2_hidden(k2_xboole_0(B_110,C_111),A_109)
      | ~ m1_subset_1(C_111,A_109)
      | ~ m1_subset_1(B_110,A_109)
      | v1_xboole_0(A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_58])).

tff(c_329,plain,(
    ! [A_25,B_26,C_28] :
      ( k10_lattice3(k2_yellow_1(k9_setfam_1(A_25)),B_26,C_28) = k2_xboole_0(B_26,C_28)
      | v1_xboole_0(k9_setfam_1(A_25))
      | ~ m1_subset_1(C_28,k9_setfam_1(A_25))
      | ~ m1_subset_1(B_26,k9_setfam_1(A_25)) ) ),
    inference(resolution,[status(thm)],[c_224,c_326])).

tff(c_388,plain,(
    ! [A_120,B_121,C_122] :
      ( k10_lattice3(k3_yellow_1(A_120),B_121,C_122) = k2_xboole_0(B_121,C_122)
      | v1_xboole_0(k9_setfam_1(A_120))
      | ~ m1_subset_1(C_122,k9_setfam_1(A_120))
      | ~ m1_subset_1(B_121,k9_setfam_1(A_120)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_329])).

tff(c_390,plain,(
    ! [B_121] :
      ( k10_lattice3(k3_yellow_1('#skF_2'),B_121,'#skF_4') = k2_xboole_0(B_121,'#skF_4')
      | v1_xboole_0(k9_setfam_1('#skF_2'))
      | ~ m1_subset_1(B_121,k9_setfam_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_132,c_388])).

tff(c_449,plain,(
    ! [B_125] :
      ( k10_lattice3(k3_yellow_1('#skF_2'),B_125,'#skF_4') = k2_xboole_0(B_125,'#skF_4')
      | ~ m1_subset_1(B_125,k9_setfam_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_390])).

tff(c_455,plain,(
    k10_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_131,c_449])).

tff(c_460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_321,c_455])).

tff(c_461,plain,(
    ! [B_84] : ~ m1_subset_1(B_84,k9_setfam_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_461,c_132])).

tff(c_466,plain,(
    k12_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') != k3_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_595,plain,(
    k11_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') != k3_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_466])).

tff(c_541,plain,(
    ! [B_141,C_142,A_143] :
      ( r2_hidden(k3_xboole_0(B_141,C_142),k9_setfam_1(A_143))
      | ~ m1_subset_1(C_142,k9_setfam_1(A_143))
      | ~ m1_subset_1(B_141,k9_setfam_1(A_143)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_97,c_50])).

tff(c_546,plain,(
    ! [A_144,C_145,B_146] :
      ( ~ v1_xboole_0(k9_setfam_1(A_144))
      | ~ m1_subset_1(C_145,k9_setfam_1(A_144))
      | ~ m1_subset_1(B_146,k9_setfam_1(A_144)) ) ),
    inference(resolution,[status(thm)],[c_541,c_2])).

tff(c_551,plain,(
    ! [B_146] :
      ( ~ v1_xboole_0(k9_setfam_1('#skF_2'))
      | ~ m1_subset_1(B_146,k9_setfam_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_132,c_546])).

tff(c_553,plain,(
    ~ v1_xboole_0(k9_setfam_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_551])).

tff(c_540,plain,(
    ! [B_26,C_28,A_25] :
      ( r2_hidden(k3_xboole_0(B_26,C_28),k9_setfam_1(A_25))
      | ~ m1_subset_1(C_28,k9_setfam_1(A_25))
      | ~ m1_subset_1(B_26,k9_setfam_1(A_25)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_97,c_50])).

tff(c_60,plain,(
    ! [A_38,B_42,C_44] :
      ( k11_lattice3(k2_yellow_1(A_38),B_42,C_44) = k3_xboole_0(B_42,C_44)
      | ~ r2_hidden(k3_xboole_0(B_42,C_44),A_38)
      | ~ m1_subset_1(C_44,u1_struct_0(k2_yellow_1(A_38)))
      | ~ m1_subset_1(B_42,u1_struct_0(k2_yellow_1(A_38)))
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_560,plain,(
    ! [A_150,B_151,C_152] :
      ( k11_lattice3(k2_yellow_1(A_150),B_151,C_152) = k3_xboole_0(B_151,C_152)
      | ~ r2_hidden(k3_xboole_0(B_151,C_152),A_150)
      | ~ m1_subset_1(C_152,A_150)
      | ~ m1_subset_1(B_151,A_150)
      | v1_xboole_0(A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_60])).

tff(c_563,plain,(
    ! [A_25,B_26,C_28] :
      ( k11_lattice3(k2_yellow_1(k9_setfam_1(A_25)),B_26,C_28) = k3_xboole_0(B_26,C_28)
      | v1_xboole_0(k9_setfam_1(A_25))
      | ~ m1_subset_1(C_28,k9_setfam_1(A_25))
      | ~ m1_subset_1(B_26,k9_setfam_1(A_25)) ) ),
    inference(resolution,[status(thm)],[c_540,c_560])).

tff(c_684,plain,(
    ! [A_178,B_179,C_180] :
      ( k11_lattice3(k3_yellow_1(A_178),B_179,C_180) = k3_xboole_0(B_179,C_180)
      | v1_xboole_0(k9_setfam_1(A_178))
      | ~ m1_subset_1(C_180,k9_setfam_1(A_178))
      | ~ m1_subset_1(B_179,k9_setfam_1(A_178)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_563])).

tff(c_686,plain,(
    ! [B_179] :
      ( k11_lattice3(k3_yellow_1('#skF_2'),B_179,'#skF_4') = k3_xboole_0(B_179,'#skF_4')
      | v1_xboole_0(k9_setfam_1('#skF_2'))
      | ~ m1_subset_1(B_179,k9_setfam_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_132,c_684])).

tff(c_695,plain,(
    ! [B_181] :
      ( k11_lattice3(k3_yellow_1('#skF_2'),B_181,'#skF_4') = k3_xboole_0(B_181,'#skF_4')
      | ~ m1_subset_1(B_181,k9_setfam_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_553,c_686])).

tff(c_701,plain,(
    k11_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_131,c_695])).

tff(c_706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_595,c_701])).

tff(c_707,plain,(
    ! [B_146] : ~ m1_subset_1(B_146,k9_setfam_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_551])).

tff(c_711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_707,c_132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:01:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.50  
% 3.17/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.50  %$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v3_lattice3 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > l1_orders_2 > k2_enumset1 > k1_enumset1 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.17/1.50  
% 3.17/1.50  %Foreground sorts:
% 3.17/1.50  
% 3.17/1.50  
% 3.17/1.50  %Background operators:
% 3.17/1.50  
% 3.17/1.50  
% 3.17/1.50  %Foreground operators:
% 3.17/1.50  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.17/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.17/1.50  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.17/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.50  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 3.17/1.50  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.17/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.17/1.50  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 3.17/1.50  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.17/1.50  tff(v3_lattice3, type, v3_lattice3: $i > $o).
% 3.17/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.17/1.50  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 3.17/1.50  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 3.17/1.50  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 3.17/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.17/1.50  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 3.17/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.17/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.17/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.17/1.50  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.17/1.50  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.17/1.50  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.17/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.17/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.17/1.50  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.17/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.17/1.50  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 3.17/1.50  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.17/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.17/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.17/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.17/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.17/1.50  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.17/1.50  
% 3.33/1.52  tff(f_116, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 3.33/1.52  tff(f_114, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.33/1.52  tff(f_152, negated_conjecture, ~(![A, B]: (m1_subset_1(B, u1_struct_0(k3_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k3_yellow_1(A))) => ((k13_lattice3(k3_yellow_1(A), B, C) = k2_xboole_0(B, C)) & (k12_lattice3(k3_yellow_1(A), B, C) = k3_xboole_0(B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_yellow_1)).
% 3.33/1.52  tff(f_97, axiom, (![A]: ((((~v2_struct_0(k3_yellow_1(A)) & v1_orders_2(k3_yellow_1(A))) & v3_orders_2(k3_yellow_1(A))) & v4_orders_2(k3_yellow_1(A))) & v5_orders_2(k3_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_yellow_1)).
% 3.33/1.52  tff(f_78, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.33/1.52  tff(f_101, axiom, (![A]: (v1_orders_2(k3_yellow_1(A)) & v3_lattice3(k3_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_yellow_1)).
% 3.33/1.52  tff(f_74, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (v3_lattice3(A) => (v1_lattice3(A) & v2_lattice3(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_lattice3)).
% 3.33/1.52  tff(f_51, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 3.33/1.52  tff(f_63, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 3.33/1.52  tff(f_110, axiom, (![A, B]: (m1_subset_1(B, u1_struct_0(k3_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k3_yellow_1(A))) => (r2_hidden(k3_xboole_0(B, C), k9_setfam_1(A)) & r2_hidden(k2_xboole_0(B, C), k9_setfam_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l19_yellow_1)).
% 3.33/1.52  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.33/1.52  tff(f_129, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r2_hidden(k2_xboole_0(B, C), A) => (k10_lattice3(k2_yellow_1(A), B, C) = k2_xboole_0(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_yellow_1)).
% 3.33/1.52  tff(f_142, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r2_hidden(k3_xboole_0(B, C), A) => (k11_lattice3(k2_yellow_1(A), B, C) = k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_1)).
% 3.33/1.52  tff(c_91, plain, (![A_58]: (k2_yellow_1(k9_setfam_1(A_58))=k3_yellow_1(A_58))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.33/1.52  tff(c_52, plain, (![A_29]: (u1_struct_0(k2_yellow_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.33/1.52  tff(c_97, plain, (![A_58]: (u1_struct_0(k3_yellow_1(A_58))=k9_setfam_1(A_58))), inference(superposition, [status(thm), theory('equality')], [c_91, c_52])).
% 3.33/1.52  tff(c_66, plain, (m1_subset_1('#skF_3', u1_struct_0(k3_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.33/1.52  tff(c_131, plain, (m1_subset_1('#skF_3', k9_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_66])).
% 3.33/1.52  tff(c_64, plain, (m1_subset_1('#skF_4', u1_struct_0(k3_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.33/1.52  tff(c_132, plain, (m1_subset_1('#skF_4', k9_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_64])).
% 3.33/1.52  tff(c_42, plain, (![A_23]: (v5_orders_2(k3_yellow_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.33/1.52  tff(c_34, plain, (![A_23]: (~v2_struct_0(k3_yellow_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.33/1.52  tff(c_24, plain, (![A_21]: (l1_orders_2(k2_yellow_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.33/1.52  tff(c_99, plain, (![A_58]: (l1_orders_2(k3_yellow_1(A_58)))), inference(superposition, [status(thm), theory('equality')], [c_91, c_24])).
% 3.33/1.52  tff(c_46, plain, (![A_24]: (v3_lattice3(k3_yellow_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.33/1.52  tff(c_522, plain, (![A_136]: (v2_lattice3(A_136) | ~v3_lattice3(A_136) | ~l1_orders_2(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.33/1.52  tff(c_525, plain, (![A_24]: (v2_lattice3(k3_yellow_1(A_24)) | ~l1_orders_2(k3_yellow_1(A_24)) | v2_struct_0(k3_yellow_1(A_24)))), inference(resolution, [status(thm)], [c_46, c_522])).
% 3.33/1.52  tff(c_528, plain, (![A_24]: (v2_lattice3(k3_yellow_1(A_24)) | v2_struct_0(k3_yellow_1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_525])).
% 3.33/1.52  tff(c_529, plain, (![A_24]: (v2_lattice3(k3_yellow_1(A_24)))), inference(negUnitSimplification, [status(thm)], [c_34, c_528])).
% 3.33/1.52  tff(c_566, plain, (![A_153, B_154, C_155]: (k12_lattice3(A_153, B_154, C_155)=k11_lattice3(A_153, B_154, C_155) | ~m1_subset_1(C_155, u1_struct_0(A_153)) | ~m1_subset_1(B_154, u1_struct_0(A_153)) | ~l1_orders_2(A_153) | ~v2_lattice3(A_153) | ~v5_orders_2(A_153))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.33/1.52  tff(c_568, plain, (![A_58, B_154, C_155]: (k12_lattice3(k3_yellow_1(A_58), B_154, C_155)=k11_lattice3(k3_yellow_1(A_58), B_154, C_155) | ~m1_subset_1(C_155, k9_setfam_1(A_58)) | ~m1_subset_1(B_154, u1_struct_0(k3_yellow_1(A_58))) | ~l1_orders_2(k3_yellow_1(A_58)) | ~v2_lattice3(k3_yellow_1(A_58)) | ~v5_orders_2(k3_yellow_1(A_58)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_566])).
% 3.33/1.52  tff(c_575, plain, (![A_156, B_157, C_158]: (k12_lattice3(k3_yellow_1(A_156), B_157, C_158)=k11_lattice3(k3_yellow_1(A_156), B_157, C_158) | ~m1_subset_1(C_158, k9_setfam_1(A_156)) | ~m1_subset_1(B_157, k9_setfam_1(A_156)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_529, c_99, c_97, c_568])).
% 3.33/1.52  tff(c_582, plain, (![B_159]: (k12_lattice3(k3_yellow_1('#skF_2'), B_159, '#skF_4')=k11_lattice3(k3_yellow_1('#skF_2'), B_159, '#skF_4') | ~m1_subset_1(B_159, k9_setfam_1('#skF_2')))), inference(resolution, [status(thm)], [c_132, c_575])).
% 3.33/1.52  tff(c_590, plain, (k12_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k11_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_131, c_582])).
% 3.33/1.52  tff(c_193, plain, (![A_74]: (v1_lattice3(A_74) | ~v3_lattice3(A_74) | ~l1_orders_2(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.33/1.52  tff(c_196, plain, (![A_24]: (v1_lattice3(k3_yellow_1(A_24)) | ~l1_orders_2(k3_yellow_1(A_24)) | v2_struct_0(k3_yellow_1(A_24)))), inference(resolution, [status(thm)], [c_46, c_193])).
% 3.33/1.52  tff(c_199, plain, (![A_24]: (v1_lattice3(k3_yellow_1(A_24)) | v2_struct_0(k3_yellow_1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_196])).
% 3.33/1.52  tff(c_200, plain, (![A_24]: (v1_lattice3(k3_yellow_1(A_24)))), inference(negUnitSimplification, [status(thm)], [c_34, c_199])).
% 3.33/1.52  tff(c_292, plain, (![A_102, B_103, C_104]: (k13_lattice3(A_102, B_103, C_104)=k10_lattice3(A_102, B_103, C_104) | ~m1_subset_1(C_104, u1_struct_0(A_102)) | ~m1_subset_1(B_103, u1_struct_0(A_102)) | ~l1_orders_2(A_102) | ~v1_lattice3(A_102) | ~v5_orders_2(A_102))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.33/1.52  tff(c_294, plain, (![A_58, B_103, C_104]: (k13_lattice3(k3_yellow_1(A_58), B_103, C_104)=k10_lattice3(k3_yellow_1(A_58), B_103, C_104) | ~m1_subset_1(C_104, k9_setfam_1(A_58)) | ~m1_subset_1(B_103, u1_struct_0(k3_yellow_1(A_58))) | ~l1_orders_2(k3_yellow_1(A_58)) | ~v1_lattice3(k3_yellow_1(A_58)) | ~v5_orders_2(k3_yellow_1(A_58)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_292])).
% 3.33/1.52  tff(c_301, plain, (![A_105, B_106, C_107]: (k13_lattice3(k3_yellow_1(A_105), B_106, C_107)=k10_lattice3(k3_yellow_1(A_105), B_106, C_107) | ~m1_subset_1(C_107, k9_setfam_1(A_105)) | ~m1_subset_1(B_106, k9_setfam_1(A_105)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_200, c_99, c_97, c_294])).
% 3.33/1.52  tff(c_308, plain, (![B_108]: (k13_lattice3(k3_yellow_1('#skF_2'), B_108, '#skF_4')=k10_lattice3(k3_yellow_1('#skF_2'), B_108, '#skF_4') | ~m1_subset_1(B_108, k9_setfam_1('#skF_2')))), inference(resolution, [status(thm)], [c_132, c_301])).
% 3.33/1.52  tff(c_316, plain, (k13_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k10_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_131, c_308])).
% 3.33/1.52  tff(c_62, plain, (k12_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')!=k3_xboole_0('#skF_3', '#skF_4') | k13_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')!=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.33/1.52  tff(c_142, plain, (k13_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')!=k2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_62])).
% 3.33/1.52  tff(c_321, plain, (k10_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')!=k2_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_142])).
% 3.33/1.52  tff(c_50, plain, (![B_26, C_28, A_25]: (r2_hidden(k3_xboole_0(B_26, C_28), k9_setfam_1(A_25)) | ~m1_subset_1(C_28, u1_struct_0(k3_yellow_1(A_25))) | ~m1_subset_1(B_26, u1_struct_0(k3_yellow_1(A_25))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.33/1.52  tff(c_212, plain, (![B_79, C_80, A_81]: (r2_hidden(k3_xboole_0(B_79, C_80), k9_setfam_1(A_81)) | ~m1_subset_1(C_80, k9_setfam_1(A_81)) | ~m1_subset_1(B_79, k9_setfam_1(A_81)))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_97, c_50])).
% 3.33/1.52  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.52  tff(c_217, plain, (![A_82, C_83, B_84]: (~v1_xboole_0(k9_setfam_1(A_82)) | ~m1_subset_1(C_83, k9_setfam_1(A_82)) | ~m1_subset_1(B_84, k9_setfam_1(A_82)))), inference(resolution, [status(thm)], [c_212, c_2])).
% 3.33/1.52  tff(c_222, plain, (![B_84]: (~v1_xboole_0(k9_setfam_1('#skF_2')) | ~m1_subset_1(B_84, k9_setfam_1('#skF_2')))), inference(resolution, [status(thm)], [c_132, c_217])).
% 3.33/1.52  tff(c_230, plain, (~v1_xboole_0(k9_setfam_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_222])).
% 3.33/1.52  tff(c_56, plain, (![A_30]: (k2_yellow_1(k9_setfam_1(A_30))=k3_yellow_1(A_30))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.33/1.52  tff(c_48, plain, (![B_26, C_28, A_25]: (r2_hidden(k2_xboole_0(B_26, C_28), k9_setfam_1(A_25)) | ~m1_subset_1(C_28, u1_struct_0(k3_yellow_1(A_25))) | ~m1_subset_1(B_26, u1_struct_0(k3_yellow_1(A_25))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.33/1.52  tff(c_224, plain, (![B_26, C_28, A_25]: (r2_hidden(k2_xboole_0(B_26, C_28), k9_setfam_1(A_25)) | ~m1_subset_1(C_28, k9_setfam_1(A_25)) | ~m1_subset_1(B_26, k9_setfam_1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_97, c_48])).
% 3.33/1.53  tff(c_58, plain, (![A_31, B_35, C_37]: (k10_lattice3(k2_yellow_1(A_31), B_35, C_37)=k2_xboole_0(B_35, C_37) | ~r2_hidden(k2_xboole_0(B_35, C_37), A_31) | ~m1_subset_1(C_37, u1_struct_0(k2_yellow_1(A_31))) | ~m1_subset_1(B_35, u1_struct_0(k2_yellow_1(A_31))) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.33/1.53  tff(c_326, plain, (![A_109, B_110, C_111]: (k10_lattice3(k2_yellow_1(A_109), B_110, C_111)=k2_xboole_0(B_110, C_111) | ~r2_hidden(k2_xboole_0(B_110, C_111), A_109) | ~m1_subset_1(C_111, A_109) | ~m1_subset_1(B_110, A_109) | v1_xboole_0(A_109))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_58])).
% 3.33/1.53  tff(c_329, plain, (![A_25, B_26, C_28]: (k10_lattice3(k2_yellow_1(k9_setfam_1(A_25)), B_26, C_28)=k2_xboole_0(B_26, C_28) | v1_xboole_0(k9_setfam_1(A_25)) | ~m1_subset_1(C_28, k9_setfam_1(A_25)) | ~m1_subset_1(B_26, k9_setfam_1(A_25)))), inference(resolution, [status(thm)], [c_224, c_326])).
% 3.33/1.53  tff(c_388, plain, (![A_120, B_121, C_122]: (k10_lattice3(k3_yellow_1(A_120), B_121, C_122)=k2_xboole_0(B_121, C_122) | v1_xboole_0(k9_setfam_1(A_120)) | ~m1_subset_1(C_122, k9_setfam_1(A_120)) | ~m1_subset_1(B_121, k9_setfam_1(A_120)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_329])).
% 3.33/1.53  tff(c_390, plain, (![B_121]: (k10_lattice3(k3_yellow_1('#skF_2'), B_121, '#skF_4')=k2_xboole_0(B_121, '#skF_4') | v1_xboole_0(k9_setfam_1('#skF_2')) | ~m1_subset_1(B_121, k9_setfam_1('#skF_2')))), inference(resolution, [status(thm)], [c_132, c_388])).
% 3.33/1.53  tff(c_449, plain, (![B_125]: (k10_lattice3(k3_yellow_1('#skF_2'), B_125, '#skF_4')=k2_xboole_0(B_125, '#skF_4') | ~m1_subset_1(B_125, k9_setfam_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_230, c_390])).
% 3.33/1.53  tff(c_455, plain, (k10_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_131, c_449])).
% 3.33/1.53  tff(c_460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_321, c_455])).
% 3.33/1.53  tff(c_461, plain, (![B_84]: (~m1_subset_1(B_84, k9_setfam_1('#skF_2')))), inference(splitRight, [status(thm)], [c_222])).
% 3.33/1.53  tff(c_465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_461, c_132])).
% 3.33/1.53  tff(c_466, plain, (k12_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')!=k3_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_62])).
% 3.33/1.53  tff(c_595, plain, (k11_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')!=k3_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_590, c_466])).
% 3.33/1.53  tff(c_541, plain, (![B_141, C_142, A_143]: (r2_hidden(k3_xboole_0(B_141, C_142), k9_setfam_1(A_143)) | ~m1_subset_1(C_142, k9_setfam_1(A_143)) | ~m1_subset_1(B_141, k9_setfam_1(A_143)))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_97, c_50])).
% 3.33/1.53  tff(c_546, plain, (![A_144, C_145, B_146]: (~v1_xboole_0(k9_setfam_1(A_144)) | ~m1_subset_1(C_145, k9_setfam_1(A_144)) | ~m1_subset_1(B_146, k9_setfam_1(A_144)))), inference(resolution, [status(thm)], [c_541, c_2])).
% 3.33/1.53  tff(c_551, plain, (![B_146]: (~v1_xboole_0(k9_setfam_1('#skF_2')) | ~m1_subset_1(B_146, k9_setfam_1('#skF_2')))), inference(resolution, [status(thm)], [c_132, c_546])).
% 3.33/1.53  tff(c_553, plain, (~v1_xboole_0(k9_setfam_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_551])).
% 3.33/1.53  tff(c_540, plain, (![B_26, C_28, A_25]: (r2_hidden(k3_xboole_0(B_26, C_28), k9_setfam_1(A_25)) | ~m1_subset_1(C_28, k9_setfam_1(A_25)) | ~m1_subset_1(B_26, k9_setfam_1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_97, c_50])).
% 3.33/1.53  tff(c_60, plain, (![A_38, B_42, C_44]: (k11_lattice3(k2_yellow_1(A_38), B_42, C_44)=k3_xboole_0(B_42, C_44) | ~r2_hidden(k3_xboole_0(B_42, C_44), A_38) | ~m1_subset_1(C_44, u1_struct_0(k2_yellow_1(A_38))) | ~m1_subset_1(B_42, u1_struct_0(k2_yellow_1(A_38))) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.33/1.53  tff(c_560, plain, (![A_150, B_151, C_152]: (k11_lattice3(k2_yellow_1(A_150), B_151, C_152)=k3_xboole_0(B_151, C_152) | ~r2_hidden(k3_xboole_0(B_151, C_152), A_150) | ~m1_subset_1(C_152, A_150) | ~m1_subset_1(B_151, A_150) | v1_xboole_0(A_150))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_60])).
% 3.33/1.53  tff(c_563, plain, (![A_25, B_26, C_28]: (k11_lattice3(k2_yellow_1(k9_setfam_1(A_25)), B_26, C_28)=k3_xboole_0(B_26, C_28) | v1_xboole_0(k9_setfam_1(A_25)) | ~m1_subset_1(C_28, k9_setfam_1(A_25)) | ~m1_subset_1(B_26, k9_setfam_1(A_25)))), inference(resolution, [status(thm)], [c_540, c_560])).
% 3.33/1.53  tff(c_684, plain, (![A_178, B_179, C_180]: (k11_lattice3(k3_yellow_1(A_178), B_179, C_180)=k3_xboole_0(B_179, C_180) | v1_xboole_0(k9_setfam_1(A_178)) | ~m1_subset_1(C_180, k9_setfam_1(A_178)) | ~m1_subset_1(B_179, k9_setfam_1(A_178)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_563])).
% 3.33/1.53  tff(c_686, plain, (![B_179]: (k11_lattice3(k3_yellow_1('#skF_2'), B_179, '#skF_4')=k3_xboole_0(B_179, '#skF_4') | v1_xboole_0(k9_setfam_1('#skF_2')) | ~m1_subset_1(B_179, k9_setfam_1('#skF_2')))), inference(resolution, [status(thm)], [c_132, c_684])).
% 3.33/1.53  tff(c_695, plain, (![B_181]: (k11_lattice3(k3_yellow_1('#skF_2'), B_181, '#skF_4')=k3_xboole_0(B_181, '#skF_4') | ~m1_subset_1(B_181, k9_setfam_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_553, c_686])).
% 3.33/1.53  tff(c_701, plain, (k11_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k3_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_131, c_695])).
% 3.33/1.53  tff(c_706, plain, $false, inference(negUnitSimplification, [status(thm)], [c_595, c_701])).
% 3.33/1.53  tff(c_707, plain, (![B_146]: (~m1_subset_1(B_146, k9_setfam_1('#skF_2')))), inference(splitRight, [status(thm)], [c_551])).
% 3.33/1.53  tff(c_711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_707, c_132])).
% 3.33/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.53  
% 3.33/1.53  Inference rules
% 3.33/1.53  ----------------------
% 3.33/1.53  #Ref     : 0
% 3.33/1.53  #Sup     : 159
% 3.33/1.53  #Fact    : 0
% 3.33/1.53  #Define  : 0
% 3.33/1.53  #Split   : 3
% 3.33/1.53  #Chain   : 0
% 3.33/1.53  #Close   : 0
% 3.33/1.53  
% 3.33/1.53  Ordering : KBO
% 3.33/1.53  
% 3.33/1.53  Simplification rules
% 3.33/1.53  ----------------------
% 3.33/1.53  #Subsume      : 8
% 3.33/1.53  #Demod        : 77
% 3.33/1.53  #Tautology    : 90
% 3.33/1.53  #SimpNegUnit  : 16
% 3.33/1.53  #BackRed      : 14
% 3.33/1.53  
% 3.33/1.53  #Partial instantiations: 0
% 3.33/1.53  #Strategies tried      : 1
% 3.33/1.53  
% 3.33/1.53  Timing (in seconds)
% 3.33/1.53  ----------------------
% 3.33/1.53  Preprocessing        : 0.37
% 3.33/1.53  Parsing              : 0.21
% 3.33/1.53  CNF conversion       : 0.02
% 3.33/1.53  Main loop            : 0.36
% 3.33/1.53  Inferencing          : 0.13
% 3.33/1.53  Reduction            : 0.12
% 3.33/1.53  Demodulation         : 0.08
% 3.33/1.53  BG Simplification    : 0.02
% 3.33/1.53  Subsumption          : 0.05
% 3.33/1.53  Abstraction          : 0.02
% 3.33/1.53  MUC search           : 0.00
% 3.33/1.53  Cooper               : 0.00
% 3.33/1.53  Total                : 0.77
% 3.33/1.53  Index Insertion      : 0.00
% 3.33/1.53  Index Deletion       : 0.00
% 3.33/1.53  Index Matching       : 0.00
% 3.33/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
