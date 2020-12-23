%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:29 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 353 expanded)
%              Number of leaves         :   53 ( 147 expanded)
%              Depth                    :   10
%              Number of atoms          :  222 ( 586 expanded)
%              Number of equality atoms :   45 ( 268 expanded)
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

tff(f_157,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
       => ! [C] :
            ( m1_subset_1(C,u1_struct_0(k3_yellow_1(A)))
           => ( k13_lattice3(k3_yellow_1(A),B,C) = k2_xboole_0(B,C)
              & k12_lattice3(k3_yellow_1(A),B,C) = k3_xboole_0(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_1)).

tff(f_121,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_119,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_115,axiom,(
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

tff(f_134,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r2_hidden(k2_xboole_0(B,C),A)
               => k10_lattice3(k2_yellow_1(A),B,C) = k2_xboole_0(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_yellow_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k3_yellow_1(A))
      & v1_orders_2(k3_yellow_1(A))
      & v3_orders_2(k3_yellow_1(A))
      & v4_orders_2(k3_yellow_1(A))
      & v5_orders_2(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_yellow_1)).

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
      ( v1_orders_2(k3_yellow_1(A))
      & l1_orders_2(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_147,axiom,(
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

tff(c_66,plain,
    ( k12_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') != k3_xboole_0('#skF_3','#skF_4')
    | k13_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') != k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_140,plain,(
    k13_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') != k2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_104,plain,(
    ! [A_53] : k2_yellow_1(k9_setfam_1(A_53)) = k3_yellow_1(A_53) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_56,plain,(
    ! [A_24] : u1_struct_0(k2_yellow_1(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_110,plain,(
    ! [A_53] : u1_struct_0(k3_yellow_1(A_53)) = k9_setfam_1(A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_56])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k3_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_129,plain,(
    m1_subset_1('#skF_3',k9_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_70])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k3_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_130,plain,(
    m1_subset_1('#skF_4',k9_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_68])).

tff(c_54,plain,(
    ! [B_21,C_23,A_20] :
      ( r2_hidden(k3_xboole_0(B_21,C_23),k9_setfam_1(A_20))
      | ~ m1_subset_1(C_23,u1_struct_0(k3_yellow_1(A_20)))
      | ~ m1_subset_1(B_21,u1_struct_0(k3_yellow_1(A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_209,plain,(
    ! [B_70,C_71,A_72] :
      ( r2_hidden(k3_xboole_0(B_70,C_71),k9_setfam_1(A_72))
      | ~ m1_subset_1(C_71,k9_setfam_1(A_72))
      | ~ m1_subset_1(B_70,k9_setfam_1(A_72)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_110,c_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_214,plain,(
    ! [A_73,C_74,B_75] :
      ( ~ v1_xboole_0(k9_setfam_1(A_73))
      | ~ m1_subset_1(C_74,k9_setfam_1(A_73))
      | ~ m1_subset_1(B_75,k9_setfam_1(A_73)) ) ),
    inference(resolution,[status(thm)],[c_209,c_2])).

tff(c_219,plain,(
    ! [B_75] :
      ( ~ v1_xboole_0(k9_setfam_1('#skF_2'))
      | ~ m1_subset_1(B_75,k9_setfam_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_130,c_214])).

tff(c_227,plain,(
    ~ v1_xboole_0(k9_setfam_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_60,plain,(
    ! [A_25] : k2_yellow_1(k9_setfam_1(A_25)) = k3_yellow_1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_52,plain,(
    ! [B_21,C_23,A_20] :
      ( r2_hidden(k2_xboole_0(B_21,C_23),k9_setfam_1(A_20))
      | ~ m1_subset_1(C_23,u1_struct_0(k3_yellow_1(A_20)))
      | ~ m1_subset_1(B_21,u1_struct_0(k3_yellow_1(A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_221,plain,(
    ! [B_21,C_23,A_20] :
      ( r2_hidden(k2_xboole_0(B_21,C_23),k9_setfam_1(A_20))
      | ~ m1_subset_1(C_23,k9_setfam_1(A_20))
      | ~ m1_subset_1(B_21,k9_setfam_1(A_20)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_110,c_52])).

tff(c_62,plain,(
    ! [A_26,B_30,C_32] :
      ( k10_lattice3(k2_yellow_1(A_26),B_30,C_32) = k2_xboole_0(B_30,C_32)
      | ~ r2_hidden(k2_xboole_0(B_30,C_32),A_26)
      | ~ m1_subset_1(C_32,u1_struct_0(k2_yellow_1(A_26)))
      | ~ m1_subset_1(B_30,u1_struct_0(k2_yellow_1(A_26)))
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_269,plain,(
    ! [A_87,B_88,C_89] :
      ( k10_lattice3(k2_yellow_1(A_87),B_88,C_89) = k2_xboole_0(B_88,C_89)
      | ~ r2_hidden(k2_xboole_0(B_88,C_89),A_87)
      | ~ m1_subset_1(C_89,A_87)
      | ~ m1_subset_1(B_88,A_87)
      | v1_xboole_0(A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_62])).

tff(c_272,plain,(
    ! [A_20,B_21,C_23] :
      ( k10_lattice3(k2_yellow_1(k9_setfam_1(A_20)),B_21,C_23) = k2_xboole_0(B_21,C_23)
      | v1_xboole_0(k9_setfam_1(A_20))
      | ~ m1_subset_1(C_23,k9_setfam_1(A_20))
      | ~ m1_subset_1(B_21,k9_setfam_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_221,c_269])).

tff(c_283,plain,(
    ! [A_90,B_91,C_92] :
      ( k10_lattice3(k3_yellow_1(A_90),B_91,C_92) = k2_xboole_0(B_91,C_92)
      | v1_xboole_0(k9_setfam_1(A_90))
      | ~ m1_subset_1(C_92,k9_setfam_1(A_90))
      | ~ m1_subset_1(B_91,k9_setfam_1(A_90)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_272])).

tff(c_285,plain,(
    ! [B_91] :
      ( k10_lattice3(k3_yellow_1('#skF_2'),B_91,'#skF_4') = k2_xboole_0(B_91,'#skF_4')
      | v1_xboole_0(k9_setfam_1('#skF_2'))
      | ~ m1_subset_1(B_91,k9_setfam_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_130,c_283])).

tff(c_294,plain,(
    ! [B_93] :
      ( k10_lattice3(k3_yellow_1('#skF_2'),B_93,'#skF_4') = k2_xboole_0(B_93,'#skF_4')
      | ~ m1_subset_1(B_93,k9_setfam_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_285])).

tff(c_302,plain,(
    k10_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_129,c_294])).

tff(c_50,plain,(
    ! [A_19] : v5_orders_2(k3_yellow_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

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

tff(c_186,plain,(
    ! [A_66] :
      ( v1_lattice3(k3_lattice3(A_66))
      | ~ l3_lattices(A_66)
      | ~ v10_lattices(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_189,plain,(
    ! [A_16] :
      ( v1_lattice3(k3_yellow_1(A_16))
      | ~ l3_lattices(k1_lattice3(A_16))
      | ~ v10_lattices(k1_lattice3(A_16))
      | v2_struct_0(k1_lattice3(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_186])).

tff(c_191,plain,(
    ! [A_16] :
      ( v1_lattice3(k3_yellow_1(A_16))
      | v2_struct_0(k1_lattice3(A_16)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_10,c_189])).

tff(c_192,plain,(
    ! [A_16] : v1_lattice3(k3_yellow_1(A_16)) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_191])).

tff(c_28,plain,(
    ! [A_17] : l1_orders_2(k3_yellow_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_391,plain,(
    ! [A_103,B_104,C_105] :
      ( k13_lattice3(A_103,B_104,C_105) = k10_lattice3(A_103,B_104,C_105)
      | ~ m1_subset_1(C_105,u1_struct_0(A_103))
      | ~ m1_subset_1(B_104,u1_struct_0(A_103))
      | ~ l1_orders_2(A_103)
      | ~ v1_lattice3(A_103)
      | ~ v5_orders_2(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_393,plain,(
    ! [A_53,B_104,C_105] :
      ( k13_lattice3(k3_yellow_1(A_53),B_104,C_105) = k10_lattice3(k3_yellow_1(A_53),B_104,C_105)
      | ~ m1_subset_1(C_105,k9_setfam_1(A_53))
      | ~ m1_subset_1(B_104,u1_struct_0(k3_yellow_1(A_53)))
      | ~ l1_orders_2(k3_yellow_1(A_53))
      | ~ v1_lattice3(k3_yellow_1(A_53))
      | ~ v5_orders_2(k3_yellow_1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_391])).

tff(c_407,plain,(
    ! [A_106,B_107,C_108] :
      ( k13_lattice3(k3_yellow_1(A_106),B_107,C_108) = k10_lattice3(k3_yellow_1(A_106),B_107,C_108)
      | ~ m1_subset_1(C_108,k9_setfam_1(A_106))
      | ~ m1_subset_1(B_107,k9_setfam_1(A_106)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_192,c_28,c_110,c_393])).

tff(c_414,plain,(
    ! [B_109] :
      ( k13_lattice3(k3_yellow_1('#skF_2'),B_109,'#skF_4') = k10_lattice3(k3_yellow_1('#skF_2'),B_109,'#skF_4')
      | ~ m1_subset_1(B_109,k9_setfam_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_130,c_407])).

tff(c_420,plain,(
    k13_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') = k10_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_129,c_414])).

tff(c_424,plain,(
    k13_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_420])).

tff(c_426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_424])).

tff(c_427,plain,(
    ! [B_75] : ~ m1_subset_1(B_75,k9_setfam_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_130])).

tff(c_432,plain,(
    k12_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') != k3_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_506,plain,(
    ! [B_122,C_123,A_124] :
      ( r2_hidden(k3_xboole_0(B_122,C_123),k9_setfam_1(A_124))
      | ~ m1_subset_1(C_123,k9_setfam_1(A_124))
      | ~ m1_subset_1(B_122,k9_setfam_1(A_124)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_110,c_54])).

tff(c_511,plain,(
    ! [A_125,C_126,B_127] :
      ( ~ v1_xboole_0(k9_setfam_1(A_125))
      | ~ m1_subset_1(C_126,k9_setfam_1(A_125))
      | ~ m1_subset_1(B_127,k9_setfam_1(A_125)) ) ),
    inference(resolution,[status(thm)],[c_506,c_2])).

tff(c_516,plain,(
    ! [B_127] :
      ( ~ v1_xboole_0(k9_setfam_1('#skF_2'))
      | ~ m1_subset_1(B_127,k9_setfam_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_130,c_511])).

tff(c_518,plain,(
    ~ v1_xboole_0(k9_setfam_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_516])).

tff(c_505,plain,(
    ! [B_21,C_23,A_20] :
      ( r2_hidden(k3_xboole_0(B_21,C_23),k9_setfam_1(A_20))
      | ~ m1_subset_1(C_23,k9_setfam_1(A_20))
      | ~ m1_subset_1(B_21,k9_setfam_1(A_20)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_110,c_54])).

tff(c_64,plain,(
    ! [A_33,B_37,C_39] :
      ( k11_lattice3(k2_yellow_1(A_33),B_37,C_39) = k3_xboole_0(B_37,C_39)
      | ~ r2_hidden(k3_xboole_0(B_37,C_39),A_33)
      | ~ m1_subset_1(C_39,u1_struct_0(k2_yellow_1(A_33)))
      | ~ m1_subset_1(B_37,u1_struct_0(k2_yellow_1(A_33)))
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_543,plain,(
    ! [A_137,B_138,C_139] :
      ( k11_lattice3(k2_yellow_1(A_137),B_138,C_139) = k3_xboole_0(B_138,C_139)
      | ~ r2_hidden(k3_xboole_0(B_138,C_139),A_137)
      | ~ m1_subset_1(C_139,A_137)
      | ~ m1_subset_1(B_138,A_137)
      | v1_xboole_0(A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_64])).

tff(c_546,plain,(
    ! [A_20,B_21,C_23] :
      ( k11_lattice3(k2_yellow_1(k9_setfam_1(A_20)),B_21,C_23) = k3_xboole_0(B_21,C_23)
      | v1_xboole_0(k9_setfam_1(A_20))
      | ~ m1_subset_1(C_23,k9_setfam_1(A_20))
      | ~ m1_subset_1(B_21,k9_setfam_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_505,c_543])).

tff(c_583,plain,(
    ! [A_142,B_143,C_144] :
      ( k11_lattice3(k3_yellow_1(A_142),B_143,C_144) = k3_xboole_0(B_143,C_144)
      | v1_xboole_0(k9_setfam_1(A_142))
      | ~ m1_subset_1(C_144,k9_setfam_1(A_142))
      | ~ m1_subset_1(B_143,k9_setfam_1(A_142)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_546])).

tff(c_585,plain,(
    ! [B_143] :
      ( k11_lattice3(k3_yellow_1('#skF_2'),B_143,'#skF_4') = k3_xboole_0(B_143,'#skF_4')
      | v1_xboole_0(k9_setfam_1('#skF_2'))
      | ~ m1_subset_1(B_143,k9_setfam_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_130,c_583])).

tff(c_594,plain,(
    ! [B_145] :
      ( k11_lattice3(k3_yellow_1('#skF_2'),B_145,'#skF_4') = k3_xboole_0(B_145,'#skF_4')
      | ~ m1_subset_1(B_145,k9_setfam_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_518,c_585])).

tff(c_602,plain,(
    k11_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_129,c_594])).

tff(c_482,plain,(
    ! [A_117] :
      ( v2_lattice3(k3_lattice3(A_117))
      | ~ l3_lattices(A_117)
      | ~ v10_lattices(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_485,plain,(
    ! [A_16] :
      ( v2_lattice3(k3_yellow_1(A_16))
      | ~ l3_lattices(k1_lattice3(A_16))
      | ~ v10_lattices(k1_lattice3(A_16))
      | v2_struct_0(k1_lattice3(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_482])).

tff(c_487,plain,(
    ! [A_16] :
      ( v2_lattice3(k3_yellow_1(A_16))
      | v2_struct_0(k1_lattice3(A_16)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_10,c_485])).

tff(c_488,plain,(
    ! [A_16] : v2_lattice3(k3_yellow_1(A_16)) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_487])).

tff(c_607,plain,(
    ! [A_146,B_147,C_148] :
      ( k12_lattice3(A_146,B_147,C_148) = k11_lattice3(A_146,B_147,C_148)
      | ~ m1_subset_1(C_148,u1_struct_0(A_146))
      | ~ m1_subset_1(B_147,u1_struct_0(A_146))
      | ~ l1_orders_2(A_146)
      | ~ v2_lattice3(A_146)
      | ~ v5_orders_2(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_609,plain,(
    ! [A_53,B_147,C_148] :
      ( k12_lattice3(k3_yellow_1(A_53),B_147,C_148) = k11_lattice3(k3_yellow_1(A_53),B_147,C_148)
      | ~ m1_subset_1(C_148,k9_setfam_1(A_53))
      | ~ m1_subset_1(B_147,u1_struct_0(k3_yellow_1(A_53)))
      | ~ l1_orders_2(k3_yellow_1(A_53))
      | ~ v2_lattice3(k3_yellow_1(A_53))
      | ~ v5_orders_2(k3_yellow_1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_607])).

tff(c_636,plain,(
    ! [A_150,B_151,C_152] :
      ( k12_lattice3(k3_yellow_1(A_150),B_151,C_152) = k11_lattice3(k3_yellow_1(A_150),B_151,C_152)
      | ~ m1_subset_1(C_152,k9_setfam_1(A_150))
      | ~ m1_subset_1(B_151,k9_setfam_1(A_150)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_488,c_28,c_110,c_609])).

tff(c_643,plain,(
    ! [B_153] :
      ( k12_lattice3(k3_yellow_1('#skF_2'),B_153,'#skF_4') = k11_lattice3(k3_yellow_1('#skF_2'),B_153,'#skF_4')
      | ~ m1_subset_1(B_153,k9_setfam_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_130,c_636])).

tff(c_649,plain,(
    k12_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') = k11_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_129,c_643])).

tff(c_653,plain,(
    k12_lattice3(k3_yellow_1('#skF_2'),'#skF_3','#skF_4') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_649])).

tff(c_655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_432,c_653])).

tff(c_656,plain,(
    ! [B_127] : ~ m1_subset_1(B_127,k9_setfam_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_516])).

tff(c_660,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_656,c_130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.72  
% 3.49/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.72  %$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v3_lattices > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > v10_lattices > l3_lattices > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k3_yellow_1 > k3_lattice3 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > k1_lattice3 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.49/1.72  
% 3.49/1.72  %Foreground sorts:
% 3.49/1.72  
% 3.49/1.72  
% 3.49/1.72  %Background operators:
% 3.49/1.72  
% 3.49/1.72  
% 3.49/1.72  %Foreground operators:
% 3.49/1.72  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.49/1.72  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.49/1.72  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.49/1.72  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.49/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.72  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.49/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.72  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 3.49/1.72  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.49/1.72  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.49/1.72  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 3.49/1.72  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.49/1.72  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 3.49/1.72  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 3.49/1.72  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 3.49/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.49/1.72  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 3.49/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.49/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.72  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.49/1.72  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.49/1.72  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.49/1.72  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.49/1.72  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.49/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.72  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.72  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.49/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.72  tff(v3_lattices, type, v3_lattices: $i > $o).
% 3.49/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.49/1.72  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 3.49/1.72  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.49/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.49/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.49/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.49/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.72  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.49/1.72  
% 3.49/1.76  tff(f_157, negated_conjecture, ~(![A, B]: (m1_subset_1(B, u1_struct_0(k3_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k3_yellow_1(A))) => ((k13_lattice3(k3_yellow_1(A), B, C) = k2_xboole_0(B, C)) & (k12_lattice3(k3_yellow_1(A), B, C) = k3_xboole_0(B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_yellow_1)).
% 3.49/1.76  tff(f_121, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 3.49/1.76  tff(f_119, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.49/1.76  tff(f_115, axiom, (![A, B]: (m1_subset_1(B, u1_struct_0(k3_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k3_yellow_1(A))) => (r2_hidden(k3_xboole_0(B, C), k9_setfam_1(A)) & r2_hidden(k2_xboole_0(B, C), k9_setfam_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l19_yellow_1)).
% 3.49/1.76  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.49/1.76  tff(f_134, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r2_hidden(k2_xboole_0(B, C), A) => (k10_lattice3(k2_yellow_1(A), B, C) = k2_xboole_0(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_yellow_1)).
% 3.49/1.76  tff(f_106, axiom, (![A]: ((((~v2_struct_0(k3_yellow_1(A)) & v1_orders_2(k3_yellow_1(A))) & v3_orders_2(k3_yellow_1(A))) & v4_orders_2(k3_yellow_1(A))) & v5_orders_2(k3_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_yellow_1)).
% 3.49/1.76  tff(f_42, axiom, (![A]: (~v2_struct_0(k1_lattice3(A)) & v3_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_lattice3)).
% 3.49/1.76  tff(f_46, axiom, (![A]: (v3_lattices(k1_lattice3(A)) & v10_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_lattice3)).
% 3.49/1.76  tff(f_37, axiom, (![A]: (v3_lattices(k1_lattice3(A)) & l3_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_lattice3)).
% 3.49/1.76  tff(f_72, axiom, (![A]: (k3_yellow_1(A) = k3_lattice3(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_yellow_1)).
% 3.49/1.76  tff(f_95, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (((((v1_orders_2(k3_lattice3(A)) & v3_orders_2(k3_lattice3(A))) & v4_orders_2(k3_lattice3(A))) & v5_orders_2(k3_lattice3(A))) & v1_lattice3(k3_lattice3(A))) & v2_lattice3(k3_lattice3(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_yellow_1)).
% 3.49/1.76  tff(f_76, axiom, (![A]: (v1_orders_2(k3_yellow_1(A)) & l1_orders_2(k3_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_1)).
% 3.49/1.76  tff(f_70, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 3.49/1.76  tff(f_147, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r2_hidden(k3_xboole_0(B, C), A) => (k11_lattice3(k2_yellow_1(A), B, C) = k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_yellow_1)).
% 3.49/1.76  tff(f_58, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 3.49/1.76  tff(c_66, plain, (k12_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')!=k3_xboole_0('#skF_3', '#skF_4') | k13_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')!=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.49/1.76  tff(c_140, plain, (k13_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')!=k2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_66])).
% 3.49/1.76  tff(c_104, plain, (![A_53]: (k2_yellow_1(k9_setfam_1(A_53))=k3_yellow_1(A_53))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.49/1.76  tff(c_56, plain, (![A_24]: (u1_struct_0(k2_yellow_1(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.49/1.76  tff(c_110, plain, (![A_53]: (u1_struct_0(k3_yellow_1(A_53))=k9_setfam_1(A_53))), inference(superposition, [status(thm), theory('equality')], [c_104, c_56])).
% 3.49/1.76  tff(c_70, plain, (m1_subset_1('#skF_3', u1_struct_0(k3_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.49/1.76  tff(c_129, plain, (m1_subset_1('#skF_3', k9_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_70])).
% 3.49/1.76  tff(c_68, plain, (m1_subset_1('#skF_4', u1_struct_0(k3_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.49/1.76  tff(c_130, plain, (m1_subset_1('#skF_4', k9_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_68])).
% 3.49/1.76  tff(c_54, plain, (![B_21, C_23, A_20]: (r2_hidden(k3_xboole_0(B_21, C_23), k9_setfam_1(A_20)) | ~m1_subset_1(C_23, u1_struct_0(k3_yellow_1(A_20))) | ~m1_subset_1(B_21, u1_struct_0(k3_yellow_1(A_20))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.49/1.76  tff(c_209, plain, (![B_70, C_71, A_72]: (r2_hidden(k3_xboole_0(B_70, C_71), k9_setfam_1(A_72)) | ~m1_subset_1(C_71, k9_setfam_1(A_72)) | ~m1_subset_1(B_70, k9_setfam_1(A_72)))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_110, c_54])).
% 3.49/1.76  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.49/1.76  tff(c_214, plain, (![A_73, C_74, B_75]: (~v1_xboole_0(k9_setfam_1(A_73)) | ~m1_subset_1(C_74, k9_setfam_1(A_73)) | ~m1_subset_1(B_75, k9_setfam_1(A_73)))), inference(resolution, [status(thm)], [c_209, c_2])).
% 3.49/1.76  tff(c_219, plain, (![B_75]: (~v1_xboole_0(k9_setfam_1('#skF_2')) | ~m1_subset_1(B_75, k9_setfam_1('#skF_2')))), inference(resolution, [status(thm)], [c_130, c_214])).
% 3.49/1.76  tff(c_227, plain, (~v1_xboole_0(k9_setfam_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_219])).
% 3.49/1.76  tff(c_60, plain, (![A_25]: (k2_yellow_1(k9_setfam_1(A_25))=k3_yellow_1(A_25))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.49/1.76  tff(c_52, plain, (![B_21, C_23, A_20]: (r2_hidden(k2_xboole_0(B_21, C_23), k9_setfam_1(A_20)) | ~m1_subset_1(C_23, u1_struct_0(k3_yellow_1(A_20))) | ~m1_subset_1(B_21, u1_struct_0(k3_yellow_1(A_20))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.49/1.76  tff(c_221, plain, (![B_21, C_23, A_20]: (r2_hidden(k2_xboole_0(B_21, C_23), k9_setfam_1(A_20)) | ~m1_subset_1(C_23, k9_setfam_1(A_20)) | ~m1_subset_1(B_21, k9_setfam_1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_110, c_52])).
% 3.49/1.76  tff(c_62, plain, (![A_26, B_30, C_32]: (k10_lattice3(k2_yellow_1(A_26), B_30, C_32)=k2_xboole_0(B_30, C_32) | ~r2_hidden(k2_xboole_0(B_30, C_32), A_26) | ~m1_subset_1(C_32, u1_struct_0(k2_yellow_1(A_26))) | ~m1_subset_1(B_30, u1_struct_0(k2_yellow_1(A_26))) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.49/1.76  tff(c_269, plain, (![A_87, B_88, C_89]: (k10_lattice3(k2_yellow_1(A_87), B_88, C_89)=k2_xboole_0(B_88, C_89) | ~r2_hidden(k2_xboole_0(B_88, C_89), A_87) | ~m1_subset_1(C_89, A_87) | ~m1_subset_1(B_88, A_87) | v1_xboole_0(A_87))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_62])).
% 3.49/1.76  tff(c_272, plain, (![A_20, B_21, C_23]: (k10_lattice3(k2_yellow_1(k9_setfam_1(A_20)), B_21, C_23)=k2_xboole_0(B_21, C_23) | v1_xboole_0(k9_setfam_1(A_20)) | ~m1_subset_1(C_23, k9_setfam_1(A_20)) | ~m1_subset_1(B_21, k9_setfam_1(A_20)))), inference(resolution, [status(thm)], [c_221, c_269])).
% 3.49/1.76  tff(c_283, plain, (![A_90, B_91, C_92]: (k10_lattice3(k3_yellow_1(A_90), B_91, C_92)=k2_xboole_0(B_91, C_92) | v1_xboole_0(k9_setfam_1(A_90)) | ~m1_subset_1(C_92, k9_setfam_1(A_90)) | ~m1_subset_1(B_91, k9_setfam_1(A_90)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_272])).
% 3.49/1.76  tff(c_285, plain, (![B_91]: (k10_lattice3(k3_yellow_1('#skF_2'), B_91, '#skF_4')=k2_xboole_0(B_91, '#skF_4') | v1_xboole_0(k9_setfam_1('#skF_2')) | ~m1_subset_1(B_91, k9_setfam_1('#skF_2')))), inference(resolution, [status(thm)], [c_130, c_283])).
% 3.49/1.76  tff(c_294, plain, (![B_93]: (k10_lattice3(k3_yellow_1('#skF_2'), B_93, '#skF_4')=k2_xboole_0(B_93, '#skF_4') | ~m1_subset_1(B_93, k9_setfam_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_227, c_285])).
% 3.49/1.76  tff(c_302, plain, (k10_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_129, c_294])).
% 3.49/1.76  tff(c_50, plain, (![A_19]: (v5_orders_2(k3_yellow_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.49/1.76  tff(c_12, plain, (![A_8]: (~v2_struct_0(k1_lattice3(A_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.49/1.76  tff(c_18, plain, (![A_9]: (v10_lattices(k1_lattice3(A_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.49/1.76  tff(c_10, plain, (![A_7]: (l3_lattices(k1_lattice3(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.49/1.76  tff(c_24, plain, (![A_16]: (k3_lattice3(k1_lattice3(A_16))=k3_yellow_1(A_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.49/1.76  tff(c_186, plain, (![A_66]: (v1_lattice3(k3_lattice3(A_66)) | ~l3_lattices(A_66) | ~v10_lattices(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.49/1.76  tff(c_189, plain, (![A_16]: (v1_lattice3(k3_yellow_1(A_16)) | ~l3_lattices(k1_lattice3(A_16)) | ~v10_lattices(k1_lattice3(A_16)) | v2_struct_0(k1_lattice3(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_186])).
% 3.49/1.76  tff(c_191, plain, (![A_16]: (v1_lattice3(k3_yellow_1(A_16)) | v2_struct_0(k1_lattice3(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_10, c_189])).
% 3.49/1.76  tff(c_192, plain, (![A_16]: (v1_lattice3(k3_yellow_1(A_16)))), inference(negUnitSimplification, [status(thm)], [c_12, c_191])).
% 3.49/1.76  tff(c_28, plain, (![A_17]: (l1_orders_2(k3_yellow_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.49/1.76  tff(c_391, plain, (![A_103, B_104, C_105]: (k13_lattice3(A_103, B_104, C_105)=k10_lattice3(A_103, B_104, C_105) | ~m1_subset_1(C_105, u1_struct_0(A_103)) | ~m1_subset_1(B_104, u1_struct_0(A_103)) | ~l1_orders_2(A_103) | ~v1_lattice3(A_103) | ~v5_orders_2(A_103))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.49/1.76  tff(c_393, plain, (![A_53, B_104, C_105]: (k13_lattice3(k3_yellow_1(A_53), B_104, C_105)=k10_lattice3(k3_yellow_1(A_53), B_104, C_105) | ~m1_subset_1(C_105, k9_setfam_1(A_53)) | ~m1_subset_1(B_104, u1_struct_0(k3_yellow_1(A_53))) | ~l1_orders_2(k3_yellow_1(A_53)) | ~v1_lattice3(k3_yellow_1(A_53)) | ~v5_orders_2(k3_yellow_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_110, c_391])).
% 3.49/1.76  tff(c_407, plain, (![A_106, B_107, C_108]: (k13_lattice3(k3_yellow_1(A_106), B_107, C_108)=k10_lattice3(k3_yellow_1(A_106), B_107, C_108) | ~m1_subset_1(C_108, k9_setfam_1(A_106)) | ~m1_subset_1(B_107, k9_setfam_1(A_106)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_192, c_28, c_110, c_393])).
% 3.49/1.76  tff(c_414, plain, (![B_109]: (k13_lattice3(k3_yellow_1('#skF_2'), B_109, '#skF_4')=k10_lattice3(k3_yellow_1('#skF_2'), B_109, '#skF_4') | ~m1_subset_1(B_109, k9_setfam_1('#skF_2')))), inference(resolution, [status(thm)], [c_130, c_407])).
% 3.49/1.76  tff(c_420, plain, (k13_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k10_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_129, c_414])).
% 3.49/1.76  tff(c_424, plain, (k13_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_302, c_420])).
% 3.49/1.76  tff(c_426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140, c_424])).
% 3.49/1.76  tff(c_427, plain, (![B_75]: (~m1_subset_1(B_75, k9_setfam_1('#skF_2')))), inference(splitRight, [status(thm)], [c_219])).
% 3.49/1.76  tff(c_431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_427, c_130])).
% 3.49/1.76  tff(c_432, plain, (k12_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')!=k3_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_66])).
% 3.49/1.76  tff(c_506, plain, (![B_122, C_123, A_124]: (r2_hidden(k3_xboole_0(B_122, C_123), k9_setfam_1(A_124)) | ~m1_subset_1(C_123, k9_setfam_1(A_124)) | ~m1_subset_1(B_122, k9_setfam_1(A_124)))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_110, c_54])).
% 3.49/1.76  tff(c_511, plain, (![A_125, C_126, B_127]: (~v1_xboole_0(k9_setfam_1(A_125)) | ~m1_subset_1(C_126, k9_setfam_1(A_125)) | ~m1_subset_1(B_127, k9_setfam_1(A_125)))), inference(resolution, [status(thm)], [c_506, c_2])).
% 3.49/1.76  tff(c_516, plain, (![B_127]: (~v1_xboole_0(k9_setfam_1('#skF_2')) | ~m1_subset_1(B_127, k9_setfam_1('#skF_2')))), inference(resolution, [status(thm)], [c_130, c_511])).
% 3.49/1.76  tff(c_518, plain, (~v1_xboole_0(k9_setfam_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_516])).
% 3.49/1.76  tff(c_505, plain, (![B_21, C_23, A_20]: (r2_hidden(k3_xboole_0(B_21, C_23), k9_setfam_1(A_20)) | ~m1_subset_1(C_23, k9_setfam_1(A_20)) | ~m1_subset_1(B_21, k9_setfam_1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_110, c_54])).
% 3.49/1.76  tff(c_64, plain, (![A_33, B_37, C_39]: (k11_lattice3(k2_yellow_1(A_33), B_37, C_39)=k3_xboole_0(B_37, C_39) | ~r2_hidden(k3_xboole_0(B_37, C_39), A_33) | ~m1_subset_1(C_39, u1_struct_0(k2_yellow_1(A_33))) | ~m1_subset_1(B_37, u1_struct_0(k2_yellow_1(A_33))) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.49/1.76  tff(c_543, plain, (![A_137, B_138, C_139]: (k11_lattice3(k2_yellow_1(A_137), B_138, C_139)=k3_xboole_0(B_138, C_139) | ~r2_hidden(k3_xboole_0(B_138, C_139), A_137) | ~m1_subset_1(C_139, A_137) | ~m1_subset_1(B_138, A_137) | v1_xboole_0(A_137))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_64])).
% 3.49/1.76  tff(c_546, plain, (![A_20, B_21, C_23]: (k11_lattice3(k2_yellow_1(k9_setfam_1(A_20)), B_21, C_23)=k3_xboole_0(B_21, C_23) | v1_xboole_0(k9_setfam_1(A_20)) | ~m1_subset_1(C_23, k9_setfam_1(A_20)) | ~m1_subset_1(B_21, k9_setfam_1(A_20)))), inference(resolution, [status(thm)], [c_505, c_543])).
% 3.49/1.76  tff(c_583, plain, (![A_142, B_143, C_144]: (k11_lattice3(k3_yellow_1(A_142), B_143, C_144)=k3_xboole_0(B_143, C_144) | v1_xboole_0(k9_setfam_1(A_142)) | ~m1_subset_1(C_144, k9_setfam_1(A_142)) | ~m1_subset_1(B_143, k9_setfam_1(A_142)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_546])).
% 3.49/1.76  tff(c_585, plain, (![B_143]: (k11_lattice3(k3_yellow_1('#skF_2'), B_143, '#skF_4')=k3_xboole_0(B_143, '#skF_4') | v1_xboole_0(k9_setfam_1('#skF_2')) | ~m1_subset_1(B_143, k9_setfam_1('#skF_2')))), inference(resolution, [status(thm)], [c_130, c_583])).
% 3.49/1.76  tff(c_594, plain, (![B_145]: (k11_lattice3(k3_yellow_1('#skF_2'), B_145, '#skF_4')=k3_xboole_0(B_145, '#skF_4') | ~m1_subset_1(B_145, k9_setfam_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_518, c_585])).
% 3.49/1.76  tff(c_602, plain, (k11_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k3_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_129, c_594])).
% 3.49/1.76  tff(c_482, plain, (![A_117]: (v2_lattice3(k3_lattice3(A_117)) | ~l3_lattices(A_117) | ~v10_lattices(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.49/1.76  tff(c_485, plain, (![A_16]: (v2_lattice3(k3_yellow_1(A_16)) | ~l3_lattices(k1_lattice3(A_16)) | ~v10_lattices(k1_lattice3(A_16)) | v2_struct_0(k1_lattice3(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_482])).
% 3.49/1.76  tff(c_487, plain, (![A_16]: (v2_lattice3(k3_yellow_1(A_16)) | v2_struct_0(k1_lattice3(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_10, c_485])).
% 3.49/1.76  tff(c_488, plain, (![A_16]: (v2_lattice3(k3_yellow_1(A_16)))), inference(negUnitSimplification, [status(thm)], [c_12, c_487])).
% 3.49/1.76  tff(c_607, plain, (![A_146, B_147, C_148]: (k12_lattice3(A_146, B_147, C_148)=k11_lattice3(A_146, B_147, C_148) | ~m1_subset_1(C_148, u1_struct_0(A_146)) | ~m1_subset_1(B_147, u1_struct_0(A_146)) | ~l1_orders_2(A_146) | ~v2_lattice3(A_146) | ~v5_orders_2(A_146))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.49/1.76  tff(c_609, plain, (![A_53, B_147, C_148]: (k12_lattice3(k3_yellow_1(A_53), B_147, C_148)=k11_lattice3(k3_yellow_1(A_53), B_147, C_148) | ~m1_subset_1(C_148, k9_setfam_1(A_53)) | ~m1_subset_1(B_147, u1_struct_0(k3_yellow_1(A_53))) | ~l1_orders_2(k3_yellow_1(A_53)) | ~v2_lattice3(k3_yellow_1(A_53)) | ~v5_orders_2(k3_yellow_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_110, c_607])).
% 3.49/1.76  tff(c_636, plain, (![A_150, B_151, C_152]: (k12_lattice3(k3_yellow_1(A_150), B_151, C_152)=k11_lattice3(k3_yellow_1(A_150), B_151, C_152) | ~m1_subset_1(C_152, k9_setfam_1(A_150)) | ~m1_subset_1(B_151, k9_setfam_1(A_150)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_488, c_28, c_110, c_609])).
% 3.49/1.76  tff(c_643, plain, (![B_153]: (k12_lattice3(k3_yellow_1('#skF_2'), B_153, '#skF_4')=k11_lattice3(k3_yellow_1('#skF_2'), B_153, '#skF_4') | ~m1_subset_1(B_153, k9_setfam_1('#skF_2')))), inference(resolution, [status(thm)], [c_130, c_636])).
% 3.49/1.76  tff(c_649, plain, (k12_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k11_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_129, c_643])).
% 3.49/1.76  tff(c_653, plain, (k12_lattice3(k3_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k3_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_602, c_649])).
% 3.49/1.76  tff(c_655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_432, c_653])).
% 3.49/1.76  tff(c_656, plain, (![B_127]: (~m1_subset_1(B_127, k9_setfam_1('#skF_2')))), inference(splitRight, [status(thm)], [c_516])).
% 3.49/1.76  tff(c_660, plain, $false, inference(negUnitSimplification, [status(thm)], [c_656, c_130])).
% 3.49/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.76  
% 3.49/1.76  Inference rules
% 3.49/1.76  ----------------------
% 3.49/1.76  #Ref     : 0
% 3.49/1.76  #Sup     : 140
% 3.49/1.76  #Fact    : 0
% 3.49/1.76  #Define  : 0
% 3.49/1.76  #Split   : 4
% 3.49/1.76  #Chain   : 0
% 3.49/1.76  #Close   : 0
% 3.49/1.76  
% 3.49/1.76  Ordering : KBO
% 3.49/1.76  
% 3.49/1.76  Simplification rules
% 3.49/1.76  ----------------------
% 3.49/1.76  #Subsume      : 4
% 3.49/1.76  #Demod        : 76
% 3.49/1.76  #Tautology    : 81
% 3.49/1.76  #SimpNegUnit  : 26
% 3.49/1.76  #BackRed      : 10
% 3.49/1.76  
% 3.49/1.76  #Partial instantiations: 0
% 3.49/1.76  #Strategies tried      : 1
% 3.49/1.76  
% 3.49/1.76  Timing (in seconds)
% 3.49/1.76  ----------------------
% 3.49/1.76  Preprocessing        : 0.41
% 3.49/1.76  Parsing              : 0.23
% 3.49/1.76  CNF conversion       : 0.03
% 3.49/1.76  Main loop            : 0.48
% 3.49/1.76  Inferencing          : 0.19
% 3.49/1.76  Reduction            : 0.15
% 3.49/1.76  Demodulation         : 0.10
% 3.49/1.76  BG Simplification    : 0.03
% 3.49/1.76  Subsumption          : 0.06
% 3.49/1.76  Abstraction          : 0.02
% 3.49/1.76  MUC search           : 0.00
% 3.49/1.76  Cooper               : 0.00
% 3.49/1.76  Total                : 0.96
% 3.49/1.76  Index Insertion      : 0.00
% 3.49/1.76  Index Deletion       : 0.00
% 3.49/1.76  Index Matching       : 0.00
% 3.49/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
