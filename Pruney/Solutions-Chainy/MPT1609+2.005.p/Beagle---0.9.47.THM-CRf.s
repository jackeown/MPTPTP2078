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
% DateTime   : Thu Dec  3 10:25:29 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 194 expanded)
%              Number of leaves         :   49 (  90 expanded)
%              Depth                    :    8
%              Number of atoms          :  209 ( 388 expanded)
%              Number of equality atoms :   39 (  94 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v3_lattices > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > v10_lattices > l3_lattices > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > k3_xboole_0 > k2_xboole_0 > g1_orders_2 > #nlpp > u1_struct_0 > k9_setfam_1 > k3_yellow_1 > k3_lattice3 > k2_yellow_1 > k1_yellow_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1

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

tff(k10_lattice3,type,(
    k10_lattice3: ( $i * $i * $i ) > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
       => ! [C] :
            ( m1_subset_1(C,u1_struct_0(k3_yellow_1(A)))
           => ( k13_lattice3(k3_yellow_1(A),B,C) = k2_xboole_0(B,C)
              & k12_lattice3(k3_yellow_1(A),B,C) = k3_xboole_0(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_1)).

tff(f_113,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k1_lattice3(A))
      & v3_lattices(k1_lattice3(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_lattice3)).

tff(f_43,axiom,(
    ! [A] :
      ( v3_lattices(k1_lattice3(A))
      & v10_lattices(k1_lattice3(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_lattice3)).

tff(f_34,axiom,(
    ! [A] :
      ( v3_lattices(k1_lattice3(A))
      & l3_lattices(k1_lattice3(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattice3)).

tff(f_71,axiom,(
    ! [A] : k3_yellow_1(A) = k3_lattice3(k1_lattice3(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

tff(f_94,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_111,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
     => ! [C] :
          ( m1_subset_1(C,u1_struct_0(k3_yellow_1(A)))
         => ( r2_hidden(k3_xboole_0(B,C),k9_setfam_1(A))
            & r2_hidden(k2_xboole_0(B,C),k9_setfam_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l19_yellow_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_126,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r2_hidden(k2_xboole_0(B,C),A)
               => k10_lattice3(k2_yellow_1(A),B,C) = k2_xboole_0(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_yellow_1)).

tff(f_139,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r2_hidden(k3_xboole_0(B,C),A)
               => k11_lattice3(k2_yellow_1(A),B,C) = k3_xboole_0(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_2',u1_struct_0(k3_yellow_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_76,plain,(
    ! [A_48] : k2_yellow_1(k9_setfam_1(A_48)) = k3_yellow_1(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_46,plain,(
    ! [A_16] : v5_orders_2(k2_yellow_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_89,plain,(
    ! [A_48] : v5_orders_2(k3_yellow_1(A_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_46])).

tff(c_8,plain,(
    ! [A_4] : ~ v2_struct_0(k1_lattice3(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_5] : v10_lattices(k1_lattice3(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_3] : l3_lattices(k1_lattice3(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    ! [A_13] : k3_lattice3(k1_lattice3(A_13)) = k3_yellow_1(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_420,plain,(
    ! [A_100] :
      ( v2_lattice3(k3_lattice3(A_100))
      | ~ l3_lattices(A_100)
      | ~ v10_lattices(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_423,plain,(
    ! [A_13] :
      ( v2_lattice3(k3_yellow_1(A_13))
      | ~ l3_lattices(k1_lattice3(A_13))
      | ~ v10_lattices(k1_lattice3(A_13))
      | v2_struct_0(k1_lattice3(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_420])).

tff(c_425,plain,(
    ! [A_13] :
      ( v2_lattice3(k3_yellow_1(A_13))
      | v2_struct_0(k1_lattice3(A_13)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6,c_423])).

tff(c_426,plain,(
    ! [A_13] : v2_lattice3(k3_yellow_1(A_13)) ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_425])).

tff(c_26,plain,(
    ! [A_14] : l1_orders_2(k2_yellow_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_85,plain,(
    ! [A_48] : l1_orders_2(k3_yellow_1(A_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_26])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k3_yellow_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_510,plain,(
    ! [A_121,B_122,C_123] :
      ( k12_lattice3(A_121,B_122,C_123) = k11_lattice3(A_121,B_122,C_123)
      | ~ m1_subset_1(C_123,u1_struct_0(A_121))
      | ~ m1_subset_1(B_122,u1_struct_0(A_121))
      | ~ l1_orders_2(A_121)
      | ~ v2_lattice3(A_121)
      | ~ v5_orders_2(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_514,plain,(
    ! [B_122] :
      ( k12_lattice3(k3_yellow_1('#skF_1'),B_122,'#skF_3') = k11_lattice3(k3_yellow_1('#skF_1'),B_122,'#skF_3')
      | ~ m1_subset_1(B_122,u1_struct_0(k3_yellow_1('#skF_1')))
      | ~ l1_orders_2(k3_yellow_1('#skF_1'))
      | ~ v2_lattice3(k3_yellow_1('#skF_1'))
      | ~ v5_orders_2(k3_yellow_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_60,c_510])).

tff(c_556,plain,(
    ! [B_126] :
      ( k12_lattice3(k3_yellow_1('#skF_1'),B_126,'#skF_3') = k11_lattice3(k3_yellow_1('#skF_1'),B_126,'#skF_3')
      | ~ m1_subset_1(B_126,u1_struct_0(k3_yellow_1('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_426,c_85,c_514])).

tff(c_563,plain,(
    k12_lattice3(k3_yellow_1('#skF_1'),'#skF_2','#skF_3') = k11_lattice3(k3_yellow_1('#skF_1'),'#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_556])).

tff(c_140,plain,(
    ! [A_59] :
      ( v1_lattice3(k3_lattice3(A_59))
      | ~ l3_lattices(A_59)
      | ~ v10_lattices(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_143,plain,(
    ! [A_13] :
      ( v1_lattice3(k3_yellow_1(A_13))
      | ~ l3_lattices(k1_lattice3(A_13))
      | ~ v10_lattices(k1_lattice3(A_13))
      | v2_struct_0(k1_lattice3(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_140])).

tff(c_145,plain,(
    ! [A_13] :
      ( v1_lattice3(k3_yellow_1(A_13))
      | v2_struct_0(k1_lattice3(A_13)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6,c_143])).

tff(c_146,plain,(
    ! [A_13] : v1_lattice3(k3_yellow_1(A_13)) ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_145])).

tff(c_181,plain,(
    ! [A_73,B_74,C_75] :
      ( k13_lattice3(A_73,B_74,C_75) = k10_lattice3(A_73,B_74,C_75)
      | ~ m1_subset_1(C_75,u1_struct_0(A_73))
      | ~ m1_subset_1(B_74,u1_struct_0(A_73))
      | ~ l1_orders_2(A_73)
      | ~ v1_lattice3(A_73)
      | ~ v5_orders_2(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_185,plain,(
    ! [B_74] :
      ( k13_lattice3(k3_yellow_1('#skF_1'),B_74,'#skF_3') = k10_lattice3(k3_yellow_1('#skF_1'),B_74,'#skF_3')
      | ~ m1_subset_1(B_74,u1_struct_0(k3_yellow_1('#skF_1')))
      | ~ l1_orders_2(k3_yellow_1('#skF_1'))
      | ~ v1_lattice3(k3_yellow_1('#skF_1'))
      | ~ v5_orders_2(k3_yellow_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_60,c_181])).

tff(c_209,plain,(
    ! [B_77] :
      ( k13_lattice3(k3_yellow_1('#skF_1'),B_77,'#skF_3') = k10_lattice3(k3_yellow_1('#skF_1'),B_77,'#skF_3')
      | ~ m1_subset_1(B_77,u1_struct_0(k3_yellow_1('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_146,c_85,c_185])).

tff(c_216,plain,(
    k13_lattice3(k3_yellow_1('#skF_1'),'#skF_2','#skF_3') = k10_lattice3(k3_yellow_1('#skF_1'),'#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_209])).

tff(c_58,plain,
    ( k12_lattice3(k3_yellow_1('#skF_1'),'#skF_2','#skF_3') != k3_xboole_0('#skF_2','#skF_3')
    | k13_lattice3(k3_yellow_1('#skF_1'),'#skF_2','#skF_3') != k2_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_109,plain,(
    k13_lattice3(k3_yellow_1('#skF_1'),'#skF_2','#skF_3') != k2_xboole_0('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_218,plain,(
    k10_lattice3(k3_yellow_1('#skF_1'),'#skF_2','#skF_3') != k2_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_109])).

tff(c_163,plain,(
    ! [B_64,C_65,A_66] :
      ( r2_hidden(k3_xboole_0(B_64,C_65),k9_setfam_1(A_66))
      | ~ m1_subset_1(C_65,u1_struct_0(k3_yellow_1(A_66)))
      | ~ m1_subset_1(B_64,u1_struct_0(k3_yellow_1(A_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_168,plain,(
    ! [A_67,C_68,B_69] :
      ( ~ v1_xboole_0(k9_setfam_1(A_67))
      | ~ m1_subset_1(C_68,u1_struct_0(k3_yellow_1(A_67)))
      | ~ m1_subset_1(B_69,u1_struct_0(k3_yellow_1(A_67))) ) ),
    inference(resolution,[status(thm)],[c_163,c_2])).

tff(c_173,plain,(
    ! [B_69] :
      ( ~ v1_xboole_0(k9_setfam_1('#skF_1'))
      | ~ m1_subset_1(B_69,u1_struct_0(k3_yellow_1('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_62,c_168])).

tff(c_175,plain,(
    ~ v1_xboole_0(k9_setfam_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_52,plain,(
    ! [A_21] : k2_yellow_1(k9_setfam_1(A_21)) = k3_yellow_1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_48,plain,(
    ! [B_18,C_20,A_17] :
      ( r2_hidden(k2_xboole_0(B_18,C_20),k9_setfam_1(A_17))
      | ~ m1_subset_1(C_20,u1_struct_0(k3_yellow_1(A_17)))
      | ~ m1_subset_1(B_18,u1_struct_0(k3_yellow_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_277,plain,(
    ! [A_86,B_87,C_88] :
      ( k10_lattice3(k2_yellow_1(A_86),B_87,C_88) = k2_xboole_0(B_87,C_88)
      | ~ r2_hidden(k2_xboole_0(B_87,C_88),A_86)
      | ~ m1_subset_1(C_88,u1_struct_0(k2_yellow_1(A_86)))
      | ~ m1_subset_1(B_87,u1_struct_0(k2_yellow_1(A_86)))
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_279,plain,(
    ! [A_17,B_18,C_20] :
      ( k10_lattice3(k2_yellow_1(k9_setfam_1(A_17)),B_18,C_20) = k2_xboole_0(B_18,C_20)
      | ~ m1_subset_1(C_20,u1_struct_0(k2_yellow_1(k9_setfam_1(A_17))))
      | ~ m1_subset_1(B_18,u1_struct_0(k2_yellow_1(k9_setfam_1(A_17))))
      | v1_xboole_0(k9_setfam_1(A_17))
      | ~ m1_subset_1(C_20,u1_struct_0(k3_yellow_1(A_17)))
      | ~ m1_subset_1(B_18,u1_struct_0(k3_yellow_1(A_17))) ) ),
    inference(resolution,[status(thm)],[c_48,c_277])).

tff(c_304,plain,(
    ! [A_93,B_94,C_95] :
      ( k10_lattice3(k3_yellow_1(A_93),B_94,C_95) = k2_xboole_0(B_94,C_95)
      | ~ m1_subset_1(C_95,u1_struct_0(k3_yellow_1(A_93)))
      | ~ m1_subset_1(B_94,u1_struct_0(k3_yellow_1(A_93)))
      | v1_xboole_0(k9_setfam_1(A_93))
      | ~ m1_subset_1(C_95,u1_struct_0(k3_yellow_1(A_93)))
      | ~ m1_subset_1(B_94,u1_struct_0(k3_yellow_1(A_93))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_52,c_279])).

tff(c_308,plain,(
    ! [B_94] :
      ( k10_lattice3(k3_yellow_1('#skF_1'),B_94,'#skF_3') = k2_xboole_0(B_94,'#skF_3')
      | v1_xboole_0(k9_setfam_1('#skF_1'))
      | ~ m1_subset_1('#skF_3',u1_struct_0(k3_yellow_1('#skF_1')))
      | ~ m1_subset_1(B_94,u1_struct_0(k3_yellow_1('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_60,c_304])).

tff(c_315,plain,(
    ! [B_94] :
      ( k10_lattice3(k3_yellow_1('#skF_1'),B_94,'#skF_3') = k2_xboole_0(B_94,'#skF_3')
      | v1_xboole_0(k9_setfam_1('#skF_1'))
      | ~ m1_subset_1(B_94,u1_struct_0(k3_yellow_1('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_308])).

tff(c_389,plain,(
    ! [B_98] :
      ( k10_lattice3(k3_yellow_1('#skF_1'),B_98,'#skF_3') = k2_xboole_0(B_98,'#skF_3')
      | ~ m1_subset_1(B_98,u1_struct_0(k3_yellow_1('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_315])).

tff(c_392,plain,(
    k10_lattice3(k3_yellow_1('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_389])).

tff(c_399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_392])).

tff(c_400,plain,(
    ! [B_69] : ~ m1_subset_1(B_69,u1_struct_0(k3_yellow_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_400,c_62])).

tff(c_405,plain,(
    k12_lattice3(k3_yellow_1('#skF_1'),'#skF_2','#skF_3') != k3_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_565,plain,(
    k11_lattice3(k3_yellow_1('#skF_1'),'#skF_2','#skF_3') != k3_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_405])).

tff(c_464,plain,(
    ! [B_108,C_109,A_110] :
      ( r2_hidden(k3_xboole_0(B_108,C_109),k9_setfam_1(A_110))
      | ~ m1_subset_1(C_109,u1_struct_0(k3_yellow_1(A_110)))
      | ~ m1_subset_1(B_108,u1_struct_0(k3_yellow_1(A_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_474,plain,(
    ! [A_114,C_115,B_116] :
      ( ~ v1_xboole_0(k9_setfam_1(A_114))
      | ~ m1_subset_1(C_115,u1_struct_0(k3_yellow_1(A_114)))
      | ~ m1_subset_1(B_116,u1_struct_0(k3_yellow_1(A_114))) ) ),
    inference(resolution,[status(thm)],[c_464,c_2])).

tff(c_479,plain,(
    ! [B_116] :
      ( ~ v1_xboole_0(k9_setfam_1('#skF_1'))
      | ~ m1_subset_1(B_116,u1_struct_0(k3_yellow_1('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_62,c_474])).

tff(c_481,plain,(
    ~ v1_xboole_0(k9_setfam_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_479])).

tff(c_50,plain,(
    ! [B_18,C_20,A_17] :
      ( r2_hidden(k3_xboole_0(B_18,C_20),k9_setfam_1(A_17))
      | ~ m1_subset_1(C_20,u1_struct_0(k3_yellow_1(A_17)))
      | ~ m1_subset_1(B_18,u1_struct_0(k3_yellow_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_570,plain,(
    ! [A_127,B_128,C_129] :
      ( k11_lattice3(k2_yellow_1(A_127),B_128,C_129) = k3_xboole_0(B_128,C_129)
      | ~ r2_hidden(k3_xboole_0(B_128,C_129),A_127)
      | ~ m1_subset_1(C_129,u1_struct_0(k2_yellow_1(A_127)))
      | ~ m1_subset_1(B_128,u1_struct_0(k2_yellow_1(A_127)))
      | v1_xboole_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_572,plain,(
    ! [A_17,B_18,C_20] :
      ( k11_lattice3(k2_yellow_1(k9_setfam_1(A_17)),B_18,C_20) = k3_xboole_0(B_18,C_20)
      | ~ m1_subset_1(C_20,u1_struct_0(k2_yellow_1(k9_setfam_1(A_17))))
      | ~ m1_subset_1(B_18,u1_struct_0(k2_yellow_1(k9_setfam_1(A_17))))
      | v1_xboole_0(k9_setfam_1(A_17))
      | ~ m1_subset_1(C_20,u1_struct_0(k3_yellow_1(A_17)))
      | ~ m1_subset_1(B_18,u1_struct_0(k3_yellow_1(A_17))) ) ),
    inference(resolution,[status(thm)],[c_50,c_570])).

tff(c_584,plain,(
    ! [A_133,B_134,C_135] :
      ( k11_lattice3(k3_yellow_1(A_133),B_134,C_135) = k3_xboole_0(B_134,C_135)
      | ~ m1_subset_1(C_135,u1_struct_0(k3_yellow_1(A_133)))
      | ~ m1_subset_1(B_134,u1_struct_0(k3_yellow_1(A_133)))
      | v1_xboole_0(k9_setfam_1(A_133))
      | ~ m1_subset_1(C_135,u1_struct_0(k3_yellow_1(A_133)))
      | ~ m1_subset_1(B_134,u1_struct_0(k3_yellow_1(A_133))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_52,c_572])).

tff(c_588,plain,(
    ! [B_134] :
      ( k11_lattice3(k3_yellow_1('#skF_1'),B_134,'#skF_3') = k3_xboole_0(B_134,'#skF_3')
      | v1_xboole_0(k9_setfam_1('#skF_1'))
      | ~ m1_subset_1('#skF_3',u1_struct_0(k3_yellow_1('#skF_1')))
      | ~ m1_subset_1(B_134,u1_struct_0(k3_yellow_1('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_60,c_584])).

tff(c_595,plain,(
    ! [B_134] :
      ( k11_lattice3(k3_yellow_1('#skF_1'),B_134,'#skF_3') = k3_xboole_0(B_134,'#skF_3')
      | v1_xboole_0(k9_setfam_1('#skF_1'))
      | ~ m1_subset_1(B_134,u1_struct_0(k3_yellow_1('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_588])).

tff(c_624,plain,(
    ! [B_137] :
      ( k11_lattice3(k3_yellow_1('#skF_1'),B_137,'#skF_3') = k3_xboole_0(B_137,'#skF_3')
      | ~ m1_subset_1(B_137,u1_struct_0(k3_yellow_1('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_481,c_595])).

tff(c_627,plain,(
    k11_lattice3(k3_yellow_1('#skF_1'),'#skF_2','#skF_3') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_624])).

tff(c_634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_565,c_627])).

tff(c_635,plain,(
    ! [B_116] : ~ m1_subset_1(B_116,u1_struct_0(k3_yellow_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_479])).

tff(c_650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_635,c_62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:07:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.44  
% 3.06/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.45  %$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v3_lattices > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > v10_lattices > l3_lattices > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > k3_xboole_0 > k2_xboole_0 > g1_orders_2 > #nlpp > u1_struct_0 > k9_setfam_1 > k3_yellow_1 > k3_lattice3 > k2_yellow_1 > k1_yellow_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1
% 3.06/1.45  
% 3.06/1.45  %Foreground sorts:
% 3.06/1.45  
% 3.06/1.45  
% 3.06/1.45  %Background operators:
% 3.06/1.45  
% 3.06/1.45  
% 3.06/1.45  %Foreground operators:
% 3.06/1.45  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.06/1.45  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.06/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.06/1.45  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.06/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.45  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.06/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.45  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 3.06/1.45  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.06/1.45  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 3.06/1.45  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.06/1.45  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 3.06/1.45  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 3.06/1.45  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 3.06/1.45  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 3.06/1.45  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 3.06/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.06/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.45  tff('#skF_1', type, '#skF_1': $i).
% 3.06/1.45  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.06/1.45  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.06/1.45  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.06/1.45  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.06/1.45  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.06/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.45  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.06/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.45  tff(v3_lattices, type, v3_lattices: $i > $o).
% 3.06/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.06/1.45  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 3.06/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.06/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.06/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.06/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.45  
% 3.21/1.47  tff(f_149, negated_conjecture, ~(![A, B]: (m1_subset_1(B, u1_struct_0(k3_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k3_yellow_1(A))) => ((k13_lattice3(k3_yellow_1(A), B, C) = k2_xboole_0(B, C)) & (k12_lattice3(k3_yellow_1(A), B, C) = k3_xboole_0(B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_yellow_1)).
% 3.21/1.47  tff(f_113, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 3.21/1.47  tff(f_102, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.21/1.47  tff(f_39, axiom, (![A]: (~v2_struct_0(k1_lattice3(A)) & v3_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_lattice3)).
% 3.21/1.47  tff(f_43, axiom, (![A]: (v3_lattices(k1_lattice3(A)) & v10_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_lattice3)).
% 3.21/1.47  tff(f_34, axiom, (![A]: (v3_lattices(k1_lattice3(A)) & l3_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_lattice3)).
% 3.21/1.47  tff(f_71, axiom, (![A]: (k3_yellow_1(A) = k3_lattice3(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_yellow_1)).
% 3.21/1.47  tff(f_94, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (((((v1_orders_2(k3_lattice3(A)) & v3_orders_2(k3_lattice3(A))) & v4_orders_2(k3_lattice3(A))) & v5_orders_2(k3_lattice3(A))) & v1_lattice3(k3_lattice3(A))) & v2_lattice3(k3_lattice3(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_yellow_1)).
% 3.21/1.47  tff(f_75, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.21/1.47  tff(f_55, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 3.21/1.47  tff(f_67, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 3.21/1.47  tff(f_111, axiom, (![A, B]: (m1_subset_1(B, u1_struct_0(k3_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k3_yellow_1(A))) => (r2_hidden(k3_xboole_0(B, C), k9_setfam_1(A)) & r2_hidden(k2_xboole_0(B, C), k9_setfam_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l19_yellow_1)).
% 3.21/1.47  tff(f_30, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 3.21/1.47  tff(f_126, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r2_hidden(k2_xboole_0(B, C), A) => (k10_lattice3(k2_yellow_1(A), B, C) = k2_xboole_0(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_yellow_1)).
% 3.21/1.47  tff(f_139, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r2_hidden(k3_xboole_0(B, C), A) => (k11_lattice3(k2_yellow_1(A), B, C) = k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_yellow_1)).
% 3.21/1.47  tff(c_62, plain, (m1_subset_1('#skF_2', u1_struct_0(k3_yellow_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.21/1.47  tff(c_76, plain, (![A_48]: (k2_yellow_1(k9_setfam_1(A_48))=k3_yellow_1(A_48))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.21/1.47  tff(c_46, plain, (![A_16]: (v5_orders_2(k2_yellow_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.21/1.47  tff(c_89, plain, (![A_48]: (v5_orders_2(k3_yellow_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_46])).
% 3.21/1.47  tff(c_8, plain, (![A_4]: (~v2_struct_0(k1_lattice3(A_4)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.21/1.47  tff(c_14, plain, (![A_5]: (v10_lattices(k1_lattice3(A_5)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.21/1.47  tff(c_6, plain, (![A_3]: (l3_lattices(k1_lattice3(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.21/1.47  tff(c_22, plain, (![A_13]: (k3_lattice3(k1_lattice3(A_13))=k3_yellow_1(A_13))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.21/1.47  tff(c_420, plain, (![A_100]: (v2_lattice3(k3_lattice3(A_100)) | ~l3_lattices(A_100) | ~v10_lattices(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.21/1.47  tff(c_423, plain, (![A_13]: (v2_lattice3(k3_yellow_1(A_13)) | ~l3_lattices(k1_lattice3(A_13)) | ~v10_lattices(k1_lattice3(A_13)) | v2_struct_0(k1_lattice3(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_420])).
% 3.21/1.47  tff(c_425, plain, (![A_13]: (v2_lattice3(k3_yellow_1(A_13)) | v2_struct_0(k1_lattice3(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_6, c_423])).
% 3.21/1.47  tff(c_426, plain, (![A_13]: (v2_lattice3(k3_yellow_1(A_13)))), inference(negUnitSimplification, [status(thm)], [c_8, c_425])).
% 3.21/1.47  tff(c_26, plain, (![A_14]: (l1_orders_2(k2_yellow_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.21/1.47  tff(c_85, plain, (![A_48]: (l1_orders_2(k3_yellow_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_26])).
% 3.21/1.47  tff(c_60, plain, (m1_subset_1('#skF_3', u1_struct_0(k3_yellow_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.21/1.47  tff(c_510, plain, (![A_121, B_122, C_123]: (k12_lattice3(A_121, B_122, C_123)=k11_lattice3(A_121, B_122, C_123) | ~m1_subset_1(C_123, u1_struct_0(A_121)) | ~m1_subset_1(B_122, u1_struct_0(A_121)) | ~l1_orders_2(A_121) | ~v2_lattice3(A_121) | ~v5_orders_2(A_121))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.21/1.47  tff(c_514, plain, (![B_122]: (k12_lattice3(k3_yellow_1('#skF_1'), B_122, '#skF_3')=k11_lattice3(k3_yellow_1('#skF_1'), B_122, '#skF_3') | ~m1_subset_1(B_122, u1_struct_0(k3_yellow_1('#skF_1'))) | ~l1_orders_2(k3_yellow_1('#skF_1')) | ~v2_lattice3(k3_yellow_1('#skF_1')) | ~v5_orders_2(k3_yellow_1('#skF_1')))), inference(resolution, [status(thm)], [c_60, c_510])).
% 3.21/1.47  tff(c_556, plain, (![B_126]: (k12_lattice3(k3_yellow_1('#skF_1'), B_126, '#skF_3')=k11_lattice3(k3_yellow_1('#skF_1'), B_126, '#skF_3') | ~m1_subset_1(B_126, u1_struct_0(k3_yellow_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_426, c_85, c_514])).
% 3.21/1.47  tff(c_563, plain, (k12_lattice3(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3')=k11_lattice3(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_556])).
% 3.21/1.47  tff(c_140, plain, (![A_59]: (v1_lattice3(k3_lattice3(A_59)) | ~l3_lattices(A_59) | ~v10_lattices(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.21/1.47  tff(c_143, plain, (![A_13]: (v1_lattice3(k3_yellow_1(A_13)) | ~l3_lattices(k1_lattice3(A_13)) | ~v10_lattices(k1_lattice3(A_13)) | v2_struct_0(k1_lattice3(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_140])).
% 3.21/1.47  tff(c_145, plain, (![A_13]: (v1_lattice3(k3_yellow_1(A_13)) | v2_struct_0(k1_lattice3(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_6, c_143])).
% 3.21/1.47  tff(c_146, plain, (![A_13]: (v1_lattice3(k3_yellow_1(A_13)))), inference(negUnitSimplification, [status(thm)], [c_8, c_145])).
% 3.21/1.47  tff(c_181, plain, (![A_73, B_74, C_75]: (k13_lattice3(A_73, B_74, C_75)=k10_lattice3(A_73, B_74, C_75) | ~m1_subset_1(C_75, u1_struct_0(A_73)) | ~m1_subset_1(B_74, u1_struct_0(A_73)) | ~l1_orders_2(A_73) | ~v1_lattice3(A_73) | ~v5_orders_2(A_73))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.21/1.47  tff(c_185, plain, (![B_74]: (k13_lattice3(k3_yellow_1('#skF_1'), B_74, '#skF_3')=k10_lattice3(k3_yellow_1('#skF_1'), B_74, '#skF_3') | ~m1_subset_1(B_74, u1_struct_0(k3_yellow_1('#skF_1'))) | ~l1_orders_2(k3_yellow_1('#skF_1')) | ~v1_lattice3(k3_yellow_1('#skF_1')) | ~v5_orders_2(k3_yellow_1('#skF_1')))), inference(resolution, [status(thm)], [c_60, c_181])).
% 3.21/1.47  tff(c_209, plain, (![B_77]: (k13_lattice3(k3_yellow_1('#skF_1'), B_77, '#skF_3')=k10_lattice3(k3_yellow_1('#skF_1'), B_77, '#skF_3') | ~m1_subset_1(B_77, u1_struct_0(k3_yellow_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_146, c_85, c_185])).
% 3.21/1.47  tff(c_216, plain, (k13_lattice3(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3')=k10_lattice3(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_209])).
% 3.21/1.47  tff(c_58, plain, (k12_lattice3(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3')!=k3_xboole_0('#skF_2', '#skF_3') | k13_lattice3(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3')!=k2_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.21/1.47  tff(c_109, plain, (k13_lattice3(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3')!=k2_xboole_0('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 3.21/1.47  tff(c_218, plain, (k10_lattice3(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3')!=k2_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_109])).
% 3.21/1.47  tff(c_163, plain, (![B_64, C_65, A_66]: (r2_hidden(k3_xboole_0(B_64, C_65), k9_setfam_1(A_66)) | ~m1_subset_1(C_65, u1_struct_0(k3_yellow_1(A_66))) | ~m1_subset_1(B_64, u1_struct_0(k3_yellow_1(A_66))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.21/1.47  tff(c_2, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.21/1.47  tff(c_168, plain, (![A_67, C_68, B_69]: (~v1_xboole_0(k9_setfam_1(A_67)) | ~m1_subset_1(C_68, u1_struct_0(k3_yellow_1(A_67))) | ~m1_subset_1(B_69, u1_struct_0(k3_yellow_1(A_67))))), inference(resolution, [status(thm)], [c_163, c_2])).
% 3.21/1.47  tff(c_173, plain, (![B_69]: (~v1_xboole_0(k9_setfam_1('#skF_1')) | ~m1_subset_1(B_69, u1_struct_0(k3_yellow_1('#skF_1'))))), inference(resolution, [status(thm)], [c_62, c_168])).
% 3.21/1.47  tff(c_175, plain, (~v1_xboole_0(k9_setfam_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_173])).
% 3.21/1.47  tff(c_52, plain, (![A_21]: (k2_yellow_1(k9_setfam_1(A_21))=k3_yellow_1(A_21))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.21/1.47  tff(c_48, plain, (![B_18, C_20, A_17]: (r2_hidden(k2_xboole_0(B_18, C_20), k9_setfam_1(A_17)) | ~m1_subset_1(C_20, u1_struct_0(k3_yellow_1(A_17))) | ~m1_subset_1(B_18, u1_struct_0(k3_yellow_1(A_17))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.21/1.47  tff(c_277, plain, (![A_86, B_87, C_88]: (k10_lattice3(k2_yellow_1(A_86), B_87, C_88)=k2_xboole_0(B_87, C_88) | ~r2_hidden(k2_xboole_0(B_87, C_88), A_86) | ~m1_subset_1(C_88, u1_struct_0(k2_yellow_1(A_86))) | ~m1_subset_1(B_87, u1_struct_0(k2_yellow_1(A_86))) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.21/1.47  tff(c_279, plain, (![A_17, B_18, C_20]: (k10_lattice3(k2_yellow_1(k9_setfam_1(A_17)), B_18, C_20)=k2_xboole_0(B_18, C_20) | ~m1_subset_1(C_20, u1_struct_0(k2_yellow_1(k9_setfam_1(A_17)))) | ~m1_subset_1(B_18, u1_struct_0(k2_yellow_1(k9_setfam_1(A_17)))) | v1_xboole_0(k9_setfam_1(A_17)) | ~m1_subset_1(C_20, u1_struct_0(k3_yellow_1(A_17))) | ~m1_subset_1(B_18, u1_struct_0(k3_yellow_1(A_17))))), inference(resolution, [status(thm)], [c_48, c_277])).
% 3.21/1.47  tff(c_304, plain, (![A_93, B_94, C_95]: (k10_lattice3(k3_yellow_1(A_93), B_94, C_95)=k2_xboole_0(B_94, C_95) | ~m1_subset_1(C_95, u1_struct_0(k3_yellow_1(A_93))) | ~m1_subset_1(B_94, u1_struct_0(k3_yellow_1(A_93))) | v1_xboole_0(k9_setfam_1(A_93)) | ~m1_subset_1(C_95, u1_struct_0(k3_yellow_1(A_93))) | ~m1_subset_1(B_94, u1_struct_0(k3_yellow_1(A_93))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_52, c_279])).
% 3.21/1.47  tff(c_308, plain, (![B_94]: (k10_lattice3(k3_yellow_1('#skF_1'), B_94, '#skF_3')=k2_xboole_0(B_94, '#skF_3') | v1_xboole_0(k9_setfam_1('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0(k3_yellow_1('#skF_1'))) | ~m1_subset_1(B_94, u1_struct_0(k3_yellow_1('#skF_1'))))), inference(resolution, [status(thm)], [c_60, c_304])).
% 3.21/1.47  tff(c_315, plain, (![B_94]: (k10_lattice3(k3_yellow_1('#skF_1'), B_94, '#skF_3')=k2_xboole_0(B_94, '#skF_3') | v1_xboole_0(k9_setfam_1('#skF_1')) | ~m1_subset_1(B_94, u1_struct_0(k3_yellow_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_308])).
% 3.21/1.47  tff(c_389, plain, (![B_98]: (k10_lattice3(k3_yellow_1('#skF_1'), B_98, '#skF_3')=k2_xboole_0(B_98, '#skF_3') | ~m1_subset_1(B_98, u1_struct_0(k3_yellow_1('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_175, c_315])).
% 3.21/1.47  tff(c_392, plain, (k10_lattice3(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_389])).
% 3.21/1.47  tff(c_399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_218, c_392])).
% 3.21/1.47  tff(c_400, plain, (![B_69]: (~m1_subset_1(B_69, u1_struct_0(k3_yellow_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_173])).
% 3.21/1.47  tff(c_404, plain, $false, inference(negUnitSimplification, [status(thm)], [c_400, c_62])).
% 3.21/1.47  tff(c_405, plain, (k12_lattice3(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3')!=k3_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 3.21/1.47  tff(c_565, plain, (k11_lattice3(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3')!=k3_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_563, c_405])).
% 3.21/1.47  tff(c_464, plain, (![B_108, C_109, A_110]: (r2_hidden(k3_xboole_0(B_108, C_109), k9_setfam_1(A_110)) | ~m1_subset_1(C_109, u1_struct_0(k3_yellow_1(A_110))) | ~m1_subset_1(B_108, u1_struct_0(k3_yellow_1(A_110))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.21/1.47  tff(c_474, plain, (![A_114, C_115, B_116]: (~v1_xboole_0(k9_setfam_1(A_114)) | ~m1_subset_1(C_115, u1_struct_0(k3_yellow_1(A_114))) | ~m1_subset_1(B_116, u1_struct_0(k3_yellow_1(A_114))))), inference(resolution, [status(thm)], [c_464, c_2])).
% 3.21/1.47  tff(c_479, plain, (![B_116]: (~v1_xboole_0(k9_setfam_1('#skF_1')) | ~m1_subset_1(B_116, u1_struct_0(k3_yellow_1('#skF_1'))))), inference(resolution, [status(thm)], [c_62, c_474])).
% 3.21/1.47  tff(c_481, plain, (~v1_xboole_0(k9_setfam_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_479])).
% 3.21/1.47  tff(c_50, plain, (![B_18, C_20, A_17]: (r2_hidden(k3_xboole_0(B_18, C_20), k9_setfam_1(A_17)) | ~m1_subset_1(C_20, u1_struct_0(k3_yellow_1(A_17))) | ~m1_subset_1(B_18, u1_struct_0(k3_yellow_1(A_17))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.21/1.47  tff(c_570, plain, (![A_127, B_128, C_129]: (k11_lattice3(k2_yellow_1(A_127), B_128, C_129)=k3_xboole_0(B_128, C_129) | ~r2_hidden(k3_xboole_0(B_128, C_129), A_127) | ~m1_subset_1(C_129, u1_struct_0(k2_yellow_1(A_127))) | ~m1_subset_1(B_128, u1_struct_0(k2_yellow_1(A_127))) | v1_xboole_0(A_127))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.21/1.47  tff(c_572, plain, (![A_17, B_18, C_20]: (k11_lattice3(k2_yellow_1(k9_setfam_1(A_17)), B_18, C_20)=k3_xboole_0(B_18, C_20) | ~m1_subset_1(C_20, u1_struct_0(k2_yellow_1(k9_setfam_1(A_17)))) | ~m1_subset_1(B_18, u1_struct_0(k2_yellow_1(k9_setfam_1(A_17)))) | v1_xboole_0(k9_setfam_1(A_17)) | ~m1_subset_1(C_20, u1_struct_0(k3_yellow_1(A_17))) | ~m1_subset_1(B_18, u1_struct_0(k3_yellow_1(A_17))))), inference(resolution, [status(thm)], [c_50, c_570])).
% 3.21/1.47  tff(c_584, plain, (![A_133, B_134, C_135]: (k11_lattice3(k3_yellow_1(A_133), B_134, C_135)=k3_xboole_0(B_134, C_135) | ~m1_subset_1(C_135, u1_struct_0(k3_yellow_1(A_133))) | ~m1_subset_1(B_134, u1_struct_0(k3_yellow_1(A_133))) | v1_xboole_0(k9_setfam_1(A_133)) | ~m1_subset_1(C_135, u1_struct_0(k3_yellow_1(A_133))) | ~m1_subset_1(B_134, u1_struct_0(k3_yellow_1(A_133))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_52, c_572])).
% 3.21/1.47  tff(c_588, plain, (![B_134]: (k11_lattice3(k3_yellow_1('#skF_1'), B_134, '#skF_3')=k3_xboole_0(B_134, '#skF_3') | v1_xboole_0(k9_setfam_1('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0(k3_yellow_1('#skF_1'))) | ~m1_subset_1(B_134, u1_struct_0(k3_yellow_1('#skF_1'))))), inference(resolution, [status(thm)], [c_60, c_584])).
% 3.21/1.47  tff(c_595, plain, (![B_134]: (k11_lattice3(k3_yellow_1('#skF_1'), B_134, '#skF_3')=k3_xboole_0(B_134, '#skF_3') | v1_xboole_0(k9_setfam_1('#skF_1')) | ~m1_subset_1(B_134, u1_struct_0(k3_yellow_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_588])).
% 3.21/1.47  tff(c_624, plain, (![B_137]: (k11_lattice3(k3_yellow_1('#skF_1'), B_137, '#skF_3')=k3_xboole_0(B_137, '#skF_3') | ~m1_subset_1(B_137, u1_struct_0(k3_yellow_1('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_481, c_595])).
% 3.21/1.47  tff(c_627, plain, (k11_lattice3(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3')=k3_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_624])).
% 3.21/1.47  tff(c_634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_565, c_627])).
% 3.21/1.47  tff(c_635, plain, (![B_116]: (~m1_subset_1(B_116, u1_struct_0(k3_yellow_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_479])).
% 3.21/1.47  tff(c_650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_635, c_62])).
% 3.21/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.47  
% 3.21/1.47  Inference rules
% 3.21/1.47  ----------------------
% 3.21/1.47  #Ref     : 0
% 3.21/1.47  #Sup     : 147
% 3.21/1.47  #Fact    : 0
% 3.21/1.47  #Define  : 0
% 3.21/1.47  #Split   : 3
% 3.21/1.47  #Chain   : 0
% 3.21/1.47  #Close   : 0
% 3.21/1.47  
% 3.21/1.47  Ordering : KBO
% 3.21/1.47  
% 3.21/1.47  Simplification rules
% 3.21/1.47  ----------------------
% 3.21/1.47  #Subsume      : 4
% 3.21/1.47  #Demod        : 94
% 3.21/1.47  #Tautology    : 85
% 3.21/1.47  #SimpNegUnit  : 24
% 3.21/1.47  #BackRed      : 14
% 3.21/1.47  
% 3.21/1.47  #Partial instantiations: 0
% 3.21/1.47  #Strategies tried      : 1
% 3.21/1.47  
% 3.21/1.47  Timing (in seconds)
% 3.21/1.47  ----------------------
% 3.21/1.47  Preprocessing        : 0.35
% 3.21/1.47  Parsing              : 0.19
% 3.21/1.47  CNF conversion       : 0.02
% 3.21/1.47  Main loop            : 0.33
% 3.21/1.47  Inferencing          : 0.13
% 3.21/1.47  Reduction            : 0.11
% 3.21/1.47  Demodulation         : 0.08
% 3.21/1.47  BG Simplification    : 0.02
% 3.21/1.47  Subsumption          : 0.04
% 3.21/1.47  Abstraction          : 0.02
% 3.21/1.47  MUC search           : 0.00
% 3.21/1.47  Cooper               : 0.00
% 3.21/1.47  Total                : 0.72
% 3.21/1.47  Index Insertion      : 0.00
% 3.21/1.47  Index Deletion       : 0.00
% 3.21/1.47  Index Matching       : 0.00
% 3.21/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
