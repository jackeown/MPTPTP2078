%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:24 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 4.26s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 548 expanded)
%              Number of leaves         :   36 ( 230 expanded)
%              Depth                    :   17
%              Number of atoms          :  263 (1650 expanded)
%              Number of equality atoms :   10 (  72 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > g1_orders_2 > #nlpp > u1_struct_0 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v2_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(A),B,C),k3_xboole_0(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_114,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k12_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_lattice3)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k12_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,D,B)
                      & r1_orders_2(A,D,C)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,E,B)
                              & r1_orders_2(A,E,C) )
                           => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_122,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(f_135,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_74,plain,(
    ! [A_81,B_82,C_83] :
      ( r1_tarski(A_81,k3_xboole_0(B_82,C_83))
      | ~ r1_tarski(A_81,C_83)
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_78,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_48])).

tff(c_79,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_38,plain,(
    ! [A_61] : v5_orders_2(k2_yellow_1(A_61)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_54,plain,(
    v2_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_30,plain,(
    ! [A_60] : l1_orders_2(k2_yellow_1(A_60)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_176,plain,(
    ! [A_99,B_100,C_101] :
      ( k12_lattice3(A_99,B_100,C_101) = k11_lattice3(A_99,B_100,C_101)
      | ~ m1_subset_1(C_101,u1_struct_0(A_99))
      | ~ m1_subset_1(B_100,u1_struct_0(A_99))
      | ~ l1_orders_2(A_99)
      | ~ v2_lattice3(A_99)
      | ~ v5_orders_2(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_180,plain,(
    ! [B_100] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_100,'#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),B_100,'#skF_4')
      | ~ m1_subset_1(B_100,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_50,c_176])).

tff(c_191,plain,(
    ! [B_102] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_102,'#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),B_102,'#skF_4')
      | ~ m1_subset_1(B_102,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_54,c_30,c_180])).

tff(c_206,plain,(
    k12_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_191])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k12_lattice3(A_7,B_8,C_9),u1_struct_0(A_7))
      | ~ m1_subset_1(C_9,u1_struct_0(A_7))
      | ~ m1_subset_1(B_8,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7)
      | ~ v2_lattice3(A_7)
      | ~ v5_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_251,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2'))
    | ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ v5_orders_2(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_8])).

tff(c_255,plain,(
    m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_54,c_30,c_52,c_50,c_251])).

tff(c_793,plain,(
    ! [A_135,B_136,C_137] :
      ( r1_orders_2(A_135,k12_lattice3(A_135,B_136,C_137),B_136)
      | ~ m1_subset_1(k12_lattice3(A_135,B_136,C_137),u1_struct_0(A_135))
      | ~ m1_subset_1(C_137,u1_struct_0(A_135))
      | ~ m1_subset_1(B_136,u1_struct_0(A_135))
      | ~ l1_orders_2(A_135)
      | ~ v2_lattice3(A_135)
      | ~ v5_orders_2(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_799,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),k12_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2'))
    | ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ v5_orders_2(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_793])).

tff(c_809,plain,(
    r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_54,c_30,c_52,c_50,c_255,c_206,c_799])).

tff(c_34,plain,(
    ! [A_61] : v3_orders_2(k2_yellow_1(A_61)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_135,plain,(
    ! [A_95,B_96,C_97] :
      ( r3_orders_2(A_95,B_96,C_97)
      | ~ r1_orders_2(A_95,B_96,C_97)
      | ~ m1_subset_1(C_97,u1_struct_0(A_95))
      | ~ m1_subset_1(B_96,u1_struct_0(A_95))
      | ~ l1_orders_2(A_95)
      | ~ v3_orders_2(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_139,plain,(
    ! [B_96] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_96,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_96,'#skF_4')
      | ~ m1_subset_1(B_96,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_50,c_135])).

tff(c_145,plain,(
    ! [B_96] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_96,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_96,'#skF_4')
      | ~ m1_subset_1(B_96,u1_struct_0(k2_yellow_1('#skF_2')))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_139])).

tff(c_149,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_42,plain,(
    ! [A_62] :
      ( ~ v2_struct_0(k2_yellow_1(A_62))
      | v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_152,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_149,c_42])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_152])).

tff(c_158,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_141,plain,(
    ! [B_96] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_96,'#skF_3')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_96,'#skF_3')
      | ~ m1_subset_1(B_96,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_52,c_135])).

tff(c_148,plain,(
    ! [B_96] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_96,'#skF_3')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_96,'#skF_3')
      | ~ m1_subset_1(B_96,u1_struct_0(k2_yellow_1('#skF_2')))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_141])).

tff(c_814,plain,(
    ! [B_138] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_138,'#skF_3')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_138,'#skF_3')
      | ~ m1_subset_1(B_138,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_148])).

tff(c_823,plain,
    ( r3_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3')
    | ~ r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_255,c_814])).

tff(c_845,plain,(
    r3_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_809,c_823])).

tff(c_46,plain,(
    ! [B_67,C_69,A_63] :
      ( r1_tarski(B_67,C_69)
      | ~ r3_orders_2(k2_yellow_1(A_63),B_67,C_69)
      | ~ m1_subset_1(C_69,u1_struct_0(k2_yellow_1(A_63)))
      | ~ m1_subset_1(B_67,u1_struct_0(k2_yellow_1(A_63)))
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_856,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2')))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_845,c_46])).

tff(c_863,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_52,c_856])).

tff(c_865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_79,c_863])).

tff(c_866,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_923,plain,(
    ! [A_150,B_151,C_152] :
      ( k12_lattice3(A_150,B_151,C_152) = k11_lattice3(A_150,B_151,C_152)
      | ~ m1_subset_1(C_152,u1_struct_0(A_150))
      | ~ m1_subset_1(B_151,u1_struct_0(A_150))
      | ~ l1_orders_2(A_150)
      | ~ v2_lattice3(A_150)
      | ~ v5_orders_2(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_927,plain,(
    ! [B_151] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_151,'#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),B_151,'#skF_4')
      | ~ m1_subset_1(B_151,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_50,c_923])).

tff(c_937,plain,(
    ! [B_153] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_153,'#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),B_153,'#skF_4')
      | ~ m1_subset_1(B_153,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_54,c_30,c_927])).

tff(c_952,plain,(
    k12_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_937])).

tff(c_987,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2'))
    | ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ v5_orders_2(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_952,c_8])).

tff(c_991,plain,(
    m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_54,c_30,c_52,c_50,c_987])).

tff(c_1331,plain,(
    ! [A_172,B_173,C_174] :
      ( r1_orders_2(A_172,k12_lattice3(A_172,B_173,C_174),C_174)
      | ~ m1_subset_1(k12_lattice3(A_172,B_173,C_174),u1_struct_0(A_172))
      | ~ m1_subset_1(C_174,u1_struct_0(A_172))
      | ~ m1_subset_1(B_173,u1_struct_0(A_172))
      | ~ l1_orders_2(A_172)
      | ~ v2_lattice3(A_172)
      | ~ v5_orders_2(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1337,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),k12_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2'))
    | ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ v5_orders_2(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_952,c_1331])).

tff(c_1347,plain,(
    r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_54,c_30,c_52,c_50,c_991,c_952,c_1337])).

tff(c_867,plain,(
    r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_868,plain,(
    ! [A_139,B_140,C_141] :
      ( r3_orders_2(k2_yellow_1(A_139),B_140,C_141)
      | ~ r1_tarski(B_140,C_141)
      | ~ m1_subset_1(C_141,u1_struct_0(k2_yellow_1(A_139)))
      | ~ m1_subset_1(B_140,u1_struct_0(k2_yellow_1(A_139)))
      | v1_xboole_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_872,plain,(
    ! [B_140] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_140,'#skF_3')
      | ~ r1_tarski(B_140,'#skF_3')
      | ~ m1_subset_1(B_140,u1_struct_0(k2_yellow_1('#skF_2')))
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_52,c_868])).

tff(c_878,plain,(
    ! [B_140] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_140,'#skF_3')
      | ~ r1_tarski(B_140,'#skF_3')
      | ~ m1_subset_1(B_140,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_872])).

tff(c_1000,plain,
    ( r3_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_991,c_878])).

tff(c_1012,plain,(
    r3_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_867,c_1000])).

tff(c_1160,plain,(
    ! [A_159,B_160,C_161] :
      ( r1_orders_2(A_159,B_160,C_161)
      | ~ r3_orders_2(A_159,B_160,C_161)
      | ~ m1_subset_1(C_161,u1_struct_0(A_159))
      | ~ m1_subset_1(B_160,u1_struct_0(A_159))
      | ~ l1_orders_2(A_159)
      | ~ v3_orders_2(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1164,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2'))
    | ~ v3_orders_2(k2_yellow_1('#skF_2'))
    | v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1012,c_1160])).

tff(c_1170,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_991,c_52,c_1164])).

tff(c_1171,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1170])).

tff(c_1174,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1171,c_42])).

tff(c_1178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1174])).

tff(c_1180,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1170])).

tff(c_1047,plain,(
    ! [A_155,B_156,C_157] :
      ( r3_orders_2(A_155,B_156,C_157)
      | ~ r1_orders_2(A_155,B_156,C_157)
      | ~ m1_subset_1(C_157,u1_struct_0(A_155))
      | ~ m1_subset_1(B_156,u1_struct_0(A_155))
      | ~ l1_orders_2(A_155)
      | ~ v3_orders_2(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1055,plain,(
    ! [B_156] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_156,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_156,'#skF_4')
      | ~ m1_subset_1(B_156,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_50,c_1047])).

tff(c_1067,plain,(
    ! [B_156] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_156,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_156,'#skF_4')
      | ~ m1_subset_1(B_156,u1_struct_0(k2_yellow_1('#skF_2')))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1055])).

tff(c_1366,plain,(
    ! [B_176] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_176,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_176,'#skF_4')
      | ~ m1_subset_1(B_176,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1180,c_1067])).

tff(c_1375,plain,
    ( r3_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_991,c_1366])).

tff(c_1393,plain,(
    r3_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1347,c_1375])).

tff(c_1405,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2')))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1393,c_46])).

tff(c_1412,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_991,c_50,c_1405])).

tff(c_1414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_866,c_1412])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:52 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.70  
% 3.91/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.70  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > g1_orders_2 > #nlpp > u1_struct_0 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.91/1.70  
% 3.91/1.70  %Foreground sorts:
% 3.91/1.70  
% 3.91/1.70  
% 3.91/1.70  %Background operators:
% 3.91/1.70  
% 3.91/1.70  
% 3.91/1.70  %Foreground operators:
% 3.91/1.70  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.91/1.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.91/1.70  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.91/1.70  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.91/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.70  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.91/1.70  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.91/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.91/1.70  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 3.91/1.70  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 3.91/1.70  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 3.91/1.70  tff('#skF_2', type, '#skF_2': $i).
% 3.91/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.91/1.70  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.91/1.70  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.91/1.70  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.91/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.70  tff('#skF_4', type, '#skF_4': $i).
% 3.91/1.70  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.91/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.91/1.70  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 3.91/1.70  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.91/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.91/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.91/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.91/1.70  
% 4.26/1.72  tff(f_149, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v2_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k11_lattice3(k2_yellow_1(A), B, C), k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_1)).
% 4.26/1.72  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 4.26/1.72  tff(f_114, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 4.26/1.72  tff(f_106, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 4.26/1.72  tff(f_70, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 4.26/1.72  tff(f_58, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k12_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k12_lattice3)).
% 4.26/1.72  tff(f_100, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k12_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_yellow_0)).
% 4.26/1.72  tff(f_46, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 4.26/1.72  tff(f_122, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 4.26/1.72  tff(f_135, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 4.26/1.72  tff(c_56, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.26/1.72  tff(c_74, plain, (![A_81, B_82, C_83]: (r1_tarski(A_81, k3_xboole_0(B_82, C_83)) | ~r1_tarski(A_81, C_83) | ~r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.26/1.72  tff(c_48, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.26/1.72  tff(c_78, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_74, c_48])).
% 4.26/1.72  tff(c_79, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_78])).
% 4.26/1.72  tff(c_38, plain, (![A_61]: (v5_orders_2(k2_yellow_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.26/1.72  tff(c_54, plain, (v2_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.26/1.72  tff(c_30, plain, (![A_60]: (l1_orders_2(k2_yellow_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.26/1.72  tff(c_52, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.26/1.72  tff(c_50, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.26/1.72  tff(c_176, plain, (![A_99, B_100, C_101]: (k12_lattice3(A_99, B_100, C_101)=k11_lattice3(A_99, B_100, C_101) | ~m1_subset_1(C_101, u1_struct_0(A_99)) | ~m1_subset_1(B_100, u1_struct_0(A_99)) | ~l1_orders_2(A_99) | ~v2_lattice3(A_99) | ~v5_orders_2(A_99))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.26/1.72  tff(c_180, plain, (![B_100]: (k12_lattice3(k2_yellow_1('#skF_2'), B_100, '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), B_100, '#skF_4') | ~m1_subset_1(B_100, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_50, c_176])).
% 4.26/1.72  tff(c_191, plain, (![B_102]: (k12_lattice3(k2_yellow_1('#skF_2'), B_102, '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), B_102, '#skF_4') | ~m1_subset_1(B_102, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_54, c_30, c_180])).
% 4.26/1.72  tff(c_206, plain, (k12_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_191])).
% 4.26/1.72  tff(c_8, plain, (![A_7, B_8, C_9]: (m1_subset_1(k12_lattice3(A_7, B_8, C_9), u1_struct_0(A_7)) | ~m1_subset_1(C_9, u1_struct_0(A_7)) | ~m1_subset_1(B_8, u1_struct_0(A_7)) | ~l1_orders_2(A_7) | ~v2_lattice3(A_7) | ~v5_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.26/1.72  tff(c_251, plain, (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_206, c_8])).
% 4.26/1.72  tff(c_255, plain, (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_54, c_30, c_52, c_50, c_251])).
% 4.26/1.72  tff(c_793, plain, (![A_135, B_136, C_137]: (r1_orders_2(A_135, k12_lattice3(A_135, B_136, C_137), B_136) | ~m1_subset_1(k12_lattice3(A_135, B_136, C_137), u1_struct_0(A_135)) | ~m1_subset_1(C_137, u1_struct_0(A_135)) | ~m1_subset_1(B_136, u1_struct_0(A_135)) | ~l1_orders_2(A_135) | ~v2_lattice3(A_135) | ~v5_orders_2(A_135))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.26/1.72  tff(c_799, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k12_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_206, c_793])).
% 4.26/1.72  tff(c_809, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_54, c_30, c_52, c_50, c_255, c_206, c_799])).
% 4.26/1.72  tff(c_34, plain, (![A_61]: (v3_orders_2(k2_yellow_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.26/1.72  tff(c_135, plain, (![A_95, B_96, C_97]: (r3_orders_2(A_95, B_96, C_97) | ~r1_orders_2(A_95, B_96, C_97) | ~m1_subset_1(C_97, u1_struct_0(A_95)) | ~m1_subset_1(B_96, u1_struct_0(A_95)) | ~l1_orders_2(A_95) | ~v3_orders_2(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.26/1.72  tff(c_139, plain, (![B_96]: (r3_orders_2(k2_yellow_1('#skF_2'), B_96, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_96, '#skF_4') | ~m1_subset_1(B_96, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_50, c_135])).
% 4.26/1.73  tff(c_145, plain, (![B_96]: (r3_orders_2(k2_yellow_1('#skF_2'), B_96, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_96, '#skF_4') | ~m1_subset_1(B_96, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_139])).
% 4.26/1.73  tff(c_149, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_145])).
% 4.26/1.73  tff(c_42, plain, (![A_62]: (~v2_struct_0(k2_yellow_1(A_62)) | v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.26/1.73  tff(c_152, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_149, c_42])).
% 4.26/1.73  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_152])).
% 4.26/1.73  tff(c_158, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_145])).
% 4.26/1.73  tff(c_141, plain, (![B_96]: (r3_orders_2(k2_yellow_1('#skF_2'), B_96, '#skF_3') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_96, '#skF_3') | ~m1_subset_1(B_96, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_52, c_135])).
% 4.26/1.73  tff(c_148, plain, (![B_96]: (r3_orders_2(k2_yellow_1('#skF_2'), B_96, '#skF_3') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_96, '#skF_3') | ~m1_subset_1(B_96, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_141])).
% 4.26/1.73  tff(c_814, plain, (![B_138]: (r3_orders_2(k2_yellow_1('#skF_2'), B_138, '#skF_3') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_138, '#skF_3') | ~m1_subset_1(B_138, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_158, c_148])).
% 4.26/1.73  tff(c_823, plain, (r3_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3') | ~r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_255, c_814])).
% 4.26/1.73  tff(c_845, plain, (r3_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_809, c_823])).
% 4.26/1.73  tff(c_46, plain, (![B_67, C_69, A_63]: (r1_tarski(B_67, C_69) | ~r3_orders_2(k2_yellow_1(A_63), B_67, C_69) | ~m1_subset_1(C_69, u1_struct_0(k2_yellow_1(A_63))) | ~m1_subset_1(B_67, u1_struct_0(k2_yellow_1(A_63))) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.26/1.73  tff(c_856, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2'))) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_845, c_46])).
% 4.26/1.73  tff(c_863, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_255, c_52, c_856])).
% 4.26/1.73  tff(c_865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_79, c_863])).
% 4.26/1.73  tff(c_866, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_78])).
% 4.26/1.73  tff(c_923, plain, (![A_150, B_151, C_152]: (k12_lattice3(A_150, B_151, C_152)=k11_lattice3(A_150, B_151, C_152) | ~m1_subset_1(C_152, u1_struct_0(A_150)) | ~m1_subset_1(B_151, u1_struct_0(A_150)) | ~l1_orders_2(A_150) | ~v2_lattice3(A_150) | ~v5_orders_2(A_150))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.26/1.73  tff(c_927, plain, (![B_151]: (k12_lattice3(k2_yellow_1('#skF_2'), B_151, '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), B_151, '#skF_4') | ~m1_subset_1(B_151, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_50, c_923])).
% 4.26/1.73  tff(c_937, plain, (![B_153]: (k12_lattice3(k2_yellow_1('#skF_2'), B_153, '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), B_153, '#skF_4') | ~m1_subset_1(B_153, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_54, c_30, c_927])).
% 4.26/1.73  tff(c_952, plain, (k12_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_937])).
% 4.26/1.73  tff(c_987, plain, (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_952, c_8])).
% 4.26/1.73  tff(c_991, plain, (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_54, c_30, c_52, c_50, c_987])).
% 4.26/1.73  tff(c_1331, plain, (![A_172, B_173, C_174]: (r1_orders_2(A_172, k12_lattice3(A_172, B_173, C_174), C_174) | ~m1_subset_1(k12_lattice3(A_172, B_173, C_174), u1_struct_0(A_172)) | ~m1_subset_1(C_174, u1_struct_0(A_172)) | ~m1_subset_1(B_173, u1_struct_0(A_172)) | ~l1_orders_2(A_172) | ~v2_lattice3(A_172) | ~v5_orders_2(A_172))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.26/1.73  tff(c_1337, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k12_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_952, c_1331])).
% 4.26/1.73  tff(c_1347, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_54, c_30, c_52, c_50, c_991, c_952, c_1337])).
% 4.26/1.73  tff(c_867, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_78])).
% 4.26/1.73  tff(c_868, plain, (![A_139, B_140, C_141]: (r3_orders_2(k2_yellow_1(A_139), B_140, C_141) | ~r1_tarski(B_140, C_141) | ~m1_subset_1(C_141, u1_struct_0(k2_yellow_1(A_139))) | ~m1_subset_1(B_140, u1_struct_0(k2_yellow_1(A_139))) | v1_xboole_0(A_139))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.26/1.73  tff(c_872, plain, (![B_140]: (r3_orders_2(k2_yellow_1('#skF_2'), B_140, '#skF_3') | ~r1_tarski(B_140, '#skF_3') | ~m1_subset_1(B_140, u1_struct_0(k2_yellow_1('#skF_2'))) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_868])).
% 4.26/1.73  tff(c_878, plain, (![B_140]: (r3_orders_2(k2_yellow_1('#skF_2'), B_140, '#skF_3') | ~r1_tarski(B_140, '#skF_3') | ~m1_subset_1(B_140, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_872])).
% 4.26/1.73  tff(c_1000, plain, (r3_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_991, c_878])).
% 4.26/1.73  tff(c_1012, plain, (r3_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_867, c_1000])).
% 4.26/1.73  tff(c_1160, plain, (![A_159, B_160, C_161]: (r1_orders_2(A_159, B_160, C_161) | ~r3_orders_2(A_159, B_160, C_161) | ~m1_subset_1(C_161, u1_struct_0(A_159)) | ~m1_subset_1(B_160, u1_struct_0(A_159)) | ~l1_orders_2(A_159) | ~v3_orders_2(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.26/1.73  tff(c_1164, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_1012, c_1160])).
% 4.26/1.73  tff(c_1170, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3') | v2_struct_0(k2_yellow_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_991, c_52, c_1164])).
% 4.26/1.73  tff(c_1171, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1170])).
% 4.26/1.73  tff(c_1174, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_1171, c_42])).
% 4.26/1.73  tff(c_1178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1174])).
% 4.26/1.73  tff(c_1180, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1170])).
% 4.26/1.73  tff(c_1047, plain, (![A_155, B_156, C_157]: (r3_orders_2(A_155, B_156, C_157) | ~r1_orders_2(A_155, B_156, C_157) | ~m1_subset_1(C_157, u1_struct_0(A_155)) | ~m1_subset_1(B_156, u1_struct_0(A_155)) | ~l1_orders_2(A_155) | ~v3_orders_2(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.26/1.73  tff(c_1055, plain, (![B_156]: (r3_orders_2(k2_yellow_1('#skF_2'), B_156, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_156, '#skF_4') | ~m1_subset_1(B_156, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_50, c_1047])).
% 4.26/1.73  tff(c_1067, plain, (![B_156]: (r3_orders_2(k2_yellow_1('#skF_2'), B_156, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_156, '#skF_4') | ~m1_subset_1(B_156, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_1055])).
% 4.26/1.73  tff(c_1366, plain, (![B_176]: (r3_orders_2(k2_yellow_1('#skF_2'), B_176, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_176, '#skF_4') | ~m1_subset_1(B_176, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_1180, c_1067])).
% 4.26/1.73  tff(c_1375, plain, (r3_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_991, c_1366])).
% 4.26/1.73  tff(c_1393, plain, (r3_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1347, c_1375])).
% 4.26/1.73  tff(c_1405, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2'))) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_1393, c_46])).
% 4.26/1.73  tff(c_1412, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_991, c_50, c_1405])).
% 4.26/1.73  tff(c_1414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_866, c_1412])).
% 4.26/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.26/1.73  
% 4.26/1.73  Inference rules
% 4.26/1.73  ----------------------
% 4.26/1.73  #Ref     : 0
% 4.26/1.73  #Sup     : 265
% 4.26/1.73  #Fact    : 0
% 4.26/1.73  #Define  : 0
% 4.26/1.73  #Split   : 36
% 4.26/1.73  #Chain   : 0
% 4.26/1.73  #Close   : 0
% 4.26/1.73  
% 4.26/1.73  Ordering : KBO
% 4.26/1.73  
% 4.26/1.73  Simplification rules
% 4.26/1.73  ----------------------
% 4.26/1.73  #Subsume      : 2
% 4.26/1.73  #Demod        : 562
% 4.26/1.73  #Tautology    : 63
% 4.26/1.73  #SimpNegUnit  : 66
% 4.26/1.73  #BackRed      : 0
% 4.26/1.73  
% 4.26/1.73  #Partial instantiations: 0
% 4.26/1.73  #Strategies tried      : 1
% 4.26/1.73  
% 4.26/1.73  Timing (in seconds)
% 4.26/1.73  ----------------------
% 4.26/1.73  Preprocessing        : 0.36
% 4.26/1.73  Parsing              : 0.18
% 4.26/1.73  CNF conversion       : 0.03
% 4.26/1.73  Main loop            : 0.59
% 4.26/1.73  Inferencing          : 0.18
% 4.26/1.73  Reduction            : 0.22
% 4.26/1.73  Demodulation         : 0.15
% 4.26/1.73  BG Simplification    : 0.03
% 4.26/1.73  Subsumption          : 0.11
% 4.26/1.73  Abstraction          : 0.03
% 4.26/1.73  MUC search           : 0.00
% 4.26/1.73  Cooper               : 0.00
% 4.26/1.73  Total                : 0.99
% 4.26/1.73  Index Insertion      : 0.00
% 4.26/1.73  Index Deletion       : 0.00
% 4.26/1.73  Index Matching       : 0.00
% 4.26/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
