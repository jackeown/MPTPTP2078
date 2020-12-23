%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:22 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  125 (1102 expanded)
%              Number of leaves         :   35 ( 438 expanded)
%              Depth                    :   18
%              Number of atoms          :  314 (3260 expanded)
%              Number of equality atoms :   28 ( 280 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_154,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v2_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(A),B,C),k3_xboole_0(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).

tff(f_127,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_119,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k12_lattice3(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k12_lattice3)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

tff(f_115,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_140,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_40,plain,(
    ! [A_64] : v5_orders_2(k2_yellow_1(A_64)) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_52,plain,(
    v2_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_32,plain,(
    ! [A_63] : l1_orders_2(k2_yellow_1(A_63)) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_727,plain,(
    ! [A_140,B_141,C_142] :
      ( k12_lattice3(A_140,B_141,C_142) = k11_lattice3(A_140,B_141,C_142)
      | ~ m1_subset_1(C_142,u1_struct_0(A_140))
      | ~ m1_subset_1(B_141,u1_struct_0(A_140))
      | ~ l1_orders_2(A_140)
      | ~ v2_lattice3(A_140)
      | ~ v5_orders_2(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_733,plain,(
    ! [B_141] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_141,'#skF_3') = k11_lattice3(k2_yellow_1('#skF_2'),B_141,'#skF_3')
      | ~ m1_subset_1(B_141,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_50,c_727])).

tff(c_766,plain,(
    ! [B_147] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_147,'#skF_3') = k11_lattice3(k2_yellow_1('#skF_2'),B_147,'#skF_3')
      | ~ m1_subset_1(B_147,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52,c_32,c_733])).

tff(c_780,plain,(
    k12_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3') = k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_766])).

tff(c_731,plain,(
    ! [B_141] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_141,'#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),B_141,'#skF_4')
      | ~ m1_subset_1(B_141,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_48,c_727])).

tff(c_741,plain,(
    ! [B_143] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_143,'#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),B_143,'#skF_4')
      | ~ m1_subset_1(B_143,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52,c_32,c_731])).

tff(c_756,plain,(
    k12_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_741])).

tff(c_790,plain,(
    ! [A_148,C_149,B_150] :
      ( k12_lattice3(A_148,C_149,B_150) = k12_lattice3(A_148,B_150,C_149)
      | ~ m1_subset_1(C_149,u1_struct_0(A_148))
      | ~ m1_subset_1(B_150,u1_struct_0(A_148))
      | ~ l1_orders_2(A_148)
      | ~ v2_lattice3(A_148)
      | ~ v5_orders_2(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_794,plain,(
    ! [B_150] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_150,'#skF_4') = k12_lattice3(k2_yellow_1('#skF_2'),'#skF_4',B_150)
      | ~ m1_subset_1(B_150,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_48,c_790])).

tff(c_804,plain,(
    ! [B_151] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_151,'#skF_4') = k12_lattice3(k2_yellow_1('#skF_2'),'#skF_4',B_151)
      | ~ m1_subset_1(B_151,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52,c_32,c_794])).

tff(c_814,plain,(
    k12_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k12_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_804])).

tff(c_821,plain,(
    k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_756,c_814])).

tff(c_122,plain,(
    ! [A_96,B_97,C_98] :
      ( k12_lattice3(A_96,B_97,C_98) = k11_lattice3(A_96,B_97,C_98)
      | ~ m1_subset_1(C_98,u1_struct_0(A_96))
      | ~ m1_subset_1(B_97,u1_struct_0(A_96))
      | ~ l1_orders_2(A_96)
      | ~ v2_lattice3(A_96)
      | ~ v5_orders_2(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_126,plain,(
    ! [B_97] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_97,'#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),B_97,'#skF_4')
      | ~ m1_subset_1(B_97,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_48,c_122])).

tff(c_137,plain,(
    ! [B_99] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_99,'#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),B_99,'#skF_4')
      | ~ m1_subset_1(B_99,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52,c_32,c_126])).

tff(c_152,plain,(
    k12_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_137])).

tff(c_128,plain,(
    ! [B_97] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_97,'#skF_3') = k11_lattice3(k2_yellow_1('#skF_2'),B_97,'#skF_3')
      | ~ m1_subset_1(B_97,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_50,c_122])).

tff(c_161,plain,(
    ! [B_100] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_100,'#skF_3') = k11_lattice3(k2_yellow_1('#skF_2'),B_100,'#skF_3')
      | ~ m1_subset_1(B_100,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52,c_32,c_128])).

tff(c_175,plain,(
    k12_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3') = k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_161])).

tff(c_245,plain,(
    ! [A_109,C_110,B_111] :
      ( k12_lattice3(A_109,C_110,B_111) = k12_lattice3(A_109,B_111,C_110)
      | ~ m1_subset_1(C_110,u1_struct_0(A_109))
      | ~ m1_subset_1(B_111,u1_struct_0(A_109))
      | ~ l1_orders_2(A_109)
      | ~ v2_lattice3(A_109)
      | ~ v5_orders_2(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_251,plain,(
    ! [B_111] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_111,'#skF_3') = k12_lattice3(k2_yellow_1('#skF_2'),'#skF_3',B_111)
      | ~ m1_subset_1(B_111,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_50,c_245])).

tff(c_261,plain,(
    ! [B_112] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_112,'#skF_3') = k12_lattice3(k2_yellow_1('#skF_2'),'#skF_3',B_112)
      | ~ m1_subset_1(B_112,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52,c_32,c_251])).

tff(c_268,plain,(
    k12_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k12_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_261])).

tff(c_276,plain,(
    k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_175,c_268])).

tff(c_62,plain,(
    ! [A_82,B_83,C_84] :
      ( r1_tarski(A_82,k3_xboole_0(B_83,C_84))
      | ~ r1_tarski(A_82,C_84)
      | ~ r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_66,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_46])).

tff(c_67,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_280,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_67])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] :
      ( m1_subset_1(k11_lattice3(A_11,B_12,C_13),u1_struct_0(A_11))
      | ~ m1_subset_1(C_13,u1_struct_0(A_11))
      | ~ m1_subset_1(B_12,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_285,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_12])).

tff(c_289,plain,(
    m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_50,c_48,c_285])).

tff(c_279,plain,(
    k12_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_152])).

tff(c_28,plain,(
    ! [A_17,B_41,C_53] :
      ( r1_orders_2(A_17,k12_lattice3(A_17,B_41,C_53),B_41)
      | ~ m1_subset_1(k12_lattice3(A_17,B_41,C_53),u1_struct_0(A_17))
      | ~ m1_subset_1(C_53,u1_struct_0(A_17))
      | ~ m1_subset_1(B_41,u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | ~ v2_lattice3(A_17)
      | ~ v5_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_359,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),k12_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2'))
    | ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ v5_orders_2(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_28])).

tff(c_363,plain,(
    r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52,c_32,c_50,c_48,c_289,c_279,c_359])).

tff(c_36,plain,(
    ! [A_64] : v3_orders_2(k2_yellow_1(A_64)) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_186,plain,(
    ! [A_104,B_105,C_106] :
      ( r3_orders_2(A_104,B_105,C_106)
      | ~ r1_orders_2(A_104,B_105,C_106)
      | ~ m1_subset_1(C_106,u1_struct_0(A_104))
      | ~ m1_subset_1(B_105,u1_struct_0(A_104))
      | ~ l1_orders_2(A_104)
      | ~ v3_orders_2(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_190,plain,(
    ! [B_105] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_4')
      | ~ m1_subset_1(B_105,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_48,c_186])).

tff(c_196,plain,(
    ! [B_105] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_4')
      | ~ m1_subset_1(B_105,u1_struct_0(k2_yellow_1('#skF_2')))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_190])).

tff(c_200,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ v2_struct_0(A_7)
      | ~ v2_lattice3(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_203,plain,
    ( ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_200,c_8])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_52,c_203])).

tff(c_209,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_192,plain,(
    ! [B_105] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_3')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_3')
      | ~ m1_subset_1(B_105,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_50,c_186])).

tff(c_199,plain,(
    ! [B_105] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_3')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_3')
      | ~ m1_subset_1(B_105,u1_struct_0(k2_yellow_1('#skF_2')))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_192])).

tff(c_210,plain,(
    ! [B_105] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_3')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_3')
      | ~ m1_subset_1(B_105,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_199])).

tff(c_329,plain,
    ( r3_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3')
    | ~ r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_289,c_210])).

tff(c_656,plain,(
    r3_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_329])).

tff(c_44,plain,(
    ! [B_69,C_71,A_65] :
      ( r1_tarski(B_69,C_71)
      | ~ r3_orders_2(k2_yellow_1(A_65),B_69,C_71)
      | ~ m1_subset_1(C_71,u1_struct_0(k2_yellow_1(A_65)))
      | ~ m1_subset_1(B_69,u1_struct_0(k2_yellow_1(A_65)))
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_660,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2')))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_656,c_44])).

tff(c_667,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_50,c_660])).

tff(c_669,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_280,c_667])).

tff(c_670,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_824,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_670])).

tff(c_829,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_821,c_12])).

tff(c_833,plain,(
    m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_50,c_48,c_829])).

tff(c_934,plain,(
    ! [A_156,B_157,C_158] :
      ( r1_orders_2(A_156,k12_lattice3(A_156,B_157,C_158),B_157)
      | ~ m1_subset_1(k12_lattice3(A_156,B_157,C_158),u1_struct_0(A_156))
      | ~ m1_subset_1(C_158,u1_struct_0(A_156))
      | ~ m1_subset_1(B_157,u1_struct_0(A_156))
      | ~ l1_orders_2(A_156)
      | ~ v2_lattice3(A_156)
      | ~ v5_orders_2(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_940,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),k12_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_4')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2'))
    | ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ v5_orders_2(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_934])).

tff(c_948,plain,(
    r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52,c_32,c_48,c_50,c_833,c_780,c_940])).

tff(c_671,plain,(
    r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_823,plain,(
    r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_671])).

tff(c_673,plain,(
    ! [A_132,B_133,C_134] :
      ( r3_orders_2(k2_yellow_1(A_132),B_133,C_134)
      | ~ r1_tarski(B_133,C_134)
      | ~ m1_subset_1(C_134,u1_struct_0(k2_yellow_1(A_132)))
      | ~ m1_subset_1(B_133,u1_struct_0(k2_yellow_1(A_132)))
      | v1_xboole_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_680,plain,(
    ! [B_133] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_133,'#skF_3')
      | ~ r1_tarski(B_133,'#skF_3')
      | ~ m1_subset_1(B_133,u1_struct_0(k2_yellow_1('#skF_2')))
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_50,c_673])).

tff(c_689,plain,(
    ! [B_133] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_133,'#skF_3')
      | ~ r1_tarski(B_133,'#skF_3')
      | ~ m1_subset_1(B_133,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_680])).

tff(c_872,plain,
    ( r3_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_833,c_689])).

tff(c_892,plain,(
    r3_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_823,c_872])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] :
      ( r1_orders_2(A_4,B_5,C_6)
      | ~ r3_orders_2(A_4,B_5,C_6)
      | ~ m1_subset_1(C_6,u1_struct_0(A_4))
      | ~ m1_subset_1(B_5,u1_struct_0(A_4))
      | ~ l1_orders_2(A_4)
      | ~ v3_orders_2(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_898,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2'))
    | ~ v3_orders_2(k2_yellow_1('#skF_2'))
    | v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_892,c_6])).

tff(c_903,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3')
    | v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_833,c_50,c_898])).

tff(c_924,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_903])).

tff(c_927,plain,
    ( ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_924,c_8])).

tff(c_931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_52,c_927])).

tff(c_933,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_903])).

tff(c_835,plain,(
    ! [A_152,B_153,C_154] :
      ( r3_orders_2(A_152,B_153,C_154)
      | ~ r1_orders_2(A_152,B_153,C_154)
      | ~ m1_subset_1(C_154,u1_struct_0(A_152))
      | ~ m1_subset_1(B_153,u1_struct_0(A_152))
      | ~ l1_orders_2(A_152)
      | ~ v3_orders_2(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_839,plain,(
    ! [B_153] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_153,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_153,'#skF_4')
      | ~ m1_subset_1(B_153,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_48,c_835])).

tff(c_845,plain,(
    ! [B_153] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_153,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_153,'#skF_4')
      | ~ m1_subset_1(B_153,u1_struct_0(k2_yellow_1('#skF_2')))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_839])).

tff(c_974,plain,(
    ! [B_160] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_160,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_160,'#skF_4')
      | ~ m1_subset_1(B_160,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_933,c_845])).

tff(c_977,plain,
    ( r3_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_4')
    | ~ r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_833,c_974])).

tff(c_990,plain,(
    r3_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_948,c_977])).

tff(c_1000,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2')))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_990,c_44])).

tff(c_1007,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_48,c_1000])).

tff(c_1009,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_824,c_1007])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:45:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.54  
% 3.43/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.54  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.43/1.54  
% 3.43/1.54  %Foreground sorts:
% 3.43/1.54  
% 3.43/1.54  
% 3.43/1.54  %Background operators:
% 3.43/1.54  
% 3.43/1.54  
% 3.43/1.54  %Foreground operators:
% 3.43/1.54  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.43/1.54  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.43/1.54  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.43/1.54  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.43/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.54  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.43/1.54  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.43/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.43/1.54  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 3.43/1.54  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 3.43/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.43/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.43/1.54  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.43/1.54  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.43/1.54  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.43/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.43/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.43/1.54  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 3.43/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.43/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.43/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.43/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.43/1.54  
% 3.43/1.56  tff(f_154, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v2_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k11_lattice3(k2_yellow_1(A), B, C), k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_1)).
% 3.43/1.56  tff(f_127, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.43/1.56  tff(f_119, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.43/1.56  tff(f_85, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 3.43/1.56  tff(f_65, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k12_lattice3(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k12_lattice3)).
% 3.43/1.56  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.43/1.56  tff(f_73, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k11_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 3.43/1.56  tff(f_115, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k12_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_yellow_0)).
% 3.43/1.56  tff(f_46, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.43/1.56  tff(f_53, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_lattice3)).
% 3.43/1.56  tff(f_140, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.43/1.56  tff(c_54, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.43/1.56  tff(c_48, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.43/1.56  tff(c_40, plain, (![A_64]: (v5_orders_2(k2_yellow_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.43/1.56  tff(c_52, plain, (v2_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.43/1.56  tff(c_32, plain, (![A_63]: (l1_orders_2(k2_yellow_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.43/1.56  tff(c_50, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.43/1.56  tff(c_727, plain, (![A_140, B_141, C_142]: (k12_lattice3(A_140, B_141, C_142)=k11_lattice3(A_140, B_141, C_142) | ~m1_subset_1(C_142, u1_struct_0(A_140)) | ~m1_subset_1(B_141, u1_struct_0(A_140)) | ~l1_orders_2(A_140) | ~v2_lattice3(A_140) | ~v5_orders_2(A_140))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.43/1.56  tff(c_733, plain, (![B_141]: (k12_lattice3(k2_yellow_1('#skF_2'), B_141, '#skF_3')=k11_lattice3(k2_yellow_1('#skF_2'), B_141, '#skF_3') | ~m1_subset_1(B_141, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_50, c_727])).
% 3.43/1.56  tff(c_766, plain, (![B_147]: (k12_lattice3(k2_yellow_1('#skF_2'), B_147, '#skF_3')=k11_lattice3(k2_yellow_1('#skF_2'), B_147, '#skF_3') | ~m1_subset_1(B_147, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52, c_32, c_733])).
% 3.43/1.56  tff(c_780, plain, (k12_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')=k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_766])).
% 3.43/1.56  tff(c_731, plain, (![B_141]: (k12_lattice3(k2_yellow_1('#skF_2'), B_141, '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), B_141, '#skF_4') | ~m1_subset_1(B_141, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_48, c_727])).
% 3.43/1.56  tff(c_741, plain, (![B_143]: (k12_lattice3(k2_yellow_1('#skF_2'), B_143, '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), B_143, '#skF_4') | ~m1_subset_1(B_143, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52, c_32, c_731])).
% 3.43/1.56  tff(c_756, plain, (k12_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_741])).
% 3.43/1.56  tff(c_790, plain, (![A_148, C_149, B_150]: (k12_lattice3(A_148, C_149, B_150)=k12_lattice3(A_148, B_150, C_149) | ~m1_subset_1(C_149, u1_struct_0(A_148)) | ~m1_subset_1(B_150, u1_struct_0(A_148)) | ~l1_orders_2(A_148) | ~v2_lattice3(A_148) | ~v5_orders_2(A_148))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.43/1.56  tff(c_794, plain, (![B_150]: (k12_lattice3(k2_yellow_1('#skF_2'), B_150, '#skF_4')=k12_lattice3(k2_yellow_1('#skF_2'), '#skF_4', B_150) | ~m1_subset_1(B_150, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_48, c_790])).
% 3.43/1.56  tff(c_804, plain, (![B_151]: (k12_lattice3(k2_yellow_1('#skF_2'), B_151, '#skF_4')=k12_lattice3(k2_yellow_1('#skF_2'), '#skF_4', B_151) | ~m1_subset_1(B_151, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52, c_32, c_794])).
% 3.43/1.56  tff(c_814, plain, (k12_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k12_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_804])).
% 3.43/1.56  tff(c_821, plain, (k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_780, c_756, c_814])).
% 3.43/1.56  tff(c_122, plain, (![A_96, B_97, C_98]: (k12_lattice3(A_96, B_97, C_98)=k11_lattice3(A_96, B_97, C_98) | ~m1_subset_1(C_98, u1_struct_0(A_96)) | ~m1_subset_1(B_97, u1_struct_0(A_96)) | ~l1_orders_2(A_96) | ~v2_lattice3(A_96) | ~v5_orders_2(A_96))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.43/1.56  tff(c_126, plain, (![B_97]: (k12_lattice3(k2_yellow_1('#skF_2'), B_97, '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), B_97, '#skF_4') | ~m1_subset_1(B_97, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_48, c_122])).
% 3.43/1.56  tff(c_137, plain, (![B_99]: (k12_lattice3(k2_yellow_1('#skF_2'), B_99, '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), B_99, '#skF_4') | ~m1_subset_1(B_99, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52, c_32, c_126])).
% 3.43/1.56  tff(c_152, plain, (k12_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_137])).
% 3.43/1.56  tff(c_128, plain, (![B_97]: (k12_lattice3(k2_yellow_1('#skF_2'), B_97, '#skF_3')=k11_lattice3(k2_yellow_1('#skF_2'), B_97, '#skF_3') | ~m1_subset_1(B_97, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_50, c_122])).
% 3.43/1.56  tff(c_161, plain, (![B_100]: (k12_lattice3(k2_yellow_1('#skF_2'), B_100, '#skF_3')=k11_lattice3(k2_yellow_1('#skF_2'), B_100, '#skF_3') | ~m1_subset_1(B_100, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52, c_32, c_128])).
% 3.43/1.56  tff(c_175, plain, (k12_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')=k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_161])).
% 3.43/1.56  tff(c_245, plain, (![A_109, C_110, B_111]: (k12_lattice3(A_109, C_110, B_111)=k12_lattice3(A_109, B_111, C_110) | ~m1_subset_1(C_110, u1_struct_0(A_109)) | ~m1_subset_1(B_111, u1_struct_0(A_109)) | ~l1_orders_2(A_109) | ~v2_lattice3(A_109) | ~v5_orders_2(A_109))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.43/1.56  tff(c_251, plain, (![B_111]: (k12_lattice3(k2_yellow_1('#skF_2'), B_111, '#skF_3')=k12_lattice3(k2_yellow_1('#skF_2'), '#skF_3', B_111) | ~m1_subset_1(B_111, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_50, c_245])).
% 3.43/1.56  tff(c_261, plain, (![B_112]: (k12_lattice3(k2_yellow_1('#skF_2'), B_112, '#skF_3')=k12_lattice3(k2_yellow_1('#skF_2'), '#skF_3', B_112) | ~m1_subset_1(B_112, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52, c_32, c_251])).
% 3.43/1.56  tff(c_268, plain, (k12_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k12_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_261])).
% 3.43/1.56  tff(c_276, plain, (k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_175, c_268])).
% 3.43/1.56  tff(c_62, plain, (![A_82, B_83, C_84]: (r1_tarski(A_82, k3_xboole_0(B_83, C_84)) | ~r1_tarski(A_82, C_84) | ~r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.43/1.56  tff(c_46, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.43/1.56  tff(c_66, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_62, c_46])).
% 3.43/1.56  tff(c_67, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 3.43/1.56  tff(c_280, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_67])).
% 3.43/1.56  tff(c_12, plain, (![A_11, B_12, C_13]: (m1_subset_1(k11_lattice3(A_11, B_12, C_13), u1_struct_0(A_11)) | ~m1_subset_1(C_13, u1_struct_0(A_11)) | ~m1_subset_1(B_12, u1_struct_0(A_11)) | ~l1_orders_2(A_11))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.43/1.56  tff(c_285, plain, (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_276, c_12])).
% 3.43/1.56  tff(c_289, plain, (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_50, c_48, c_285])).
% 3.43/1.56  tff(c_279, plain, (k12_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_152])).
% 3.43/1.56  tff(c_28, plain, (![A_17, B_41, C_53]: (r1_orders_2(A_17, k12_lattice3(A_17, B_41, C_53), B_41) | ~m1_subset_1(k12_lattice3(A_17, B_41, C_53), u1_struct_0(A_17)) | ~m1_subset_1(C_53, u1_struct_0(A_17)) | ~m1_subset_1(B_41, u1_struct_0(A_17)) | ~l1_orders_2(A_17) | ~v2_lattice3(A_17) | ~v5_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.43/1.56  tff(c_359, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k12_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_279, c_28])).
% 3.43/1.56  tff(c_363, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52, c_32, c_50, c_48, c_289, c_279, c_359])).
% 3.43/1.56  tff(c_36, plain, (![A_64]: (v3_orders_2(k2_yellow_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.43/1.56  tff(c_186, plain, (![A_104, B_105, C_106]: (r3_orders_2(A_104, B_105, C_106) | ~r1_orders_2(A_104, B_105, C_106) | ~m1_subset_1(C_106, u1_struct_0(A_104)) | ~m1_subset_1(B_105, u1_struct_0(A_104)) | ~l1_orders_2(A_104) | ~v3_orders_2(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.43/1.56  tff(c_190, plain, (![B_105]: (r3_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_4') | ~m1_subset_1(B_105, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_48, c_186])).
% 3.43/1.56  tff(c_196, plain, (![B_105]: (r3_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_4') | ~m1_subset_1(B_105, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_190])).
% 3.43/1.56  tff(c_200, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_196])).
% 3.43/1.56  tff(c_8, plain, (![A_7]: (~v2_struct_0(A_7) | ~v2_lattice3(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.43/1.56  tff(c_203, plain, (~v2_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_200, c_8])).
% 3.43/1.56  tff(c_207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_52, c_203])).
% 3.43/1.56  tff(c_209, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_196])).
% 3.43/1.56  tff(c_192, plain, (![B_105]: (r3_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_3') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_3') | ~m1_subset_1(B_105, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_50, c_186])).
% 3.43/1.56  tff(c_199, plain, (![B_105]: (r3_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_3') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_3') | ~m1_subset_1(B_105, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_192])).
% 3.43/1.56  tff(c_210, plain, (![B_105]: (r3_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_3') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_3') | ~m1_subset_1(B_105, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_209, c_199])).
% 3.43/1.56  tff(c_329, plain, (r3_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3') | ~r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_289, c_210])).
% 3.57/1.56  tff(c_656, plain, (r3_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_363, c_329])).
% 3.57/1.56  tff(c_44, plain, (![B_69, C_71, A_65]: (r1_tarski(B_69, C_71) | ~r3_orders_2(k2_yellow_1(A_65), B_69, C_71) | ~m1_subset_1(C_71, u1_struct_0(k2_yellow_1(A_65))) | ~m1_subset_1(B_69, u1_struct_0(k2_yellow_1(A_65))) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.57/1.56  tff(c_660, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2'))) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_656, c_44])).
% 3.57/1.56  tff(c_667, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_289, c_50, c_660])).
% 3.57/1.56  tff(c_669, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_280, c_667])).
% 3.57/1.56  tff(c_670, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_66])).
% 3.57/1.56  tff(c_824, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_821, c_670])).
% 3.57/1.56  tff(c_829, plain, (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_821, c_12])).
% 3.57/1.56  tff(c_833, plain, (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_50, c_48, c_829])).
% 3.57/1.56  tff(c_934, plain, (![A_156, B_157, C_158]: (r1_orders_2(A_156, k12_lattice3(A_156, B_157, C_158), B_157) | ~m1_subset_1(k12_lattice3(A_156, B_157, C_158), u1_struct_0(A_156)) | ~m1_subset_1(C_158, u1_struct_0(A_156)) | ~m1_subset_1(B_157, u1_struct_0(A_156)) | ~l1_orders_2(A_156) | ~v2_lattice3(A_156) | ~v5_orders_2(A_156))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.57/1.56  tff(c_940, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k12_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_4') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_780, c_934])).
% 3.57/1.56  tff(c_948, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52, c_32, c_48, c_50, c_833, c_780, c_940])).
% 3.57/1.56  tff(c_671, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_66])).
% 3.57/1.56  tff(c_823, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_821, c_671])).
% 3.57/1.56  tff(c_673, plain, (![A_132, B_133, C_134]: (r3_orders_2(k2_yellow_1(A_132), B_133, C_134) | ~r1_tarski(B_133, C_134) | ~m1_subset_1(C_134, u1_struct_0(k2_yellow_1(A_132))) | ~m1_subset_1(B_133, u1_struct_0(k2_yellow_1(A_132))) | v1_xboole_0(A_132))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.57/1.56  tff(c_680, plain, (![B_133]: (r3_orders_2(k2_yellow_1('#skF_2'), B_133, '#skF_3') | ~r1_tarski(B_133, '#skF_3') | ~m1_subset_1(B_133, u1_struct_0(k2_yellow_1('#skF_2'))) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_673])).
% 3.57/1.56  tff(c_689, plain, (![B_133]: (r3_orders_2(k2_yellow_1('#skF_2'), B_133, '#skF_3') | ~r1_tarski(B_133, '#skF_3') | ~m1_subset_1(B_133, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_680])).
% 3.57/1.56  tff(c_872, plain, (r3_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_833, c_689])).
% 3.57/1.56  tff(c_892, plain, (r3_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_823, c_872])).
% 3.57/1.56  tff(c_6, plain, (![A_4, B_5, C_6]: (r1_orders_2(A_4, B_5, C_6) | ~r3_orders_2(A_4, B_5, C_6) | ~m1_subset_1(C_6, u1_struct_0(A_4)) | ~m1_subset_1(B_5, u1_struct_0(A_4)) | ~l1_orders_2(A_4) | ~v3_orders_2(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.57/1.56  tff(c_898, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_892, c_6])).
% 3.57/1.56  tff(c_903, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3') | v2_struct_0(k2_yellow_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_833, c_50, c_898])).
% 3.57/1.56  tff(c_924, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_903])).
% 3.57/1.56  tff(c_927, plain, (~v2_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_924, c_8])).
% 3.57/1.56  tff(c_931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_52, c_927])).
% 3.57/1.56  tff(c_933, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_903])).
% 3.57/1.56  tff(c_835, plain, (![A_152, B_153, C_154]: (r3_orders_2(A_152, B_153, C_154) | ~r1_orders_2(A_152, B_153, C_154) | ~m1_subset_1(C_154, u1_struct_0(A_152)) | ~m1_subset_1(B_153, u1_struct_0(A_152)) | ~l1_orders_2(A_152) | ~v3_orders_2(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.57/1.56  tff(c_839, plain, (![B_153]: (r3_orders_2(k2_yellow_1('#skF_2'), B_153, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_153, '#skF_4') | ~m1_subset_1(B_153, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_48, c_835])).
% 3.57/1.56  tff(c_845, plain, (![B_153]: (r3_orders_2(k2_yellow_1('#skF_2'), B_153, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_153, '#skF_4') | ~m1_subset_1(B_153, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_839])).
% 3.57/1.56  tff(c_974, plain, (![B_160]: (r3_orders_2(k2_yellow_1('#skF_2'), B_160, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_160, '#skF_4') | ~m1_subset_1(B_160, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_933, c_845])).
% 3.57/1.56  tff(c_977, plain, (r3_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_833, c_974])).
% 3.57/1.56  tff(c_990, plain, (r3_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_948, c_977])).
% 3.57/1.56  tff(c_1000, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2'))) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_990, c_44])).
% 3.57/1.56  tff(c_1007, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_833, c_48, c_1000])).
% 3.57/1.56  tff(c_1009, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_824, c_1007])).
% 3.57/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.56  
% 3.57/1.56  Inference rules
% 3.57/1.56  ----------------------
% 3.57/1.56  #Ref     : 0
% 3.57/1.56  #Sup     : 187
% 3.57/1.56  #Fact    : 0
% 3.57/1.56  #Define  : 0
% 3.57/1.56  #Split   : 21
% 3.57/1.56  #Chain   : 0
% 3.57/1.56  #Close   : 0
% 3.57/1.56  
% 3.57/1.56  Ordering : KBO
% 3.57/1.56  
% 3.57/1.56  Simplification rules
% 3.57/1.56  ----------------------
% 3.57/1.56  #Subsume      : 4
% 3.57/1.56  #Demod        : 283
% 3.57/1.56  #Tautology    : 45
% 3.57/1.56  #SimpNegUnit  : 25
% 3.57/1.56  #BackRed      : 7
% 3.57/1.56  
% 3.57/1.56  #Partial instantiations: 0
% 3.57/1.56  #Strategies tried      : 1
% 3.57/1.56  
% 3.57/1.56  Timing (in seconds)
% 3.57/1.56  ----------------------
% 3.57/1.57  Preprocessing        : 0.35
% 3.57/1.57  Parsing              : 0.18
% 3.57/1.57  CNF conversion       : 0.03
% 3.57/1.57  Main loop            : 0.43
% 3.57/1.57  Inferencing          : 0.14
% 3.57/1.57  Reduction            : 0.16
% 3.57/1.57  Demodulation         : 0.11
% 3.57/1.57  BG Simplification    : 0.03
% 3.57/1.57  Subsumption          : 0.08
% 3.57/1.57  Abstraction          : 0.03
% 3.57/1.57  MUC search           : 0.00
% 3.57/1.57  Cooper               : 0.00
% 3.57/1.57  Total                : 0.83
% 3.57/1.57  Index Insertion      : 0.00
% 3.57/1.57  Index Deletion       : 0.00
% 3.57/1.57  Index Matching       : 0.00
% 3.57/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
