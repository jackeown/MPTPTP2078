%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:24 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 431 expanded)
%              Number of leaves         :   35 ( 179 expanded)
%              Depth                    :   12
%              Number of atoms          :  245 (1276 expanded)
%              Number of equality atoms :   10 (  62 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k11_lattice3 > k3_xboole_0 > g1_orders_2 > #nlpp > u1_struct_0 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_150,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v2_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(A),B,C),k3_xboole_0(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).

tff(f_115,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_107,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k11_lattice3(A,B,C) = k11_lattice3(A,C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_lattice3)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

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

tff(f_123,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k11_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,D,B)
                      & r1_orders_2(A,D,C)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,E,B)
                              & r1_orders_2(A,E,C) )
                           => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).

tff(f_136,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_38,plain,(
    ! [A_65] : v5_orders_2(k2_yellow_1(A_65)) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_54,plain,(
    v2_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_30,plain,(
    ! [A_64] : l1_orders_2(k2_yellow_1(A_64)) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_457,plain,(
    ! [A_133,C_134,B_135] :
      ( k11_lattice3(A_133,C_134,B_135) = k11_lattice3(A_133,B_135,C_134)
      | ~ m1_subset_1(C_134,u1_struct_0(A_133))
      | ~ m1_subset_1(B_135,u1_struct_0(A_133))
      | ~ l1_orders_2(A_133)
      | ~ v2_lattice3(A_133)
      | ~ v5_orders_2(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_463,plain,(
    ! [B_135] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_135,'#skF_3') = k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3',B_135)
      | ~ m1_subset_1(B_135,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_52,c_457])).

tff(c_473,plain,(
    ! [B_136] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_136,'#skF_3') = k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3',B_136)
      | ~ m1_subset_1(B_136,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_54,c_30,c_463])).

tff(c_487,plain,(
    k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_473])).

tff(c_188,plain,(
    ! [A_108,C_109,B_110] :
      ( k11_lattice3(A_108,C_109,B_110) = k11_lattice3(A_108,B_110,C_109)
      | ~ m1_subset_1(C_109,u1_struct_0(A_108))
      | ~ m1_subset_1(B_110,u1_struct_0(A_108))
      | ~ l1_orders_2(A_108)
      | ~ v2_lattice3(A_108)
      | ~ v5_orders_2(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_194,plain,(
    ! [B_110] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_110,'#skF_3') = k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3',B_110)
      | ~ m1_subset_1(B_110,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_52,c_188])).

tff(c_204,plain,(
    ! [B_111] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_111,'#skF_3') = k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3',B_111)
      | ~ m1_subset_1(B_111,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_54,c_30,c_194])).

tff(c_218,plain,(
    k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_204])).

tff(c_74,plain,(
    ! [A_85,B_86,C_87] :
      ( r1_tarski(A_85,k3_xboole_0(B_86,C_87))
      | ~ r1_tarski(A_85,C_87)
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_78,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_48])).

tff(c_79,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_221,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_79])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k11_lattice3(A_7,B_8,C_9),u1_struct_0(A_7))
      | ~ m1_subset_1(C_9,u1_struct_0(A_7))
      | ~ m1_subset_1(B_8,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_229,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_8])).

tff(c_235,plain,(
    m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_52,c_50,c_229])).

tff(c_34,plain,(
    ! [A_65] : v3_orders_2(k2_yellow_1(A_65)) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_148,plain,(
    ! [A_104,B_105,C_106] :
      ( r3_orders_2(A_104,B_105,C_106)
      | ~ r1_orders_2(A_104,B_105,C_106)
      | ~ m1_subset_1(C_106,u1_struct_0(A_104))
      | ~ m1_subset_1(B_105,u1_struct_0(A_104))
      | ~ l1_orders_2(A_104)
      | ~ v3_orders_2(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_152,plain,(
    ! [B_105] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_4')
      | ~ m1_subset_1(B_105,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_50,c_148])).

tff(c_158,plain,(
    ! [B_105] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_4')
      | ~ m1_subset_1(B_105,u1_struct_0(k2_yellow_1('#skF_2')))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_152])).

tff(c_162,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_42,plain,(
    ! [A_66] :
      ( ~ v2_struct_0(k2_yellow_1(A_66))
      | v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_165,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_162,c_42])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_165])).

tff(c_171,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_273,plain,(
    ! [A_112,B_113,C_114] :
      ( r1_orders_2(A_112,k11_lattice3(A_112,B_113,C_114),B_113)
      | ~ m1_subset_1(k11_lattice3(A_112,B_113,C_114),u1_struct_0(A_112))
      | ~ m1_subset_1(C_114,u1_struct_0(A_112))
      | ~ m1_subset_1(B_113,u1_struct_0(A_112))
      | ~ l1_orders_2(A_112)
      | ~ v2_lattice3(A_112)
      | ~ v5_orders_2(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_277,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2'))
    | ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ v5_orders_2(k2_yellow_1('#skF_2'))
    | v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_273])).

tff(c_285,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3')
    | v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_54,c_30,c_52,c_50,c_235,c_218,c_277])).

tff(c_286,plain,(
    r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_285])).

tff(c_154,plain,(
    ! [B_105] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_3')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_3')
      | ~ m1_subset_1(B_105,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_52,c_148])).

tff(c_161,plain,(
    ! [B_105] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_3')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_3')
      | ~ m1_subset_1(B_105,u1_struct_0(k2_yellow_1('#skF_2')))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_154])).

tff(c_325,plain,(
    ! [B_117] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_117,'#skF_3')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_117,'#skF_3')
      | ~ m1_subset_1(B_117,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_161])).

tff(c_328,plain,
    ( r3_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3')
    | ~ r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_235,c_325])).

tff(c_341,plain,(
    r3_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_328])).

tff(c_46,plain,(
    ! [B_71,C_73,A_67] :
      ( r1_tarski(B_71,C_73)
      | ~ r3_orders_2(k2_yellow_1(A_67),B_71,C_73)
      | ~ m1_subset_1(C_73,u1_struct_0(k2_yellow_1(A_67)))
      | ~ m1_subset_1(B_71,u1_struct_0(k2_yellow_1(A_67)))
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_350,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2')))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_341,c_46])).

tff(c_357,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_52,c_350])).

tff(c_359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_221,c_357])).

tff(c_360,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_491,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_360])).

tff(c_496,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_8])).

tff(c_500,plain,(
    m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_52,c_50,c_496])).

tff(c_399,plain,(
    ! [A_128,B_129,C_130] :
      ( r3_orders_2(A_128,B_129,C_130)
      | ~ r1_orders_2(A_128,B_129,C_130)
      | ~ m1_subset_1(C_130,u1_struct_0(A_128))
      | ~ m1_subset_1(B_129,u1_struct_0(A_128))
      | ~ l1_orders_2(A_128)
      | ~ v3_orders_2(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_405,plain,(
    ! [B_129] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_129,'#skF_3')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_129,'#skF_3')
      | ~ m1_subset_1(B_129,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_52,c_399])).

tff(c_412,plain,(
    ! [B_129] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_129,'#skF_3')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_129,'#skF_3')
      | ~ m1_subset_1(B_129,u1_struct_0(k2_yellow_1('#skF_2')))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_405])).

tff(c_431,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_412])).

tff(c_434,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_431,c_42])).

tff(c_438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_434])).

tff(c_440,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_412])).

tff(c_613,plain,(
    ! [A_143,B_144,C_145] :
      ( r1_orders_2(A_143,k11_lattice3(A_143,B_144,C_145),C_145)
      | ~ m1_subset_1(k11_lattice3(A_143,B_144,C_145),u1_struct_0(A_143))
      | ~ m1_subset_1(C_145,u1_struct_0(A_143))
      | ~ m1_subset_1(B_144,u1_struct_0(A_143))
      | ~ l1_orders_2(A_143)
      | ~ v2_lattice3(A_143)
      | ~ v5_orders_2(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_617,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2'))
    | ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ v5_orders_2(k2_yellow_1('#skF_2'))
    | v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_613])).

tff(c_625,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_4')
    | v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_54,c_30,c_52,c_50,c_500,c_487,c_617])).

tff(c_626,plain,(
    r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_440,c_625])).

tff(c_403,plain,(
    ! [B_129] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_129,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_129,'#skF_4')
      | ~ m1_subset_1(B_129,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_50,c_399])).

tff(c_409,plain,(
    ! [B_129] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_129,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_129,'#skF_4')
      | ~ m1_subset_1(B_129,u1_struct_0(k2_yellow_1('#skF_2')))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_403])).

tff(c_591,plain,(
    ! [B_142] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_142,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_142,'#skF_4')
      | ~ m1_subset_1(B_142,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_440,c_409])).

tff(c_605,plain,
    ( r3_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_4')
    | ~ r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_500,c_591])).

tff(c_788,plain,(
    r3_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_626,c_605])).

tff(c_792,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2')))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_788,c_46])).

tff(c_799,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_500,c_50,c_792])).

tff(c_801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_491,c_799])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.45  
% 2.94/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.45  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k11_lattice3 > k3_xboole_0 > g1_orders_2 > #nlpp > u1_struct_0 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.94/1.45  
% 2.94/1.45  %Foreground sorts:
% 2.94/1.45  
% 2.94/1.45  
% 2.94/1.45  %Background operators:
% 2.94/1.45  
% 2.94/1.45  
% 2.94/1.45  %Foreground operators:
% 2.94/1.45  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.94/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.94/1.45  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.94/1.45  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.94/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.45  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.94/1.45  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.94/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.45  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 2.94/1.45  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.94/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.94/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.94/1.45  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.94/1.45  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.94/1.45  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.94/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.94/1.45  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.94/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.94/1.45  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 2.94/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.94/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.94/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.94/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.45  
% 3.22/1.47  tff(f_150, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v2_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k11_lattice3(k2_yellow_1(A), B, C), k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_1)).
% 3.22/1.47  tff(f_115, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.22/1.47  tff(f_107, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.22/1.47  tff(f_101, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k11_lattice3(A, B, C) = k11_lattice3(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_lattice3)).
% 3.22/1.47  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.22/1.47  tff(f_54, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k11_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 3.22/1.47  tff(f_46, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.22/1.47  tff(f_123, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_yellow_1)).
% 3.22/1.47  tff(f_87, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 3.22/1.47  tff(f_136, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.22/1.47  tff(c_56, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.22/1.47  tff(c_50, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.22/1.47  tff(c_38, plain, (![A_65]: (v5_orders_2(k2_yellow_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.22/1.47  tff(c_54, plain, (v2_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.22/1.47  tff(c_30, plain, (![A_64]: (l1_orders_2(k2_yellow_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.22/1.47  tff(c_52, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.22/1.47  tff(c_457, plain, (![A_133, C_134, B_135]: (k11_lattice3(A_133, C_134, B_135)=k11_lattice3(A_133, B_135, C_134) | ~m1_subset_1(C_134, u1_struct_0(A_133)) | ~m1_subset_1(B_135, u1_struct_0(A_133)) | ~l1_orders_2(A_133) | ~v2_lattice3(A_133) | ~v5_orders_2(A_133))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.22/1.47  tff(c_463, plain, (![B_135]: (k11_lattice3(k2_yellow_1('#skF_2'), B_135, '#skF_3')=k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', B_135) | ~m1_subset_1(B_135, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_52, c_457])).
% 3.22/1.47  tff(c_473, plain, (![B_136]: (k11_lattice3(k2_yellow_1('#skF_2'), B_136, '#skF_3')=k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', B_136) | ~m1_subset_1(B_136, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_54, c_30, c_463])).
% 3.22/1.47  tff(c_487, plain, (k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_473])).
% 3.22/1.47  tff(c_188, plain, (![A_108, C_109, B_110]: (k11_lattice3(A_108, C_109, B_110)=k11_lattice3(A_108, B_110, C_109) | ~m1_subset_1(C_109, u1_struct_0(A_108)) | ~m1_subset_1(B_110, u1_struct_0(A_108)) | ~l1_orders_2(A_108) | ~v2_lattice3(A_108) | ~v5_orders_2(A_108))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.22/1.47  tff(c_194, plain, (![B_110]: (k11_lattice3(k2_yellow_1('#skF_2'), B_110, '#skF_3')=k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', B_110) | ~m1_subset_1(B_110, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_52, c_188])).
% 3.22/1.47  tff(c_204, plain, (![B_111]: (k11_lattice3(k2_yellow_1('#skF_2'), B_111, '#skF_3')=k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', B_111) | ~m1_subset_1(B_111, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_54, c_30, c_194])).
% 3.22/1.47  tff(c_218, plain, (k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_204])).
% 3.22/1.47  tff(c_74, plain, (![A_85, B_86, C_87]: (r1_tarski(A_85, k3_xboole_0(B_86, C_87)) | ~r1_tarski(A_85, C_87) | ~r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.47  tff(c_48, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.22/1.47  tff(c_78, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_74, c_48])).
% 3.22/1.47  tff(c_79, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_78])).
% 3.22/1.47  tff(c_221, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_218, c_79])).
% 3.22/1.47  tff(c_8, plain, (![A_7, B_8, C_9]: (m1_subset_1(k11_lattice3(A_7, B_8, C_9), u1_struct_0(A_7)) | ~m1_subset_1(C_9, u1_struct_0(A_7)) | ~m1_subset_1(B_8, u1_struct_0(A_7)) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.22/1.47  tff(c_229, plain, (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_218, c_8])).
% 3.22/1.47  tff(c_235, plain, (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_52, c_50, c_229])).
% 3.22/1.47  tff(c_34, plain, (![A_65]: (v3_orders_2(k2_yellow_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.22/1.47  tff(c_148, plain, (![A_104, B_105, C_106]: (r3_orders_2(A_104, B_105, C_106) | ~r1_orders_2(A_104, B_105, C_106) | ~m1_subset_1(C_106, u1_struct_0(A_104)) | ~m1_subset_1(B_105, u1_struct_0(A_104)) | ~l1_orders_2(A_104) | ~v3_orders_2(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.22/1.47  tff(c_152, plain, (![B_105]: (r3_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_4') | ~m1_subset_1(B_105, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_50, c_148])).
% 3.22/1.47  tff(c_158, plain, (![B_105]: (r3_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_4') | ~m1_subset_1(B_105, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_152])).
% 3.22/1.47  tff(c_162, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_158])).
% 3.22/1.47  tff(c_42, plain, (![A_66]: (~v2_struct_0(k2_yellow_1(A_66)) | v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.22/1.47  tff(c_165, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_162, c_42])).
% 3.22/1.47  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_165])).
% 3.22/1.47  tff(c_171, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_158])).
% 3.22/1.47  tff(c_273, plain, (![A_112, B_113, C_114]: (r1_orders_2(A_112, k11_lattice3(A_112, B_113, C_114), B_113) | ~m1_subset_1(k11_lattice3(A_112, B_113, C_114), u1_struct_0(A_112)) | ~m1_subset_1(C_114, u1_struct_0(A_112)) | ~m1_subset_1(B_113, u1_struct_0(A_112)) | ~l1_orders_2(A_112) | ~v2_lattice3(A_112) | ~v5_orders_2(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.22/1.47  tff(c_277, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_218, c_273])).
% 3.22/1.47  tff(c_285, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3') | v2_struct_0(k2_yellow_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_54, c_30, c_52, c_50, c_235, c_218, c_277])).
% 3.22/1.47  tff(c_286, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_171, c_285])).
% 3.22/1.47  tff(c_154, plain, (![B_105]: (r3_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_3') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_3') | ~m1_subset_1(B_105, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_52, c_148])).
% 3.22/1.47  tff(c_161, plain, (![B_105]: (r3_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_3') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_3') | ~m1_subset_1(B_105, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_154])).
% 3.22/1.47  tff(c_325, plain, (![B_117]: (r3_orders_2(k2_yellow_1('#skF_2'), B_117, '#skF_3') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_117, '#skF_3') | ~m1_subset_1(B_117, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_171, c_161])).
% 3.22/1.47  tff(c_328, plain, (r3_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3') | ~r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_235, c_325])).
% 3.22/1.47  tff(c_341, plain, (r3_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_286, c_328])).
% 3.22/1.47  tff(c_46, plain, (![B_71, C_73, A_67]: (r1_tarski(B_71, C_73) | ~r3_orders_2(k2_yellow_1(A_67), B_71, C_73) | ~m1_subset_1(C_73, u1_struct_0(k2_yellow_1(A_67))) | ~m1_subset_1(B_71, u1_struct_0(k2_yellow_1(A_67))) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.22/1.47  tff(c_350, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2'))) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_341, c_46])).
% 3.22/1.47  tff(c_357, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_235, c_52, c_350])).
% 3.22/1.47  tff(c_359, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_221, c_357])).
% 3.22/1.47  tff(c_360, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_78])).
% 3.22/1.47  tff(c_491, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_487, c_360])).
% 3.22/1.47  tff(c_496, plain, (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_487, c_8])).
% 3.22/1.47  tff(c_500, plain, (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_52, c_50, c_496])).
% 3.22/1.47  tff(c_399, plain, (![A_128, B_129, C_130]: (r3_orders_2(A_128, B_129, C_130) | ~r1_orders_2(A_128, B_129, C_130) | ~m1_subset_1(C_130, u1_struct_0(A_128)) | ~m1_subset_1(B_129, u1_struct_0(A_128)) | ~l1_orders_2(A_128) | ~v3_orders_2(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.22/1.47  tff(c_405, plain, (![B_129]: (r3_orders_2(k2_yellow_1('#skF_2'), B_129, '#skF_3') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_129, '#skF_3') | ~m1_subset_1(B_129, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_52, c_399])).
% 3.22/1.47  tff(c_412, plain, (![B_129]: (r3_orders_2(k2_yellow_1('#skF_2'), B_129, '#skF_3') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_129, '#skF_3') | ~m1_subset_1(B_129, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_405])).
% 3.22/1.47  tff(c_431, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_412])).
% 3.22/1.47  tff(c_434, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_431, c_42])).
% 3.22/1.47  tff(c_438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_434])).
% 3.22/1.47  tff(c_440, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_412])).
% 3.22/1.47  tff(c_613, plain, (![A_143, B_144, C_145]: (r1_orders_2(A_143, k11_lattice3(A_143, B_144, C_145), C_145) | ~m1_subset_1(k11_lattice3(A_143, B_144, C_145), u1_struct_0(A_143)) | ~m1_subset_1(C_145, u1_struct_0(A_143)) | ~m1_subset_1(B_144, u1_struct_0(A_143)) | ~l1_orders_2(A_143) | ~v2_lattice3(A_143) | ~v5_orders_2(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.22/1.47  tff(c_617, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_487, c_613])).
% 3.22/1.47  tff(c_625, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_4') | v2_struct_0(k2_yellow_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_54, c_30, c_52, c_50, c_500, c_487, c_617])).
% 3.22/1.47  tff(c_626, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_440, c_625])).
% 3.22/1.47  tff(c_403, plain, (![B_129]: (r3_orders_2(k2_yellow_1('#skF_2'), B_129, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_129, '#skF_4') | ~m1_subset_1(B_129, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_50, c_399])).
% 3.22/1.47  tff(c_409, plain, (![B_129]: (r3_orders_2(k2_yellow_1('#skF_2'), B_129, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_129, '#skF_4') | ~m1_subset_1(B_129, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_403])).
% 3.22/1.47  tff(c_591, plain, (![B_142]: (r3_orders_2(k2_yellow_1('#skF_2'), B_142, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_142, '#skF_4') | ~m1_subset_1(B_142, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_440, c_409])).
% 3.22/1.47  tff(c_605, plain, (r3_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_500, c_591])).
% 3.22/1.47  tff(c_788, plain, (r3_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_626, c_605])).
% 3.22/1.47  tff(c_792, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2'))) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_788, c_46])).
% 3.22/1.47  tff(c_799, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_500, c_50, c_792])).
% 3.22/1.47  tff(c_801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_491, c_799])).
% 3.22/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.47  
% 3.22/1.47  Inference rules
% 3.22/1.47  ----------------------
% 3.22/1.47  #Ref     : 0
% 3.22/1.47  #Sup     : 139
% 3.22/1.47  #Fact    : 0
% 3.22/1.47  #Define  : 0
% 3.22/1.47  #Split   : 18
% 3.22/1.47  #Chain   : 0
% 3.22/1.47  #Close   : 0
% 3.22/1.47  
% 3.22/1.47  Ordering : KBO
% 3.22/1.47  
% 3.22/1.47  Simplification rules
% 3.22/1.47  ----------------------
% 3.22/1.47  #Subsume      : 5
% 3.22/1.47  #Demod        : 204
% 3.22/1.47  #Tautology    : 30
% 3.22/1.47  #SimpNegUnit  : 41
% 3.22/1.47  #BackRed      : 5
% 3.22/1.47  
% 3.22/1.47  #Partial instantiations: 0
% 3.22/1.47  #Strategies tried      : 1
% 3.22/1.47  
% 3.22/1.47  Timing (in seconds)
% 3.22/1.47  ----------------------
% 3.22/1.48  Preprocessing        : 0.33
% 3.22/1.48  Parsing              : 0.18
% 3.22/1.48  CNF conversion       : 0.03
% 3.22/1.48  Main loop            : 0.37
% 3.22/1.48  Inferencing          : 0.12
% 3.22/1.48  Reduction            : 0.13
% 3.22/1.48  Demodulation         : 0.09
% 3.22/1.48  BG Simplification    : 0.02
% 3.22/1.48  Subsumption          : 0.07
% 3.22/1.48  Abstraction          : 0.02
% 3.22/1.48  MUC search           : 0.00
% 3.22/1.48  Cooper               : 0.00
% 3.22/1.48  Total                : 0.74
% 3.22/1.48  Index Insertion      : 0.00
% 3.22/1.48  Index Deletion       : 0.00
% 3.22/1.48  Index Matching       : 0.00
% 3.22/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
