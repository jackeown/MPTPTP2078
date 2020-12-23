%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:42 EST 2020

% Result     : Theorem 8.97s
% Output     : CNFRefutation 9.11s
% Verified   : 
% Statistics : Number of formulae       :   97 (1011 expanded)
%              Number of leaves         :   31 ( 408 expanded)
%              Depth                    :   15
%              Number of atoms          :  297 (4332 expanded)
%              Number of equality atoms :   45 ( 606 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k13_lattice3,type,(
    k13_lattice3: ( $i * $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k10_lattice3,type,(
    k10_lattice3: ( $i * $i * $i ) > $i )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_195,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k12_lattice3(A,B,k13_lattice3(A,B,C)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_lattice3)).

tff(f_158,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k13_lattice3(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k13_lattice3)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k13_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k13_lattice3)).

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k10_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,B,D)
                      & r1_orders_2(A,C,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,B,E)
                              & r1_orders_2(A,C,E) )
                           => r1_orders_2(A,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_146,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k12_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k12_lattice3)).

tff(f_176,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k13_lattice3(A,k12_lattice3(A,B,C),C) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattice3)).

tff(f_134,axiom,(
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

tff(c_48,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_56,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_54,plain,(
    v1_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_50,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_299,plain,(
    ! [A_136,B_137,C_138] :
      ( k13_lattice3(A_136,B_137,C_138) = k10_lattice3(A_136,B_137,C_138)
      | ~ m1_subset_1(C_138,u1_struct_0(A_136))
      | ~ m1_subset_1(B_137,u1_struct_0(A_136))
      | ~ l1_orders_2(A_136)
      | ~ v1_lattice3(A_136)
      | ~ v5_orders_2(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_313,plain,(
    ! [B_137] :
      ( k13_lattice3('#skF_3',B_137,'#skF_5') = k10_lattice3('#skF_3',B_137,'#skF_5')
      | ~ m1_subset_1(B_137,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_299])).

tff(c_408,plain,(
    ! [B_140] :
      ( k13_lattice3('#skF_3',B_140,'#skF_5') = k10_lattice3('#skF_3',B_140,'#skF_5')
      | ~ m1_subset_1(B_140,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_313])).

tff(c_450,plain,(
    k13_lattice3('#skF_3','#skF_4','#skF_5') = k10_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_408])).

tff(c_44,plain,(
    k12_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_497,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_44])).

tff(c_120,plain,(
    ! [A_131,C_132,B_133] :
      ( k13_lattice3(A_131,C_132,B_133) = k13_lattice3(A_131,B_133,C_132)
      | ~ m1_subset_1(C_132,u1_struct_0(A_131))
      | ~ m1_subset_1(B_133,u1_struct_0(A_131))
      | ~ l1_orders_2(A_131)
      | ~ v1_lattice3(A_131)
      | ~ v5_orders_2(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_130,plain,(
    ! [B_133] :
      ( k13_lattice3('#skF_3',B_133,'#skF_4') = k13_lattice3('#skF_3','#skF_4',B_133)
      | ~ m1_subset_1(B_133,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_120])).

tff(c_250,plain,(
    ! [B_135] :
      ( k13_lattice3('#skF_3',B_135,'#skF_4') = k13_lattice3('#skF_3','#skF_4',B_135)
      | ~ m1_subset_1(B_135,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_130])).

tff(c_287,plain,(
    k13_lattice3('#skF_3','#skF_5','#skF_4') = k13_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_250])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k13_lattice3(A_8,B_9,C_10),u1_struct_0(A_8))
      | ~ m1_subset_1(C_10,u1_struct_0(A_8))
      | ~ m1_subset_1(B_9,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8)
      | ~ v1_lattice3(A_8)
      | ~ v5_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_293,plain,
    ( m1_subset_1(k13_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_8])).

tff(c_297,plain,(
    m1_subset_1(k13_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_46,c_48,c_293])).

tff(c_495,plain,(
    m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_297])).

tff(c_496,plain,(
    k13_lattice3('#skF_3','#skF_5','#skF_4') = k10_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_287])).

tff(c_315,plain,(
    ! [B_137] :
      ( k13_lattice3('#skF_3',B_137,'#skF_4') = k10_lattice3('#skF_3',B_137,'#skF_4')
      | ~ m1_subset_1(B_137,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_299])).

tff(c_599,plain,(
    ! [B_144] :
      ( k13_lattice3('#skF_3',B_144,'#skF_4') = k10_lattice3('#skF_3',B_144,'#skF_4')
      | ~ m1_subset_1(B_144,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_315])).

tff(c_628,plain,(
    k13_lattice3('#skF_3','#skF_5','#skF_4') = k10_lattice3('#skF_3','#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_599])).

tff(c_645,plain,(
    k10_lattice3('#skF_3','#skF_5','#skF_4') = k10_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_628])).

tff(c_784,plain,(
    ! [A_146,C_147,B_148] :
      ( r1_orders_2(A_146,C_147,k10_lattice3(A_146,B_148,C_147))
      | ~ m1_subset_1(k10_lattice3(A_146,B_148,C_147),u1_struct_0(A_146))
      | ~ m1_subset_1(C_147,u1_struct_0(A_146))
      | ~ m1_subset_1(B_148,u1_struct_0(A_146))
      | ~ l1_orders_2(A_146)
      | ~ v1_lattice3(A_146)
      | ~ v5_orders_2(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_788,plain,
    ( r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_5','#skF_4'))
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_784])).

tff(c_797,plain,
    ( r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_46,c_48,c_495,c_645,c_788])).

tff(c_804,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_797])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v1_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_807,plain,
    ( ~ v1_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_804,c_2])).

tff(c_811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_807])).

tff(c_813,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_797])).

tff(c_52,plain,(
    v2_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_62,plain,(
    ! [A_127,B_128,C_129] :
      ( k12_lattice3(A_127,B_128,C_129) = k11_lattice3(A_127,B_128,C_129)
      | ~ m1_subset_1(C_129,u1_struct_0(A_127))
      | ~ m1_subset_1(B_128,u1_struct_0(A_127))
      | ~ l1_orders_2(A_127)
      | ~ v2_lattice3(A_127)
      | ~ v5_orders_2(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_70,plain,(
    ! [B_128] :
      ( k12_lattice3('#skF_3',B_128,'#skF_4') = k11_lattice3('#skF_3',B_128,'#skF_4')
      | ~ m1_subset_1(B_128,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_62])).

tff(c_165,plain,(
    ! [B_134] :
      ( k12_lattice3('#skF_3',B_134,'#skF_4') = k11_lattice3('#skF_3',B_134,'#skF_4')
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_70])).

tff(c_194,plain,(
    k12_lattice3('#skF_3','#skF_5','#skF_4') = k11_lattice3('#skF_3','#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_165])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k12_lattice3(A_5,B_6,C_7),u1_struct_0(A_5))
      | ~ m1_subset_1(C_7,u1_struct_0(A_5))
      | ~ m1_subset_1(B_6,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5)
      | ~ v2_lattice3(A_5)
      | ~ v5_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_199,plain,
    ( m1_subset_1(k11_lattice3('#skF_3','#skF_5','#skF_4'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_6])).

tff(c_203,plain,(
    m1_subset_1(k11_lattice3('#skF_3','#skF_5','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_46,c_48,c_199])).

tff(c_58,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_552,plain,(
    ! [A_141,B_142,C_143] :
      ( k13_lattice3(A_141,k12_lattice3(A_141,B_142,C_143),C_143) = C_143
      | ~ m1_subset_1(C_143,u1_struct_0(A_141))
      | ~ m1_subset_1(B_142,u1_struct_0(A_141))
      | ~ l1_orders_2(A_141)
      | ~ v2_lattice3(A_141)
      | ~ v1_lattice3(A_141)
      | ~ v5_orders_2(A_141)
      | ~ v3_orders_2(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_572,plain,(
    ! [B_142] :
      ( k13_lattice3('#skF_3',k12_lattice3('#skF_3',B_142,'#skF_4'),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(B_142,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_552])).

tff(c_704,plain,(
    ! [B_145] :
      ( k13_lattice3('#skF_3',k12_lattice3('#skF_3',B_145,'#skF_4'),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_50,c_572])).

tff(c_736,plain,(
    k13_lattice3('#skF_3',k12_lattice3('#skF_3','#skF_5','#skF_4'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_704])).

tff(c_754,plain,(
    k13_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_5','#skF_4'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_736])).

tff(c_635,plain,(
    k13_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_5','#skF_4'),'#skF_4') = k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_5','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_203,c_599])).

tff(c_2126,plain,(
    k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_5','#skF_4'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_754,c_635])).

tff(c_20,plain,(
    ! [A_11,C_47,B_35] :
      ( r1_orders_2(A_11,C_47,k10_lattice3(A_11,B_35,C_47))
      | ~ m1_subset_1(k10_lattice3(A_11,B_35,C_47),u1_struct_0(A_11))
      | ~ m1_subset_1(C_47,u1_struct_0(A_11))
      | ~ m1_subset_1(B_35,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11)
      | ~ v1_lattice3(A_11)
      | ~ v5_orders_2(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2131,plain,
    ( r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_5','#skF_4'),'#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k11_lattice3('#skF_3','#skF_5','#skF_4'),u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2126,c_20])).

tff(c_2138,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_203,c_48,c_48,c_2126,c_2131])).

tff(c_2139,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_813,c_2138])).

tff(c_812,plain,(
    r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_797])).

tff(c_1904,plain,(
    ! [A_175,B_176,C_177,D_178] :
      ( r1_orders_2(A_175,'#skF_2'(A_175,B_176,C_177,D_178),B_176)
      | k11_lattice3(A_175,B_176,C_177) = D_178
      | ~ r1_orders_2(A_175,D_178,C_177)
      | ~ r1_orders_2(A_175,D_178,B_176)
      | ~ m1_subset_1(D_178,u1_struct_0(A_175))
      | ~ m1_subset_1(C_177,u1_struct_0(A_175))
      | ~ m1_subset_1(B_176,u1_struct_0(A_175))
      | ~ l1_orders_2(A_175)
      | ~ v2_lattice3(A_175)
      | ~ v5_orders_2(A_175)
      | v2_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_24,plain,(
    ! [A_57,B_81,C_93,D_99] :
      ( ~ r1_orders_2(A_57,'#skF_2'(A_57,B_81,C_93,D_99),D_99)
      | k11_lattice3(A_57,B_81,C_93) = D_99
      | ~ r1_orders_2(A_57,D_99,C_93)
      | ~ r1_orders_2(A_57,D_99,B_81)
      | ~ m1_subset_1(D_99,u1_struct_0(A_57))
      | ~ m1_subset_1(C_93,u1_struct_0(A_57))
      | ~ m1_subset_1(B_81,u1_struct_0(A_57))
      | ~ l1_orders_2(A_57)
      | ~ v2_lattice3(A_57)
      | ~ v5_orders_2(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3938,plain,(
    ! [A_209,B_210,C_211] :
      ( k11_lattice3(A_209,B_210,C_211) = B_210
      | ~ r1_orders_2(A_209,B_210,C_211)
      | ~ r1_orders_2(A_209,B_210,B_210)
      | ~ m1_subset_1(C_211,u1_struct_0(A_209))
      | ~ m1_subset_1(B_210,u1_struct_0(A_209))
      | ~ l1_orders_2(A_209)
      | ~ v2_lattice3(A_209)
      | ~ v5_orders_2(A_209)
      | v2_struct_0(A_209) ) ),
    inference(resolution,[status(thm)],[c_1904,c_24])).

tff(c_4012,plain,
    ( k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4'
    | ~ r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_812,c_3938])).

tff(c_4147,plain,
    ( k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_48,c_495,c_2139,c_4012])).

tff(c_4148,plain,(
    k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_813,c_4147])).

tff(c_5771,plain,(
    ! [A_242,B_243,B_244,C_245] :
      ( k12_lattice3(A_242,B_243,k13_lattice3(A_242,B_244,C_245)) = k11_lattice3(A_242,B_243,k13_lattice3(A_242,B_244,C_245))
      | ~ m1_subset_1(B_243,u1_struct_0(A_242))
      | ~ v2_lattice3(A_242)
      | ~ m1_subset_1(C_245,u1_struct_0(A_242))
      | ~ m1_subset_1(B_244,u1_struct_0(A_242))
      | ~ l1_orders_2(A_242)
      | ~ v1_lattice3(A_242)
      | ~ v5_orders_2(A_242) ) ),
    inference(resolution,[status(thm)],[c_8,c_62])).

tff(c_5799,plain,(
    ! [B_244,C_245] :
      ( k12_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3',B_244,C_245)) = k11_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3',B_244,C_245))
      | ~ v2_lattice3('#skF_3')
      | ~ m1_subset_1(C_245,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_244,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_5771])).

tff(c_7882,plain,(
    ! [B_288,C_289] :
      ( k12_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3',B_288,C_289)) = k11_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3',B_288,C_289))
      | ~ m1_subset_1(C_289,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_288,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_52,c_5799])).

tff(c_8047,plain,(
    ! [B_295] :
      ( k12_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3',B_295,'#skF_4')) = k11_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3',B_295,'#skF_4'))
      | ~ m1_subset_1(B_295,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_48,c_7882])).

tff(c_8093,plain,(
    k12_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3','#skF_5','#skF_4')) = k11_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3','#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_8047])).

tff(c_8126,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4148,c_496,c_496,c_8093])).

tff(c_8128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_497,c_8126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:24:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.97/3.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.11/3.01  
% 9.11/3.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.11/3.01  %$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 9.11/3.01  
% 9.11/3.01  %Foreground sorts:
% 9.11/3.01  
% 9.11/3.01  
% 9.11/3.01  %Background operators:
% 9.11/3.01  
% 9.11/3.01  
% 9.11/3.01  %Foreground operators:
% 9.11/3.01  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.11/3.01  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 9.11/3.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.11/3.01  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 9.11/3.01  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 9.11/3.01  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 9.11/3.01  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 9.11/3.01  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 9.11/3.01  tff('#skF_5', type, '#skF_5': $i).
% 9.11/3.01  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 9.11/3.01  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.11/3.01  tff('#skF_3', type, '#skF_3': $i).
% 9.11/3.01  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 9.11/3.01  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 9.11/3.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.11/3.01  tff('#skF_4', type, '#skF_4': $i).
% 9.11/3.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.11/3.01  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 9.11/3.01  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 9.11/3.01  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.11/3.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.11/3.01  
% 9.11/3.03  tff(f_195, negated_conjecture, ~(![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k12_lattice3(A, B, k13_lattice3(A, B, C)) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_lattice3)).
% 9.11/3.03  tff(f_158, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 9.11/3.03  tff(f_44, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k13_lattice3(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k13_lattice3)).
% 9.11/3.03  tff(f_68, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k13_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k13_lattice3)).
% 9.11/3.03  tff(f_101, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l26_lattice3)).
% 9.11/3.03  tff(f_32, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 9.11/3.03  tff(f_146, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 9.11/3.03  tff(f_56, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k12_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k12_lattice3)).
% 9.11/3.03  tff(f_176, axiom, (![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k13_lattice3(A, k12_lattice3(A, B, C), C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_lattice3)).
% 9.11/3.03  tff(f_134, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 9.11/3.03  tff(c_48, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 9.11/3.03  tff(c_56, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 9.11/3.03  tff(c_54, plain, (v1_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 9.11/3.03  tff(c_50, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 9.11/3.03  tff(c_46, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 9.11/3.03  tff(c_299, plain, (![A_136, B_137, C_138]: (k13_lattice3(A_136, B_137, C_138)=k10_lattice3(A_136, B_137, C_138) | ~m1_subset_1(C_138, u1_struct_0(A_136)) | ~m1_subset_1(B_137, u1_struct_0(A_136)) | ~l1_orders_2(A_136) | ~v1_lattice3(A_136) | ~v5_orders_2(A_136))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.11/3.03  tff(c_313, plain, (![B_137]: (k13_lattice3('#skF_3', B_137, '#skF_5')=k10_lattice3('#skF_3', B_137, '#skF_5') | ~m1_subset_1(B_137, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_299])).
% 9.11/3.03  tff(c_408, plain, (![B_140]: (k13_lattice3('#skF_3', B_140, '#skF_5')=k10_lattice3('#skF_3', B_140, '#skF_5') | ~m1_subset_1(B_140, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_313])).
% 9.11/3.03  tff(c_450, plain, (k13_lattice3('#skF_3', '#skF_4', '#skF_5')=k10_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_408])).
% 9.11/3.03  tff(c_44, plain, (k12_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_195])).
% 9.11/3.03  tff(c_497, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_450, c_44])).
% 9.11/3.03  tff(c_120, plain, (![A_131, C_132, B_133]: (k13_lattice3(A_131, C_132, B_133)=k13_lattice3(A_131, B_133, C_132) | ~m1_subset_1(C_132, u1_struct_0(A_131)) | ~m1_subset_1(B_133, u1_struct_0(A_131)) | ~l1_orders_2(A_131) | ~v1_lattice3(A_131) | ~v5_orders_2(A_131))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.11/3.03  tff(c_130, plain, (![B_133]: (k13_lattice3('#skF_3', B_133, '#skF_4')=k13_lattice3('#skF_3', '#skF_4', B_133) | ~m1_subset_1(B_133, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_120])).
% 9.11/3.03  tff(c_250, plain, (![B_135]: (k13_lattice3('#skF_3', B_135, '#skF_4')=k13_lattice3('#skF_3', '#skF_4', B_135) | ~m1_subset_1(B_135, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_130])).
% 9.11/3.03  tff(c_287, plain, (k13_lattice3('#skF_3', '#skF_5', '#skF_4')=k13_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_250])).
% 9.11/3.03  tff(c_8, plain, (![A_8, B_9, C_10]: (m1_subset_1(k13_lattice3(A_8, B_9, C_10), u1_struct_0(A_8)) | ~m1_subset_1(C_10, u1_struct_0(A_8)) | ~m1_subset_1(B_9, u1_struct_0(A_8)) | ~l1_orders_2(A_8) | ~v1_lattice3(A_8) | ~v5_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.11/3.03  tff(c_293, plain, (m1_subset_1(k13_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_287, c_8])).
% 9.11/3.03  tff(c_297, plain, (m1_subset_1(k13_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_46, c_48, c_293])).
% 9.11/3.03  tff(c_495, plain, (m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_450, c_297])).
% 9.11/3.03  tff(c_496, plain, (k13_lattice3('#skF_3', '#skF_5', '#skF_4')=k10_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_450, c_287])).
% 9.11/3.03  tff(c_315, plain, (![B_137]: (k13_lattice3('#skF_3', B_137, '#skF_4')=k10_lattice3('#skF_3', B_137, '#skF_4') | ~m1_subset_1(B_137, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_299])).
% 9.11/3.03  tff(c_599, plain, (![B_144]: (k13_lattice3('#skF_3', B_144, '#skF_4')=k10_lattice3('#skF_3', B_144, '#skF_4') | ~m1_subset_1(B_144, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_315])).
% 9.11/3.03  tff(c_628, plain, (k13_lattice3('#skF_3', '#skF_5', '#skF_4')=k10_lattice3('#skF_3', '#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_599])).
% 9.11/3.03  tff(c_645, plain, (k10_lattice3('#skF_3', '#skF_5', '#skF_4')=k10_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_496, c_628])).
% 9.11/3.03  tff(c_784, plain, (![A_146, C_147, B_148]: (r1_orders_2(A_146, C_147, k10_lattice3(A_146, B_148, C_147)) | ~m1_subset_1(k10_lattice3(A_146, B_148, C_147), u1_struct_0(A_146)) | ~m1_subset_1(C_147, u1_struct_0(A_146)) | ~m1_subset_1(B_148, u1_struct_0(A_146)) | ~l1_orders_2(A_146) | ~v1_lattice3(A_146) | ~v5_orders_2(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.11/3.03  tff(c_788, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_5', '#skF_4')) | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_645, c_784])).
% 9.11/3.03  tff(c_797, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_46, c_48, c_495, c_645, c_788])).
% 9.11/3.03  tff(c_804, plain, (v2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_797])).
% 9.11/3.03  tff(c_2, plain, (![A_1]: (~v2_struct_0(A_1) | ~v1_lattice3(A_1) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.11/3.03  tff(c_807, plain, (~v1_lattice3('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_804, c_2])).
% 9.11/3.03  tff(c_811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_807])).
% 9.11/3.03  tff(c_813, plain, (~v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_797])).
% 9.11/3.03  tff(c_52, plain, (v2_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 9.11/3.03  tff(c_62, plain, (![A_127, B_128, C_129]: (k12_lattice3(A_127, B_128, C_129)=k11_lattice3(A_127, B_128, C_129) | ~m1_subset_1(C_129, u1_struct_0(A_127)) | ~m1_subset_1(B_128, u1_struct_0(A_127)) | ~l1_orders_2(A_127) | ~v2_lattice3(A_127) | ~v5_orders_2(A_127))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.11/3.03  tff(c_70, plain, (![B_128]: (k12_lattice3('#skF_3', B_128, '#skF_4')=k11_lattice3('#skF_3', B_128, '#skF_4') | ~m1_subset_1(B_128, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_62])).
% 9.11/3.03  tff(c_165, plain, (![B_134]: (k12_lattice3('#skF_3', B_134, '#skF_4')=k11_lattice3('#skF_3', B_134, '#skF_4') | ~m1_subset_1(B_134, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_70])).
% 9.11/3.03  tff(c_194, plain, (k12_lattice3('#skF_3', '#skF_5', '#skF_4')=k11_lattice3('#skF_3', '#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_165])).
% 9.11/3.03  tff(c_6, plain, (![A_5, B_6, C_7]: (m1_subset_1(k12_lattice3(A_5, B_6, C_7), u1_struct_0(A_5)) | ~m1_subset_1(C_7, u1_struct_0(A_5)) | ~m1_subset_1(B_6, u1_struct_0(A_5)) | ~l1_orders_2(A_5) | ~v2_lattice3(A_5) | ~v5_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.11/3.03  tff(c_199, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_194, c_6])).
% 9.11/3.03  tff(c_203, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_5', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_46, c_48, c_199])).
% 9.11/3.03  tff(c_58, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 9.11/3.03  tff(c_552, plain, (![A_141, B_142, C_143]: (k13_lattice3(A_141, k12_lattice3(A_141, B_142, C_143), C_143)=C_143 | ~m1_subset_1(C_143, u1_struct_0(A_141)) | ~m1_subset_1(B_142, u1_struct_0(A_141)) | ~l1_orders_2(A_141) | ~v2_lattice3(A_141) | ~v1_lattice3(A_141) | ~v5_orders_2(A_141) | ~v3_orders_2(A_141))), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.11/3.03  tff(c_572, plain, (![B_142]: (k13_lattice3('#skF_3', k12_lattice3('#skF_3', B_142, '#skF_4'), '#skF_4')='#skF_4' | ~m1_subset_1(B_142, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | ~v3_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_552])).
% 9.11/3.03  tff(c_704, plain, (![B_145]: (k13_lattice3('#skF_3', k12_lattice3('#skF_3', B_145, '#skF_4'), '#skF_4')='#skF_4' | ~m1_subset_1(B_145, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_50, c_572])).
% 9.11/3.03  tff(c_736, plain, (k13_lattice3('#skF_3', k12_lattice3('#skF_3', '#skF_5', '#skF_4'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_46, c_704])).
% 9.11/3.03  tff(c_754, plain, (k13_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_5', '#skF_4'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_194, c_736])).
% 9.11/3.03  tff(c_635, plain, (k13_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_5', '#skF_4'), '#skF_4')=k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_5', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_203, c_599])).
% 9.11/3.03  tff(c_2126, plain, (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_5', '#skF_4'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_754, c_635])).
% 9.11/3.03  tff(c_20, plain, (![A_11, C_47, B_35]: (r1_orders_2(A_11, C_47, k10_lattice3(A_11, B_35, C_47)) | ~m1_subset_1(k10_lattice3(A_11, B_35, C_47), u1_struct_0(A_11)) | ~m1_subset_1(C_47, u1_struct_0(A_11)) | ~m1_subset_1(B_35, u1_struct_0(A_11)) | ~l1_orders_2(A_11) | ~v1_lattice3(A_11) | ~v5_orders_2(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.11/3.03  tff(c_2131, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_5', '#skF_4'), '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(k11_lattice3('#skF_3', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2126, c_20])).
% 9.11/3.03  tff(c_2138, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_203, c_48, c_48, c_2126, c_2131])).
% 9.11/3.03  tff(c_2139, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_813, c_2138])).
% 9.11/3.03  tff(c_812, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_797])).
% 9.11/3.03  tff(c_1904, plain, (![A_175, B_176, C_177, D_178]: (r1_orders_2(A_175, '#skF_2'(A_175, B_176, C_177, D_178), B_176) | k11_lattice3(A_175, B_176, C_177)=D_178 | ~r1_orders_2(A_175, D_178, C_177) | ~r1_orders_2(A_175, D_178, B_176) | ~m1_subset_1(D_178, u1_struct_0(A_175)) | ~m1_subset_1(C_177, u1_struct_0(A_175)) | ~m1_subset_1(B_176, u1_struct_0(A_175)) | ~l1_orders_2(A_175) | ~v2_lattice3(A_175) | ~v5_orders_2(A_175) | v2_struct_0(A_175))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.11/3.03  tff(c_24, plain, (![A_57, B_81, C_93, D_99]: (~r1_orders_2(A_57, '#skF_2'(A_57, B_81, C_93, D_99), D_99) | k11_lattice3(A_57, B_81, C_93)=D_99 | ~r1_orders_2(A_57, D_99, C_93) | ~r1_orders_2(A_57, D_99, B_81) | ~m1_subset_1(D_99, u1_struct_0(A_57)) | ~m1_subset_1(C_93, u1_struct_0(A_57)) | ~m1_subset_1(B_81, u1_struct_0(A_57)) | ~l1_orders_2(A_57) | ~v2_lattice3(A_57) | ~v5_orders_2(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.11/3.03  tff(c_3938, plain, (![A_209, B_210, C_211]: (k11_lattice3(A_209, B_210, C_211)=B_210 | ~r1_orders_2(A_209, B_210, C_211) | ~r1_orders_2(A_209, B_210, B_210) | ~m1_subset_1(C_211, u1_struct_0(A_209)) | ~m1_subset_1(B_210, u1_struct_0(A_209)) | ~l1_orders_2(A_209) | ~v2_lattice3(A_209) | ~v5_orders_2(A_209) | v2_struct_0(A_209))), inference(resolution, [status(thm)], [c_1904, c_24])).
% 9.11/3.03  tff(c_4012, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_812, c_3938])).
% 9.11/3.03  tff(c_4147, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_48, c_495, c_2139, c_4012])).
% 9.11/3.03  tff(c_4148, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_813, c_4147])).
% 9.11/3.03  tff(c_5771, plain, (![A_242, B_243, B_244, C_245]: (k12_lattice3(A_242, B_243, k13_lattice3(A_242, B_244, C_245))=k11_lattice3(A_242, B_243, k13_lattice3(A_242, B_244, C_245)) | ~m1_subset_1(B_243, u1_struct_0(A_242)) | ~v2_lattice3(A_242) | ~m1_subset_1(C_245, u1_struct_0(A_242)) | ~m1_subset_1(B_244, u1_struct_0(A_242)) | ~l1_orders_2(A_242) | ~v1_lattice3(A_242) | ~v5_orders_2(A_242))), inference(resolution, [status(thm)], [c_8, c_62])).
% 9.11/3.03  tff(c_5799, plain, (![B_244, C_245]: (k12_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', B_244, C_245))=k11_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', B_244, C_245)) | ~v2_lattice3('#skF_3') | ~m1_subset_1(C_245, u1_struct_0('#skF_3')) | ~m1_subset_1(B_244, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_5771])).
% 9.11/3.03  tff(c_7882, plain, (![B_288, C_289]: (k12_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', B_288, C_289))=k11_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', B_288, C_289)) | ~m1_subset_1(C_289, u1_struct_0('#skF_3')) | ~m1_subset_1(B_288, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_52, c_5799])).
% 9.11/3.03  tff(c_8047, plain, (![B_295]: (k12_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', B_295, '#skF_4'))=k11_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', B_295, '#skF_4')) | ~m1_subset_1(B_295, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_48, c_7882])).
% 9.11/3.03  tff(c_8093, plain, (k12_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', '#skF_5', '#skF_4'))=k11_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', '#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_8047])).
% 9.11/3.03  tff(c_8126, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4148, c_496, c_496, c_8093])).
% 9.11/3.03  tff(c_8128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_497, c_8126])).
% 9.11/3.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.11/3.03  
% 9.11/3.03  Inference rules
% 9.11/3.03  ----------------------
% 9.11/3.03  #Ref     : 0
% 9.11/3.03  #Sup     : 1744
% 9.11/3.03  #Fact    : 0
% 9.11/3.03  #Define  : 0
% 9.11/3.03  #Split   : 3
% 9.11/3.03  #Chain   : 0
% 9.11/3.03  #Close   : 0
% 9.11/3.03  
% 9.11/3.03  Ordering : KBO
% 9.11/3.03  
% 9.11/3.03  Simplification rules
% 9.11/3.03  ----------------------
% 9.11/3.03  #Subsume      : 74
% 9.11/3.03  #Demod        : 5110
% 9.11/3.03  #Tautology    : 659
% 9.11/3.03  #SimpNegUnit  : 409
% 9.11/3.03  #BackRed      : 115
% 9.11/3.03  
% 9.11/3.03  #Partial instantiations: 0
% 9.11/3.03  #Strategies tried      : 1
% 9.11/3.03  
% 9.11/3.03  Timing (in seconds)
% 9.11/3.03  ----------------------
% 9.11/3.03  Preprocessing        : 0.36
% 9.11/3.03  Parsing              : 0.19
% 9.11/3.03  CNF conversion       : 0.03
% 9.11/3.03  Main loop            : 1.91
% 9.11/3.03  Inferencing          : 0.46
% 9.11/3.03  Reduction            : 0.86
% 9.11/3.03  Demodulation         : 0.68
% 9.11/3.03  BG Simplification    : 0.08
% 9.11/3.03  Subsumption          : 0.40
% 9.11/3.03  Abstraction          : 0.12
% 9.11/3.03  MUC search           : 0.00
% 9.11/3.03  Cooper               : 0.00
% 9.11/3.03  Total                : 2.31
% 9.11/3.03  Index Insertion      : 0.00
% 9.11/3.03  Index Deletion       : 0.00
% 9.11/3.03  Index Matching       : 0.00
% 9.11/3.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
