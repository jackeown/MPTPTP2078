%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:41 EST 2020

% Result     : Theorem 9.13s
% Output     : CNFRefutation 9.42s
% Verified   : 
% Statistics : Number of formulae       :  119 (1549 expanded)
%              Number of leaves         :   31 ( 622 expanded)
%              Depth                    :   21
%              Number of atoms          :  369 (6730 expanded)
%              Number of equality atoms :   58 ( 888 expanded)
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

tff(f_212,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_lattice3)).

tff(f_175,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k11_lattice3(A,B,C) = k11_lattice3(A,C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

tff(f_161,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_149,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_193,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattice3)).

tff(f_104,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k10_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_lattice3)).

tff(f_137,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

tff(c_54,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_56,plain,(
    v2_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_60,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_58,plain,(
    v1_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_68,plain,(
    ! [A_143,C_144,B_145] :
      ( k11_lattice3(A_143,C_144,B_145) = k11_lattice3(A_143,B_145,C_144)
      | ~ m1_subset_1(C_144,u1_struct_0(A_143))
      | ~ m1_subset_1(B_145,u1_struct_0(A_143))
      | ~ l1_orders_2(A_143)
      | ~ v2_lattice3(A_143)
      | ~ v5_orders_2(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_74,plain,(
    ! [B_145] :
      ( k11_lattice3('#skF_3',B_145,'#skF_5') = k11_lattice3('#skF_3','#skF_5',B_145)
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_68])).

tff(c_85,plain,(
    ! [B_146] :
      ( k11_lattice3('#skF_3',B_146,'#skF_5') = k11_lattice3('#skF_3','#skF_5',B_146)
      | ~ m1_subset_1(B_146,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_74])).

tff(c_108,plain,(
    k11_lattice3('#skF_3','#skF_5','#skF_4') = k11_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_85])).

tff(c_10,plain,(
    ! [A_13,B_14,C_15] :
      ( m1_subset_1(k11_lattice3(A_13,B_14,C_15),u1_struct_0(A_13))
      | ~ m1_subset_1(C_15,u1_struct_0(A_13))
      | ~ m1_subset_1(B_14,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_129,plain,
    ( m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_10])).

tff(c_133,plain,(
    m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_52,c_129])).

tff(c_249,plain,(
    ! [A_153,B_154,C_155] :
      ( k13_lattice3(A_153,B_154,C_155) = k10_lattice3(A_153,B_154,C_155)
      | ~ m1_subset_1(C_155,u1_struct_0(A_153))
      | ~ m1_subset_1(B_154,u1_struct_0(A_153))
      | ~ l1_orders_2(A_153)
      | ~ v1_lattice3(A_153)
      | ~ v5_orders_2(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_257,plain,(
    ! [B_154] :
      ( k13_lattice3('#skF_3',B_154,'#skF_5') = k10_lattice3('#skF_3',B_154,'#skF_5')
      | ~ m1_subset_1(B_154,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_249])).

tff(c_271,plain,(
    ! [B_156] :
      ( k13_lattice3('#skF_3',B_156,'#skF_5') = k10_lattice3('#skF_3',B_156,'#skF_5')
      | ~ m1_subset_1(B_156,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_257])).

tff(c_289,plain,(
    k13_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') = k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_133,c_271])).

tff(c_109,plain,(
    ! [A_147,B_148,C_149] :
      ( k12_lattice3(A_147,B_148,C_149) = k11_lattice3(A_147,B_148,C_149)
      | ~ m1_subset_1(C_149,u1_struct_0(A_147))
      | ~ m1_subset_1(B_148,u1_struct_0(A_147))
      | ~ l1_orders_2(A_147)
      | ~ v2_lattice3(A_147)
      | ~ v5_orders_2(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_115,plain,(
    ! [B_148] :
      ( k12_lattice3('#skF_3',B_148,'#skF_5') = k11_lattice3('#skF_3',B_148,'#skF_5')
      | ~ m1_subset_1(B_148,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_109])).

tff(c_178,plain,(
    ! [B_151] :
      ( k12_lattice3('#skF_3',B_151,'#skF_5') = k11_lattice3('#skF_3',B_151,'#skF_5')
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_115])).

tff(c_204,plain,(
    k12_lattice3('#skF_3','#skF_4','#skF_5') = k11_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_178])).

tff(c_62,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_350,plain,(
    ! [A_158,B_159,C_160] :
      ( k13_lattice3(A_158,k12_lattice3(A_158,B_159,C_160),C_160) = C_160
      | ~ m1_subset_1(C_160,u1_struct_0(A_158))
      | ~ m1_subset_1(B_159,u1_struct_0(A_158))
      | ~ l1_orders_2(A_158)
      | ~ v2_lattice3(A_158)
      | ~ v1_lattice3(A_158)
      | ~ v5_orders_2(A_158)
      | ~ v3_orders_2(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_358,plain,(
    ! [B_159] :
      ( k13_lattice3('#skF_3',k12_lattice3('#skF_3',B_159,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_159,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_350])).

tff(c_372,plain,(
    ! [B_161] :
      ( k13_lattice3('#skF_3',k12_lattice3('#skF_3',B_161,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_161,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_358])).

tff(c_389,plain,(
    k13_lattice3('#skF_3',k12_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_52,c_372])).

tff(c_400,plain,(
    k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_204,c_389])).

tff(c_465,plain,(
    ! [A_163,B_164,C_165] :
      ( r1_orders_2(A_163,B_164,k10_lattice3(A_163,B_164,C_165))
      | ~ m1_subset_1(k10_lattice3(A_163,B_164,C_165),u1_struct_0(A_163))
      | ~ m1_subset_1(C_165,u1_struct_0(A_163))
      | ~ m1_subset_1(B_164,u1_struct_0(A_163))
      | ~ l1_orders_2(A_163)
      | ~ v1_lattice3(A_163)
      | ~ v5_orders_2(A_163)
      | v2_struct_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_467,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_465])).

tff(c_471,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_133,c_50,c_50,c_400,c_467])).

tff(c_473,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_471])).

tff(c_6,plain,(
    ! [A_9] :
      ( ~ v2_struct_0(A_9)
      | ~ v2_lattice3(A_9)
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_476,plain,
    ( ~ v2_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_473,c_6])).

tff(c_483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_476])).

tff(c_485,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_8,plain,(
    ! [A_10,B_11,C_12] :
      ( m1_subset_1(k10_lattice3(A_10,B_11,C_12),u1_struct_0(A_10))
      | ~ m1_subset_1(C_12,u1_struct_0(A_10))
      | ~ m1_subset_1(B_11,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_472,plain,(
    ! [A_10,B_11,C_12] :
      ( r1_orders_2(A_10,B_11,k10_lattice3(A_10,B_11,C_12))
      | ~ v1_lattice3(A_10)
      | ~ v5_orders_2(A_10)
      | v2_struct_0(A_10)
      | ~ m1_subset_1(C_12,u1_struct_0(A_10))
      | ~ m1_subset_1(B_11,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(resolution,[status(thm)],[c_8,c_465])).

tff(c_5706,plain,(
    ! [A_280,B_281,B_282,C_283] :
      ( k12_lattice3(A_280,B_281,k10_lattice3(A_280,B_282,C_283)) = k11_lattice3(A_280,B_281,k10_lattice3(A_280,B_282,C_283))
      | ~ m1_subset_1(B_281,u1_struct_0(A_280))
      | ~ v2_lattice3(A_280)
      | ~ v5_orders_2(A_280)
      | ~ m1_subset_1(C_283,u1_struct_0(A_280))
      | ~ m1_subset_1(B_282,u1_struct_0(A_280))
      | ~ l1_orders_2(A_280) ) ),
    inference(resolution,[status(thm)],[c_8,c_109])).

tff(c_5734,plain,(
    ! [B_282,C_283] :
      ( k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_282,C_283)) = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_282,C_283))
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ m1_subset_1(C_283,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_282,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_5706])).

tff(c_6722,plain,(
    ! [B_309,C_310] :
      ( k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_309,C_310)) = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_309,C_310))
      | ~ m1_subset_1(C_310,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_309,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_60,c_56,c_5734])).

tff(c_6779,plain,(
    ! [B_311] :
      ( k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_311,'#skF_5')) = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_311,'#skF_5'))
      | ~ m1_subset_1(B_311,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_50,c_6722])).

tff(c_6855,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_6779])).

tff(c_297,plain,(
    k13_lattice3('#skF_3','#skF_4','#skF_5') = k10_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_271])).

tff(c_48,plain,(
    k12_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_302,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_48])).

tff(c_6856,plain,(
    k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6855,c_302])).

tff(c_6941,plain,(
    ! [A_313,B_314,C_315,B_316] :
      ( k11_lattice3(A_313,k10_lattice3(A_313,B_314,C_315),B_316) = k11_lattice3(A_313,B_316,k10_lattice3(A_313,B_314,C_315))
      | ~ m1_subset_1(B_316,u1_struct_0(A_313))
      | ~ v2_lattice3(A_313)
      | ~ v5_orders_2(A_313)
      | ~ m1_subset_1(C_315,u1_struct_0(A_313))
      | ~ m1_subset_1(B_314,u1_struct_0(A_313))
      | ~ l1_orders_2(A_313) ) ),
    inference(resolution,[status(thm)],[c_8,c_68])).

tff(c_6969,plain,(
    ! [B_314,C_315] :
      ( k11_lattice3('#skF_3',k10_lattice3('#skF_3',B_314,C_315),'#skF_4') = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_314,C_315))
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ m1_subset_1(C_315,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_314,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_6941])).

tff(c_7340,plain,(
    ! [B_325,C_326] :
      ( k11_lattice3('#skF_3',k10_lattice3('#skF_3',B_325,C_326),'#skF_4') = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_325,C_326))
      | ~ m1_subset_1(C_326,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_325,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_60,c_56,c_6969])).

tff(c_7397,plain,(
    ! [B_327] :
      ( k11_lattice3('#skF_3',k10_lattice3('#skF_3',B_327,'#skF_5'),'#skF_4') = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_327,'#skF_5'))
      | ~ m1_subset_1(B_327,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_50,c_7340])).

tff(c_7473,plain,(
    k11_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_7397])).

tff(c_750,plain,(
    ! [A_172,B_173,C_174] :
      ( r1_orders_2(A_172,k11_lattice3(A_172,B_173,C_174),C_174)
      | ~ m1_subset_1(k11_lattice3(A_172,B_173,C_174),u1_struct_0(A_172))
      | ~ m1_subset_1(C_174,u1_struct_0(A_172))
      | ~ m1_subset_1(B_173,u1_struct_0(A_172))
      | ~ l1_orders_2(A_172)
      | ~ v2_lattice3(A_172)
      | ~ v5_orders_2(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_786,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_orders_2(A_13,k11_lattice3(A_13,B_14,C_15),C_15)
      | ~ v2_lattice3(A_13)
      | ~ v5_orders_2(A_13)
      | v2_struct_0(A_13)
      | ~ m1_subset_1(C_15,u1_struct_0(A_13))
      | ~ m1_subset_1(B_14,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(resolution,[status(thm)],[c_10,c_750])).

tff(c_7483,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7473,c_786])).

tff(c_7502,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | v2_struct_0('#skF_3')
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_60,c_56,c_7483])).

tff(c_7503,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_485,c_7502])).

tff(c_7511,plain,(
    ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7503])).

tff(c_7514,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_7511])).

tff(c_7518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_7514])).

tff(c_7520,plain,(
    m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7503])).

tff(c_117,plain,(
    ! [B_148] :
      ( k12_lattice3('#skF_3',B_148,'#skF_4') = k11_lattice3('#skF_3',B_148,'#skF_4')
      | ~ m1_subset_1(B_148,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_109])).

tff(c_213,plain,(
    ! [B_152] :
      ( k12_lattice3('#skF_3',B_152,'#skF_4') = k11_lattice3('#skF_3',B_152,'#skF_4')
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_117])).

tff(c_227,plain,(
    k12_lattice3('#skF_3','#skF_5','#skF_4') = k11_lattice3('#skF_3','#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_213])).

tff(c_239,plain,(
    k12_lattice3('#skF_3','#skF_5','#skF_4') = k11_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_227])).

tff(c_360,plain,(
    ! [B_159] :
      ( k13_lattice3('#skF_3',k12_lattice3('#skF_3',B_159,'#skF_4'),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(B_159,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_350])).

tff(c_415,plain,(
    ! [B_162] :
      ( k13_lattice3('#skF_3',k12_lattice3('#skF_3',B_162,'#skF_4'),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(B_162,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_360])).

tff(c_429,plain,(
    k13_lattice3('#skF_3',k12_lattice3('#skF_3','#skF_5','#skF_4'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_415])).

tff(c_442,plain,(
    k13_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_429])).

tff(c_259,plain,(
    ! [B_154] :
      ( k13_lattice3('#skF_3',B_154,'#skF_4') = k10_lattice3('#skF_3',B_154,'#skF_4')
      | ~ m1_subset_1(B_154,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_249])).

tff(c_307,plain,(
    ! [B_157] :
      ( k13_lattice3('#skF_3',B_157,'#skF_4') = k10_lattice3('#skF_3',B_157,'#skF_4')
      | ~ m1_subset_1(B_157,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_259])).

tff(c_325,plain,(
    k13_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_307])).

tff(c_553,plain,(
    k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_325])).

tff(c_568,plain,(
    ! [A_166,C_167,B_168] :
      ( r1_orders_2(A_166,C_167,k10_lattice3(A_166,B_168,C_167))
      | ~ m1_subset_1(k10_lattice3(A_166,B_168,C_167),u1_struct_0(A_166))
      | ~ m1_subset_1(C_167,u1_struct_0(A_166))
      | ~ m1_subset_1(B_168,u1_struct_0(A_166))
      | ~ l1_orders_2(A_166)
      | ~ v1_lattice3(A_166)
      | ~ v5_orders_2(A_166)
      | v2_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_570,plain,
    ( r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_568])).

tff(c_576,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_133,c_52,c_52,c_553,c_570])).

tff(c_577,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_485,c_576])).

tff(c_2017,plain,(
    ! [A_210,B_211,C_212,D_213] :
      ( r1_orders_2(A_210,'#skF_2'(A_210,B_211,C_212,D_213),C_212)
      | k11_lattice3(A_210,B_211,C_212) = D_213
      | ~ r1_orders_2(A_210,D_213,C_212)
      | ~ r1_orders_2(A_210,D_213,B_211)
      | ~ m1_subset_1(D_213,u1_struct_0(A_210))
      | ~ m1_subset_1(C_212,u1_struct_0(A_210))
      | ~ m1_subset_1(B_211,u1_struct_0(A_210))
      | ~ l1_orders_2(A_210)
      | ~ v2_lattice3(A_210)
      | ~ v5_orders_2(A_210)
      | v2_struct_0(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_26,plain,(
    ! [A_62,B_86,C_98,D_104] :
      ( ~ r1_orders_2(A_62,'#skF_2'(A_62,B_86,C_98,D_104),D_104)
      | k11_lattice3(A_62,B_86,C_98) = D_104
      | ~ r1_orders_2(A_62,D_104,C_98)
      | ~ r1_orders_2(A_62,D_104,B_86)
      | ~ m1_subset_1(D_104,u1_struct_0(A_62))
      | ~ m1_subset_1(C_98,u1_struct_0(A_62))
      | ~ m1_subset_1(B_86,u1_struct_0(A_62))
      | ~ l1_orders_2(A_62)
      | ~ v2_lattice3(A_62)
      | ~ v5_orders_2(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_4232,plain,(
    ! [A_255,B_256,C_257] :
      ( k11_lattice3(A_255,B_256,C_257) = C_257
      | ~ r1_orders_2(A_255,C_257,C_257)
      | ~ r1_orders_2(A_255,C_257,B_256)
      | ~ m1_subset_1(C_257,u1_struct_0(A_255))
      | ~ m1_subset_1(B_256,u1_struct_0(A_255))
      | ~ l1_orders_2(A_255)
      | ~ v2_lattice3(A_255)
      | ~ v5_orders_2(A_255)
      | v2_struct_0(A_255) ) ),
    inference(resolution,[status(thm)],[c_2017,c_26])).

tff(c_4236,plain,(
    ! [B_256] :
      ( k11_lattice3('#skF_3',B_256,'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',B_256)
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_256,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_577,c_4232])).

tff(c_4243,plain,(
    ! [B_256] :
      ( k11_lattice3('#skF_3',B_256,'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',B_256)
      | ~ m1_subset_1(B_256,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_52,c_4236])).

tff(c_4244,plain,(
    ! [B_256] :
      ( k11_lattice3('#skF_3',B_256,'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',B_256)
      | ~ m1_subset_1(B_256,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_485,c_4243])).

tff(c_7597,plain,
    ( k11_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = '#skF_4'
    | ~ r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_7520,c_4244])).

tff(c_7697,plain,
    ( k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4'
    | ~ r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7473,c_7597])).

tff(c_7698,plain,(
    ~ r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_6856,c_7697])).

tff(c_7878,plain,
    ( ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_472,c_7698])).

tff(c_7881,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_60,c_58,c_7878])).

tff(c_7883,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_485,c_7881])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.13/3.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.13/3.09  
% 9.13/3.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.13/3.09  %$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 9.13/3.09  
% 9.13/3.09  %Foreground sorts:
% 9.13/3.09  
% 9.13/3.09  
% 9.13/3.09  %Background operators:
% 9.13/3.09  
% 9.13/3.09  
% 9.13/3.09  %Foreground operators:
% 9.13/3.09  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.13/3.09  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 9.13/3.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.13/3.09  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 9.13/3.09  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 9.13/3.09  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 9.13/3.09  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 9.13/3.09  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 9.13/3.09  tff('#skF_5', type, '#skF_5': $i).
% 9.13/3.09  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 9.13/3.09  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.13/3.09  tff('#skF_3', type, '#skF_3': $i).
% 9.13/3.09  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 9.13/3.09  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 9.13/3.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.13/3.09  tff('#skF_4', type, '#skF_4': $i).
% 9.13/3.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.13/3.09  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 9.13/3.09  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 9.13/3.09  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.13/3.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.13/3.09  
% 9.42/3.11  tff(f_212, negated_conjecture, ~(![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k12_lattice3(A, B, k13_lattice3(A, B, C)) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_lattice3)).
% 9.42/3.11  tff(f_175, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k11_lattice3(A, B, C) = k11_lattice3(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_lattice3)).
% 9.42/3.11  tff(f_71, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k11_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 9.42/3.11  tff(f_161, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 9.42/3.11  tff(f_149, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 9.42/3.11  tff(f_193, axiom, (![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k13_lattice3(A, k12_lattice3(A, B, C), C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_lattice3)).
% 9.42/3.11  tff(f_104, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l26_lattice3)).
% 9.42/3.11  tff(f_55, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 9.42/3.11  tff(f_63, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k10_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_lattice3)).
% 9.42/3.11  tff(f_137, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l28_lattice3)).
% 9.42/3.11  tff(c_54, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.42/3.11  tff(c_56, plain, (v2_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.42/3.11  tff(c_60, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.42/3.11  tff(c_58, plain, (v1_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.42/3.11  tff(c_50, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.42/3.11  tff(c_52, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.42/3.11  tff(c_68, plain, (![A_143, C_144, B_145]: (k11_lattice3(A_143, C_144, B_145)=k11_lattice3(A_143, B_145, C_144) | ~m1_subset_1(C_144, u1_struct_0(A_143)) | ~m1_subset_1(B_145, u1_struct_0(A_143)) | ~l1_orders_2(A_143) | ~v2_lattice3(A_143) | ~v5_orders_2(A_143))), inference(cnfTransformation, [status(thm)], [f_175])).
% 9.42/3.11  tff(c_74, plain, (![B_145]: (k11_lattice3('#skF_3', B_145, '#skF_5')=k11_lattice3('#skF_3', '#skF_5', B_145) | ~m1_subset_1(B_145, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_68])).
% 9.42/3.11  tff(c_85, plain, (![B_146]: (k11_lattice3('#skF_3', B_146, '#skF_5')=k11_lattice3('#skF_3', '#skF_5', B_146) | ~m1_subset_1(B_146, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_54, c_74])).
% 9.42/3.11  tff(c_108, plain, (k11_lattice3('#skF_3', '#skF_5', '#skF_4')=k11_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_85])).
% 9.42/3.11  tff(c_10, plain, (![A_13, B_14, C_15]: (m1_subset_1(k11_lattice3(A_13, B_14, C_15), u1_struct_0(A_13)) | ~m1_subset_1(C_15, u1_struct_0(A_13)) | ~m1_subset_1(B_14, u1_struct_0(A_13)) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.42/3.11  tff(c_129, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_108, c_10])).
% 9.42/3.11  tff(c_133, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_52, c_129])).
% 9.42/3.11  tff(c_249, plain, (![A_153, B_154, C_155]: (k13_lattice3(A_153, B_154, C_155)=k10_lattice3(A_153, B_154, C_155) | ~m1_subset_1(C_155, u1_struct_0(A_153)) | ~m1_subset_1(B_154, u1_struct_0(A_153)) | ~l1_orders_2(A_153) | ~v1_lattice3(A_153) | ~v5_orders_2(A_153))), inference(cnfTransformation, [status(thm)], [f_161])).
% 9.42/3.11  tff(c_257, plain, (![B_154]: (k13_lattice3('#skF_3', B_154, '#skF_5')=k10_lattice3('#skF_3', B_154, '#skF_5') | ~m1_subset_1(B_154, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_249])).
% 9.42/3.11  tff(c_271, plain, (![B_156]: (k13_lattice3('#skF_3', B_156, '#skF_5')=k10_lattice3('#skF_3', B_156, '#skF_5') | ~m1_subset_1(B_156, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_257])).
% 9.42/3.11  tff(c_289, plain, (k13_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')=k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_133, c_271])).
% 9.42/3.11  tff(c_109, plain, (![A_147, B_148, C_149]: (k12_lattice3(A_147, B_148, C_149)=k11_lattice3(A_147, B_148, C_149) | ~m1_subset_1(C_149, u1_struct_0(A_147)) | ~m1_subset_1(B_148, u1_struct_0(A_147)) | ~l1_orders_2(A_147) | ~v2_lattice3(A_147) | ~v5_orders_2(A_147))), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.42/3.11  tff(c_115, plain, (![B_148]: (k12_lattice3('#skF_3', B_148, '#skF_5')=k11_lattice3('#skF_3', B_148, '#skF_5') | ~m1_subset_1(B_148, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_109])).
% 9.42/3.11  tff(c_178, plain, (![B_151]: (k12_lattice3('#skF_3', B_151, '#skF_5')=k11_lattice3('#skF_3', B_151, '#skF_5') | ~m1_subset_1(B_151, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_54, c_115])).
% 9.42/3.11  tff(c_204, plain, (k12_lattice3('#skF_3', '#skF_4', '#skF_5')=k11_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_178])).
% 9.42/3.11  tff(c_62, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.42/3.11  tff(c_350, plain, (![A_158, B_159, C_160]: (k13_lattice3(A_158, k12_lattice3(A_158, B_159, C_160), C_160)=C_160 | ~m1_subset_1(C_160, u1_struct_0(A_158)) | ~m1_subset_1(B_159, u1_struct_0(A_158)) | ~l1_orders_2(A_158) | ~v2_lattice3(A_158) | ~v1_lattice3(A_158) | ~v5_orders_2(A_158) | ~v3_orders_2(A_158))), inference(cnfTransformation, [status(thm)], [f_193])).
% 9.42/3.11  tff(c_358, plain, (![B_159]: (k13_lattice3('#skF_3', k12_lattice3('#skF_3', B_159, '#skF_5'), '#skF_5')='#skF_5' | ~m1_subset_1(B_159, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | ~v3_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_350])).
% 9.42/3.11  tff(c_372, plain, (![B_161]: (k13_lattice3('#skF_3', k12_lattice3('#skF_3', B_161, '#skF_5'), '#skF_5')='#skF_5' | ~m1_subset_1(B_161, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_358])).
% 9.42/3.11  tff(c_389, plain, (k13_lattice3('#skF_3', k12_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_52, c_372])).
% 9.42/3.11  tff(c_400, plain, (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_289, c_204, c_389])).
% 9.42/3.11  tff(c_465, plain, (![A_163, B_164, C_165]: (r1_orders_2(A_163, B_164, k10_lattice3(A_163, B_164, C_165)) | ~m1_subset_1(k10_lattice3(A_163, B_164, C_165), u1_struct_0(A_163)) | ~m1_subset_1(C_165, u1_struct_0(A_163)) | ~m1_subset_1(B_164, u1_struct_0(A_163)) | ~l1_orders_2(A_163) | ~v1_lattice3(A_163) | ~v5_orders_2(A_163) | v2_struct_0(A_163))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.42/3.11  tff(c_467, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_400, c_465])).
% 9.42/3.11  tff(c_471, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_133, c_50, c_50, c_400, c_467])).
% 9.42/3.11  tff(c_473, plain, (v2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_471])).
% 9.42/3.11  tff(c_6, plain, (![A_9]: (~v2_struct_0(A_9) | ~v2_lattice3(A_9) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.42/3.11  tff(c_476, plain, (~v2_lattice3('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_473, c_6])).
% 9.42/3.11  tff(c_483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_476])).
% 9.42/3.11  tff(c_485, plain, (~v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_471])).
% 9.42/3.11  tff(c_8, plain, (![A_10, B_11, C_12]: (m1_subset_1(k10_lattice3(A_10, B_11, C_12), u1_struct_0(A_10)) | ~m1_subset_1(C_12, u1_struct_0(A_10)) | ~m1_subset_1(B_11, u1_struct_0(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.42/3.11  tff(c_472, plain, (![A_10, B_11, C_12]: (r1_orders_2(A_10, B_11, k10_lattice3(A_10, B_11, C_12)) | ~v1_lattice3(A_10) | ~v5_orders_2(A_10) | v2_struct_0(A_10) | ~m1_subset_1(C_12, u1_struct_0(A_10)) | ~m1_subset_1(B_11, u1_struct_0(A_10)) | ~l1_orders_2(A_10))), inference(resolution, [status(thm)], [c_8, c_465])).
% 9.42/3.11  tff(c_5706, plain, (![A_280, B_281, B_282, C_283]: (k12_lattice3(A_280, B_281, k10_lattice3(A_280, B_282, C_283))=k11_lattice3(A_280, B_281, k10_lattice3(A_280, B_282, C_283)) | ~m1_subset_1(B_281, u1_struct_0(A_280)) | ~v2_lattice3(A_280) | ~v5_orders_2(A_280) | ~m1_subset_1(C_283, u1_struct_0(A_280)) | ~m1_subset_1(B_282, u1_struct_0(A_280)) | ~l1_orders_2(A_280))), inference(resolution, [status(thm)], [c_8, c_109])).
% 9.42/3.11  tff(c_5734, plain, (![B_282, C_283]: (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_282, C_283))=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_282, C_283)) | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | ~m1_subset_1(C_283, u1_struct_0('#skF_3')) | ~m1_subset_1(B_282, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_5706])).
% 9.42/3.11  tff(c_6722, plain, (![B_309, C_310]: (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_309, C_310))=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_309, C_310)) | ~m1_subset_1(C_310, u1_struct_0('#skF_3')) | ~m1_subset_1(B_309, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_60, c_56, c_5734])).
% 9.42/3.11  tff(c_6779, plain, (![B_311]: (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_311, '#skF_5'))=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_311, '#skF_5')) | ~m1_subset_1(B_311, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_50, c_6722])).
% 9.42/3.11  tff(c_6855, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_6779])).
% 9.42/3.11  tff(c_297, plain, (k13_lattice3('#skF_3', '#skF_4', '#skF_5')=k10_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_271])).
% 9.42/3.11  tff(c_48, plain, (k12_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.42/3.11  tff(c_302, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_297, c_48])).
% 9.42/3.11  tff(c_6856, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6855, c_302])).
% 9.42/3.11  tff(c_6941, plain, (![A_313, B_314, C_315, B_316]: (k11_lattice3(A_313, k10_lattice3(A_313, B_314, C_315), B_316)=k11_lattice3(A_313, B_316, k10_lattice3(A_313, B_314, C_315)) | ~m1_subset_1(B_316, u1_struct_0(A_313)) | ~v2_lattice3(A_313) | ~v5_orders_2(A_313) | ~m1_subset_1(C_315, u1_struct_0(A_313)) | ~m1_subset_1(B_314, u1_struct_0(A_313)) | ~l1_orders_2(A_313))), inference(resolution, [status(thm)], [c_8, c_68])).
% 9.42/3.11  tff(c_6969, plain, (![B_314, C_315]: (k11_lattice3('#skF_3', k10_lattice3('#skF_3', B_314, C_315), '#skF_4')=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_314, C_315)) | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | ~m1_subset_1(C_315, u1_struct_0('#skF_3')) | ~m1_subset_1(B_314, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_6941])).
% 9.42/3.11  tff(c_7340, plain, (![B_325, C_326]: (k11_lattice3('#skF_3', k10_lattice3('#skF_3', B_325, C_326), '#skF_4')=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_325, C_326)) | ~m1_subset_1(C_326, u1_struct_0('#skF_3')) | ~m1_subset_1(B_325, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_60, c_56, c_6969])).
% 9.42/3.11  tff(c_7397, plain, (![B_327]: (k11_lattice3('#skF_3', k10_lattice3('#skF_3', B_327, '#skF_5'), '#skF_4')=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_327, '#skF_5')) | ~m1_subset_1(B_327, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_50, c_7340])).
% 9.42/3.11  tff(c_7473, plain, (k11_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_7397])).
% 9.42/3.11  tff(c_750, plain, (![A_172, B_173, C_174]: (r1_orders_2(A_172, k11_lattice3(A_172, B_173, C_174), C_174) | ~m1_subset_1(k11_lattice3(A_172, B_173, C_174), u1_struct_0(A_172)) | ~m1_subset_1(C_174, u1_struct_0(A_172)) | ~m1_subset_1(B_173, u1_struct_0(A_172)) | ~l1_orders_2(A_172) | ~v2_lattice3(A_172) | ~v5_orders_2(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.42/3.11  tff(c_786, plain, (![A_13, B_14, C_15]: (r1_orders_2(A_13, k11_lattice3(A_13, B_14, C_15), C_15) | ~v2_lattice3(A_13) | ~v5_orders_2(A_13) | v2_struct_0(A_13) | ~m1_subset_1(C_15, u1_struct_0(A_13)) | ~m1_subset_1(B_14, u1_struct_0(A_13)) | ~l1_orders_2(A_13))), inference(resolution, [status(thm)], [c_10, c_750])).
% 9.42/3.11  tff(c_7483, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7473, c_786])).
% 9.42/3.11  tff(c_7502, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | v2_struct_0('#skF_3') | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_60, c_56, c_7483])).
% 9.42/3.11  tff(c_7503, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_485, c_7502])).
% 9.42/3.11  tff(c_7511, plain, (~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_7503])).
% 9.42/3.11  tff(c_7514, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_8, c_7511])).
% 9.42/3.11  tff(c_7518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_7514])).
% 9.42/3.11  tff(c_7520, plain, (m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_7503])).
% 9.42/3.11  tff(c_117, plain, (![B_148]: (k12_lattice3('#skF_3', B_148, '#skF_4')=k11_lattice3('#skF_3', B_148, '#skF_4') | ~m1_subset_1(B_148, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_109])).
% 9.42/3.11  tff(c_213, plain, (![B_152]: (k12_lattice3('#skF_3', B_152, '#skF_4')=k11_lattice3('#skF_3', B_152, '#skF_4') | ~m1_subset_1(B_152, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_54, c_117])).
% 9.42/3.11  tff(c_227, plain, (k12_lattice3('#skF_3', '#skF_5', '#skF_4')=k11_lattice3('#skF_3', '#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_213])).
% 9.42/3.11  tff(c_239, plain, (k12_lattice3('#skF_3', '#skF_5', '#skF_4')=k11_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_227])).
% 9.42/3.11  tff(c_360, plain, (![B_159]: (k13_lattice3('#skF_3', k12_lattice3('#skF_3', B_159, '#skF_4'), '#skF_4')='#skF_4' | ~m1_subset_1(B_159, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | ~v3_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_350])).
% 9.42/3.11  tff(c_415, plain, (![B_162]: (k13_lattice3('#skF_3', k12_lattice3('#skF_3', B_162, '#skF_4'), '#skF_4')='#skF_4' | ~m1_subset_1(B_162, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_360])).
% 9.42/3.11  tff(c_429, plain, (k13_lattice3('#skF_3', k12_lattice3('#skF_3', '#skF_5', '#skF_4'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_50, c_415])).
% 9.42/3.11  tff(c_442, plain, (k13_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_239, c_429])).
% 9.42/3.11  tff(c_259, plain, (![B_154]: (k13_lattice3('#skF_3', B_154, '#skF_4')=k10_lattice3('#skF_3', B_154, '#skF_4') | ~m1_subset_1(B_154, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_249])).
% 9.42/3.11  tff(c_307, plain, (![B_157]: (k13_lattice3('#skF_3', B_157, '#skF_4')=k10_lattice3('#skF_3', B_157, '#skF_4') | ~m1_subset_1(B_157, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_259])).
% 9.42/3.11  tff(c_325, plain, (k13_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')=k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_133, c_307])).
% 9.42/3.11  tff(c_553, plain, (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_442, c_325])).
% 9.42/3.11  tff(c_568, plain, (![A_166, C_167, B_168]: (r1_orders_2(A_166, C_167, k10_lattice3(A_166, B_168, C_167)) | ~m1_subset_1(k10_lattice3(A_166, B_168, C_167), u1_struct_0(A_166)) | ~m1_subset_1(C_167, u1_struct_0(A_166)) | ~m1_subset_1(B_168, u1_struct_0(A_166)) | ~l1_orders_2(A_166) | ~v1_lattice3(A_166) | ~v5_orders_2(A_166) | v2_struct_0(A_166))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.42/3.11  tff(c_570, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_553, c_568])).
% 9.42/3.11  tff(c_576, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_133, c_52, c_52, c_553, c_570])).
% 9.42/3.11  tff(c_577, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_485, c_576])).
% 9.42/3.11  tff(c_2017, plain, (![A_210, B_211, C_212, D_213]: (r1_orders_2(A_210, '#skF_2'(A_210, B_211, C_212, D_213), C_212) | k11_lattice3(A_210, B_211, C_212)=D_213 | ~r1_orders_2(A_210, D_213, C_212) | ~r1_orders_2(A_210, D_213, B_211) | ~m1_subset_1(D_213, u1_struct_0(A_210)) | ~m1_subset_1(C_212, u1_struct_0(A_210)) | ~m1_subset_1(B_211, u1_struct_0(A_210)) | ~l1_orders_2(A_210) | ~v2_lattice3(A_210) | ~v5_orders_2(A_210) | v2_struct_0(A_210))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.42/3.11  tff(c_26, plain, (![A_62, B_86, C_98, D_104]: (~r1_orders_2(A_62, '#skF_2'(A_62, B_86, C_98, D_104), D_104) | k11_lattice3(A_62, B_86, C_98)=D_104 | ~r1_orders_2(A_62, D_104, C_98) | ~r1_orders_2(A_62, D_104, B_86) | ~m1_subset_1(D_104, u1_struct_0(A_62)) | ~m1_subset_1(C_98, u1_struct_0(A_62)) | ~m1_subset_1(B_86, u1_struct_0(A_62)) | ~l1_orders_2(A_62) | ~v2_lattice3(A_62) | ~v5_orders_2(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.42/3.11  tff(c_4232, plain, (![A_255, B_256, C_257]: (k11_lattice3(A_255, B_256, C_257)=C_257 | ~r1_orders_2(A_255, C_257, C_257) | ~r1_orders_2(A_255, C_257, B_256) | ~m1_subset_1(C_257, u1_struct_0(A_255)) | ~m1_subset_1(B_256, u1_struct_0(A_255)) | ~l1_orders_2(A_255) | ~v2_lattice3(A_255) | ~v5_orders_2(A_255) | v2_struct_0(A_255))), inference(resolution, [status(thm)], [c_2017, c_26])).
% 9.42/3.11  tff(c_4236, plain, (![B_256]: (k11_lattice3('#skF_3', B_256, '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', B_256) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(B_256, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_577, c_4232])).
% 9.42/3.11  tff(c_4243, plain, (![B_256]: (k11_lattice3('#skF_3', B_256, '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', B_256) | ~m1_subset_1(B_256, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_54, c_52, c_4236])).
% 9.42/3.11  tff(c_4244, plain, (![B_256]: (k11_lattice3('#skF_3', B_256, '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', B_256) | ~m1_subset_1(B_256, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_485, c_4243])).
% 9.42/3.11  tff(c_7597, plain, (k11_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_7520, c_4244])).
% 9.42/3.11  tff(c_7697, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7473, c_7597])).
% 9.42/3.11  tff(c_7698, plain, (~r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_6856, c_7697])).
% 9.42/3.11  tff(c_7878, plain, (~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_472, c_7698])).
% 9.42/3.11  tff(c_7881, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_60, c_58, c_7878])).
% 9.42/3.11  tff(c_7883, plain, $false, inference(negUnitSimplification, [status(thm)], [c_485, c_7881])).
% 9.42/3.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.42/3.11  
% 9.42/3.11  Inference rules
% 9.42/3.11  ----------------------
% 9.42/3.11  #Ref     : 0
% 9.42/3.11  #Sup     : 1660
% 9.42/3.11  #Fact    : 0
% 9.42/3.11  #Define  : 0
% 9.42/3.11  #Split   : 12
% 9.42/3.11  #Chain   : 0
% 9.42/3.11  #Close   : 0
% 9.42/3.11  
% 9.42/3.11  Ordering : KBO
% 9.42/3.11  
% 9.42/3.11  Simplification rules
% 9.42/3.11  ----------------------
% 9.42/3.11  #Subsume      : 30
% 9.42/3.11  #Demod        : 3682
% 9.42/3.11  #Tautology    : 724
% 9.42/3.11  #SimpNegUnit  : 370
% 9.42/3.11  #BackRed      : 96
% 9.42/3.11  
% 9.42/3.11  #Partial instantiations: 0
% 9.42/3.11  #Strategies tried      : 1
% 9.42/3.11  
% 9.42/3.11  Timing (in seconds)
% 9.42/3.11  ----------------------
% 9.42/3.11  Preprocessing        : 0.39
% 9.42/3.11  Parsing              : 0.20
% 9.42/3.11  CNF conversion       : 0.04
% 9.42/3.11  Main loop            : 1.94
% 9.42/3.11  Inferencing          : 0.52
% 9.42/3.11  Reduction            : 0.83
% 9.42/3.11  Demodulation         : 0.65
% 9.42/3.11  BG Simplification    : 0.09
% 9.42/3.11  Subsumption          : 0.40
% 9.42/3.12  Abstraction          : 0.11
% 9.42/3.12  MUC search           : 0.00
% 9.42/3.12  Cooper               : 0.00
% 9.42/3.12  Total                : 2.38
% 9.42/3.12  Index Insertion      : 0.00
% 9.42/3.12  Index Deletion       : 0.00
% 9.42/3.12  Index Matching       : 0.00
% 9.42/3.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
