%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:41 EST 2020

% Result     : Theorem 9.45s
% Output     : CNFRefutation 9.45s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 662 expanded)
%              Number of leaves         :   31 ( 278 expanded)
%              Depth                    :   15
%              Number of atoms          :  304 (2904 expanded)
%              Number of equality atoms :   43 ( 353 expanded)
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

tff(f_204,negated_conjecture,(
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

tff(f_153,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_141,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k12_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_lattice3)).

tff(f_129,axiom,(
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

tff(f_32,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k13_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k13_lattice3)).

tff(f_167,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k10_lattice3(A,B,C) = k10_lattice3(A,C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_lattice3)).

tff(f_185,axiom,(
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

tff(f_96,axiom,(
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

tff(c_50,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_58,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_56,plain,(
    v1_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_52,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_110,plain,(
    ! [A_137,B_138,C_139] :
      ( k13_lattice3(A_137,B_138,C_139) = k10_lattice3(A_137,B_138,C_139)
      | ~ m1_subset_1(C_139,u1_struct_0(A_137))
      | ~ m1_subset_1(B_138,u1_struct_0(A_137))
      | ~ l1_orders_2(A_137)
      | ~ v1_lattice3(A_137)
      | ~ v5_orders_2(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_116,plain,(
    ! [B_138] :
      ( k13_lattice3('#skF_3',B_138,'#skF_5') = k10_lattice3('#skF_3',B_138,'#skF_5')
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_110])).

tff(c_152,plain,(
    ! [B_141] :
      ( k13_lattice3('#skF_3',B_141,'#skF_5') = k10_lattice3('#skF_3',B_141,'#skF_5')
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_116])).

tff(c_174,plain,(
    k13_lattice3('#skF_3','#skF_4','#skF_5') = k10_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_152])).

tff(c_46,plain,(
    k12_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_184,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_46])).

tff(c_54,plain,(
    v2_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_279,plain,(
    ! [A_143,B_144,C_145] :
      ( k12_lattice3(A_143,B_144,C_145) = k11_lattice3(A_143,B_144,C_145)
      | ~ m1_subset_1(C_145,u1_struct_0(A_143))
      | ~ m1_subset_1(B_144,u1_struct_0(A_143))
      | ~ l1_orders_2(A_143)
      | ~ v2_lattice3(A_143)
      | ~ v5_orders_2(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_291,plain,(
    ! [B_144] :
      ( k12_lattice3('#skF_3',B_144,'#skF_4') = k11_lattice3('#skF_3',B_144,'#skF_4')
      | ~ m1_subset_1(B_144,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_279])).

tff(c_469,plain,(
    ! [B_147] :
      ( k12_lattice3('#skF_3',B_147,'#skF_4') = k11_lattice3('#skF_3',B_147,'#skF_4')
      | ~ m1_subset_1(B_147,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_291])).

tff(c_511,plain,(
    k12_lattice3('#skF_3','#skF_4','#skF_4') = k11_lattice3('#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_469])).

tff(c_6,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1(k12_lattice3(A_3,B_4,C_5),u1_struct_0(A_3))
      | ~ m1_subset_1(C_5,u1_struct_0(A_3))
      | ~ m1_subset_1(B_4,u1_struct_0(A_3))
      | ~ l1_orders_2(A_3)
      | ~ v2_lattice3(A_3)
      | ~ v5_orders_2(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_610,plain,
    ( m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_6])).

tff(c_614,plain,(
    m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_50,c_50,c_610])).

tff(c_758,plain,(
    ! [A_152,B_153,C_154] :
      ( r1_orders_2(A_152,k11_lattice3(A_152,B_153,C_154),C_154)
      | ~ m1_subset_1(k11_lattice3(A_152,B_153,C_154),u1_struct_0(A_152))
      | ~ m1_subset_1(C_154,u1_struct_0(A_152))
      | ~ m1_subset_1(B_153,u1_struct_0(A_152))
      | ~ l1_orders_2(A_152)
      | ~ v2_lattice3(A_152)
      | ~ v5_orders_2(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_760,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_614,c_758])).

tff(c_769,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_4'),'#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_50,c_760])).

tff(c_779,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_769])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v1_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_782,plain,
    ( ~ v1_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_779,c_2])).

tff(c_789,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_782])).

tff(c_791,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_769])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] :
      ( m1_subset_1(k13_lattice3(A_6,B_7,C_8),u1_struct_0(A_6))
      | ~ m1_subset_1(C_8,u1_struct_0(A_6))
      | ~ m1_subset_1(B_7,u1_struct_0(A_6))
      | ~ l1_orders_2(A_6)
      | ~ v1_lattice3(A_6)
      | ~ v5_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_188,plain,
    ( m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_8])).

tff(c_192,plain,(
    m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_188])).

tff(c_65,plain,(
    ! [A_133,C_134,B_135] :
      ( k10_lattice3(A_133,C_134,B_135) = k10_lattice3(A_133,B_135,C_134)
      | ~ m1_subset_1(C_134,u1_struct_0(A_133))
      | ~ m1_subset_1(B_135,u1_struct_0(A_133))
      | ~ l1_orders_2(A_133)
      | ~ v1_lattice3(A_133)
      | ~ v5_orders_2(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_73,plain,(
    ! [B_135] :
      ( k10_lattice3('#skF_3',B_135,'#skF_4') = k10_lattice3('#skF_3','#skF_4',B_135)
      | ~ m1_subset_1(B_135,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_65])).

tff(c_81,plain,(
    ! [B_135] :
      ( k10_lattice3('#skF_3',B_135,'#skF_4') = k10_lattice3('#skF_3','#skF_4',B_135)
      | ~ m1_subset_1(B_135,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_73])).

tff(c_652,plain,(
    k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_4'),'#skF_4') = k10_lattice3('#skF_3','#skF_4',k11_lattice3('#skF_3','#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_614,c_81])).

tff(c_60,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_521,plain,(
    ! [A_148,B_149,C_150] :
      ( k13_lattice3(A_148,k12_lattice3(A_148,B_149,C_150),C_150) = C_150
      | ~ m1_subset_1(C_150,u1_struct_0(A_148))
      | ~ m1_subset_1(B_149,u1_struct_0(A_148))
      | ~ l1_orders_2(A_148)
      | ~ v2_lattice3(A_148)
      | ~ v1_lattice3(A_148)
      | ~ v5_orders_2(A_148)
      | ~ v3_orders_2(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_539,plain,(
    ! [B_149] :
      ( k13_lattice3('#skF_3',k12_lattice3('#skF_3',B_149,'#skF_4'),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(B_149,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_521])).

tff(c_660,plain,(
    ! [B_151] :
      ( k13_lattice3('#skF_3',k12_lattice3('#skF_3',B_151,'#skF_4'),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_539])).

tff(c_695,plain,(
    k13_lattice3('#skF_3',k12_lattice3('#skF_3','#skF_4','#skF_4'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_660])).

tff(c_712,plain,(
    k13_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_4'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_695])).

tff(c_118,plain,(
    ! [B_138] :
      ( k13_lattice3('#skF_3',B_138,'#skF_4') = k10_lattice3('#skF_3',B_138,'#skF_4')
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_110])).

tff(c_126,plain,(
    ! [B_138] :
      ( k13_lattice3('#skF_3',B_138,'#skF_4') = k10_lattice3('#skF_3',B_138,'#skF_4')
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_118])).

tff(c_650,plain,(
    k13_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_4'),'#skF_4') = k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_614,c_126])).

tff(c_2388,plain,(
    k10_lattice3('#skF_3','#skF_4',k11_lattice3('#skF_3','#skF_4','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_712,c_650])).

tff(c_22,plain,(
    ! [A_9,B_33,C_45] :
      ( r1_orders_2(A_9,B_33,k10_lattice3(A_9,B_33,C_45))
      | ~ m1_subset_1(k10_lattice3(A_9,B_33,C_45),u1_struct_0(A_9))
      | ~ m1_subset_1(C_45,u1_struct_0(A_9))
      | ~ m1_subset_1(B_33,u1_struct_0(A_9))
      | ~ l1_orders_2(A_9)
      | ~ v1_lattice3(A_9)
      | ~ v5_orders_2(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2392,plain,
    ( r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4',k11_lattice3('#skF_3','#skF_4','#skF_4')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2388,c_22])).

tff(c_2398,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_614,c_50,c_2388,c_2392])).

tff(c_2399,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_791,c_2398])).

tff(c_71,plain,(
    ! [B_135] :
      ( k10_lattice3('#skF_3',B_135,'#skF_5') = k10_lattice3('#skF_3','#skF_5',B_135)
      | ~ m1_subset_1(B_135,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_65])).

tff(c_82,plain,(
    ! [B_136] :
      ( k10_lattice3('#skF_3',B_136,'#skF_5') = k10_lattice3('#skF_3','#skF_5',B_136)
      | ~ m1_subset_1(B_136,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_71])).

tff(c_105,plain,(
    k10_lattice3('#skF_3','#skF_5','#skF_4') = k10_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_82])).

tff(c_937,plain,(
    ! [A_159,C_160,B_161] :
      ( r1_orders_2(A_159,C_160,k10_lattice3(A_159,B_161,C_160))
      | ~ m1_subset_1(k10_lattice3(A_159,B_161,C_160),u1_struct_0(A_159))
      | ~ m1_subset_1(C_160,u1_struct_0(A_159))
      | ~ m1_subset_1(B_161,u1_struct_0(A_159))
      | ~ l1_orders_2(A_159)
      | ~ v1_lattice3(A_159)
      | ~ v5_orders_2(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_945,plain,
    ( r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_5','#skF_4'))
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_937])).

tff(c_959,plain,
    ( r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_48,c_50,c_192,c_105,c_945])).

tff(c_960,plain,(
    r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_791,c_959])).

tff(c_2404,plain,(
    ! [A_193,B_194,C_195,D_196] :
      ( r1_orders_2(A_193,'#skF_2'(A_193,B_194,C_195,D_196),B_194)
      | k11_lattice3(A_193,B_194,C_195) = D_196
      | ~ r1_orders_2(A_193,D_196,C_195)
      | ~ r1_orders_2(A_193,D_196,B_194)
      | ~ m1_subset_1(D_196,u1_struct_0(A_193))
      | ~ m1_subset_1(C_195,u1_struct_0(A_193))
      | ~ m1_subset_1(B_194,u1_struct_0(A_193))
      | ~ l1_orders_2(A_193)
      | ~ v2_lattice3(A_193)
      | ~ v5_orders_2(A_193)
      | v2_struct_0(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_24,plain,(
    ! [A_55,B_79,C_91,D_97] :
      ( ~ r1_orders_2(A_55,'#skF_2'(A_55,B_79,C_91,D_97),D_97)
      | k11_lattice3(A_55,B_79,C_91) = D_97
      | ~ r1_orders_2(A_55,D_97,C_91)
      | ~ r1_orders_2(A_55,D_97,B_79)
      | ~ m1_subset_1(D_97,u1_struct_0(A_55))
      | ~ m1_subset_1(C_91,u1_struct_0(A_55))
      | ~ m1_subset_1(B_79,u1_struct_0(A_55))
      | ~ l1_orders_2(A_55)
      | ~ v2_lattice3(A_55)
      | ~ v5_orders_2(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3876,plain,(
    ! [A_215,B_216,C_217] :
      ( k11_lattice3(A_215,B_216,C_217) = B_216
      | ~ r1_orders_2(A_215,B_216,C_217)
      | ~ r1_orders_2(A_215,B_216,B_216)
      | ~ m1_subset_1(C_217,u1_struct_0(A_215))
      | ~ m1_subset_1(B_216,u1_struct_0(A_215))
      | ~ l1_orders_2(A_215)
      | ~ v2_lattice3(A_215)
      | ~ v5_orders_2(A_215)
      | v2_struct_0(A_215) ) ),
    inference(resolution,[status(thm)],[c_2404,c_24])).

tff(c_3924,plain,
    ( k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4'
    | ~ r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_960,c_3876])).

tff(c_4019,plain,
    ( k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_50,c_192,c_2399,c_3924])).

tff(c_4020,plain,(
    k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_791,c_4019])).

tff(c_281,plain,(
    ! [B_144] :
      ( k12_lattice3('#skF_3',B_144,k10_lattice3('#skF_3','#skF_4','#skF_5')) = k11_lattice3('#skF_3',B_144,k10_lattice3('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(B_144,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_192,c_279])).

tff(c_9664,plain,(
    ! [B_320] :
      ( k12_lattice3('#skF_3',B_320,k10_lattice3('#skF_3','#skF_4','#skF_5')) = k11_lattice3('#skF_3',B_320,k10_lattice3('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(B_320,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_281])).

tff(c_9725,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_50,c_9664])).

tff(c_9756,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4020,c_9725])).

tff(c_9758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_9756])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.45/3.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.45/3.37  
% 9.45/3.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.45/3.37  %$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 9.45/3.37  
% 9.45/3.37  %Foreground sorts:
% 9.45/3.37  
% 9.45/3.37  
% 9.45/3.37  %Background operators:
% 9.45/3.37  
% 9.45/3.37  
% 9.45/3.37  %Foreground operators:
% 9.45/3.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.45/3.37  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 9.45/3.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.45/3.37  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 9.45/3.37  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 9.45/3.37  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 9.45/3.37  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 9.45/3.37  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 9.45/3.37  tff('#skF_5', type, '#skF_5': $i).
% 9.45/3.37  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 9.45/3.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.45/3.37  tff('#skF_3', type, '#skF_3': $i).
% 9.45/3.37  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 9.45/3.37  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 9.45/3.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.45/3.37  tff('#skF_4', type, '#skF_4': $i).
% 9.45/3.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.45/3.37  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 9.45/3.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 9.45/3.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.45/3.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.45/3.37  
% 9.45/3.39  tff(f_204, negated_conjecture, ~(![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k12_lattice3(A, B, k13_lattice3(A, B, C)) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_lattice3)).
% 9.45/3.39  tff(f_153, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 9.45/3.39  tff(f_141, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 9.45/3.39  tff(f_51, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k12_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k12_lattice3)).
% 9.45/3.39  tff(f_129, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l28_lattice3)).
% 9.45/3.39  tff(f_32, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 9.45/3.39  tff(f_63, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k13_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k13_lattice3)).
% 9.45/3.39  tff(f_167, axiom, (![A]: (((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k10_lattice3(A, B, C) = k10_lattice3(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_lattice3)).
% 9.45/3.39  tff(f_185, axiom, (![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k13_lattice3(A, k12_lattice3(A, B, C), C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_lattice3)).
% 9.45/3.39  tff(f_96, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l26_lattice3)).
% 9.45/3.39  tff(c_50, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 9.45/3.39  tff(c_58, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_204])).
% 9.45/3.39  tff(c_56, plain, (v1_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_204])).
% 9.45/3.39  tff(c_52, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_204])).
% 9.45/3.39  tff(c_48, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 9.45/3.39  tff(c_110, plain, (![A_137, B_138, C_139]: (k13_lattice3(A_137, B_138, C_139)=k10_lattice3(A_137, B_138, C_139) | ~m1_subset_1(C_139, u1_struct_0(A_137)) | ~m1_subset_1(B_138, u1_struct_0(A_137)) | ~l1_orders_2(A_137) | ~v1_lattice3(A_137) | ~v5_orders_2(A_137))), inference(cnfTransformation, [status(thm)], [f_153])).
% 9.45/3.39  tff(c_116, plain, (![B_138]: (k13_lattice3('#skF_3', B_138, '#skF_5')=k10_lattice3('#skF_3', B_138, '#skF_5') | ~m1_subset_1(B_138, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_110])).
% 9.45/3.39  tff(c_152, plain, (![B_141]: (k13_lattice3('#skF_3', B_141, '#skF_5')=k10_lattice3('#skF_3', B_141, '#skF_5') | ~m1_subset_1(B_141, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_116])).
% 9.45/3.39  tff(c_174, plain, (k13_lattice3('#skF_3', '#skF_4', '#skF_5')=k10_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_152])).
% 9.45/3.39  tff(c_46, plain, (k12_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_204])).
% 9.45/3.39  tff(c_184, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_174, c_46])).
% 9.45/3.39  tff(c_54, plain, (v2_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_204])).
% 9.45/3.39  tff(c_279, plain, (![A_143, B_144, C_145]: (k12_lattice3(A_143, B_144, C_145)=k11_lattice3(A_143, B_144, C_145) | ~m1_subset_1(C_145, u1_struct_0(A_143)) | ~m1_subset_1(B_144, u1_struct_0(A_143)) | ~l1_orders_2(A_143) | ~v2_lattice3(A_143) | ~v5_orders_2(A_143))), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.45/3.39  tff(c_291, plain, (![B_144]: (k12_lattice3('#skF_3', B_144, '#skF_4')=k11_lattice3('#skF_3', B_144, '#skF_4') | ~m1_subset_1(B_144, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_279])).
% 9.45/3.39  tff(c_469, plain, (![B_147]: (k12_lattice3('#skF_3', B_147, '#skF_4')=k11_lattice3('#skF_3', B_147, '#skF_4') | ~m1_subset_1(B_147, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_291])).
% 9.45/3.39  tff(c_511, plain, (k12_lattice3('#skF_3', '#skF_4', '#skF_4')=k11_lattice3('#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_469])).
% 9.45/3.39  tff(c_6, plain, (![A_3, B_4, C_5]: (m1_subset_1(k12_lattice3(A_3, B_4, C_5), u1_struct_0(A_3)) | ~m1_subset_1(C_5, u1_struct_0(A_3)) | ~m1_subset_1(B_4, u1_struct_0(A_3)) | ~l1_orders_2(A_3) | ~v2_lattice3(A_3) | ~v5_orders_2(A_3))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.45/3.39  tff(c_610, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_511, c_6])).
% 9.45/3.39  tff(c_614, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_50, c_50, c_610])).
% 9.45/3.39  tff(c_758, plain, (![A_152, B_153, C_154]: (r1_orders_2(A_152, k11_lattice3(A_152, B_153, C_154), C_154) | ~m1_subset_1(k11_lattice3(A_152, B_153, C_154), u1_struct_0(A_152)) | ~m1_subset_1(C_154, u1_struct_0(A_152)) | ~m1_subset_1(B_153, u1_struct_0(A_152)) | ~l1_orders_2(A_152) | ~v2_lattice3(A_152) | ~v5_orders_2(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.45/3.39  tff(c_760, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_614, c_758])).
% 9.45/3.39  tff(c_769, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_4'), '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_50, c_760])).
% 9.45/3.39  tff(c_779, plain, (v2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_769])).
% 9.45/3.39  tff(c_2, plain, (![A_1]: (~v2_struct_0(A_1) | ~v1_lattice3(A_1) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.45/3.39  tff(c_782, plain, (~v1_lattice3('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_779, c_2])).
% 9.45/3.39  tff(c_789, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_782])).
% 9.45/3.39  tff(c_791, plain, (~v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_769])).
% 9.45/3.39  tff(c_8, plain, (![A_6, B_7, C_8]: (m1_subset_1(k13_lattice3(A_6, B_7, C_8), u1_struct_0(A_6)) | ~m1_subset_1(C_8, u1_struct_0(A_6)) | ~m1_subset_1(B_7, u1_struct_0(A_6)) | ~l1_orders_2(A_6) | ~v1_lattice3(A_6) | ~v5_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.45/3.39  tff(c_188, plain, (m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_174, c_8])).
% 9.45/3.39  tff(c_192, plain, (m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_188])).
% 9.45/3.39  tff(c_65, plain, (![A_133, C_134, B_135]: (k10_lattice3(A_133, C_134, B_135)=k10_lattice3(A_133, B_135, C_134) | ~m1_subset_1(C_134, u1_struct_0(A_133)) | ~m1_subset_1(B_135, u1_struct_0(A_133)) | ~l1_orders_2(A_133) | ~v1_lattice3(A_133) | ~v5_orders_2(A_133))), inference(cnfTransformation, [status(thm)], [f_167])).
% 9.45/3.39  tff(c_73, plain, (![B_135]: (k10_lattice3('#skF_3', B_135, '#skF_4')=k10_lattice3('#skF_3', '#skF_4', B_135) | ~m1_subset_1(B_135, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_65])).
% 9.45/3.39  tff(c_81, plain, (![B_135]: (k10_lattice3('#skF_3', B_135, '#skF_4')=k10_lattice3('#skF_3', '#skF_4', B_135) | ~m1_subset_1(B_135, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_73])).
% 9.45/3.39  tff(c_652, plain, (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_4'), '#skF_4')=k10_lattice3('#skF_3', '#skF_4', k11_lattice3('#skF_3', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_614, c_81])).
% 9.45/3.39  tff(c_60, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_204])).
% 9.45/3.39  tff(c_521, plain, (![A_148, B_149, C_150]: (k13_lattice3(A_148, k12_lattice3(A_148, B_149, C_150), C_150)=C_150 | ~m1_subset_1(C_150, u1_struct_0(A_148)) | ~m1_subset_1(B_149, u1_struct_0(A_148)) | ~l1_orders_2(A_148) | ~v2_lattice3(A_148) | ~v1_lattice3(A_148) | ~v5_orders_2(A_148) | ~v3_orders_2(A_148))), inference(cnfTransformation, [status(thm)], [f_185])).
% 9.45/3.39  tff(c_539, plain, (![B_149]: (k13_lattice3('#skF_3', k12_lattice3('#skF_3', B_149, '#skF_4'), '#skF_4')='#skF_4' | ~m1_subset_1(B_149, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | ~v3_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_521])).
% 9.45/3.39  tff(c_660, plain, (![B_151]: (k13_lattice3('#skF_3', k12_lattice3('#skF_3', B_151, '#skF_4'), '#skF_4')='#skF_4' | ~m1_subset_1(B_151, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_539])).
% 9.45/3.39  tff(c_695, plain, (k13_lattice3('#skF_3', k12_lattice3('#skF_3', '#skF_4', '#skF_4'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_50, c_660])).
% 9.45/3.39  tff(c_712, plain, (k13_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_4'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_511, c_695])).
% 9.45/3.39  tff(c_118, plain, (![B_138]: (k13_lattice3('#skF_3', B_138, '#skF_4')=k10_lattice3('#skF_3', B_138, '#skF_4') | ~m1_subset_1(B_138, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_110])).
% 9.45/3.39  tff(c_126, plain, (![B_138]: (k13_lattice3('#skF_3', B_138, '#skF_4')=k10_lattice3('#skF_3', B_138, '#skF_4') | ~m1_subset_1(B_138, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_118])).
% 9.45/3.39  tff(c_650, plain, (k13_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_4'), '#skF_4')=k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_614, c_126])).
% 9.45/3.39  tff(c_2388, plain, (k10_lattice3('#skF_3', '#skF_4', k11_lattice3('#skF_3', '#skF_4', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_652, c_712, c_650])).
% 9.45/3.39  tff(c_22, plain, (![A_9, B_33, C_45]: (r1_orders_2(A_9, B_33, k10_lattice3(A_9, B_33, C_45)) | ~m1_subset_1(k10_lattice3(A_9, B_33, C_45), u1_struct_0(A_9)) | ~m1_subset_1(C_45, u1_struct_0(A_9)) | ~m1_subset_1(B_33, u1_struct_0(A_9)) | ~l1_orders_2(A_9) | ~v1_lattice3(A_9) | ~v5_orders_2(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.45/3.39  tff(c_2392, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', k11_lattice3('#skF_3', '#skF_4', '#skF_4'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2388, c_22])).
% 9.45/3.39  tff(c_2398, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_614, c_50, c_2388, c_2392])).
% 9.45/3.39  tff(c_2399, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_791, c_2398])).
% 9.45/3.39  tff(c_71, plain, (![B_135]: (k10_lattice3('#skF_3', B_135, '#skF_5')=k10_lattice3('#skF_3', '#skF_5', B_135) | ~m1_subset_1(B_135, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_65])).
% 9.45/3.39  tff(c_82, plain, (![B_136]: (k10_lattice3('#skF_3', B_136, '#skF_5')=k10_lattice3('#skF_3', '#skF_5', B_136) | ~m1_subset_1(B_136, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_71])).
% 9.45/3.39  tff(c_105, plain, (k10_lattice3('#skF_3', '#skF_5', '#skF_4')=k10_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_82])).
% 9.45/3.39  tff(c_937, plain, (![A_159, C_160, B_161]: (r1_orders_2(A_159, C_160, k10_lattice3(A_159, B_161, C_160)) | ~m1_subset_1(k10_lattice3(A_159, B_161, C_160), u1_struct_0(A_159)) | ~m1_subset_1(C_160, u1_struct_0(A_159)) | ~m1_subset_1(B_161, u1_struct_0(A_159)) | ~l1_orders_2(A_159) | ~v1_lattice3(A_159) | ~v5_orders_2(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.45/3.39  tff(c_945, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_5', '#skF_4')) | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_105, c_937])).
% 9.45/3.39  tff(c_959, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_48, c_50, c_192, c_105, c_945])).
% 9.45/3.39  tff(c_960, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_791, c_959])).
% 9.45/3.39  tff(c_2404, plain, (![A_193, B_194, C_195, D_196]: (r1_orders_2(A_193, '#skF_2'(A_193, B_194, C_195, D_196), B_194) | k11_lattice3(A_193, B_194, C_195)=D_196 | ~r1_orders_2(A_193, D_196, C_195) | ~r1_orders_2(A_193, D_196, B_194) | ~m1_subset_1(D_196, u1_struct_0(A_193)) | ~m1_subset_1(C_195, u1_struct_0(A_193)) | ~m1_subset_1(B_194, u1_struct_0(A_193)) | ~l1_orders_2(A_193) | ~v2_lattice3(A_193) | ~v5_orders_2(A_193) | v2_struct_0(A_193))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.45/3.39  tff(c_24, plain, (![A_55, B_79, C_91, D_97]: (~r1_orders_2(A_55, '#skF_2'(A_55, B_79, C_91, D_97), D_97) | k11_lattice3(A_55, B_79, C_91)=D_97 | ~r1_orders_2(A_55, D_97, C_91) | ~r1_orders_2(A_55, D_97, B_79) | ~m1_subset_1(D_97, u1_struct_0(A_55)) | ~m1_subset_1(C_91, u1_struct_0(A_55)) | ~m1_subset_1(B_79, u1_struct_0(A_55)) | ~l1_orders_2(A_55) | ~v2_lattice3(A_55) | ~v5_orders_2(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.45/3.39  tff(c_3876, plain, (![A_215, B_216, C_217]: (k11_lattice3(A_215, B_216, C_217)=B_216 | ~r1_orders_2(A_215, B_216, C_217) | ~r1_orders_2(A_215, B_216, B_216) | ~m1_subset_1(C_217, u1_struct_0(A_215)) | ~m1_subset_1(B_216, u1_struct_0(A_215)) | ~l1_orders_2(A_215) | ~v2_lattice3(A_215) | ~v5_orders_2(A_215) | v2_struct_0(A_215))), inference(resolution, [status(thm)], [c_2404, c_24])).
% 9.45/3.39  tff(c_3924, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_960, c_3876])).
% 9.45/3.39  tff(c_4019, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_50, c_192, c_2399, c_3924])).
% 9.45/3.39  tff(c_4020, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_791, c_4019])).
% 9.45/3.39  tff(c_281, plain, (![B_144]: (k12_lattice3('#skF_3', B_144, k10_lattice3('#skF_3', '#skF_4', '#skF_5'))=k11_lattice3('#skF_3', B_144, k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(B_144, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_192, c_279])).
% 9.45/3.39  tff(c_9664, plain, (![B_320]: (k12_lattice3('#skF_3', B_320, k10_lattice3('#skF_3', '#skF_4', '#skF_5'))=k11_lattice3('#skF_3', B_320, k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(B_320, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_281])).
% 9.45/3.39  tff(c_9725, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_9664])).
% 9.45/3.39  tff(c_9756, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4020, c_9725])).
% 9.45/3.39  tff(c_9758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_184, c_9756])).
% 9.45/3.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.45/3.39  
% 9.45/3.39  Inference rules
% 9.45/3.39  ----------------------
% 9.45/3.39  #Ref     : 0
% 9.45/3.39  #Sup     : 2082
% 9.45/3.39  #Fact    : 0
% 9.45/3.39  #Define  : 0
% 9.45/3.39  #Split   : 9
% 9.45/3.39  #Chain   : 0
% 9.45/3.39  #Close   : 0
% 9.45/3.39  
% 9.45/3.39  Ordering : KBO
% 9.45/3.39  
% 9.45/3.39  Simplification rules
% 9.45/3.39  ----------------------
% 9.45/3.39  #Subsume      : 85
% 9.45/3.39  #Demod        : 5990
% 9.45/3.39  #Tautology    : 769
% 9.45/3.39  #SimpNegUnit  : 496
% 9.45/3.39  #BackRed      : 114
% 9.45/3.39  
% 9.45/3.39  #Partial instantiations: 0
% 9.45/3.39  #Strategies tried      : 1
% 9.45/3.39  
% 9.45/3.39  Timing (in seconds)
% 9.45/3.39  ----------------------
% 9.45/3.39  Preprocessing        : 0.37
% 9.45/3.39  Parsing              : 0.18
% 9.45/3.39  CNF conversion       : 0.04
% 9.45/3.39  Main loop            : 2.23
% 9.45/3.39  Inferencing          : 0.53
% 9.45/3.39  Reduction            : 1.01
% 9.45/3.39  Demodulation         : 0.81
% 9.45/3.39  BG Simplification    : 0.09
% 9.45/3.39  Subsumption          : 0.47
% 9.45/3.39  Abstraction          : 0.13
% 9.45/3.39  MUC search           : 0.00
% 9.45/3.39  Cooper               : 0.00
% 9.45/3.39  Total                : 2.64
% 9.45/3.39  Index Insertion      : 0.00
% 9.45/3.39  Index Deletion       : 0.00
% 9.45/3.39  Index Matching       : 0.00
% 9.45/3.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
