%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:42 EST 2020

% Result     : Theorem 7.69s
% Output     : CNFRefutation 7.96s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 222 expanded)
%              Number of leaves         :   30 (  98 expanded)
%              Depth                    :   12
%              Number of atoms          :  213 ( 877 expanded)
%              Number of equality atoms :   26 (  96 expanded)
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

tff(f_183,negated_conjecture,(
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

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_164,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k10_lattice3(A,B,C) = k10_lattice3(A,C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_lattice3)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k10_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).

tff(f_138,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_150,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_93,axiom,(
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

tff(f_126,axiom,(
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

tff(c_50,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_54,plain,(
    v1_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_58,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_60,plain,(
    ! [A_121,B_122] :
      ( r1_orders_2(A_121,B_122,B_122)
      | ~ m1_subset_1(B_122,u1_struct_0(A_121))
      | ~ l1_orders_2(A_121)
      | ~ v3_orders_2(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_62,plain,
    ( r1_orders_2('#skF_3','#skF_5','#skF_5')
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_60])).

tff(c_67,plain,
    ( r1_orders_2('#skF_3','#skF_5','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_62])).

tff(c_71,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_4,plain,(
    ! [A_4] :
      ( ~ v2_struct_0(A_4)
      | ~ v1_lattice3(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_74,plain,
    ( ~ v1_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_4])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_74])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_56,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_52,plain,(
    v2_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_186,plain,(
    ! [A_137,C_138,B_139] :
      ( k10_lattice3(A_137,C_138,B_139) = k10_lattice3(A_137,B_139,C_138)
      | ~ m1_subset_1(C_138,u1_struct_0(A_137))
      | ~ m1_subset_1(B_139,u1_struct_0(A_137))
      | ~ l1_orders_2(A_137)
      | ~ v1_lattice3(A_137)
      | ~ v5_orders_2(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_194,plain,(
    ! [B_139] :
      ( k10_lattice3('#skF_3',B_139,'#skF_4') = k10_lattice3('#skF_3','#skF_4',B_139)
      | ~ m1_subset_1(B_139,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_186])).

tff(c_235,plain,(
    ! [B_141] :
      ( k10_lattice3('#skF_3',B_141,'#skF_4') = k10_lattice3('#skF_3','#skF_4',B_141)
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_194])).

tff(c_256,plain,(
    k10_lattice3('#skF_3','#skF_5','#skF_4') = k10_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_235])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k10_lattice3(A_5,B_6,C_7),u1_struct_0(A_5))
      | ~ m1_subset_1(C_7,u1_struct_0(A_5))
      | ~ m1_subset_1(B_6,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_262,plain,
    ( m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_6])).

tff(c_266,plain,(
    m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_48,c_262])).

tff(c_38,plain,(
    ! [A_103,B_104,C_105] :
      ( k12_lattice3(A_103,B_104,C_105) = k11_lattice3(A_103,B_104,C_105)
      | ~ m1_subset_1(C_105,u1_struct_0(A_103))
      | ~ m1_subset_1(B_104,u1_struct_0(A_103))
      | ~ l1_orders_2(A_103)
      | ~ v2_lattice3(A_103)
      | ~ v5_orders_2(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_285,plain,(
    ! [B_104] :
      ( k12_lattice3('#skF_3',B_104,k10_lattice3('#skF_3','#skF_4','#skF_5')) = k11_lattice3('#skF_3',B_104,k10_lattice3('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(B_104,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_266,c_38])).

tff(c_550,plain,(
    ! [B_151] :
      ( k12_lattice3('#skF_3',B_151,k10_lattice3('#skF_3','#skF_4','#skF_5')) = k11_lattice3('#skF_3',B_151,k10_lattice3('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_285])).

tff(c_584,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_48,c_550])).

tff(c_169,plain,(
    ! [A_134,B_135,C_136] :
      ( k13_lattice3(A_134,B_135,C_136) = k10_lattice3(A_134,B_135,C_136)
      | ~ m1_subset_1(C_136,u1_struct_0(A_134))
      | ~ m1_subset_1(B_135,u1_struct_0(A_134))
      | ~ l1_orders_2(A_134)
      | ~ v1_lattice3(A_134)
      | ~ v5_orders_2(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_175,plain,(
    ! [B_135] :
      ( k13_lattice3('#skF_3',B_135,'#skF_5') = k10_lattice3('#skF_3',B_135,'#skF_5')
      | ~ m1_subset_1(B_135,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_169])).

tff(c_203,plain,(
    ! [B_140] :
      ( k13_lattice3('#skF_3',B_140,'#skF_5') = k10_lattice3('#skF_3',B_140,'#skF_5')
      | ~ m1_subset_1(B_140,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_175])).

tff(c_225,plain,(
    k13_lattice3('#skF_3','#skF_4','#skF_5') = k10_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_203])).

tff(c_44,plain,(
    k12_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_230,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_44])).

tff(c_626,plain,(
    k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_230])).

tff(c_64,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_60])).

tff(c_70,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_64])).

tff(c_81,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_70])).

tff(c_589,plain,(
    ! [A_152,B_153,C_154] :
      ( r1_orders_2(A_152,B_153,k10_lattice3(A_152,B_153,C_154))
      | ~ m1_subset_1(k10_lattice3(A_152,B_153,C_154),u1_struct_0(A_152))
      | ~ m1_subset_1(C_154,u1_struct_0(A_152))
      | ~ m1_subset_1(B_153,u1_struct_0(A_152))
      | ~ l1_orders_2(A_152)
      | ~ v1_lattice3(A_152)
      | ~ v5_orders_2(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_599,plain,
    ( r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_266,c_589])).

tff(c_620,plain,
    ( r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_48,c_46,c_599])).

tff(c_621,plain,(
    r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_620])).

tff(c_28,plain,(
    ! [A_57,B_81,C_93,D_99] :
      ( r1_orders_2(A_57,'#skF_2'(A_57,B_81,C_93,D_99),B_81)
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
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1679,plain,(
    ! [A_186,B_187,C_188,D_189] :
      ( ~ r1_orders_2(A_186,'#skF_2'(A_186,B_187,C_188,D_189),D_189)
      | k11_lattice3(A_186,B_187,C_188) = D_189
      | ~ r1_orders_2(A_186,D_189,C_188)
      | ~ r1_orders_2(A_186,D_189,B_187)
      | ~ m1_subset_1(D_189,u1_struct_0(A_186))
      | ~ m1_subset_1(C_188,u1_struct_0(A_186))
      | ~ m1_subset_1(B_187,u1_struct_0(A_186))
      | ~ l1_orders_2(A_186)
      | ~ v2_lattice3(A_186)
      | ~ v5_orders_2(A_186)
      | v2_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_5309,plain,(
    ! [A_242,B_243,C_244] :
      ( k11_lattice3(A_242,B_243,C_244) = B_243
      | ~ r1_orders_2(A_242,B_243,C_244)
      | ~ r1_orders_2(A_242,B_243,B_243)
      | ~ m1_subset_1(C_244,u1_struct_0(A_242))
      | ~ m1_subset_1(B_243,u1_struct_0(A_242))
      | ~ l1_orders_2(A_242)
      | ~ v2_lattice3(A_242)
      | ~ v5_orders_2(A_242)
      | v2_struct_0(A_242) ) ),
    inference(resolution,[status(thm)],[c_28,c_1679])).

tff(c_5421,plain,
    ( k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4'
    | ~ r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_621,c_5309])).

tff(c_5626,plain,
    ( k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_48,c_266,c_81,c_5421])).

tff(c_5628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_626,c_5626])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:33:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.69/2.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.69/2.65  
% 7.69/2.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.69/2.65  %$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.69/2.65  
% 7.69/2.65  %Foreground sorts:
% 7.69/2.65  
% 7.69/2.65  
% 7.69/2.65  %Background operators:
% 7.69/2.65  
% 7.69/2.65  
% 7.69/2.65  %Foreground operators:
% 7.69/2.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.69/2.65  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.69/2.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.69/2.65  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 7.69/2.65  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 7.69/2.65  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 7.69/2.65  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 7.69/2.65  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 7.69/2.65  tff('#skF_5', type, '#skF_5': $i).
% 7.69/2.65  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 7.69/2.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.69/2.65  tff('#skF_3', type, '#skF_3': $i).
% 7.69/2.65  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 7.69/2.65  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.69/2.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.69/2.65  tff('#skF_4', type, '#skF_4': $i).
% 7.69/2.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.69/2.65  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 7.69/2.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 7.69/2.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.69/2.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.69/2.65  
% 7.96/2.67  tff(f_183, negated_conjecture, ~(![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k12_lattice3(A, B, k13_lattice3(A, B, C)) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_lattice3)).
% 7.96/2.67  tff(f_37, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 7.96/2.67  tff(f_44, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 7.96/2.67  tff(f_164, axiom, (![A]: (((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k10_lattice3(A, B, C) = k10_lattice3(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_lattice3)).
% 7.96/2.67  tff(f_52, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k10_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_lattice3)).
% 7.96/2.67  tff(f_138, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 7.96/2.67  tff(f_150, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 7.96/2.67  tff(f_93, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l26_lattice3)).
% 7.96/2.67  tff(f_126, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 7.96/2.67  tff(c_50, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.96/2.67  tff(c_54, plain, (v1_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.96/2.67  tff(c_58, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.96/2.67  tff(c_46, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.96/2.67  tff(c_60, plain, (![A_121, B_122]: (r1_orders_2(A_121, B_122, B_122) | ~m1_subset_1(B_122, u1_struct_0(A_121)) | ~l1_orders_2(A_121) | ~v3_orders_2(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.96/2.67  tff(c_62, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5') | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_60])).
% 7.96/2.67  tff(c_67, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50, c_62])).
% 7.96/2.67  tff(c_71, plain, (v2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_67])).
% 7.96/2.67  tff(c_4, plain, (![A_4]: (~v2_struct_0(A_4) | ~v1_lattice3(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.96/2.67  tff(c_74, plain, (~v1_lattice3('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_71, c_4])).
% 7.96/2.67  tff(c_78, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_74])).
% 7.96/2.67  tff(c_80, plain, (~v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_67])).
% 7.96/2.67  tff(c_48, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.96/2.67  tff(c_56, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.96/2.67  tff(c_52, plain, (v2_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.96/2.67  tff(c_186, plain, (![A_137, C_138, B_139]: (k10_lattice3(A_137, C_138, B_139)=k10_lattice3(A_137, B_139, C_138) | ~m1_subset_1(C_138, u1_struct_0(A_137)) | ~m1_subset_1(B_139, u1_struct_0(A_137)) | ~l1_orders_2(A_137) | ~v1_lattice3(A_137) | ~v5_orders_2(A_137))), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.96/2.67  tff(c_194, plain, (![B_139]: (k10_lattice3('#skF_3', B_139, '#skF_4')=k10_lattice3('#skF_3', '#skF_4', B_139) | ~m1_subset_1(B_139, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_186])).
% 7.96/2.67  tff(c_235, plain, (![B_141]: (k10_lattice3('#skF_3', B_141, '#skF_4')=k10_lattice3('#skF_3', '#skF_4', B_141) | ~m1_subset_1(B_141, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_194])).
% 7.96/2.67  tff(c_256, plain, (k10_lattice3('#skF_3', '#skF_5', '#skF_4')=k10_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_235])).
% 7.96/2.67  tff(c_6, plain, (![A_5, B_6, C_7]: (m1_subset_1(k10_lattice3(A_5, B_6, C_7), u1_struct_0(A_5)) | ~m1_subset_1(C_7, u1_struct_0(A_5)) | ~m1_subset_1(B_6, u1_struct_0(A_5)) | ~l1_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.96/2.67  tff(c_262, plain, (m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_256, c_6])).
% 7.96/2.67  tff(c_266, plain, (m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_48, c_262])).
% 7.96/2.67  tff(c_38, plain, (![A_103, B_104, C_105]: (k12_lattice3(A_103, B_104, C_105)=k11_lattice3(A_103, B_104, C_105) | ~m1_subset_1(C_105, u1_struct_0(A_103)) | ~m1_subset_1(B_104, u1_struct_0(A_103)) | ~l1_orders_2(A_103) | ~v2_lattice3(A_103) | ~v5_orders_2(A_103))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.96/2.67  tff(c_285, plain, (![B_104]: (k12_lattice3('#skF_3', B_104, k10_lattice3('#skF_3', '#skF_4', '#skF_5'))=k11_lattice3('#skF_3', B_104, k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(B_104, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_266, c_38])).
% 7.96/2.67  tff(c_550, plain, (![B_151]: (k12_lattice3('#skF_3', B_151, k10_lattice3('#skF_3', '#skF_4', '#skF_5'))=k11_lattice3('#skF_3', B_151, k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(B_151, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_285])).
% 7.96/2.67  tff(c_584, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_550])).
% 7.96/2.67  tff(c_169, plain, (![A_134, B_135, C_136]: (k13_lattice3(A_134, B_135, C_136)=k10_lattice3(A_134, B_135, C_136) | ~m1_subset_1(C_136, u1_struct_0(A_134)) | ~m1_subset_1(B_135, u1_struct_0(A_134)) | ~l1_orders_2(A_134) | ~v1_lattice3(A_134) | ~v5_orders_2(A_134))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.96/2.67  tff(c_175, plain, (![B_135]: (k13_lattice3('#skF_3', B_135, '#skF_5')=k10_lattice3('#skF_3', B_135, '#skF_5') | ~m1_subset_1(B_135, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_169])).
% 7.96/2.67  tff(c_203, plain, (![B_140]: (k13_lattice3('#skF_3', B_140, '#skF_5')=k10_lattice3('#skF_3', B_140, '#skF_5') | ~m1_subset_1(B_140, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_175])).
% 7.96/2.67  tff(c_225, plain, (k13_lattice3('#skF_3', '#skF_4', '#skF_5')=k10_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_203])).
% 7.96/2.67  tff(c_44, plain, (k12_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.96/2.67  tff(c_230, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_225, c_44])).
% 7.96/2.67  tff(c_626, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_584, c_230])).
% 7.96/2.67  tff(c_64, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_60])).
% 7.96/2.67  tff(c_70, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50, c_64])).
% 7.96/2.67  tff(c_81, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_80, c_70])).
% 7.96/2.67  tff(c_589, plain, (![A_152, B_153, C_154]: (r1_orders_2(A_152, B_153, k10_lattice3(A_152, B_153, C_154)) | ~m1_subset_1(k10_lattice3(A_152, B_153, C_154), u1_struct_0(A_152)) | ~m1_subset_1(C_154, u1_struct_0(A_152)) | ~m1_subset_1(B_153, u1_struct_0(A_152)) | ~l1_orders_2(A_152) | ~v1_lattice3(A_152) | ~v5_orders_2(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.96/2.67  tff(c_599, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_266, c_589])).
% 7.96/2.67  tff(c_620, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_48, c_46, c_599])).
% 7.96/2.67  tff(c_621, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_620])).
% 7.96/2.67  tff(c_28, plain, (![A_57, B_81, C_93, D_99]: (r1_orders_2(A_57, '#skF_2'(A_57, B_81, C_93, D_99), B_81) | k11_lattice3(A_57, B_81, C_93)=D_99 | ~r1_orders_2(A_57, D_99, C_93) | ~r1_orders_2(A_57, D_99, B_81) | ~m1_subset_1(D_99, u1_struct_0(A_57)) | ~m1_subset_1(C_93, u1_struct_0(A_57)) | ~m1_subset_1(B_81, u1_struct_0(A_57)) | ~l1_orders_2(A_57) | ~v2_lattice3(A_57) | ~v5_orders_2(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.96/2.67  tff(c_1679, plain, (![A_186, B_187, C_188, D_189]: (~r1_orders_2(A_186, '#skF_2'(A_186, B_187, C_188, D_189), D_189) | k11_lattice3(A_186, B_187, C_188)=D_189 | ~r1_orders_2(A_186, D_189, C_188) | ~r1_orders_2(A_186, D_189, B_187) | ~m1_subset_1(D_189, u1_struct_0(A_186)) | ~m1_subset_1(C_188, u1_struct_0(A_186)) | ~m1_subset_1(B_187, u1_struct_0(A_186)) | ~l1_orders_2(A_186) | ~v2_lattice3(A_186) | ~v5_orders_2(A_186) | v2_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.96/2.67  tff(c_5309, plain, (![A_242, B_243, C_244]: (k11_lattice3(A_242, B_243, C_244)=B_243 | ~r1_orders_2(A_242, B_243, C_244) | ~r1_orders_2(A_242, B_243, B_243) | ~m1_subset_1(C_244, u1_struct_0(A_242)) | ~m1_subset_1(B_243, u1_struct_0(A_242)) | ~l1_orders_2(A_242) | ~v2_lattice3(A_242) | ~v5_orders_2(A_242) | v2_struct_0(A_242))), inference(resolution, [status(thm)], [c_28, c_1679])).
% 7.96/2.67  tff(c_5421, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_621, c_5309])).
% 7.96/2.67  tff(c_5626, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_48, c_266, c_81, c_5421])).
% 7.96/2.67  tff(c_5628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_626, c_5626])).
% 7.96/2.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.96/2.67  
% 7.96/2.67  Inference rules
% 7.96/2.67  ----------------------
% 7.96/2.67  #Ref     : 0
% 7.96/2.67  #Sup     : 1241
% 7.96/2.67  #Fact    : 0
% 7.96/2.67  #Define  : 0
% 7.96/2.67  #Split   : 4
% 7.96/2.67  #Chain   : 0
% 7.96/2.67  #Close   : 0
% 7.96/2.67  
% 7.96/2.67  Ordering : KBO
% 7.96/2.67  
% 7.96/2.67  Simplification rules
% 7.96/2.67  ----------------------
% 7.96/2.67  #Subsume      : 5
% 7.96/2.67  #Demod        : 1986
% 7.96/2.67  #Tautology    : 281
% 7.96/2.67  #SimpNegUnit  : 317
% 7.96/2.67  #BackRed      : 18
% 7.96/2.67  
% 7.96/2.67  #Partial instantiations: 0
% 7.96/2.67  #Strategies tried      : 1
% 7.96/2.67  
% 7.96/2.67  Timing (in seconds)
% 7.96/2.67  ----------------------
% 7.96/2.67  Preprocessing        : 0.38
% 7.96/2.67  Parsing              : 0.20
% 7.96/2.67  CNF conversion       : 0.03
% 7.96/2.67  Main loop            : 1.49
% 7.96/2.67  Inferencing          : 0.38
% 7.96/2.67  Reduction            : 0.64
% 7.96/2.67  Demodulation         : 0.50
% 7.96/2.67  BG Simplification    : 0.06
% 7.96/2.67  Subsumption          : 0.31
% 7.96/2.67  Abstraction          : 0.08
% 7.96/2.67  MUC search           : 0.00
% 7.96/2.67  Cooper               : 0.00
% 7.96/2.67  Total                : 1.91
% 7.96/2.67  Index Insertion      : 0.00
% 7.96/2.67  Index Deletion       : 0.00
% 7.96/2.67  Index Matching       : 0.00
% 7.96/2.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
