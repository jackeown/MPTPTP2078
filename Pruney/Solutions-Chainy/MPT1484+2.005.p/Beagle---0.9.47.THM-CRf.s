%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:40 EST 2020

% Result     : Theorem 5.90s
% Output     : CNFRefutation 5.90s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 252 expanded)
%              Number of leaves         :   31 ( 110 expanded)
%              Depth                    :   14
%              Number of atoms          :  229 (1037 expanded)
%              Number of equality atoms :   24 ( 109 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

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

tff(f_181,negated_conjecture,(
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
               => k13_lattice3(A,k12_lattice3(A,B,C),C) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattice3)).

tff(f_150,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k12_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k12_lattice3)).

tff(f_162,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_138,axiom,(
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

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_105,axiom,(
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

tff(c_56,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_52,plain,(
    v2_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_50,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_100,plain,(
    ! [A_123,B_124,C_125] :
      ( k12_lattice3(A_123,B_124,C_125) = k11_lattice3(A_123,B_124,C_125)
      | ~ m1_subset_1(C_125,u1_struct_0(A_123))
      | ~ m1_subset_1(B_124,u1_struct_0(A_123))
      | ~ l1_orders_2(A_123)
      | ~ v2_lattice3(A_123)
      | ~ v5_orders_2(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_104,plain,(
    ! [B_124] :
      ( k12_lattice3('#skF_3',B_124,'#skF_5') = k11_lattice3('#skF_3',B_124,'#skF_5')
      | ~ m1_subset_1(B_124,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_100])).

tff(c_114,plain,(
    ! [B_126] :
      ( k12_lattice3('#skF_3',B_126,'#skF_5') = k11_lattice3('#skF_3',B_126,'#skF_5')
      | ~ m1_subset_1(B_126,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_104])).

tff(c_129,plain,(
    k12_lattice3('#skF_3','#skF_4','#skF_5') = k11_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_114])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k12_lattice3(A_8,B_9,C_10),u1_struct_0(A_8))
      | ~ m1_subset_1(C_10,u1_struct_0(A_8))
      | ~ m1_subset_1(B_9,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8)
      | ~ v2_lattice3(A_8)
      | ~ v5_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_177,plain,
    ( m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_10])).

tff(c_185,plain,(
    m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_48,c_46,c_177])).

tff(c_54,plain,(
    v1_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_205,plain,(
    ! [A_127,B_128,C_129] :
      ( k13_lattice3(A_127,B_128,C_129) = k10_lattice3(A_127,B_128,C_129)
      | ~ m1_subset_1(C_129,u1_struct_0(A_127))
      | ~ m1_subset_1(B_128,u1_struct_0(A_127))
      | ~ l1_orders_2(A_127)
      | ~ v1_lattice3(A_127)
      | ~ v5_orders_2(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_213,plain,(
    ! [B_128] :
      ( k13_lattice3('#skF_3',B_128,'#skF_5') = k10_lattice3('#skF_3',B_128,'#skF_5')
      | ~ m1_subset_1(B_128,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_205])).

tff(c_230,plain,(
    ! [B_130] :
      ( k13_lattice3('#skF_3',B_130,'#skF_5') = k10_lattice3('#skF_3',B_130,'#skF_5')
      | ~ m1_subset_1(B_130,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_213])).

tff(c_247,plain,(
    k13_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') = k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_185,c_230])).

tff(c_44,plain,(
    k13_lattice3('#skF_3',k12_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_167,plain,(
    k13_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_44])).

tff(c_770,plain,(
    k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_167])).

tff(c_58,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_60,plain,(
    ! [A_114,B_115,C_116] :
      ( r3_orders_2(A_114,B_115,B_115)
      | ~ m1_subset_1(C_116,u1_struct_0(A_114))
      | ~ m1_subset_1(B_115,u1_struct_0(A_114))
      | ~ l1_orders_2(A_114)
      | ~ v3_orders_2(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_62,plain,(
    ! [B_115] :
      ( r3_orders_2('#skF_3',B_115,B_115)
      | ~ m1_subset_1(B_115,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_60])).

tff(c_67,plain,(
    ! [B_115] :
      ( r3_orders_2('#skF_3',B_115,B_115)
      | ~ m1_subset_1(B_115,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_62])).

tff(c_71,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ v2_struct_0(A_7)
      | ~ v1_lattice3(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_74,plain,
    ( ~ v1_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_8])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_74])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_515,plain,(
    ! [A_139,B_140,C_141] :
      ( r1_orders_2(A_139,k11_lattice3(A_139,B_140,C_141),C_141)
      | ~ m1_subset_1(k11_lattice3(A_139,B_140,C_141),u1_struct_0(A_139))
      | ~ m1_subset_1(C_141,u1_struct_0(A_139))
      | ~ m1_subset_1(B_140,u1_struct_0(A_139))
      | ~ l1_orders_2(A_139)
      | ~ v2_lattice3(A_139)
      | ~ v5_orders_2(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_521,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_185,c_515])).

tff(c_534,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_48,c_46,c_521])).

tff(c_535,plain,(
    r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_534])).

tff(c_81,plain,(
    ! [B_117] :
      ( r3_orders_2('#skF_3',B_117,B_117)
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_86,plain,(
    r3_orders_2('#skF_3','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_81])).

tff(c_264,plain,(
    ! [A_131,B_132,C_133] :
      ( r1_orders_2(A_131,B_132,C_133)
      | ~ r3_orders_2(A_131,B_132,C_133)
      | ~ m1_subset_1(C_133,u1_struct_0(A_131))
      | ~ m1_subset_1(B_132,u1_struct_0(A_131))
      | ~ l1_orders_2(A_131)
      | ~ v3_orders_2(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_274,plain,
    ( r1_orders_2('#skF_3','#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_264])).

tff(c_293,plain,
    ( r1_orders_2('#skF_3','#skF_5','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_46,c_274])).

tff(c_294,plain,(
    r1_orders_2('#skF_3','#skF_5','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_293])).

tff(c_14,plain,(
    ! [A_11,C_47,B_35,D_53] :
      ( r1_orders_2(A_11,C_47,'#skF_1'(A_11,B_35,C_47,D_53))
      | k10_lattice3(A_11,B_35,C_47) = D_53
      | ~ r1_orders_2(A_11,C_47,D_53)
      | ~ r1_orders_2(A_11,B_35,D_53)
      | ~ m1_subset_1(D_53,u1_struct_0(A_11))
      | ~ m1_subset_1(C_47,u1_struct_0(A_11))
      | ~ m1_subset_1(B_35,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11)
      | ~ v1_lattice3(A_11)
      | ~ v5_orders_2(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1501,plain,(
    ! [A_173,D_174,B_175,C_176] :
      ( ~ r1_orders_2(A_173,D_174,'#skF_1'(A_173,B_175,C_176,D_174))
      | k10_lattice3(A_173,B_175,C_176) = D_174
      | ~ r1_orders_2(A_173,C_176,D_174)
      | ~ r1_orders_2(A_173,B_175,D_174)
      | ~ m1_subset_1(D_174,u1_struct_0(A_173))
      | ~ m1_subset_1(C_176,u1_struct_0(A_173))
      | ~ m1_subset_1(B_175,u1_struct_0(A_173))
      | ~ l1_orders_2(A_173)
      | ~ v1_lattice3(A_173)
      | ~ v5_orders_2(A_173)
      | v2_struct_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3388,plain,(
    ! [A_207,B_208,D_209] :
      ( k10_lattice3(A_207,B_208,D_209) = D_209
      | ~ r1_orders_2(A_207,D_209,D_209)
      | ~ r1_orders_2(A_207,B_208,D_209)
      | ~ m1_subset_1(D_209,u1_struct_0(A_207))
      | ~ m1_subset_1(B_208,u1_struct_0(A_207))
      | ~ l1_orders_2(A_207)
      | ~ v1_lattice3(A_207)
      | ~ v5_orders_2(A_207)
      | v2_struct_0(A_207) ) ),
    inference(resolution,[status(thm)],[c_14,c_1501])).

tff(c_3396,plain,(
    ! [B_208] :
      ( k10_lattice3('#skF_3',B_208,'#skF_5') = '#skF_5'
      | ~ r1_orders_2('#skF_3',B_208,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_208,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_294,c_3388])).

tff(c_3413,plain,(
    ! [B_208] :
      ( k10_lattice3('#skF_3',B_208,'#skF_5') = '#skF_5'
      | ~ r1_orders_2('#skF_3',B_208,'#skF_5')
      | ~ m1_subset_1(B_208,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_46,c_3396])).

tff(c_3768,plain,(
    ! [B_221] :
      ( k10_lattice3('#skF_3',B_221,'#skF_5') = '#skF_5'
      | ~ r1_orders_2('#skF_3',B_221,'#skF_5')
      | ~ m1_subset_1(B_221,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_3413])).

tff(c_3782,plain,
    ( k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') = '#skF_5'
    | ~ r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_185,c_3768])).

tff(c_3806,plain,(
    k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_3782])).

tff(c_3808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_770,c_3806])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.90/2.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.19  
% 5.90/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.19  %$ r3_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.90/2.19  
% 5.90/2.19  %Foreground sorts:
% 5.90/2.19  
% 5.90/2.19  
% 5.90/2.19  %Background operators:
% 5.90/2.19  
% 5.90/2.19  
% 5.90/2.19  %Foreground operators:
% 5.90/2.19  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.90/2.19  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 5.90/2.19  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.90/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.90/2.19  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 5.90/2.19  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.90/2.19  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 5.90/2.19  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 5.90/2.19  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 5.90/2.19  tff('#skF_5', type, '#skF_5': $i).
% 5.90/2.19  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 5.90/2.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.90/2.19  tff('#skF_3', type, '#skF_3': $i).
% 5.90/2.19  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.90/2.19  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.90/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.90/2.19  tff('#skF_4', type, '#skF_4': $i).
% 5.90/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.90/2.19  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 5.90/2.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.90/2.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.90/2.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.90/2.19  
% 5.90/2.21  tff(f_181, negated_conjecture, ~(![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k13_lattice3(A, k12_lattice3(A, B, C), C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_lattice3)).
% 5.90/2.21  tff(f_150, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 5.90/2.21  tff(f_72, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k12_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k12_lattice3)).
% 5.90/2.21  tff(f_162, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 5.90/2.21  tff(f_53, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_orders_2(A, B, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 5.90/2.21  tff(f_60, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 5.90/2.21  tff(f_138, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 5.90/2.21  tff(f_40, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 5.90/2.21  tff(f_105, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l26_lattice3)).
% 5.90/2.21  tff(c_56, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.90/2.21  tff(c_52, plain, (v2_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.90/2.21  tff(c_50, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.90/2.21  tff(c_48, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.90/2.21  tff(c_46, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.90/2.21  tff(c_100, plain, (![A_123, B_124, C_125]: (k12_lattice3(A_123, B_124, C_125)=k11_lattice3(A_123, B_124, C_125) | ~m1_subset_1(C_125, u1_struct_0(A_123)) | ~m1_subset_1(B_124, u1_struct_0(A_123)) | ~l1_orders_2(A_123) | ~v2_lattice3(A_123) | ~v5_orders_2(A_123))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.90/2.21  tff(c_104, plain, (![B_124]: (k12_lattice3('#skF_3', B_124, '#skF_5')=k11_lattice3('#skF_3', B_124, '#skF_5') | ~m1_subset_1(B_124, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_100])).
% 5.90/2.21  tff(c_114, plain, (![B_126]: (k12_lattice3('#skF_3', B_126, '#skF_5')=k11_lattice3('#skF_3', B_126, '#skF_5') | ~m1_subset_1(B_126, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_104])).
% 5.90/2.21  tff(c_129, plain, (k12_lattice3('#skF_3', '#skF_4', '#skF_5')=k11_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_114])).
% 5.90/2.21  tff(c_10, plain, (![A_8, B_9, C_10]: (m1_subset_1(k12_lattice3(A_8, B_9, C_10), u1_struct_0(A_8)) | ~m1_subset_1(C_10, u1_struct_0(A_8)) | ~m1_subset_1(B_9, u1_struct_0(A_8)) | ~l1_orders_2(A_8) | ~v2_lattice3(A_8) | ~v5_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.90/2.21  tff(c_177, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_129, c_10])).
% 5.90/2.21  tff(c_185, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_48, c_46, c_177])).
% 5.90/2.21  tff(c_54, plain, (v1_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.90/2.21  tff(c_205, plain, (![A_127, B_128, C_129]: (k13_lattice3(A_127, B_128, C_129)=k10_lattice3(A_127, B_128, C_129) | ~m1_subset_1(C_129, u1_struct_0(A_127)) | ~m1_subset_1(B_128, u1_struct_0(A_127)) | ~l1_orders_2(A_127) | ~v1_lattice3(A_127) | ~v5_orders_2(A_127))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.90/2.21  tff(c_213, plain, (![B_128]: (k13_lattice3('#skF_3', B_128, '#skF_5')=k10_lattice3('#skF_3', B_128, '#skF_5') | ~m1_subset_1(B_128, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_205])).
% 5.90/2.21  tff(c_230, plain, (![B_130]: (k13_lattice3('#skF_3', B_130, '#skF_5')=k10_lattice3('#skF_3', B_130, '#skF_5') | ~m1_subset_1(B_130, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_213])).
% 5.90/2.21  tff(c_247, plain, (k13_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')=k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_185, c_230])).
% 5.90/2.21  tff(c_44, plain, (k13_lattice3('#skF_3', k12_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.90/2.21  tff(c_167, plain, (k13_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_44])).
% 5.90/2.21  tff(c_770, plain, (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_247, c_167])).
% 5.90/2.21  tff(c_58, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.90/2.21  tff(c_60, plain, (![A_114, B_115, C_116]: (r3_orders_2(A_114, B_115, B_115) | ~m1_subset_1(C_116, u1_struct_0(A_114)) | ~m1_subset_1(B_115, u1_struct_0(A_114)) | ~l1_orders_2(A_114) | ~v3_orders_2(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.90/2.21  tff(c_62, plain, (![B_115]: (r3_orders_2('#skF_3', B_115, B_115) | ~m1_subset_1(B_115, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_60])).
% 5.90/2.21  tff(c_67, plain, (![B_115]: (r3_orders_2('#skF_3', B_115, B_115) | ~m1_subset_1(B_115, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50, c_62])).
% 5.90/2.21  tff(c_71, plain, (v2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_67])).
% 5.90/2.21  tff(c_8, plain, (![A_7]: (~v2_struct_0(A_7) | ~v1_lattice3(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.90/2.21  tff(c_74, plain, (~v1_lattice3('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_71, c_8])).
% 5.90/2.21  tff(c_78, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_74])).
% 5.90/2.21  tff(c_80, plain, (~v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_67])).
% 5.90/2.21  tff(c_515, plain, (![A_139, B_140, C_141]: (r1_orders_2(A_139, k11_lattice3(A_139, B_140, C_141), C_141) | ~m1_subset_1(k11_lattice3(A_139, B_140, C_141), u1_struct_0(A_139)) | ~m1_subset_1(C_141, u1_struct_0(A_139)) | ~m1_subset_1(B_140, u1_struct_0(A_139)) | ~l1_orders_2(A_139) | ~v2_lattice3(A_139) | ~v5_orders_2(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.90/2.21  tff(c_521, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_185, c_515])).
% 5.90/2.21  tff(c_534, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_48, c_46, c_521])).
% 5.90/2.21  tff(c_535, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80, c_534])).
% 5.90/2.21  tff(c_81, plain, (![B_117]: (r3_orders_2('#skF_3', B_117, B_117) | ~m1_subset_1(B_117, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_67])).
% 5.90/2.21  tff(c_86, plain, (r3_orders_2('#skF_3', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_81])).
% 5.90/2.21  tff(c_264, plain, (![A_131, B_132, C_133]: (r1_orders_2(A_131, B_132, C_133) | ~r3_orders_2(A_131, B_132, C_133) | ~m1_subset_1(C_133, u1_struct_0(A_131)) | ~m1_subset_1(B_132, u1_struct_0(A_131)) | ~l1_orders_2(A_131) | ~v3_orders_2(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.90/2.21  tff(c_274, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_86, c_264])).
% 5.90/2.21  tff(c_293, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50, c_46, c_274])).
% 5.90/2.21  tff(c_294, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80, c_293])).
% 5.90/2.21  tff(c_14, plain, (![A_11, C_47, B_35, D_53]: (r1_orders_2(A_11, C_47, '#skF_1'(A_11, B_35, C_47, D_53)) | k10_lattice3(A_11, B_35, C_47)=D_53 | ~r1_orders_2(A_11, C_47, D_53) | ~r1_orders_2(A_11, B_35, D_53) | ~m1_subset_1(D_53, u1_struct_0(A_11)) | ~m1_subset_1(C_47, u1_struct_0(A_11)) | ~m1_subset_1(B_35, u1_struct_0(A_11)) | ~l1_orders_2(A_11) | ~v1_lattice3(A_11) | ~v5_orders_2(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.90/2.21  tff(c_1501, plain, (![A_173, D_174, B_175, C_176]: (~r1_orders_2(A_173, D_174, '#skF_1'(A_173, B_175, C_176, D_174)) | k10_lattice3(A_173, B_175, C_176)=D_174 | ~r1_orders_2(A_173, C_176, D_174) | ~r1_orders_2(A_173, B_175, D_174) | ~m1_subset_1(D_174, u1_struct_0(A_173)) | ~m1_subset_1(C_176, u1_struct_0(A_173)) | ~m1_subset_1(B_175, u1_struct_0(A_173)) | ~l1_orders_2(A_173) | ~v1_lattice3(A_173) | ~v5_orders_2(A_173) | v2_struct_0(A_173))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.90/2.21  tff(c_3388, plain, (![A_207, B_208, D_209]: (k10_lattice3(A_207, B_208, D_209)=D_209 | ~r1_orders_2(A_207, D_209, D_209) | ~r1_orders_2(A_207, B_208, D_209) | ~m1_subset_1(D_209, u1_struct_0(A_207)) | ~m1_subset_1(B_208, u1_struct_0(A_207)) | ~l1_orders_2(A_207) | ~v1_lattice3(A_207) | ~v5_orders_2(A_207) | v2_struct_0(A_207))), inference(resolution, [status(thm)], [c_14, c_1501])).
% 5.90/2.21  tff(c_3396, plain, (![B_208]: (k10_lattice3('#skF_3', B_208, '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', B_208, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1(B_208, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_294, c_3388])).
% 5.90/2.21  tff(c_3413, plain, (![B_208]: (k10_lattice3('#skF_3', B_208, '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', B_208, '#skF_5') | ~m1_subset_1(B_208, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_46, c_3396])).
% 5.90/2.21  tff(c_3768, plain, (![B_221]: (k10_lattice3('#skF_3', B_221, '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', B_221, '#skF_5') | ~m1_subset_1(B_221, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_80, c_3413])).
% 5.90/2.21  tff(c_3782, plain, (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_185, c_3768])).
% 5.90/2.21  tff(c_3806, plain, (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_535, c_3782])).
% 5.90/2.21  tff(c_3808, plain, $false, inference(negUnitSimplification, [status(thm)], [c_770, c_3806])).
% 5.90/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.21  
% 5.90/2.21  Inference rules
% 5.90/2.21  ----------------------
% 5.90/2.21  #Ref     : 0
% 5.90/2.21  #Sup     : 747
% 5.90/2.21  #Fact    : 0
% 5.90/2.21  #Define  : 0
% 5.90/2.21  #Split   : 7
% 5.90/2.21  #Chain   : 0
% 5.90/2.21  #Close   : 0
% 5.90/2.21  
% 5.90/2.21  Ordering : KBO
% 5.90/2.21  
% 5.90/2.21  Simplification rules
% 5.90/2.21  ----------------------
% 5.90/2.21  #Subsume      : 25
% 5.90/2.21  #Demod        : 2134
% 5.90/2.21  #Tautology    : 325
% 5.90/2.21  #SimpNegUnit  : 285
% 5.90/2.21  #BackRed      : 102
% 5.90/2.21  
% 5.90/2.21  #Partial instantiations: 0
% 5.90/2.21  #Strategies tried      : 1
% 5.90/2.21  
% 5.90/2.21  Timing (in seconds)
% 5.90/2.21  ----------------------
% 5.90/2.21  Preprocessing        : 0.37
% 5.90/2.21  Parsing              : 0.19
% 5.90/2.21  CNF conversion       : 0.03
% 5.90/2.21  Main loop            : 1.07
% 5.90/2.21  Inferencing          : 0.29
% 5.90/2.21  Reduction            : 0.44
% 5.90/2.21  Demodulation         : 0.33
% 5.90/2.21  BG Simplification    : 0.04
% 5.90/2.21  Subsumption          : 0.22
% 5.90/2.21  Abstraction          : 0.06
% 5.90/2.21  MUC search           : 0.00
% 5.90/2.21  Cooper               : 0.00
% 5.90/2.21  Total                : 1.47
% 5.90/2.21  Index Insertion      : 0.00
% 5.90/2.21  Index Deletion       : 0.00
% 5.90/2.21  Index Matching       : 0.00
% 5.90/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
