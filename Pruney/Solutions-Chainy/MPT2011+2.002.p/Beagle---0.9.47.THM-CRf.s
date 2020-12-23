%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:08 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 245 expanded)
%              Number of leaves         :   31 (  98 expanded)
%              Depth                    :   14
%              Number of atoms          :  293 (1163 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_waybel_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_waybel_2 > k11_lattice3 > u1_waybel_0 > k1_funct_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_waybel_0,type,(
    v6_waybel_0: ( $i * $i ) > $o )).

tff(k3_waybel_2,type,(
    k3_waybel_2: ( $i * $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_157,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & v4_orders_2(C)
                  & v7_waybel_0(C)
                  & l1_waybel_0(C,A) )
               => ( ~ v2_struct_0(k3_waybel_2(A,B,C))
                  & v4_orders_2(k3_waybel_2(A,B,C))
                  & v7_waybel_0(k3_waybel_2(A,B,C))
                  & l1_waybel_0(k3_waybel_2(A,B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_9)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & ~ v2_struct_0(C)
        & v7_waybel_0(C)
        & l1_waybel_0(C,A) )
     => ( v6_waybel_0(k3_waybel_2(A,B,C),A)
        & v7_waybel_0(k3_waybel_2(A,B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_waybel_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & ~ v2_struct_0(C)
        & l1_waybel_0(C,A) )
     => ( v6_waybel_0(k3_waybel_2(A,B,C),A)
        & l1_waybel_0(k3_waybel_2(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_waybel_2)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & ~ v2_struct_0(C)
        & l1_waybel_0(C,A) )
     => ( ~ v2_struct_0(k3_waybel_2(A,B,C))
        & v6_waybel_0(k3_waybel_2(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_waybel_2)).

tff(f_45,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ( v4_orders_2(A)
      <=> v4_orders_2(g1_orders_2(u1_struct_0(A),u1_orders_2(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l16_yellow_6)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & l1_waybel_0(C,A) )
             => ! [D] :
                  ( ( v6_waybel_0(D,A)
                    & l1_waybel_0(D,A) )
                 => ( D = k3_waybel_2(A,B,C)
                  <=> ( g1_orders_2(u1_struct_0(D),u1_orders_2(D)) = g1_orders_2(u1_struct_0(C),u1_orders_2(C))
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(D))
                         => ? [F] :
                              ( m1_subset_1(F,u1_struct_0(A))
                              & F = k1_funct_1(u1_waybel_0(A,C),E)
                              & k1_funct_1(u1_waybel_0(A,D),E) = k11_lattice3(A,B,F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_waybel_2)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_46,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_36,plain,(
    l1_waybel_0('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_38,plain,(
    v7_waybel_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_271,plain,(
    ! [A_212,B_213,C_214] :
      ( v7_waybel_0(k3_waybel_2(A_212,B_213,C_214))
      | ~ l1_waybel_0(C_214,A_212)
      | ~ v7_waybel_0(C_214)
      | v2_struct_0(C_214)
      | ~ m1_subset_1(B_213,u1_struct_0(A_212))
      | ~ l1_orders_2(A_212)
      | v2_struct_0(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_273,plain,(
    ! [C_214] :
      ( v7_waybel_0(k3_waybel_2('#skF_3','#skF_4',C_214))
      | ~ l1_waybel_0(C_214,'#skF_3')
      | ~ v7_waybel_0(C_214)
      | v2_struct_0(C_214)
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_271])).

tff(c_276,plain,(
    ! [C_214] :
      ( v7_waybel_0(k3_waybel_2('#skF_3','#skF_4',C_214))
      | ~ l1_waybel_0(C_214,'#skF_3')
      | ~ v7_waybel_0(C_214)
      | v2_struct_0(C_214)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_273])).

tff(c_278,plain,(
    ! [C_215] :
      ( v7_waybel_0(k3_waybel_2('#skF_3','#skF_4',C_215))
      | ~ l1_waybel_0(C_215,'#skF_3')
      | ~ v7_waybel_0(C_215)
      | v2_struct_0(C_215) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_276])).

tff(c_226,plain,(
    ! [A_197,B_198,C_199] :
      ( l1_waybel_0(k3_waybel_2(A_197,B_198,C_199),A_197)
      | ~ l1_waybel_0(C_199,A_197)
      | v2_struct_0(C_199)
      | ~ m1_subset_1(B_198,u1_struct_0(A_197))
      | ~ l1_orders_2(A_197)
      | v2_struct_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_228,plain,(
    ! [C_199] :
      ( l1_waybel_0(k3_waybel_2('#skF_3','#skF_4',C_199),'#skF_3')
      | ~ l1_waybel_0(C_199,'#skF_3')
      | v2_struct_0(C_199)
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_226])).

tff(c_231,plain,(
    ! [C_199] :
      ( l1_waybel_0(k3_waybel_2('#skF_3','#skF_4',C_199),'#skF_3')
      | ~ l1_waybel_0(C_199,'#skF_3')
      | v2_struct_0(C_199)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_228])).

tff(c_233,plain,(
    ! [C_200] :
      ( l1_waybel_0(k3_waybel_2('#skF_3','#skF_4',C_200),'#skF_3')
      | ~ l1_waybel_0(C_200,'#skF_3')
      | v2_struct_0(C_200) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_231])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_50,plain,(
    ! [B_129,A_130] :
      ( l1_orders_2(B_129)
      | ~ l1_waybel_0(B_129,A_130)
      | ~ l1_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_54,plain,
    ( l1_orders_2('#skF_5')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_50])).

tff(c_56,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_59,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_56])).

tff(c_63,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_59])).

tff(c_65,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_73,plain,(
    ! [A_136,B_137,C_138] :
      ( l1_waybel_0(k3_waybel_2(A_136,B_137,C_138),A_136)
      | ~ l1_waybel_0(C_138,A_136)
      | v2_struct_0(C_138)
      | ~ m1_subset_1(B_137,u1_struct_0(A_136))
      | ~ l1_orders_2(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_75,plain,(
    ! [C_138] :
      ( l1_waybel_0(k3_waybel_2('#skF_3','#skF_4',C_138),'#skF_3')
      | ~ l1_waybel_0(C_138,'#skF_3')
      | v2_struct_0(C_138)
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_73])).

tff(c_78,plain,(
    ! [C_138] :
      ( l1_waybel_0(k3_waybel_2('#skF_3','#skF_4',C_138),'#skF_3')
      | ~ l1_waybel_0(C_138,'#skF_3')
      | v2_struct_0(C_138)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_75])).

tff(c_80,plain,(
    ! [C_139] :
      ( l1_waybel_0(k3_waybel_2('#skF_3','#skF_4',C_139),'#skF_3')
      | ~ l1_waybel_0(C_139,'#skF_3')
      | v2_struct_0(C_139) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_78])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( l1_orders_2(B_4)
      | ~ l1_waybel_0(B_4,A_2)
      | ~ l1_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_83,plain,(
    ! [C_139] :
      ( l1_orders_2(k3_waybel_2('#skF_3','#skF_4',C_139))
      | ~ l1_struct_0('#skF_3')
      | ~ l1_waybel_0(C_139,'#skF_3')
      | v2_struct_0(C_139) ) ),
    inference(resolution,[status(thm)],[c_80,c_4])).

tff(c_86,plain,(
    ! [C_139] :
      ( l1_orders_2(k3_waybel_2('#skF_3','#skF_4',C_139))
      | ~ l1_waybel_0(C_139,'#skF_3')
      | v2_struct_0(C_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_83])).

tff(c_64,plain,(
    l1_orders_2('#skF_5') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_40,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_79,plain,(
    ! [C_138] :
      ( l1_waybel_0(k3_waybel_2('#skF_3','#skF_4',C_138),'#skF_3')
      | ~ l1_waybel_0(C_138,'#skF_3')
      | v2_struct_0(C_138) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_78])).

tff(c_26,plain,(
    ! [A_118,B_119,C_120] :
      ( v6_waybel_0(k3_waybel_2(A_118,B_119,C_120),A_118)
      | ~ l1_waybel_0(C_120,A_118)
      | v2_struct_0(C_120)
      | ~ m1_subset_1(B_119,u1_struct_0(A_118))
      | ~ l1_orders_2(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_8,plain,(
    ! [A_5] :
      ( v4_orders_2(g1_orders_2(u1_struct_0(A_5),u1_orders_2(A_5)))
      | ~ v4_orders_2(A_5)
      | ~ l1_orders_2(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_97,plain,(
    ! [A_148,B_149,C_150] :
      ( g1_orders_2(u1_struct_0(k3_waybel_2(A_148,B_149,C_150)),u1_orders_2(k3_waybel_2(A_148,B_149,C_150))) = g1_orders_2(u1_struct_0(C_150),u1_orders_2(C_150))
      | ~ l1_waybel_0(k3_waybel_2(A_148,B_149,C_150),A_148)
      | ~ v6_waybel_0(k3_waybel_2(A_148,B_149,C_150),A_148)
      | ~ l1_waybel_0(C_150,A_148)
      | v2_struct_0(C_150)
      | ~ m1_subset_1(B_149,u1_struct_0(A_148))
      | ~ l1_orders_2(A_148)
      | v2_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_5] :
      ( v4_orders_2(A_5)
      | ~ v4_orders_2(g1_orders_2(u1_struct_0(A_5),u1_orders_2(A_5)))
      | ~ l1_orders_2(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_150,plain,(
    ! [A_178,B_179,C_180] :
      ( v4_orders_2(k3_waybel_2(A_178,B_179,C_180))
      | ~ v4_orders_2(g1_orders_2(u1_struct_0(C_180),u1_orders_2(C_180)))
      | ~ l1_orders_2(k3_waybel_2(A_178,B_179,C_180))
      | v2_struct_0(k3_waybel_2(A_178,B_179,C_180))
      | ~ l1_waybel_0(k3_waybel_2(A_178,B_179,C_180),A_178)
      | ~ v6_waybel_0(k3_waybel_2(A_178,B_179,C_180),A_178)
      | ~ l1_waybel_0(C_180,A_178)
      | v2_struct_0(C_180)
      | ~ m1_subset_1(B_179,u1_struct_0(A_178))
      | ~ l1_orders_2(A_178)
      | v2_struct_0(A_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_6])).

tff(c_156,plain,(
    ! [A_181,B_182,A_183] :
      ( v4_orders_2(k3_waybel_2(A_181,B_182,A_183))
      | ~ l1_orders_2(k3_waybel_2(A_181,B_182,A_183))
      | v2_struct_0(k3_waybel_2(A_181,B_182,A_183))
      | ~ l1_waybel_0(k3_waybel_2(A_181,B_182,A_183),A_181)
      | ~ v6_waybel_0(k3_waybel_2(A_181,B_182,A_183),A_181)
      | ~ l1_waybel_0(A_183,A_181)
      | ~ m1_subset_1(B_182,u1_struct_0(A_181))
      | ~ l1_orders_2(A_181)
      | v2_struct_0(A_181)
      | ~ v4_orders_2(A_183)
      | ~ l1_orders_2(A_183)
      | v2_struct_0(A_183) ) ),
    inference(resolution,[status(thm)],[c_8,c_150])).

tff(c_161,plain,(
    ! [A_184,B_185,C_186] :
      ( v4_orders_2(k3_waybel_2(A_184,B_185,C_186))
      | ~ l1_orders_2(k3_waybel_2(A_184,B_185,C_186))
      | v2_struct_0(k3_waybel_2(A_184,B_185,C_186))
      | ~ l1_waybel_0(k3_waybel_2(A_184,B_185,C_186),A_184)
      | ~ v4_orders_2(C_186)
      | ~ l1_orders_2(C_186)
      | ~ l1_waybel_0(C_186,A_184)
      | v2_struct_0(C_186)
      | ~ m1_subset_1(B_185,u1_struct_0(A_184))
      | ~ l1_orders_2(A_184)
      | v2_struct_0(A_184) ) ),
    inference(resolution,[status(thm)],[c_26,c_156])).

tff(c_165,plain,(
    ! [C_138] :
      ( v4_orders_2(k3_waybel_2('#skF_3','#skF_4',C_138))
      | ~ l1_orders_2(k3_waybel_2('#skF_3','#skF_4',C_138))
      | v2_struct_0(k3_waybel_2('#skF_3','#skF_4',C_138))
      | ~ v4_orders_2(C_138)
      | ~ l1_orders_2(C_138)
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_waybel_0(C_138,'#skF_3')
      | v2_struct_0(C_138) ) ),
    inference(resolution,[status(thm)],[c_79,c_161])).

tff(c_169,plain,(
    ! [C_138] :
      ( v4_orders_2(k3_waybel_2('#skF_3','#skF_4',C_138))
      | ~ l1_orders_2(k3_waybel_2('#skF_3','#skF_4',C_138))
      | v2_struct_0(k3_waybel_2('#skF_3','#skF_4',C_138))
      | ~ v4_orders_2(C_138)
      | ~ l1_orders_2(C_138)
      | v2_struct_0('#skF_3')
      | ~ l1_waybel_0(C_138,'#skF_3')
      | v2_struct_0(C_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_165])).

tff(c_180,plain,(
    ! [C_191] :
      ( v4_orders_2(k3_waybel_2('#skF_3','#skF_4',C_191))
      | ~ l1_orders_2(k3_waybel_2('#skF_3','#skF_4',C_191))
      | v2_struct_0(k3_waybel_2('#skF_3','#skF_4',C_191))
      | ~ v4_orders_2(C_191)
      | ~ l1_orders_2(C_191)
      | ~ l1_waybel_0(C_191,'#skF_3')
      | v2_struct_0(C_191) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_169])).

tff(c_34,plain,
    ( ~ l1_waybel_0(k3_waybel_2('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0(k3_waybel_2('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2(k3_waybel_2('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0(k3_waybel_2('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_55,plain,(
    ~ v4_orders_2(k3_waybel_2('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_183,plain,
    ( ~ l1_orders_2(k3_waybel_2('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0(k3_waybel_2('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_5')
    | ~ l1_orders_2('#skF_5')
    | ~ l1_waybel_0('#skF_5','#skF_3')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_180,c_55])).

tff(c_186,plain,
    ( ~ l1_orders_2(k3_waybel_2('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0(k3_waybel_2('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_64,c_40,c_183])).

tff(c_187,plain,
    ( ~ l1_orders_2(k3_waybel_2('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0(k3_waybel_2('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_186])).

tff(c_188,plain,(
    ~ l1_orders_2(k3_waybel_2('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_191,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_3')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_188])).

tff(c_194,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_191])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_194])).

tff(c_197,plain,(
    v2_struct_0(k3_waybel_2('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_28,plain,(
    ! [A_118,B_119,C_120] :
      ( ~ v2_struct_0(k3_waybel_2(A_118,B_119,C_120))
      | ~ l1_waybel_0(C_120,A_118)
      | v2_struct_0(C_120)
      | ~ m1_subset_1(B_119,u1_struct_0(A_118))
      | ~ l1_orders_2(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_200,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_197,c_28])).

tff(c_203,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_36,c_200])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_203])).

tff(c_206,plain,
    ( ~ v7_waybel_0(k3_waybel_2('#skF_3','#skF_4','#skF_5'))
    | ~ l1_waybel_0(k3_waybel_2('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0(k3_waybel_2('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_224,plain,(
    ~ l1_waybel_0(k3_waybel_2('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_236,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_3')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_233,c_224])).

tff(c_242,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_236])).

tff(c_244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_242])).

tff(c_245,plain,
    ( ~ v7_waybel_0(k3_waybel_2('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0(k3_waybel_2('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_253,plain,(
    ~ v7_waybel_0(k3_waybel_2('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_281,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_3')
    | ~ v7_waybel_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_278,c_253])).

tff(c_284,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_281])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_284])).

tff(c_287,plain,(
    v2_struct_0(k3_waybel_2('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_289,plain,(
    ! [A_216,B_217,C_218] :
      ( ~ v2_struct_0(k3_waybel_2(A_216,B_217,C_218))
      | ~ l1_waybel_0(C_218,A_216)
      | v2_struct_0(C_218)
      | ~ m1_subset_1(B_217,u1_struct_0(A_216))
      | ~ l1_orders_2(A_216)
      | v2_struct_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_291,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_287,c_289])).

tff(c_294,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_36,c_291])).

tff(c_296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_294])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:31:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.36  
% 2.61/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.36  %$ v6_waybel_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_waybel_2 > k11_lattice3 > u1_waybel_0 > k1_funct_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.61/1.36  
% 2.61/1.36  %Foreground sorts:
% 2.61/1.36  
% 2.61/1.36  
% 2.61/1.36  %Background operators:
% 2.61/1.36  
% 2.61/1.36  
% 2.61/1.36  %Foreground operators:
% 2.61/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.36  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 2.61/1.36  tff(k3_waybel_2, type, k3_waybel_2: ($i * $i * $i) > $i).
% 2.61/1.36  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.61/1.36  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 2.61/1.36  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.61/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.61/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.61/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.36  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.61/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.61/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.61/1.36  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.61/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.61/1.36  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.36  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.61/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.36  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.61/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.61/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.36  
% 2.83/1.38  tff(f_157, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)) => (((~v2_struct_0(k3_waybel_2(A, B, C)) & v4_orders_2(k3_waybel_2(A, B, C))) & v7_waybel_0(k3_waybel_2(A, B, C))) & l1_waybel_0(k3_waybel_2(A, B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_waybel_9)).
% 2.83/1.38  tff(f_129, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & ~v2_struct_0(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)) => (v6_waybel_0(k3_waybel_2(A, B, C), A) & v7_waybel_0(k3_waybel_2(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_waybel_2)).
% 2.83/1.38  tff(f_94, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & ~v2_struct_0(C)) & l1_waybel_0(C, A)) => (v6_waybel_0(k3_waybel_2(A, B, C), A) & l1_waybel_0(k3_waybel_2(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_waybel_2)).
% 2.83/1.38  tff(f_29, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.83/1.38  tff(f_36, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 2.83/1.38  tff(f_111, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & ~v2_struct_0(C)) & l1_waybel_0(C, A)) => (~v2_struct_0(k3_waybel_2(A, B, C)) & v6_waybel_0(k3_waybel_2(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_waybel_2)).
% 2.83/1.38  tff(f_45, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (v4_orders_2(A) <=> v4_orders_2(g1_orders_2(u1_struct_0(A), u1_orders_2(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l16_yellow_6)).
% 2.83/1.38  tff(f_78, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((~v2_struct_0(C) & l1_waybel_0(C, A)) => (![D]: ((v6_waybel_0(D, A) & l1_waybel_0(D, A)) => ((D = k3_waybel_2(A, B, C)) <=> ((g1_orders_2(u1_struct_0(D), u1_orders_2(D)) = g1_orders_2(u1_struct_0(C), u1_orders_2(C))) & (![E]: (m1_subset_1(E, u1_struct_0(D)) => (?[F]: ((m1_subset_1(F, u1_struct_0(A)) & (F = k1_funct_1(u1_waybel_0(A, C), E))) & (k1_funct_1(u1_waybel_0(A, D), E) = k11_lattice3(A, B, F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_waybel_2)).
% 2.83/1.38  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.83/1.38  tff(c_42, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.83/1.38  tff(c_46, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.83/1.38  tff(c_44, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.83/1.38  tff(c_36, plain, (l1_waybel_0('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.83/1.38  tff(c_38, plain, (v7_waybel_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.83/1.38  tff(c_271, plain, (![A_212, B_213, C_214]: (v7_waybel_0(k3_waybel_2(A_212, B_213, C_214)) | ~l1_waybel_0(C_214, A_212) | ~v7_waybel_0(C_214) | v2_struct_0(C_214) | ~m1_subset_1(B_213, u1_struct_0(A_212)) | ~l1_orders_2(A_212) | v2_struct_0(A_212))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.83/1.38  tff(c_273, plain, (![C_214]: (v7_waybel_0(k3_waybel_2('#skF_3', '#skF_4', C_214)) | ~l1_waybel_0(C_214, '#skF_3') | ~v7_waybel_0(C_214) | v2_struct_0(C_214) | ~l1_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_271])).
% 2.83/1.38  tff(c_276, plain, (![C_214]: (v7_waybel_0(k3_waybel_2('#skF_3', '#skF_4', C_214)) | ~l1_waybel_0(C_214, '#skF_3') | ~v7_waybel_0(C_214) | v2_struct_0(C_214) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_273])).
% 2.83/1.38  tff(c_278, plain, (![C_215]: (v7_waybel_0(k3_waybel_2('#skF_3', '#skF_4', C_215)) | ~l1_waybel_0(C_215, '#skF_3') | ~v7_waybel_0(C_215) | v2_struct_0(C_215))), inference(negUnitSimplification, [status(thm)], [c_48, c_276])).
% 2.83/1.38  tff(c_226, plain, (![A_197, B_198, C_199]: (l1_waybel_0(k3_waybel_2(A_197, B_198, C_199), A_197) | ~l1_waybel_0(C_199, A_197) | v2_struct_0(C_199) | ~m1_subset_1(B_198, u1_struct_0(A_197)) | ~l1_orders_2(A_197) | v2_struct_0(A_197))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.83/1.38  tff(c_228, plain, (![C_199]: (l1_waybel_0(k3_waybel_2('#skF_3', '#skF_4', C_199), '#skF_3') | ~l1_waybel_0(C_199, '#skF_3') | v2_struct_0(C_199) | ~l1_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_226])).
% 2.83/1.38  tff(c_231, plain, (![C_199]: (l1_waybel_0(k3_waybel_2('#skF_3', '#skF_4', C_199), '#skF_3') | ~l1_waybel_0(C_199, '#skF_3') | v2_struct_0(C_199) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_228])).
% 2.83/1.38  tff(c_233, plain, (![C_200]: (l1_waybel_0(k3_waybel_2('#skF_3', '#skF_4', C_200), '#skF_3') | ~l1_waybel_0(C_200, '#skF_3') | v2_struct_0(C_200))), inference(negUnitSimplification, [status(thm)], [c_48, c_231])).
% 2.83/1.38  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.38  tff(c_50, plain, (![B_129, A_130]: (l1_orders_2(B_129) | ~l1_waybel_0(B_129, A_130) | ~l1_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.83/1.38  tff(c_54, plain, (l1_orders_2('#skF_5') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_50])).
% 2.83/1.38  tff(c_56, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 2.83/1.38  tff(c_59, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_2, c_56])).
% 2.83/1.38  tff(c_63, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_59])).
% 2.83/1.38  tff(c_65, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_54])).
% 2.83/1.38  tff(c_73, plain, (![A_136, B_137, C_138]: (l1_waybel_0(k3_waybel_2(A_136, B_137, C_138), A_136) | ~l1_waybel_0(C_138, A_136) | v2_struct_0(C_138) | ~m1_subset_1(B_137, u1_struct_0(A_136)) | ~l1_orders_2(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.83/1.38  tff(c_75, plain, (![C_138]: (l1_waybel_0(k3_waybel_2('#skF_3', '#skF_4', C_138), '#skF_3') | ~l1_waybel_0(C_138, '#skF_3') | v2_struct_0(C_138) | ~l1_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_73])).
% 2.83/1.38  tff(c_78, plain, (![C_138]: (l1_waybel_0(k3_waybel_2('#skF_3', '#skF_4', C_138), '#skF_3') | ~l1_waybel_0(C_138, '#skF_3') | v2_struct_0(C_138) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_75])).
% 2.83/1.38  tff(c_80, plain, (![C_139]: (l1_waybel_0(k3_waybel_2('#skF_3', '#skF_4', C_139), '#skF_3') | ~l1_waybel_0(C_139, '#skF_3') | v2_struct_0(C_139))), inference(negUnitSimplification, [status(thm)], [c_48, c_78])).
% 2.83/1.38  tff(c_4, plain, (![B_4, A_2]: (l1_orders_2(B_4) | ~l1_waybel_0(B_4, A_2) | ~l1_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.83/1.38  tff(c_83, plain, (![C_139]: (l1_orders_2(k3_waybel_2('#skF_3', '#skF_4', C_139)) | ~l1_struct_0('#skF_3') | ~l1_waybel_0(C_139, '#skF_3') | v2_struct_0(C_139))), inference(resolution, [status(thm)], [c_80, c_4])).
% 2.83/1.38  tff(c_86, plain, (![C_139]: (l1_orders_2(k3_waybel_2('#skF_3', '#skF_4', C_139)) | ~l1_waybel_0(C_139, '#skF_3') | v2_struct_0(C_139))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_83])).
% 2.83/1.38  tff(c_64, plain, (l1_orders_2('#skF_5')), inference(splitRight, [status(thm)], [c_54])).
% 2.83/1.38  tff(c_40, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.83/1.38  tff(c_79, plain, (![C_138]: (l1_waybel_0(k3_waybel_2('#skF_3', '#skF_4', C_138), '#skF_3') | ~l1_waybel_0(C_138, '#skF_3') | v2_struct_0(C_138))), inference(negUnitSimplification, [status(thm)], [c_48, c_78])).
% 2.83/1.38  tff(c_26, plain, (![A_118, B_119, C_120]: (v6_waybel_0(k3_waybel_2(A_118, B_119, C_120), A_118) | ~l1_waybel_0(C_120, A_118) | v2_struct_0(C_120) | ~m1_subset_1(B_119, u1_struct_0(A_118)) | ~l1_orders_2(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.83/1.38  tff(c_8, plain, (![A_5]: (v4_orders_2(g1_orders_2(u1_struct_0(A_5), u1_orders_2(A_5))) | ~v4_orders_2(A_5) | ~l1_orders_2(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.83/1.38  tff(c_97, plain, (![A_148, B_149, C_150]: (g1_orders_2(u1_struct_0(k3_waybel_2(A_148, B_149, C_150)), u1_orders_2(k3_waybel_2(A_148, B_149, C_150)))=g1_orders_2(u1_struct_0(C_150), u1_orders_2(C_150)) | ~l1_waybel_0(k3_waybel_2(A_148, B_149, C_150), A_148) | ~v6_waybel_0(k3_waybel_2(A_148, B_149, C_150), A_148) | ~l1_waybel_0(C_150, A_148) | v2_struct_0(C_150) | ~m1_subset_1(B_149, u1_struct_0(A_148)) | ~l1_orders_2(A_148) | v2_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.83/1.38  tff(c_6, plain, (![A_5]: (v4_orders_2(A_5) | ~v4_orders_2(g1_orders_2(u1_struct_0(A_5), u1_orders_2(A_5))) | ~l1_orders_2(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.83/1.38  tff(c_150, plain, (![A_178, B_179, C_180]: (v4_orders_2(k3_waybel_2(A_178, B_179, C_180)) | ~v4_orders_2(g1_orders_2(u1_struct_0(C_180), u1_orders_2(C_180))) | ~l1_orders_2(k3_waybel_2(A_178, B_179, C_180)) | v2_struct_0(k3_waybel_2(A_178, B_179, C_180)) | ~l1_waybel_0(k3_waybel_2(A_178, B_179, C_180), A_178) | ~v6_waybel_0(k3_waybel_2(A_178, B_179, C_180), A_178) | ~l1_waybel_0(C_180, A_178) | v2_struct_0(C_180) | ~m1_subset_1(B_179, u1_struct_0(A_178)) | ~l1_orders_2(A_178) | v2_struct_0(A_178))), inference(superposition, [status(thm), theory('equality')], [c_97, c_6])).
% 2.83/1.38  tff(c_156, plain, (![A_181, B_182, A_183]: (v4_orders_2(k3_waybel_2(A_181, B_182, A_183)) | ~l1_orders_2(k3_waybel_2(A_181, B_182, A_183)) | v2_struct_0(k3_waybel_2(A_181, B_182, A_183)) | ~l1_waybel_0(k3_waybel_2(A_181, B_182, A_183), A_181) | ~v6_waybel_0(k3_waybel_2(A_181, B_182, A_183), A_181) | ~l1_waybel_0(A_183, A_181) | ~m1_subset_1(B_182, u1_struct_0(A_181)) | ~l1_orders_2(A_181) | v2_struct_0(A_181) | ~v4_orders_2(A_183) | ~l1_orders_2(A_183) | v2_struct_0(A_183))), inference(resolution, [status(thm)], [c_8, c_150])).
% 2.83/1.38  tff(c_161, plain, (![A_184, B_185, C_186]: (v4_orders_2(k3_waybel_2(A_184, B_185, C_186)) | ~l1_orders_2(k3_waybel_2(A_184, B_185, C_186)) | v2_struct_0(k3_waybel_2(A_184, B_185, C_186)) | ~l1_waybel_0(k3_waybel_2(A_184, B_185, C_186), A_184) | ~v4_orders_2(C_186) | ~l1_orders_2(C_186) | ~l1_waybel_0(C_186, A_184) | v2_struct_0(C_186) | ~m1_subset_1(B_185, u1_struct_0(A_184)) | ~l1_orders_2(A_184) | v2_struct_0(A_184))), inference(resolution, [status(thm)], [c_26, c_156])).
% 2.83/1.38  tff(c_165, plain, (![C_138]: (v4_orders_2(k3_waybel_2('#skF_3', '#skF_4', C_138)) | ~l1_orders_2(k3_waybel_2('#skF_3', '#skF_4', C_138)) | v2_struct_0(k3_waybel_2('#skF_3', '#skF_4', C_138)) | ~v4_orders_2(C_138) | ~l1_orders_2(C_138) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~l1_waybel_0(C_138, '#skF_3') | v2_struct_0(C_138))), inference(resolution, [status(thm)], [c_79, c_161])).
% 2.83/1.38  tff(c_169, plain, (![C_138]: (v4_orders_2(k3_waybel_2('#skF_3', '#skF_4', C_138)) | ~l1_orders_2(k3_waybel_2('#skF_3', '#skF_4', C_138)) | v2_struct_0(k3_waybel_2('#skF_3', '#skF_4', C_138)) | ~v4_orders_2(C_138) | ~l1_orders_2(C_138) | v2_struct_0('#skF_3') | ~l1_waybel_0(C_138, '#skF_3') | v2_struct_0(C_138))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_165])).
% 2.83/1.38  tff(c_180, plain, (![C_191]: (v4_orders_2(k3_waybel_2('#skF_3', '#skF_4', C_191)) | ~l1_orders_2(k3_waybel_2('#skF_3', '#skF_4', C_191)) | v2_struct_0(k3_waybel_2('#skF_3', '#skF_4', C_191)) | ~v4_orders_2(C_191) | ~l1_orders_2(C_191) | ~l1_waybel_0(C_191, '#skF_3') | v2_struct_0(C_191))), inference(negUnitSimplification, [status(thm)], [c_48, c_169])).
% 2.83/1.38  tff(c_34, plain, (~l1_waybel_0(k3_waybel_2('#skF_3', '#skF_4', '#skF_5'), '#skF_3') | ~v7_waybel_0(k3_waybel_2('#skF_3', '#skF_4', '#skF_5')) | ~v4_orders_2(k3_waybel_2('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0(k3_waybel_2('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.83/1.38  tff(c_55, plain, (~v4_orders_2(k3_waybel_2('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_34])).
% 2.83/1.38  tff(c_183, plain, (~l1_orders_2(k3_waybel_2('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0(k3_waybel_2('#skF_3', '#skF_4', '#skF_5')) | ~v4_orders_2('#skF_5') | ~l1_orders_2('#skF_5') | ~l1_waybel_0('#skF_5', '#skF_3') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_180, c_55])).
% 2.83/1.38  tff(c_186, plain, (~l1_orders_2(k3_waybel_2('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0(k3_waybel_2('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_64, c_40, c_183])).
% 2.83/1.38  tff(c_187, plain, (~l1_orders_2(k3_waybel_2('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0(k3_waybel_2('#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_42, c_186])).
% 2.83/1.38  tff(c_188, plain, (~l1_orders_2(k3_waybel_2('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_187])).
% 2.83/1.38  tff(c_191, plain, (~l1_waybel_0('#skF_5', '#skF_3') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_86, c_188])).
% 2.83/1.38  tff(c_194, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_191])).
% 2.83/1.38  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_194])).
% 2.83/1.38  tff(c_197, plain, (v2_struct_0(k3_waybel_2('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_187])).
% 2.83/1.38  tff(c_28, plain, (![A_118, B_119, C_120]: (~v2_struct_0(k3_waybel_2(A_118, B_119, C_120)) | ~l1_waybel_0(C_120, A_118) | v2_struct_0(C_120) | ~m1_subset_1(B_119, u1_struct_0(A_118)) | ~l1_orders_2(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.83/1.38  tff(c_200, plain, (~l1_waybel_0('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_197, c_28])).
% 2.83/1.38  tff(c_203, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_36, c_200])).
% 2.83/1.38  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_203])).
% 2.83/1.38  tff(c_206, plain, (~v7_waybel_0(k3_waybel_2('#skF_3', '#skF_4', '#skF_5')) | ~l1_waybel_0(k3_waybel_2('#skF_3', '#skF_4', '#skF_5'), '#skF_3') | v2_struct_0(k3_waybel_2('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_34])).
% 2.83/1.38  tff(c_224, plain, (~l1_waybel_0(k3_waybel_2('#skF_3', '#skF_4', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_206])).
% 2.83/1.38  tff(c_236, plain, (~l1_waybel_0('#skF_5', '#skF_3') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_233, c_224])).
% 2.83/1.38  tff(c_242, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_236])).
% 2.83/1.38  tff(c_244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_242])).
% 2.83/1.38  tff(c_245, plain, (~v7_waybel_0(k3_waybel_2('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0(k3_waybel_2('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_206])).
% 2.83/1.38  tff(c_253, plain, (~v7_waybel_0(k3_waybel_2('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_245])).
% 2.83/1.38  tff(c_281, plain, (~l1_waybel_0('#skF_5', '#skF_3') | ~v7_waybel_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_278, c_253])).
% 2.83/1.38  tff(c_284, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_281])).
% 2.83/1.38  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_284])).
% 2.83/1.38  tff(c_287, plain, (v2_struct_0(k3_waybel_2('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_245])).
% 2.83/1.38  tff(c_289, plain, (![A_216, B_217, C_218]: (~v2_struct_0(k3_waybel_2(A_216, B_217, C_218)) | ~l1_waybel_0(C_218, A_216) | v2_struct_0(C_218) | ~m1_subset_1(B_217, u1_struct_0(A_216)) | ~l1_orders_2(A_216) | v2_struct_0(A_216))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.83/1.38  tff(c_291, plain, (~l1_waybel_0('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_287, c_289])).
% 2.83/1.38  tff(c_294, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_36, c_291])).
% 2.83/1.38  tff(c_296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_294])).
% 2.83/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.38  
% 2.83/1.38  Inference rules
% 2.83/1.38  ----------------------
% 2.83/1.38  #Ref     : 1
% 2.83/1.38  #Sup     : 40
% 2.83/1.38  #Fact    : 0
% 2.83/1.38  #Define  : 0
% 2.83/1.38  #Split   : 6
% 2.83/1.38  #Chain   : 0
% 2.83/1.38  #Close   : 0
% 2.83/1.38  
% 2.83/1.38  Ordering : KBO
% 2.83/1.38  
% 2.83/1.38  Simplification rules
% 2.83/1.38  ----------------------
% 2.83/1.38  #Subsume      : 3
% 2.83/1.38  #Demod        : 25
% 2.83/1.38  #Tautology    : 4
% 2.83/1.38  #SimpNegUnit  : 12
% 2.83/1.38  #BackRed      : 0
% 2.83/1.38  
% 2.83/1.38  #Partial instantiations: 0
% 2.83/1.38  #Strategies tried      : 1
% 2.83/1.38  
% 2.83/1.38  Timing (in seconds)
% 2.83/1.38  ----------------------
% 2.83/1.38  Preprocessing        : 0.35
% 2.83/1.38  Parsing              : 0.17
% 2.83/1.38  CNF conversion       : 0.04
% 2.83/1.38  Main loop            : 0.26
% 2.83/1.39  Inferencing          : 0.10
% 2.83/1.39  Reduction            : 0.07
% 2.83/1.39  Demodulation         : 0.05
% 2.83/1.39  BG Simplification    : 0.02
% 2.83/1.39  Subsumption          : 0.06
% 2.83/1.39  Abstraction          : 0.02
% 2.83/1.39  MUC search           : 0.00
% 2.83/1.39  Cooper               : 0.00
% 2.83/1.39  Total                : 0.66
% 2.83/1.39  Index Insertion      : 0.00
% 2.83/1.39  Index Deletion       : 0.00
% 2.83/1.39  Index Matching       : 0.00
% 2.83/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
