%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:39 EST 2020

% Result     : Theorem 10.03s
% Output     : CNFRefutation 10.03s
% Verified   : 
% Statistics : Number of formulae       :  120 (7911 expanded)
%              Number of leaves         :   23 (2824 expanded)
%              Depth                    :   27
%              Number of atoms          :  481 (53261 expanded)
%              Number of equality atoms :   50 (4137 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v2_struct_0 > v1_lattice3 > l1_orders_2 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k10_lattice3,type,(
    k10_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( v5_orders_2(A)
          & v1_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k10_lattice3(A,B,C) = k10_lattice3(A,C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_lattice3)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ? [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                    & r1_orders_2(A,B,D)
                    & r1_orders_2(A,C,D)
                    & ! [E] :
                        ( m1_subset_1(E,u1_struct_0(A))
                       => ( ( r1_orders_2(A,B,E)
                            & r1_orders_2(A,C,E) )
                         => r1_orders_2(A,D,E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_lattice3)).

tff(f_91,axiom,(
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

tff(f_32,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

tff(c_44,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_46,plain,(
    v1_lattice3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_48,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_40,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_22,plain,(
    ! [A_2,B_33,C_41] :
      ( m1_subset_1('#skF_1'(A_2,B_33,C_41),u1_struct_0(A_2))
      | ~ m1_subset_1(C_41,u1_struct_0(A_2))
      | ~ m1_subset_1(B_33,u1_struct_0(A_2))
      | ~ v1_lattice3(A_2)
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [A_2,C_41,B_33] :
      ( r1_orders_2(A_2,C_41,'#skF_1'(A_2,B_33,C_41))
      | ~ m1_subset_1(C_41,u1_struct_0(A_2))
      | ~ m1_subset_1(B_33,u1_struct_0(A_2))
      | ~ v1_lattice3(A_2)
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    ! [A_2,B_33,C_41] :
      ( r1_orders_2(A_2,B_33,'#skF_1'(A_2,B_33,C_41))
      | ~ m1_subset_1(C_41,u1_struct_0(A_2))
      | ~ m1_subset_1(B_33,u1_struct_0(A_2))
      | ~ v1_lattice3(A_2)
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ! [A_2,B_33,C_41,E_46] :
      ( r1_orders_2(A_2,'#skF_1'(A_2,B_33,C_41),E_46)
      | ~ r1_orders_2(A_2,C_41,E_46)
      | ~ r1_orders_2(A_2,B_33,E_46)
      | ~ m1_subset_1(E_46,u1_struct_0(A_2))
      | ~ m1_subset_1(C_41,u1_struct_0(A_2))
      | ~ m1_subset_1(B_33,u1_struct_0(A_2))
      | ~ v1_lattice3(A_2)
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [A_59,B_83,C_95,D_101] :
      ( r1_orders_2(A_59,B_83,'#skF_5'(A_59,B_83,C_95,D_101))
      | k10_lattice3(A_59,B_83,C_95) = D_101
      | ~ r1_orders_2(A_59,C_95,D_101)
      | ~ r1_orders_2(A_59,B_83,D_101)
      | ~ m1_subset_1(D_101,u1_struct_0(A_59))
      | ~ m1_subset_1(C_95,u1_struct_0(A_59))
      | ~ m1_subset_1(B_83,u1_struct_0(A_59))
      | ~ l1_orders_2(A_59)
      | ~ v1_lattice3(A_59)
      | ~ v5_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_79,plain,(
    ! [A_153,D_154,B_155,C_156] :
      ( ~ r1_orders_2(A_153,D_154,'#skF_5'(A_153,B_155,C_156,D_154))
      | k10_lattice3(A_153,B_155,C_156) = D_154
      | ~ r1_orders_2(A_153,C_156,D_154)
      | ~ r1_orders_2(A_153,B_155,D_154)
      | ~ m1_subset_1(D_154,u1_struct_0(A_153))
      | ~ m1_subset_1(C_156,u1_struct_0(A_153))
      | ~ m1_subset_1(B_155,u1_struct_0(A_153))
      | ~ l1_orders_2(A_153)
      | ~ v1_lattice3(A_153)
      | ~ v5_orders_2(A_153)
      | v2_struct_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_101,plain,(
    ! [A_164,D_165,C_166] :
      ( k10_lattice3(A_164,D_165,C_166) = D_165
      | ~ r1_orders_2(A_164,C_166,D_165)
      | ~ r1_orders_2(A_164,D_165,D_165)
      | ~ m1_subset_1(C_166,u1_struct_0(A_164))
      | ~ m1_subset_1(D_165,u1_struct_0(A_164))
      | ~ l1_orders_2(A_164)
      | ~ v1_lattice3(A_164)
      | ~ v5_orders_2(A_164)
      | v2_struct_0(A_164) ) ),
    inference(resolution,[status(thm)],[c_28,c_79])).

tff(c_129,plain,(
    ! [A_170,B_171,C_172] :
      ( k10_lattice3(A_170,'#skF_1'(A_170,B_171,C_172),B_171) = '#skF_1'(A_170,B_171,C_172)
      | ~ r1_orders_2(A_170,'#skF_1'(A_170,B_171,C_172),'#skF_1'(A_170,B_171,C_172))
      | ~ m1_subset_1('#skF_1'(A_170,B_171,C_172),u1_struct_0(A_170))
      | ~ v5_orders_2(A_170)
      | v2_struct_0(A_170)
      | ~ m1_subset_1(C_172,u1_struct_0(A_170))
      | ~ m1_subset_1(B_171,u1_struct_0(A_170))
      | ~ v1_lattice3(A_170)
      | ~ l1_orders_2(A_170) ) ),
    inference(resolution,[status(thm)],[c_20,c_101])).

tff(c_140,plain,(
    ! [A_177,B_178,C_179] :
      ( k10_lattice3(A_177,'#skF_1'(A_177,B_178,C_179),B_178) = '#skF_1'(A_177,B_178,C_179)
      | ~ v5_orders_2(A_177)
      | v2_struct_0(A_177)
      | ~ r1_orders_2(A_177,C_179,'#skF_1'(A_177,B_178,C_179))
      | ~ r1_orders_2(A_177,B_178,'#skF_1'(A_177,B_178,C_179))
      | ~ m1_subset_1('#skF_1'(A_177,B_178,C_179),u1_struct_0(A_177))
      | ~ m1_subset_1(C_179,u1_struct_0(A_177))
      | ~ m1_subset_1(B_178,u1_struct_0(A_177))
      | ~ v1_lattice3(A_177)
      | ~ l1_orders_2(A_177) ) ),
    inference(resolution,[status(thm)],[c_16,c_129])).

tff(c_152,plain,(
    ! [A_180,C_181] :
      ( k10_lattice3(A_180,'#skF_1'(A_180,C_181,C_181),C_181) = '#skF_1'(A_180,C_181,C_181)
      | ~ v5_orders_2(A_180)
      | v2_struct_0(A_180)
      | ~ r1_orders_2(A_180,C_181,'#skF_1'(A_180,C_181,C_181))
      | ~ m1_subset_1('#skF_1'(A_180,C_181,C_181),u1_struct_0(A_180))
      | ~ m1_subset_1(C_181,u1_struct_0(A_180))
      | ~ v1_lattice3(A_180)
      | ~ l1_orders_2(A_180) ) ),
    inference(resolution,[status(thm)],[c_20,c_140])).

tff(c_165,plain,(
    ! [A_182,B_183] :
      ( k10_lattice3(A_182,'#skF_1'(A_182,B_183,B_183),B_183) = '#skF_1'(A_182,B_183,B_183)
      | ~ v5_orders_2(A_182)
      | v2_struct_0(A_182)
      | ~ m1_subset_1('#skF_1'(A_182,B_183,B_183),u1_struct_0(A_182))
      | ~ m1_subset_1(B_183,u1_struct_0(A_182))
      | ~ v1_lattice3(A_182)
      | ~ l1_orders_2(A_182) ) ),
    inference(resolution,[status(thm)],[c_18,c_152])).

tff(c_170,plain,(
    ! [A_184,C_185] :
      ( k10_lattice3(A_184,'#skF_1'(A_184,C_185,C_185),C_185) = '#skF_1'(A_184,C_185,C_185)
      | ~ v5_orders_2(A_184)
      | v2_struct_0(A_184)
      | ~ m1_subset_1(C_185,u1_struct_0(A_184))
      | ~ v1_lattice3(A_184)
      | ~ l1_orders_2(A_184) ) ),
    inference(resolution,[status(thm)],[c_22,c_165])).

tff(c_182,plain,
    ( k10_lattice3('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_8'),'#skF_8') = '#skF_1'('#skF_6','#skF_8','#skF_8')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_170])).

tff(c_192,plain,
    ( k10_lattice3('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_8'),'#skF_8') = '#skF_1'('#skF_6','#skF_8','#skF_8')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_48,c_182])).

tff(c_209,plain,(
    v2_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v1_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_212,plain,
    ( ~ v1_lattice3('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_209,c_2])).

tff(c_216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_212])).

tff(c_218,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1139,plain,(
    ! [A_225,B_226,C_227] :
      ( k10_lattice3(A_225,'#skF_1'(A_225,B_226,C_227),B_226) = '#skF_1'(A_225,B_226,C_227)
      | ~ v5_orders_2(A_225)
      | v2_struct_0(A_225)
      | ~ r1_orders_2(A_225,B_226,'#skF_1'(A_225,B_226,C_227))
      | ~ m1_subset_1('#skF_1'(A_225,B_226,C_227),u1_struct_0(A_225))
      | ~ m1_subset_1(C_227,u1_struct_0(A_225))
      | ~ m1_subset_1(B_226,u1_struct_0(A_225))
      | ~ v1_lattice3(A_225)
      | ~ l1_orders_2(A_225) ) ),
    inference(resolution,[status(thm)],[c_18,c_140])).

tff(c_1174,plain,(
    ! [A_228,B_229,C_230] :
      ( k10_lattice3(A_228,'#skF_1'(A_228,B_229,C_230),B_229) = '#skF_1'(A_228,B_229,C_230)
      | ~ v5_orders_2(A_228)
      | v2_struct_0(A_228)
      | ~ m1_subset_1('#skF_1'(A_228,B_229,C_230),u1_struct_0(A_228))
      | ~ m1_subset_1(C_230,u1_struct_0(A_228))
      | ~ m1_subset_1(B_229,u1_struct_0(A_228))
      | ~ v1_lattice3(A_228)
      | ~ l1_orders_2(A_228) ) ),
    inference(resolution,[status(thm)],[c_20,c_1139])).

tff(c_1368,plain,(
    ! [A_236,B_237,C_238] :
      ( k10_lattice3(A_236,'#skF_1'(A_236,B_237,C_238),B_237) = '#skF_1'(A_236,B_237,C_238)
      | ~ v5_orders_2(A_236)
      | v2_struct_0(A_236)
      | ~ m1_subset_1(C_238,u1_struct_0(A_236))
      | ~ m1_subset_1(B_237,u1_struct_0(A_236))
      | ~ v1_lattice3(A_236)
      | ~ l1_orders_2(A_236) ) ),
    inference(resolution,[status(thm)],[c_22,c_1174])).

tff(c_1384,plain,(
    ! [B_237] :
      ( k10_lattice3('#skF_6','#skF_1'('#skF_6',B_237,'#skF_8'),B_237) = '#skF_1'('#skF_6',B_237,'#skF_8')
      | ~ v5_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(B_237,u1_struct_0('#skF_6'))
      | ~ v1_lattice3('#skF_6')
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_1368])).

tff(c_1402,plain,(
    ! [B_237] :
      ( k10_lattice3('#skF_6','#skF_1'('#skF_6',B_237,'#skF_8'),B_237) = '#skF_1'('#skF_6',B_237,'#skF_8')
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(B_237,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_48,c_1384])).

tff(c_1408,plain,(
    ! [B_239] :
      ( k10_lattice3('#skF_6','#skF_1'('#skF_6',B_239,'#skF_8'),B_239) = '#skF_1'('#skF_6',B_239,'#skF_8')
      | ~ m1_subset_1(B_239,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_1402])).

tff(c_1452,plain,(
    k10_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_7') = '#skF_1'('#skF_6','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_1408])).

tff(c_34,plain,(
    ! [A_59,C_95,B_83] :
      ( r1_orders_2(A_59,C_95,k10_lattice3(A_59,B_83,C_95))
      | ~ m1_subset_1(k10_lattice3(A_59,B_83,C_95),u1_struct_0(A_59))
      | ~ m1_subset_1(C_95,u1_struct_0(A_59))
      | ~ m1_subset_1(B_83,u1_struct_0(A_59))
      | ~ l1_orders_2(A_59)
      | ~ v1_lattice3(A_59)
      | ~ v5_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1457,plain,
    ( r1_orders_2('#skF_6','#skF_7',k10_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1452,c_34])).

tff(c_1466,plain,
    ( r1_orders_2('#skF_6','#skF_7','#skF_1'('#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_1452,c_1457])).

tff(c_1467,plain,
    ( r1_orders_2('#skF_6','#skF_7','#skF_1'('#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_1466])).

tff(c_1536,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1467])).

tff(c_1539,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ v1_lattice3('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_1536])).

tff(c_1543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_42,c_40,c_1539])).

tff(c_1545,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1467])).

tff(c_36,plain,(
    ! [A_59,B_83,C_95] :
      ( r1_orders_2(A_59,B_83,k10_lattice3(A_59,B_83,C_95))
      | ~ m1_subset_1(k10_lattice3(A_59,B_83,C_95),u1_struct_0(A_59))
      | ~ m1_subset_1(C_95,u1_struct_0(A_59))
      | ~ m1_subset_1(B_83,u1_struct_0(A_59))
      | ~ l1_orders_2(A_59)
      | ~ v1_lattice3(A_59)
      | ~ v5_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1459,plain,
    ( r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),k10_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1452,c_36])).

tff(c_1469,plain,
    ( r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_1'('#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_1452,c_1459])).

tff(c_1470,plain,
    ( r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_1'('#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_1469])).

tff(c_1865,plain,(
    r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_1'('#skF_6','#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1545,c_1470])).

tff(c_121,plain,(
    ! [A_2,B_33,C_41] :
      ( k10_lattice3(A_2,'#skF_1'(A_2,B_33,C_41),C_41) = '#skF_1'(A_2,B_33,C_41)
      | ~ r1_orders_2(A_2,'#skF_1'(A_2,B_33,C_41),'#skF_1'(A_2,B_33,C_41))
      | ~ m1_subset_1('#skF_1'(A_2,B_33,C_41),u1_struct_0(A_2))
      | ~ v5_orders_2(A_2)
      | v2_struct_0(A_2)
      | ~ m1_subset_1(C_41,u1_struct_0(A_2))
      | ~ m1_subset_1(B_33,u1_struct_0(A_2))
      | ~ v1_lattice3(A_2)
      | ~ l1_orders_2(A_2) ) ),
    inference(resolution,[status(thm)],[c_18,c_101])).

tff(c_1872,plain,
    ( k10_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_8') = '#skF_1'('#skF_6','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ v1_lattice3('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_1865,c_121])).

tff(c_1887,plain,
    ( k10_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_8') = '#skF_1'('#skF_6','#skF_7','#skF_8')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_42,c_40,c_48,c_1545,c_1872])).

tff(c_1888,plain,(
    k10_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_8') = '#skF_1'('#skF_6','#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_1887])).

tff(c_1901,plain,
    ( r1_orders_2('#skF_6','#skF_8',k10_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_8'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1888,c_34])).

tff(c_1910,plain,
    ( r1_orders_2('#skF_6','#skF_8','#skF_1'('#skF_6','#skF_7','#skF_8'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_1545,c_40,c_1545,c_1888,c_1901])).

tff(c_1911,plain,(
    r1_orders_2('#skF_6','#skF_8','#skF_1'('#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_1910])).

tff(c_1544,plain,(
    r1_orders_2('#skF_6','#skF_7','#skF_1'('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1467])).

tff(c_30,plain,(
    ! [A_59,B_83,C_95,D_101] :
      ( m1_subset_1('#skF_5'(A_59,B_83,C_95,D_101),u1_struct_0(A_59))
      | k10_lattice3(A_59,B_83,C_95) = D_101
      | ~ r1_orders_2(A_59,C_95,D_101)
      | ~ r1_orders_2(A_59,B_83,D_101)
      | ~ m1_subset_1(D_101,u1_struct_0(A_59))
      | ~ m1_subset_1(C_95,u1_struct_0(A_59))
      | ~ m1_subset_1(B_83,u1_struct_0(A_59))
      | ~ l1_orders_2(A_59)
      | ~ v1_lattice3(A_59)
      | ~ v5_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_26,plain,(
    ! [A_59,C_95,B_83,D_101] :
      ( r1_orders_2(A_59,C_95,'#skF_5'(A_59,B_83,C_95,D_101))
      | k10_lattice3(A_59,B_83,C_95) = D_101
      | ~ r1_orders_2(A_59,C_95,D_101)
      | ~ r1_orders_2(A_59,B_83,D_101)
      | ~ m1_subset_1(D_101,u1_struct_0(A_59))
      | ~ m1_subset_1(C_95,u1_struct_0(A_59))
      | ~ m1_subset_1(B_83,u1_struct_0(A_59))
      | ~ l1_orders_2(A_59)
      | ~ v1_lattice3(A_59)
      | ~ v5_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_196,plain,(
    ! [C_187,B_188,C_190,B_186,A_189] :
      ( k10_lattice3(A_189,B_188,C_190) = '#skF_1'(A_189,B_186,C_187)
      | ~ r1_orders_2(A_189,C_190,'#skF_1'(A_189,B_186,C_187))
      | ~ r1_orders_2(A_189,B_188,'#skF_1'(A_189,B_186,C_187))
      | ~ m1_subset_1('#skF_1'(A_189,B_186,C_187),u1_struct_0(A_189))
      | ~ m1_subset_1(C_190,u1_struct_0(A_189))
      | ~ m1_subset_1(B_188,u1_struct_0(A_189))
      | ~ v5_orders_2(A_189)
      | v2_struct_0(A_189)
      | ~ r1_orders_2(A_189,C_187,'#skF_5'(A_189,B_188,C_190,'#skF_1'(A_189,B_186,C_187)))
      | ~ r1_orders_2(A_189,B_186,'#skF_5'(A_189,B_188,C_190,'#skF_1'(A_189,B_186,C_187)))
      | ~ m1_subset_1('#skF_5'(A_189,B_188,C_190,'#skF_1'(A_189,B_186,C_187)),u1_struct_0(A_189))
      | ~ m1_subset_1(C_187,u1_struct_0(A_189))
      | ~ m1_subset_1(B_186,u1_struct_0(A_189))
      | ~ v1_lattice3(A_189)
      | ~ l1_orders_2(A_189) ) ),
    inference(resolution,[status(thm)],[c_16,c_79])).

tff(c_711,plain,(
    ! [A_205,B_206,B_207,C_208] :
      ( ~ r1_orders_2(A_205,B_206,'#skF_5'(A_205,B_207,C_208,'#skF_1'(A_205,B_206,B_207)))
      | ~ m1_subset_1('#skF_5'(A_205,B_207,C_208,'#skF_1'(A_205,B_206,B_207)),u1_struct_0(A_205))
      | ~ m1_subset_1(B_206,u1_struct_0(A_205))
      | k10_lattice3(A_205,B_207,C_208) = '#skF_1'(A_205,B_206,B_207)
      | ~ r1_orders_2(A_205,C_208,'#skF_1'(A_205,B_206,B_207))
      | ~ r1_orders_2(A_205,B_207,'#skF_1'(A_205,B_206,B_207))
      | ~ m1_subset_1('#skF_1'(A_205,B_206,B_207),u1_struct_0(A_205))
      | ~ m1_subset_1(C_208,u1_struct_0(A_205))
      | ~ m1_subset_1(B_207,u1_struct_0(A_205))
      | ~ l1_orders_2(A_205)
      | ~ v1_lattice3(A_205)
      | ~ v5_orders_2(A_205)
      | v2_struct_0(A_205) ) ),
    inference(resolution,[status(thm)],[c_28,c_196])).

tff(c_1946,plain,(
    ! [A_247,B_248,C_249] :
      ( ~ m1_subset_1('#skF_5'(A_247,B_248,C_249,'#skF_1'(A_247,C_249,B_248)),u1_struct_0(A_247))
      | k10_lattice3(A_247,B_248,C_249) = '#skF_1'(A_247,C_249,B_248)
      | ~ r1_orders_2(A_247,C_249,'#skF_1'(A_247,C_249,B_248))
      | ~ r1_orders_2(A_247,B_248,'#skF_1'(A_247,C_249,B_248))
      | ~ m1_subset_1('#skF_1'(A_247,C_249,B_248),u1_struct_0(A_247))
      | ~ m1_subset_1(C_249,u1_struct_0(A_247))
      | ~ m1_subset_1(B_248,u1_struct_0(A_247))
      | ~ l1_orders_2(A_247)
      | ~ v1_lattice3(A_247)
      | ~ v5_orders_2(A_247)
      | v2_struct_0(A_247) ) ),
    inference(resolution,[status(thm)],[c_26,c_711])).

tff(c_6509,plain,(
    ! [A_340,B_341,C_342] :
      ( k10_lattice3(A_340,B_341,C_342) = '#skF_1'(A_340,C_342,B_341)
      | ~ r1_orders_2(A_340,C_342,'#skF_1'(A_340,C_342,B_341))
      | ~ r1_orders_2(A_340,B_341,'#skF_1'(A_340,C_342,B_341))
      | ~ m1_subset_1('#skF_1'(A_340,C_342,B_341),u1_struct_0(A_340))
      | ~ m1_subset_1(C_342,u1_struct_0(A_340))
      | ~ m1_subset_1(B_341,u1_struct_0(A_340))
      | ~ l1_orders_2(A_340)
      | ~ v1_lattice3(A_340)
      | ~ v5_orders_2(A_340)
      | v2_struct_0(A_340) ) ),
    inference(resolution,[status(thm)],[c_30,c_1946])).

tff(c_6541,plain,
    ( k10_lattice3('#skF_6','#skF_8','#skF_7') = '#skF_1'('#skF_6','#skF_7','#skF_8')
    | ~ r1_orders_2('#skF_6','#skF_8','#skF_1'('#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1544,c_6509])).

tff(c_6613,plain,
    ( k10_lattice3('#skF_6','#skF_8','#skF_7') = '#skF_1'('#skF_6','#skF_7','#skF_8')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_40,c_42,c_1545,c_1911,c_6541])).

tff(c_6614,plain,(
    k10_lattice3('#skF_6','#skF_8','#skF_7') = '#skF_1'('#skF_6','#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_6613])).

tff(c_1386,plain,(
    ! [B_237] :
      ( k10_lattice3('#skF_6','#skF_1'('#skF_6',B_237,'#skF_7'),B_237) = '#skF_1'('#skF_6',B_237,'#skF_7')
      | ~ v5_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(B_237,u1_struct_0('#skF_6'))
      | ~ v1_lattice3('#skF_6')
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_1368])).

tff(c_1406,plain,(
    ! [B_237] :
      ( k10_lattice3('#skF_6','#skF_1'('#skF_6',B_237,'#skF_7'),B_237) = '#skF_1'('#skF_6',B_237,'#skF_7')
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(B_237,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_48,c_1386])).

tff(c_1472,plain,(
    ! [B_240] :
      ( k10_lattice3('#skF_6','#skF_1'('#skF_6',B_240,'#skF_7'),B_240) = '#skF_1'('#skF_6',B_240,'#skF_7')
      | ~ m1_subset_1(B_240,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_1406])).

tff(c_1514,plain,(
    k10_lattice3('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_8') = '#skF_1'('#skF_6','#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_1472])).

tff(c_1521,plain,
    ( r1_orders_2('#skF_6','#skF_8',k10_lattice3('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_8'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1514,c_34])).

tff(c_1530,plain,
    ( r1_orders_2('#skF_6','#skF_8','#skF_1'('#skF_6','#skF_8','#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_40,c_1514,c_1521])).

tff(c_1531,plain,
    ( r1_orders_2('#skF_6','#skF_8','#skF_1'('#skF_6','#skF_8','#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_1530])).

tff(c_1616,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1531])).

tff(c_1619,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ v1_lattice3('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_1616])).

tff(c_1623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_40,c_42,c_1619])).

tff(c_1625,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1531])).

tff(c_1523,plain,
    ( r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),k10_lattice3('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_8'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1514,c_36])).

tff(c_1533,plain,
    ( r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_1'('#skF_6','#skF_8','#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_40,c_1514,c_1523])).

tff(c_1534,plain,
    ( r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_1'('#skF_6','#skF_8','#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_1533])).

tff(c_1638,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1534])).

tff(c_1664,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1625,c_1638])).

tff(c_1665,plain,(
    r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_1'('#skF_6','#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1534])).

tff(c_1698,plain,
    ( k10_lattice3('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_7') = '#skF_1'('#skF_6','#skF_8','#skF_7')
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6'))
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ v1_lattice3('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_1665,c_121])).

tff(c_1713,plain,
    ( k10_lattice3('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_7') = '#skF_1'('#skF_6','#skF_8','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_40,c_42,c_48,c_1625,c_1698])).

tff(c_1714,plain,(
    k10_lattice3('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_7') = '#skF_1'('#skF_6','#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_1713])).

tff(c_1761,plain,
    ( r1_orders_2('#skF_6','#skF_7',k10_lattice3('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1714,c_34])).

tff(c_1770,plain,
    ( r1_orders_2('#skF_6','#skF_7','#skF_1'('#skF_6','#skF_8','#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_1625,c_42,c_1625,c_1714,c_1761])).

tff(c_1771,plain,(
    r1_orders_2('#skF_6','#skF_7','#skF_1'('#skF_6','#skF_8','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_1770])).

tff(c_1624,plain,(
    r1_orders_2('#skF_6','#skF_8','#skF_1'('#skF_6','#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1531])).

tff(c_6539,plain,
    ( k10_lattice3('#skF_6','#skF_7','#skF_8') = '#skF_1'('#skF_6','#skF_8','#skF_7')
    | ~ r1_orders_2('#skF_6','#skF_7','#skF_1'('#skF_6','#skF_8','#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1624,c_6509])).

tff(c_6609,plain,
    ( k10_lattice3('#skF_6','#skF_7','#skF_8') = '#skF_1'('#skF_6','#skF_8','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_1625,c_1771,c_6539])).

tff(c_6610,plain,(
    k10_lattice3('#skF_6','#skF_7','#skF_8') = '#skF_1'('#skF_6','#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_6609])).

tff(c_38,plain,(
    k10_lattice3('#skF_6','#skF_7','#skF_8') != k10_lattice3('#skF_6','#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6632,plain,(
    k10_lattice3('#skF_6','#skF_8','#skF_7') != '#skF_1'('#skF_6','#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6610,c_38])).

tff(c_6671,plain,(
    '#skF_1'('#skF_6','#skF_7','#skF_8') != '#skF_1'('#skF_6','#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6614,c_6632])).

tff(c_861,plain,(
    ! [A_209,B_210,B_211,C_212] :
      ( ~ r1_orders_2(A_209,B_210,'#skF_5'(A_209,B_211,C_212,'#skF_1'(A_209,B_210,C_212)))
      | ~ m1_subset_1('#skF_5'(A_209,B_211,C_212,'#skF_1'(A_209,B_210,C_212)),u1_struct_0(A_209))
      | ~ m1_subset_1(B_210,u1_struct_0(A_209))
      | k10_lattice3(A_209,B_211,C_212) = '#skF_1'(A_209,B_210,C_212)
      | ~ r1_orders_2(A_209,C_212,'#skF_1'(A_209,B_210,C_212))
      | ~ r1_orders_2(A_209,B_211,'#skF_1'(A_209,B_210,C_212))
      | ~ m1_subset_1('#skF_1'(A_209,B_210,C_212),u1_struct_0(A_209))
      | ~ m1_subset_1(C_212,u1_struct_0(A_209))
      | ~ m1_subset_1(B_211,u1_struct_0(A_209))
      | ~ l1_orders_2(A_209)
      | ~ v1_lattice3(A_209)
      | ~ v5_orders_2(A_209)
      | v2_struct_0(A_209) ) ),
    inference(resolution,[status(thm)],[c_26,c_196])).

tff(c_2302,plain,(
    ! [A_257,B_258,C_259] :
      ( ~ m1_subset_1('#skF_5'(A_257,B_258,C_259,'#skF_1'(A_257,B_258,C_259)),u1_struct_0(A_257))
      | k10_lattice3(A_257,B_258,C_259) = '#skF_1'(A_257,B_258,C_259)
      | ~ r1_orders_2(A_257,C_259,'#skF_1'(A_257,B_258,C_259))
      | ~ r1_orders_2(A_257,B_258,'#skF_1'(A_257,B_258,C_259))
      | ~ m1_subset_1('#skF_1'(A_257,B_258,C_259),u1_struct_0(A_257))
      | ~ m1_subset_1(C_259,u1_struct_0(A_257))
      | ~ m1_subset_1(B_258,u1_struct_0(A_257))
      | ~ l1_orders_2(A_257)
      | ~ v1_lattice3(A_257)
      | ~ v5_orders_2(A_257)
      | v2_struct_0(A_257) ) ),
    inference(resolution,[status(thm)],[c_28,c_861])).

tff(c_7474,plain,(
    ! [A_343,B_344,C_345] :
      ( k10_lattice3(A_343,B_344,C_345) = '#skF_1'(A_343,B_344,C_345)
      | ~ r1_orders_2(A_343,C_345,'#skF_1'(A_343,B_344,C_345))
      | ~ r1_orders_2(A_343,B_344,'#skF_1'(A_343,B_344,C_345))
      | ~ m1_subset_1('#skF_1'(A_343,B_344,C_345),u1_struct_0(A_343))
      | ~ m1_subset_1(C_345,u1_struct_0(A_343))
      | ~ m1_subset_1(B_344,u1_struct_0(A_343))
      | ~ l1_orders_2(A_343)
      | ~ v1_lattice3(A_343)
      | ~ v5_orders_2(A_343)
      | v2_struct_0(A_343) ) ),
    inference(resolution,[status(thm)],[c_30,c_2302])).

tff(c_7506,plain,
    ( k10_lattice3('#skF_6','#skF_7','#skF_8') = '#skF_1'('#skF_6','#skF_7','#skF_8')
    | ~ r1_orders_2('#skF_6','#skF_7','#skF_1'('#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1911,c_7474])).

tff(c_7572,plain,
    ( '#skF_1'('#skF_6','#skF_7','#skF_8') = '#skF_1'('#skF_6','#skF_8','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_1545,c_1544,c_6610,c_7506])).

tff(c_7574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_6671,c_7572])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:41:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.03/3.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.03/3.75  
% 10.03/3.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.03/3.75  %$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v2_struct_0 > v1_lattice3 > l1_orders_2 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_5 > #skF_3 > #skF_4
% 10.03/3.75  
% 10.03/3.75  %Foreground sorts:
% 10.03/3.75  
% 10.03/3.75  
% 10.03/3.75  %Background operators:
% 10.03/3.75  
% 10.03/3.75  
% 10.03/3.75  %Foreground operators:
% 10.03/3.75  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.03/3.75  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.03/3.75  tff('#skF_2', type, '#skF_2': $i > $i).
% 10.03/3.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.03/3.75  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 10.03/3.75  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 10.03/3.75  tff('#skF_7', type, '#skF_7': $i).
% 10.03/3.75  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 10.03/3.75  tff('#skF_6', type, '#skF_6': $i).
% 10.03/3.75  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 10.03/3.75  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 10.03/3.75  tff('#skF_8', type, '#skF_8': $i).
% 10.03/3.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.03/3.75  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 10.03/3.75  tff('#skF_3', type, '#skF_3': $i > $i).
% 10.03/3.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.03/3.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.03/3.75  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.03/3.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.03/3.75  
% 10.03/3.77  tff(f_106, negated_conjecture, ~(![A]: (((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k10_lattice3(A, B, C) = k10_lattice3(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_lattice3)).
% 10.03/3.77  tff(f_58, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (?[D]: (((m1_subset_1(D, u1_struct_0(A)) & r1_orders_2(A, B, D)) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_lattice3)).
% 10.03/3.77  tff(f_91, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l26_lattice3)).
% 10.03/3.77  tff(f_32, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 10.03/3.77  tff(c_44, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.03/3.77  tff(c_46, plain, (v1_lattice3('#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.03/3.77  tff(c_48, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.03/3.77  tff(c_40, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.03/3.77  tff(c_22, plain, (![A_2, B_33, C_41]: (m1_subset_1('#skF_1'(A_2, B_33, C_41), u1_struct_0(A_2)) | ~m1_subset_1(C_41, u1_struct_0(A_2)) | ~m1_subset_1(B_33, u1_struct_0(A_2)) | ~v1_lattice3(A_2) | ~l1_orders_2(A_2))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.03/3.77  tff(c_18, plain, (![A_2, C_41, B_33]: (r1_orders_2(A_2, C_41, '#skF_1'(A_2, B_33, C_41)) | ~m1_subset_1(C_41, u1_struct_0(A_2)) | ~m1_subset_1(B_33, u1_struct_0(A_2)) | ~v1_lattice3(A_2) | ~l1_orders_2(A_2))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.03/3.77  tff(c_20, plain, (![A_2, B_33, C_41]: (r1_orders_2(A_2, B_33, '#skF_1'(A_2, B_33, C_41)) | ~m1_subset_1(C_41, u1_struct_0(A_2)) | ~m1_subset_1(B_33, u1_struct_0(A_2)) | ~v1_lattice3(A_2) | ~l1_orders_2(A_2))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.03/3.77  tff(c_16, plain, (![A_2, B_33, C_41, E_46]: (r1_orders_2(A_2, '#skF_1'(A_2, B_33, C_41), E_46) | ~r1_orders_2(A_2, C_41, E_46) | ~r1_orders_2(A_2, B_33, E_46) | ~m1_subset_1(E_46, u1_struct_0(A_2)) | ~m1_subset_1(C_41, u1_struct_0(A_2)) | ~m1_subset_1(B_33, u1_struct_0(A_2)) | ~v1_lattice3(A_2) | ~l1_orders_2(A_2))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.03/3.77  tff(c_28, plain, (![A_59, B_83, C_95, D_101]: (r1_orders_2(A_59, B_83, '#skF_5'(A_59, B_83, C_95, D_101)) | k10_lattice3(A_59, B_83, C_95)=D_101 | ~r1_orders_2(A_59, C_95, D_101) | ~r1_orders_2(A_59, B_83, D_101) | ~m1_subset_1(D_101, u1_struct_0(A_59)) | ~m1_subset_1(C_95, u1_struct_0(A_59)) | ~m1_subset_1(B_83, u1_struct_0(A_59)) | ~l1_orders_2(A_59) | ~v1_lattice3(A_59) | ~v5_orders_2(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.03/3.77  tff(c_79, plain, (![A_153, D_154, B_155, C_156]: (~r1_orders_2(A_153, D_154, '#skF_5'(A_153, B_155, C_156, D_154)) | k10_lattice3(A_153, B_155, C_156)=D_154 | ~r1_orders_2(A_153, C_156, D_154) | ~r1_orders_2(A_153, B_155, D_154) | ~m1_subset_1(D_154, u1_struct_0(A_153)) | ~m1_subset_1(C_156, u1_struct_0(A_153)) | ~m1_subset_1(B_155, u1_struct_0(A_153)) | ~l1_orders_2(A_153) | ~v1_lattice3(A_153) | ~v5_orders_2(A_153) | v2_struct_0(A_153))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.03/3.77  tff(c_101, plain, (![A_164, D_165, C_166]: (k10_lattice3(A_164, D_165, C_166)=D_165 | ~r1_orders_2(A_164, C_166, D_165) | ~r1_orders_2(A_164, D_165, D_165) | ~m1_subset_1(C_166, u1_struct_0(A_164)) | ~m1_subset_1(D_165, u1_struct_0(A_164)) | ~l1_orders_2(A_164) | ~v1_lattice3(A_164) | ~v5_orders_2(A_164) | v2_struct_0(A_164))), inference(resolution, [status(thm)], [c_28, c_79])).
% 10.03/3.77  tff(c_129, plain, (![A_170, B_171, C_172]: (k10_lattice3(A_170, '#skF_1'(A_170, B_171, C_172), B_171)='#skF_1'(A_170, B_171, C_172) | ~r1_orders_2(A_170, '#skF_1'(A_170, B_171, C_172), '#skF_1'(A_170, B_171, C_172)) | ~m1_subset_1('#skF_1'(A_170, B_171, C_172), u1_struct_0(A_170)) | ~v5_orders_2(A_170) | v2_struct_0(A_170) | ~m1_subset_1(C_172, u1_struct_0(A_170)) | ~m1_subset_1(B_171, u1_struct_0(A_170)) | ~v1_lattice3(A_170) | ~l1_orders_2(A_170))), inference(resolution, [status(thm)], [c_20, c_101])).
% 10.03/3.77  tff(c_140, plain, (![A_177, B_178, C_179]: (k10_lattice3(A_177, '#skF_1'(A_177, B_178, C_179), B_178)='#skF_1'(A_177, B_178, C_179) | ~v5_orders_2(A_177) | v2_struct_0(A_177) | ~r1_orders_2(A_177, C_179, '#skF_1'(A_177, B_178, C_179)) | ~r1_orders_2(A_177, B_178, '#skF_1'(A_177, B_178, C_179)) | ~m1_subset_1('#skF_1'(A_177, B_178, C_179), u1_struct_0(A_177)) | ~m1_subset_1(C_179, u1_struct_0(A_177)) | ~m1_subset_1(B_178, u1_struct_0(A_177)) | ~v1_lattice3(A_177) | ~l1_orders_2(A_177))), inference(resolution, [status(thm)], [c_16, c_129])).
% 10.03/3.77  tff(c_152, plain, (![A_180, C_181]: (k10_lattice3(A_180, '#skF_1'(A_180, C_181, C_181), C_181)='#skF_1'(A_180, C_181, C_181) | ~v5_orders_2(A_180) | v2_struct_0(A_180) | ~r1_orders_2(A_180, C_181, '#skF_1'(A_180, C_181, C_181)) | ~m1_subset_1('#skF_1'(A_180, C_181, C_181), u1_struct_0(A_180)) | ~m1_subset_1(C_181, u1_struct_0(A_180)) | ~v1_lattice3(A_180) | ~l1_orders_2(A_180))), inference(resolution, [status(thm)], [c_20, c_140])).
% 10.03/3.77  tff(c_165, plain, (![A_182, B_183]: (k10_lattice3(A_182, '#skF_1'(A_182, B_183, B_183), B_183)='#skF_1'(A_182, B_183, B_183) | ~v5_orders_2(A_182) | v2_struct_0(A_182) | ~m1_subset_1('#skF_1'(A_182, B_183, B_183), u1_struct_0(A_182)) | ~m1_subset_1(B_183, u1_struct_0(A_182)) | ~v1_lattice3(A_182) | ~l1_orders_2(A_182))), inference(resolution, [status(thm)], [c_18, c_152])).
% 10.03/3.77  tff(c_170, plain, (![A_184, C_185]: (k10_lattice3(A_184, '#skF_1'(A_184, C_185, C_185), C_185)='#skF_1'(A_184, C_185, C_185) | ~v5_orders_2(A_184) | v2_struct_0(A_184) | ~m1_subset_1(C_185, u1_struct_0(A_184)) | ~v1_lattice3(A_184) | ~l1_orders_2(A_184))), inference(resolution, [status(thm)], [c_22, c_165])).
% 10.03/3.77  tff(c_182, plain, (k10_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_8'), '#skF_8')='#skF_1'('#skF_6', '#skF_8', '#skF_8') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~v1_lattice3('#skF_6') | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_40, c_170])).
% 10.03/3.77  tff(c_192, plain, (k10_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_8'), '#skF_8')='#skF_1'('#skF_6', '#skF_8', '#skF_8') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_48, c_182])).
% 10.03/3.77  tff(c_209, plain, (v2_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_192])).
% 10.03/3.77  tff(c_2, plain, (![A_1]: (~v2_struct_0(A_1) | ~v1_lattice3(A_1) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.03/3.77  tff(c_212, plain, (~v1_lattice3('#skF_6') | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_209, c_2])).
% 10.03/3.77  tff(c_216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_212])).
% 10.03/3.77  tff(c_218, plain, (~v2_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_192])).
% 10.03/3.77  tff(c_42, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.03/3.77  tff(c_1139, plain, (![A_225, B_226, C_227]: (k10_lattice3(A_225, '#skF_1'(A_225, B_226, C_227), B_226)='#skF_1'(A_225, B_226, C_227) | ~v5_orders_2(A_225) | v2_struct_0(A_225) | ~r1_orders_2(A_225, B_226, '#skF_1'(A_225, B_226, C_227)) | ~m1_subset_1('#skF_1'(A_225, B_226, C_227), u1_struct_0(A_225)) | ~m1_subset_1(C_227, u1_struct_0(A_225)) | ~m1_subset_1(B_226, u1_struct_0(A_225)) | ~v1_lattice3(A_225) | ~l1_orders_2(A_225))), inference(resolution, [status(thm)], [c_18, c_140])).
% 10.03/3.77  tff(c_1174, plain, (![A_228, B_229, C_230]: (k10_lattice3(A_228, '#skF_1'(A_228, B_229, C_230), B_229)='#skF_1'(A_228, B_229, C_230) | ~v5_orders_2(A_228) | v2_struct_0(A_228) | ~m1_subset_1('#skF_1'(A_228, B_229, C_230), u1_struct_0(A_228)) | ~m1_subset_1(C_230, u1_struct_0(A_228)) | ~m1_subset_1(B_229, u1_struct_0(A_228)) | ~v1_lattice3(A_228) | ~l1_orders_2(A_228))), inference(resolution, [status(thm)], [c_20, c_1139])).
% 10.03/3.77  tff(c_1368, plain, (![A_236, B_237, C_238]: (k10_lattice3(A_236, '#skF_1'(A_236, B_237, C_238), B_237)='#skF_1'(A_236, B_237, C_238) | ~v5_orders_2(A_236) | v2_struct_0(A_236) | ~m1_subset_1(C_238, u1_struct_0(A_236)) | ~m1_subset_1(B_237, u1_struct_0(A_236)) | ~v1_lattice3(A_236) | ~l1_orders_2(A_236))), inference(resolution, [status(thm)], [c_22, c_1174])).
% 10.03/3.77  tff(c_1384, plain, (![B_237]: (k10_lattice3('#skF_6', '#skF_1'('#skF_6', B_237, '#skF_8'), B_237)='#skF_1'('#skF_6', B_237, '#skF_8') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~m1_subset_1(B_237, u1_struct_0('#skF_6')) | ~v1_lattice3('#skF_6') | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_1368])).
% 10.03/3.77  tff(c_1402, plain, (![B_237]: (k10_lattice3('#skF_6', '#skF_1'('#skF_6', B_237, '#skF_8'), B_237)='#skF_1'('#skF_6', B_237, '#skF_8') | v2_struct_0('#skF_6') | ~m1_subset_1(B_237, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_48, c_1384])).
% 10.03/3.77  tff(c_1408, plain, (![B_239]: (k10_lattice3('#skF_6', '#skF_1'('#skF_6', B_239, '#skF_8'), B_239)='#skF_1'('#skF_6', B_239, '#skF_8') | ~m1_subset_1(B_239, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_218, c_1402])).
% 10.03/3.77  tff(c_1452, plain, (k10_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_7')='#skF_1'('#skF_6', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_42, c_1408])).
% 10.03/3.77  tff(c_34, plain, (![A_59, C_95, B_83]: (r1_orders_2(A_59, C_95, k10_lattice3(A_59, B_83, C_95)) | ~m1_subset_1(k10_lattice3(A_59, B_83, C_95), u1_struct_0(A_59)) | ~m1_subset_1(C_95, u1_struct_0(A_59)) | ~m1_subset_1(B_83, u1_struct_0(A_59)) | ~l1_orders_2(A_59) | ~v1_lattice3(A_59) | ~v5_orders_2(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.03/3.77  tff(c_1457, plain, (r1_orders_2('#skF_6', '#skF_7', k10_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_7')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v1_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1452, c_34])).
% 10.03/3.77  tff(c_1466, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_1'('#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_1452, c_1457])).
% 10.03/3.77  tff(c_1467, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_1'('#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_218, c_1466])).
% 10.03/3.77  tff(c_1536, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_1467])).
% 10.03/3.77  tff(c_1539, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~v1_lattice3('#skF_6') | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_22, c_1536])).
% 10.03/3.77  tff(c_1543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_42, c_40, c_1539])).
% 10.03/3.77  tff(c_1545, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_1467])).
% 10.03/3.77  tff(c_36, plain, (![A_59, B_83, C_95]: (r1_orders_2(A_59, B_83, k10_lattice3(A_59, B_83, C_95)) | ~m1_subset_1(k10_lattice3(A_59, B_83, C_95), u1_struct_0(A_59)) | ~m1_subset_1(C_95, u1_struct_0(A_59)) | ~m1_subset_1(B_83, u1_struct_0(A_59)) | ~l1_orders_2(A_59) | ~v1_lattice3(A_59) | ~v5_orders_2(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.03/3.77  tff(c_1459, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), k10_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_7')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v1_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1452, c_36])).
% 10.03/3.77  tff(c_1469, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_1'('#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_1452, c_1459])).
% 10.03/3.77  tff(c_1470, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_1'('#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_218, c_1469])).
% 10.03/3.77  tff(c_1865, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_1'('#skF_6', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1545, c_1470])).
% 10.03/3.77  tff(c_121, plain, (![A_2, B_33, C_41]: (k10_lattice3(A_2, '#skF_1'(A_2, B_33, C_41), C_41)='#skF_1'(A_2, B_33, C_41) | ~r1_orders_2(A_2, '#skF_1'(A_2, B_33, C_41), '#skF_1'(A_2, B_33, C_41)) | ~m1_subset_1('#skF_1'(A_2, B_33, C_41), u1_struct_0(A_2)) | ~v5_orders_2(A_2) | v2_struct_0(A_2) | ~m1_subset_1(C_41, u1_struct_0(A_2)) | ~m1_subset_1(B_33, u1_struct_0(A_2)) | ~v1_lattice3(A_2) | ~l1_orders_2(A_2))), inference(resolution, [status(thm)], [c_18, c_101])).
% 10.03/3.77  tff(c_1872, plain, (k10_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_8')='#skF_1'('#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~v1_lattice3('#skF_6') | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_1865, c_121])).
% 10.03/3.77  tff(c_1887, plain, (k10_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_8')='#skF_1'('#skF_6', '#skF_7', '#skF_8') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_42, c_40, c_48, c_1545, c_1872])).
% 10.03/3.77  tff(c_1888, plain, (k10_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_8')='#skF_1'('#skF_6', '#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_218, c_1887])).
% 10.03/3.77  tff(c_1901, plain, (r1_orders_2('#skF_6', '#skF_8', k10_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v1_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1888, c_34])).
% 10.03/3.77  tff(c_1910, plain, (r1_orders_2('#skF_6', '#skF_8', '#skF_1'('#skF_6', '#skF_7', '#skF_8')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_1545, c_40, c_1545, c_1888, c_1901])).
% 10.03/3.77  tff(c_1911, plain, (r1_orders_2('#skF_6', '#skF_8', '#skF_1'('#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_218, c_1910])).
% 10.03/3.77  tff(c_1544, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_1'('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_1467])).
% 10.03/3.77  tff(c_30, plain, (![A_59, B_83, C_95, D_101]: (m1_subset_1('#skF_5'(A_59, B_83, C_95, D_101), u1_struct_0(A_59)) | k10_lattice3(A_59, B_83, C_95)=D_101 | ~r1_orders_2(A_59, C_95, D_101) | ~r1_orders_2(A_59, B_83, D_101) | ~m1_subset_1(D_101, u1_struct_0(A_59)) | ~m1_subset_1(C_95, u1_struct_0(A_59)) | ~m1_subset_1(B_83, u1_struct_0(A_59)) | ~l1_orders_2(A_59) | ~v1_lattice3(A_59) | ~v5_orders_2(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.03/3.77  tff(c_26, plain, (![A_59, C_95, B_83, D_101]: (r1_orders_2(A_59, C_95, '#skF_5'(A_59, B_83, C_95, D_101)) | k10_lattice3(A_59, B_83, C_95)=D_101 | ~r1_orders_2(A_59, C_95, D_101) | ~r1_orders_2(A_59, B_83, D_101) | ~m1_subset_1(D_101, u1_struct_0(A_59)) | ~m1_subset_1(C_95, u1_struct_0(A_59)) | ~m1_subset_1(B_83, u1_struct_0(A_59)) | ~l1_orders_2(A_59) | ~v1_lattice3(A_59) | ~v5_orders_2(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.03/3.77  tff(c_196, plain, (![C_187, B_188, C_190, B_186, A_189]: (k10_lattice3(A_189, B_188, C_190)='#skF_1'(A_189, B_186, C_187) | ~r1_orders_2(A_189, C_190, '#skF_1'(A_189, B_186, C_187)) | ~r1_orders_2(A_189, B_188, '#skF_1'(A_189, B_186, C_187)) | ~m1_subset_1('#skF_1'(A_189, B_186, C_187), u1_struct_0(A_189)) | ~m1_subset_1(C_190, u1_struct_0(A_189)) | ~m1_subset_1(B_188, u1_struct_0(A_189)) | ~v5_orders_2(A_189) | v2_struct_0(A_189) | ~r1_orders_2(A_189, C_187, '#skF_5'(A_189, B_188, C_190, '#skF_1'(A_189, B_186, C_187))) | ~r1_orders_2(A_189, B_186, '#skF_5'(A_189, B_188, C_190, '#skF_1'(A_189, B_186, C_187))) | ~m1_subset_1('#skF_5'(A_189, B_188, C_190, '#skF_1'(A_189, B_186, C_187)), u1_struct_0(A_189)) | ~m1_subset_1(C_187, u1_struct_0(A_189)) | ~m1_subset_1(B_186, u1_struct_0(A_189)) | ~v1_lattice3(A_189) | ~l1_orders_2(A_189))), inference(resolution, [status(thm)], [c_16, c_79])).
% 10.03/3.77  tff(c_711, plain, (![A_205, B_206, B_207, C_208]: (~r1_orders_2(A_205, B_206, '#skF_5'(A_205, B_207, C_208, '#skF_1'(A_205, B_206, B_207))) | ~m1_subset_1('#skF_5'(A_205, B_207, C_208, '#skF_1'(A_205, B_206, B_207)), u1_struct_0(A_205)) | ~m1_subset_1(B_206, u1_struct_0(A_205)) | k10_lattice3(A_205, B_207, C_208)='#skF_1'(A_205, B_206, B_207) | ~r1_orders_2(A_205, C_208, '#skF_1'(A_205, B_206, B_207)) | ~r1_orders_2(A_205, B_207, '#skF_1'(A_205, B_206, B_207)) | ~m1_subset_1('#skF_1'(A_205, B_206, B_207), u1_struct_0(A_205)) | ~m1_subset_1(C_208, u1_struct_0(A_205)) | ~m1_subset_1(B_207, u1_struct_0(A_205)) | ~l1_orders_2(A_205) | ~v1_lattice3(A_205) | ~v5_orders_2(A_205) | v2_struct_0(A_205))), inference(resolution, [status(thm)], [c_28, c_196])).
% 10.03/3.77  tff(c_1946, plain, (![A_247, B_248, C_249]: (~m1_subset_1('#skF_5'(A_247, B_248, C_249, '#skF_1'(A_247, C_249, B_248)), u1_struct_0(A_247)) | k10_lattice3(A_247, B_248, C_249)='#skF_1'(A_247, C_249, B_248) | ~r1_orders_2(A_247, C_249, '#skF_1'(A_247, C_249, B_248)) | ~r1_orders_2(A_247, B_248, '#skF_1'(A_247, C_249, B_248)) | ~m1_subset_1('#skF_1'(A_247, C_249, B_248), u1_struct_0(A_247)) | ~m1_subset_1(C_249, u1_struct_0(A_247)) | ~m1_subset_1(B_248, u1_struct_0(A_247)) | ~l1_orders_2(A_247) | ~v1_lattice3(A_247) | ~v5_orders_2(A_247) | v2_struct_0(A_247))), inference(resolution, [status(thm)], [c_26, c_711])).
% 10.03/3.77  tff(c_6509, plain, (![A_340, B_341, C_342]: (k10_lattice3(A_340, B_341, C_342)='#skF_1'(A_340, C_342, B_341) | ~r1_orders_2(A_340, C_342, '#skF_1'(A_340, C_342, B_341)) | ~r1_orders_2(A_340, B_341, '#skF_1'(A_340, C_342, B_341)) | ~m1_subset_1('#skF_1'(A_340, C_342, B_341), u1_struct_0(A_340)) | ~m1_subset_1(C_342, u1_struct_0(A_340)) | ~m1_subset_1(B_341, u1_struct_0(A_340)) | ~l1_orders_2(A_340) | ~v1_lattice3(A_340) | ~v5_orders_2(A_340) | v2_struct_0(A_340))), inference(resolution, [status(thm)], [c_30, c_1946])).
% 10.03/3.77  tff(c_6541, plain, (k10_lattice3('#skF_6', '#skF_8', '#skF_7')='#skF_1'('#skF_6', '#skF_7', '#skF_8') | ~r1_orders_2('#skF_6', '#skF_8', '#skF_1'('#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v1_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1544, c_6509])).
% 10.03/3.77  tff(c_6613, plain, (k10_lattice3('#skF_6', '#skF_8', '#skF_7')='#skF_1'('#skF_6', '#skF_7', '#skF_8') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_40, c_42, c_1545, c_1911, c_6541])).
% 10.03/3.77  tff(c_6614, plain, (k10_lattice3('#skF_6', '#skF_8', '#skF_7')='#skF_1'('#skF_6', '#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_218, c_6613])).
% 10.03/3.77  tff(c_1386, plain, (![B_237]: (k10_lattice3('#skF_6', '#skF_1'('#skF_6', B_237, '#skF_7'), B_237)='#skF_1'('#skF_6', B_237, '#skF_7') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~m1_subset_1(B_237, u1_struct_0('#skF_6')) | ~v1_lattice3('#skF_6') | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_42, c_1368])).
% 10.03/3.77  tff(c_1406, plain, (![B_237]: (k10_lattice3('#skF_6', '#skF_1'('#skF_6', B_237, '#skF_7'), B_237)='#skF_1'('#skF_6', B_237, '#skF_7') | v2_struct_0('#skF_6') | ~m1_subset_1(B_237, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_48, c_1386])).
% 10.03/3.77  tff(c_1472, plain, (![B_240]: (k10_lattice3('#skF_6', '#skF_1'('#skF_6', B_240, '#skF_7'), B_240)='#skF_1'('#skF_6', B_240, '#skF_7') | ~m1_subset_1(B_240, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_218, c_1406])).
% 10.03/3.77  tff(c_1514, plain, (k10_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_8')='#skF_1'('#skF_6', '#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_40, c_1472])).
% 10.03/3.77  tff(c_1521, plain, (r1_orders_2('#skF_6', '#skF_8', k10_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v1_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1514, c_34])).
% 10.03/3.77  tff(c_1530, plain, (r1_orders_2('#skF_6', '#skF_8', '#skF_1'('#skF_6', '#skF_8', '#skF_7')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_40, c_1514, c_1521])).
% 10.03/3.77  tff(c_1531, plain, (r1_orders_2('#skF_6', '#skF_8', '#skF_1'('#skF_6', '#skF_8', '#skF_7')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_218, c_1530])).
% 10.03/3.77  tff(c_1616, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_1531])).
% 10.03/3.77  tff(c_1619, plain, (~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~v1_lattice3('#skF_6') | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_22, c_1616])).
% 10.03/3.77  tff(c_1623, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_40, c_42, c_1619])).
% 10.03/3.77  tff(c_1625, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_1531])).
% 10.03/3.77  tff(c_1523, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), k10_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v1_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1514, c_36])).
% 10.03/3.77  tff(c_1533, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_1'('#skF_6', '#skF_8', '#skF_7')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_40, c_1514, c_1523])).
% 10.03/3.77  tff(c_1534, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_1'('#skF_6', '#skF_8', '#skF_7')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_218, c_1533])).
% 10.03/3.77  tff(c_1638, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_1534])).
% 10.03/3.77  tff(c_1664, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1625, c_1638])).
% 10.03/3.77  tff(c_1665, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_1'('#skF_6', '#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_1534])).
% 10.03/3.77  tff(c_1698, plain, (k10_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_7')='#skF_1'('#skF_6', '#skF_8', '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6')) | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~v1_lattice3('#skF_6') | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_1665, c_121])).
% 10.03/3.77  tff(c_1713, plain, (k10_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_7')='#skF_1'('#skF_6', '#skF_8', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_40, c_42, c_48, c_1625, c_1698])).
% 10.03/3.77  tff(c_1714, plain, (k10_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_7')='#skF_1'('#skF_6', '#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_218, c_1713])).
% 10.03/3.77  tff(c_1761, plain, (r1_orders_2('#skF_6', '#skF_7', k10_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_7')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v1_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1714, c_34])).
% 10.03/3.77  tff(c_1770, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_1'('#skF_6', '#skF_8', '#skF_7')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_1625, c_42, c_1625, c_1714, c_1761])).
% 10.03/3.77  tff(c_1771, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_1'('#skF_6', '#skF_8', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_218, c_1770])).
% 10.03/3.77  tff(c_1624, plain, (r1_orders_2('#skF_6', '#skF_8', '#skF_1'('#skF_6', '#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_1531])).
% 10.03/3.77  tff(c_6539, plain, (k10_lattice3('#skF_6', '#skF_7', '#skF_8')='#skF_1'('#skF_6', '#skF_8', '#skF_7') | ~r1_orders_2('#skF_6', '#skF_7', '#skF_1'('#skF_6', '#skF_8', '#skF_7')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v1_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1624, c_6509])).
% 10.03/3.77  tff(c_6609, plain, (k10_lattice3('#skF_6', '#skF_7', '#skF_8')='#skF_1'('#skF_6', '#skF_8', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_1625, c_1771, c_6539])).
% 10.03/3.77  tff(c_6610, plain, (k10_lattice3('#skF_6', '#skF_7', '#skF_8')='#skF_1'('#skF_6', '#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_218, c_6609])).
% 10.03/3.77  tff(c_38, plain, (k10_lattice3('#skF_6', '#skF_7', '#skF_8')!=k10_lattice3('#skF_6', '#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.03/3.77  tff(c_6632, plain, (k10_lattice3('#skF_6', '#skF_8', '#skF_7')!='#skF_1'('#skF_6', '#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6610, c_38])).
% 10.03/3.77  tff(c_6671, plain, ('#skF_1'('#skF_6', '#skF_7', '#skF_8')!='#skF_1'('#skF_6', '#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6614, c_6632])).
% 10.03/3.77  tff(c_861, plain, (![A_209, B_210, B_211, C_212]: (~r1_orders_2(A_209, B_210, '#skF_5'(A_209, B_211, C_212, '#skF_1'(A_209, B_210, C_212))) | ~m1_subset_1('#skF_5'(A_209, B_211, C_212, '#skF_1'(A_209, B_210, C_212)), u1_struct_0(A_209)) | ~m1_subset_1(B_210, u1_struct_0(A_209)) | k10_lattice3(A_209, B_211, C_212)='#skF_1'(A_209, B_210, C_212) | ~r1_orders_2(A_209, C_212, '#skF_1'(A_209, B_210, C_212)) | ~r1_orders_2(A_209, B_211, '#skF_1'(A_209, B_210, C_212)) | ~m1_subset_1('#skF_1'(A_209, B_210, C_212), u1_struct_0(A_209)) | ~m1_subset_1(C_212, u1_struct_0(A_209)) | ~m1_subset_1(B_211, u1_struct_0(A_209)) | ~l1_orders_2(A_209) | ~v1_lattice3(A_209) | ~v5_orders_2(A_209) | v2_struct_0(A_209))), inference(resolution, [status(thm)], [c_26, c_196])).
% 10.03/3.77  tff(c_2302, plain, (![A_257, B_258, C_259]: (~m1_subset_1('#skF_5'(A_257, B_258, C_259, '#skF_1'(A_257, B_258, C_259)), u1_struct_0(A_257)) | k10_lattice3(A_257, B_258, C_259)='#skF_1'(A_257, B_258, C_259) | ~r1_orders_2(A_257, C_259, '#skF_1'(A_257, B_258, C_259)) | ~r1_orders_2(A_257, B_258, '#skF_1'(A_257, B_258, C_259)) | ~m1_subset_1('#skF_1'(A_257, B_258, C_259), u1_struct_0(A_257)) | ~m1_subset_1(C_259, u1_struct_0(A_257)) | ~m1_subset_1(B_258, u1_struct_0(A_257)) | ~l1_orders_2(A_257) | ~v1_lattice3(A_257) | ~v5_orders_2(A_257) | v2_struct_0(A_257))), inference(resolution, [status(thm)], [c_28, c_861])).
% 10.03/3.77  tff(c_7474, plain, (![A_343, B_344, C_345]: (k10_lattice3(A_343, B_344, C_345)='#skF_1'(A_343, B_344, C_345) | ~r1_orders_2(A_343, C_345, '#skF_1'(A_343, B_344, C_345)) | ~r1_orders_2(A_343, B_344, '#skF_1'(A_343, B_344, C_345)) | ~m1_subset_1('#skF_1'(A_343, B_344, C_345), u1_struct_0(A_343)) | ~m1_subset_1(C_345, u1_struct_0(A_343)) | ~m1_subset_1(B_344, u1_struct_0(A_343)) | ~l1_orders_2(A_343) | ~v1_lattice3(A_343) | ~v5_orders_2(A_343) | v2_struct_0(A_343))), inference(resolution, [status(thm)], [c_30, c_2302])).
% 10.03/3.77  tff(c_7506, plain, (k10_lattice3('#skF_6', '#skF_7', '#skF_8')='#skF_1'('#skF_6', '#skF_7', '#skF_8') | ~r1_orders_2('#skF_6', '#skF_7', '#skF_1'('#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v1_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1911, c_7474])).
% 10.03/3.77  tff(c_7572, plain, ('#skF_1'('#skF_6', '#skF_7', '#skF_8')='#skF_1'('#skF_6', '#skF_8', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_1545, c_1544, c_6610, c_7506])).
% 10.03/3.77  tff(c_7574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_218, c_6671, c_7572])).
% 10.03/3.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.03/3.77  
% 10.03/3.77  Inference rules
% 10.03/3.77  ----------------------
% 10.03/3.77  #Ref     : 0
% 10.03/3.77  #Sup     : 1454
% 10.03/3.77  #Fact    : 0
% 10.03/3.77  #Define  : 0
% 10.03/3.77  #Split   : 27
% 10.03/3.77  #Chain   : 0
% 10.03/3.77  #Close   : 0
% 10.03/3.77  
% 10.03/3.77  Ordering : KBO
% 10.03/3.77  
% 10.03/3.77  Simplification rules
% 10.03/3.77  ----------------------
% 10.03/3.77  #Subsume      : 96
% 10.03/3.77  #Demod        : 7980
% 10.03/3.77  #Tautology    : 823
% 10.03/3.77  #SimpNegUnit  : 871
% 10.03/3.77  #BackRed      : 72
% 10.03/3.77  
% 10.03/3.77  #Partial instantiations: 0
% 10.03/3.77  #Strategies tried      : 1
% 10.03/3.77  
% 10.03/3.77  Timing (in seconds)
% 10.03/3.77  ----------------------
% 10.03/3.77  Preprocessing        : 0.33
% 10.03/3.77  Parsing              : 0.17
% 10.03/3.77  CNF conversion       : 0.04
% 10.03/3.77  Main loop            : 2.66
% 10.03/3.78  Inferencing          : 0.52
% 10.03/3.78  Reduction            : 0.94
% 10.03/3.78  Demodulation         : 0.78
% 10.03/3.78  BG Simplification    : 0.06
% 10.03/3.78  Subsumption          : 1.06
% 10.03/3.78  Abstraction          : 0.10
% 10.03/3.78  MUC search           : 0.00
% 10.03/3.78  Cooper               : 0.00
% 10.03/3.78  Total                : 3.04
% 10.03/3.78  Index Insertion      : 0.00
% 10.03/3.78  Index Deletion       : 0.00
% 10.03/3.78  Index Matching       : 0.00
% 10.03/3.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
