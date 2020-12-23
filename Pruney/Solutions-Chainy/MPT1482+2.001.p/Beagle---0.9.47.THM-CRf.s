%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:39 EST 2020

% Result     : Theorem 9.75s
% Output     : CNFRefutation 10.00s
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
%$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v2_struct_0 > v2_lattice3 > l1_orders_2 > k11_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_5 > #skF_3 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

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

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( v5_orders_2(A)
          & v2_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k11_lattice3(A,B,C) = k11_lattice3(A,C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ? [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                    & r1_orders_2(A,D,B)
                    & r1_orders_2(A,D,C)
                    & ! [E] :
                        ( m1_subset_1(E,u1_struct_0(A))
                       => ( ( r1_orders_2(A,E,B)
                            & r1_orders_2(A,E,C) )
                         => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_lattice3)).

tff(f_91,axiom,(
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
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

tff(c_44,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_46,plain,(
    v2_lattice3('#skF_6') ),
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
      | ~ v2_lattice3(A_2)
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [A_2,B_33,C_41] :
      ( r1_orders_2(A_2,'#skF_1'(A_2,B_33,C_41),C_41)
      | ~ m1_subset_1(C_41,u1_struct_0(A_2))
      | ~ m1_subset_1(B_33,u1_struct_0(A_2))
      | ~ v2_lattice3(A_2)
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    ! [A_2,B_33,C_41] :
      ( r1_orders_2(A_2,'#skF_1'(A_2,B_33,C_41),B_33)
      | ~ m1_subset_1(C_41,u1_struct_0(A_2))
      | ~ m1_subset_1(B_33,u1_struct_0(A_2))
      | ~ v2_lattice3(A_2)
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ! [A_2,E_46,B_33,C_41] :
      ( r1_orders_2(A_2,E_46,'#skF_1'(A_2,B_33,C_41))
      | ~ r1_orders_2(A_2,E_46,C_41)
      | ~ r1_orders_2(A_2,E_46,B_33)
      | ~ m1_subset_1(E_46,u1_struct_0(A_2))
      | ~ m1_subset_1(C_41,u1_struct_0(A_2))
      | ~ m1_subset_1(B_33,u1_struct_0(A_2))
      | ~ v2_lattice3(A_2)
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [A_59,B_83,C_95,D_101] :
      ( r1_orders_2(A_59,'#skF_5'(A_59,B_83,C_95,D_101),B_83)
      | k11_lattice3(A_59,B_83,C_95) = D_101
      | ~ r1_orders_2(A_59,D_101,C_95)
      | ~ r1_orders_2(A_59,D_101,B_83)
      | ~ m1_subset_1(D_101,u1_struct_0(A_59))
      | ~ m1_subset_1(C_95,u1_struct_0(A_59))
      | ~ m1_subset_1(B_83,u1_struct_0(A_59))
      | ~ l1_orders_2(A_59)
      | ~ v2_lattice3(A_59)
      | ~ v5_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_82,plain,(
    ! [A_153,B_154,C_155,D_156] :
      ( ~ r1_orders_2(A_153,'#skF_5'(A_153,B_154,C_155,D_156),D_156)
      | k11_lattice3(A_153,B_154,C_155) = D_156
      | ~ r1_orders_2(A_153,D_156,C_155)
      | ~ r1_orders_2(A_153,D_156,B_154)
      | ~ m1_subset_1(D_156,u1_struct_0(A_153))
      | ~ m1_subset_1(C_155,u1_struct_0(A_153))
      | ~ m1_subset_1(B_154,u1_struct_0(A_153))
      | ~ l1_orders_2(A_153)
      | ~ v2_lattice3(A_153)
      | ~ v5_orders_2(A_153)
      | v2_struct_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_104,plain,(
    ! [A_164,B_165,C_166] :
      ( k11_lattice3(A_164,B_165,C_166) = B_165
      | ~ r1_orders_2(A_164,B_165,C_166)
      | ~ r1_orders_2(A_164,B_165,B_165)
      | ~ m1_subset_1(C_166,u1_struct_0(A_164))
      | ~ m1_subset_1(B_165,u1_struct_0(A_164))
      | ~ l1_orders_2(A_164)
      | ~ v2_lattice3(A_164)
      | ~ v5_orders_2(A_164)
      | v2_struct_0(A_164) ) ),
    inference(resolution,[status(thm)],[c_28,c_82])).

tff(c_132,plain,(
    ! [A_170,B_171,C_172] :
      ( k11_lattice3(A_170,'#skF_1'(A_170,B_171,C_172),B_171) = '#skF_1'(A_170,B_171,C_172)
      | ~ r1_orders_2(A_170,'#skF_1'(A_170,B_171,C_172),'#skF_1'(A_170,B_171,C_172))
      | ~ m1_subset_1('#skF_1'(A_170,B_171,C_172),u1_struct_0(A_170))
      | ~ v5_orders_2(A_170)
      | v2_struct_0(A_170)
      | ~ m1_subset_1(C_172,u1_struct_0(A_170))
      | ~ m1_subset_1(B_171,u1_struct_0(A_170))
      | ~ v2_lattice3(A_170)
      | ~ l1_orders_2(A_170) ) ),
    inference(resolution,[status(thm)],[c_20,c_104])).

tff(c_143,plain,(
    ! [A_177,B_178,C_179] :
      ( k11_lattice3(A_177,'#skF_1'(A_177,B_178,C_179),B_178) = '#skF_1'(A_177,B_178,C_179)
      | ~ v5_orders_2(A_177)
      | v2_struct_0(A_177)
      | ~ r1_orders_2(A_177,'#skF_1'(A_177,B_178,C_179),C_179)
      | ~ r1_orders_2(A_177,'#skF_1'(A_177,B_178,C_179),B_178)
      | ~ m1_subset_1('#skF_1'(A_177,B_178,C_179),u1_struct_0(A_177))
      | ~ m1_subset_1(C_179,u1_struct_0(A_177))
      | ~ m1_subset_1(B_178,u1_struct_0(A_177))
      | ~ v2_lattice3(A_177)
      | ~ l1_orders_2(A_177) ) ),
    inference(resolution,[status(thm)],[c_16,c_132])).

tff(c_155,plain,(
    ! [A_180,B_181] :
      ( k11_lattice3(A_180,'#skF_1'(A_180,B_181,B_181),B_181) = '#skF_1'(A_180,B_181,B_181)
      | ~ v5_orders_2(A_180)
      | v2_struct_0(A_180)
      | ~ r1_orders_2(A_180,'#skF_1'(A_180,B_181,B_181),B_181)
      | ~ m1_subset_1('#skF_1'(A_180,B_181,B_181),u1_struct_0(A_180))
      | ~ m1_subset_1(B_181,u1_struct_0(A_180))
      | ~ v2_lattice3(A_180)
      | ~ l1_orders_2(A_180) ) ),
    inference(resolution,[status(thm)],[c_20,c_143])).

tff(c_168,plain,(
    ! [A_182,C_183] :
      ( k11_lattice3(A_182,'#skF_1'(A_182,C_183,C_183),C_183) = '#skF_1'(A_182,C_183,C_183)
      | ~ v5_orders_2(A_182)
      | v2_struct_0(A_182)
      | ~ m1_subset_1('#skF_1'(A_182,C_183,C_183),u1_struct_0(A_182))
      | ~ m1_subset_1(C_183,u1_struct_0(A_182))
      | ~ v2_lattice3(A_182)
      | ~ l1_orders_2(A_182) ) ),
    inference(resolution,[status(thm)],[c_18,c_155])).

tff(c_173,plain,(
    ! [A_184,C_185] :
      ( k11_lattice3(A_184,'#skF_1'(A_184,C_185,C_185),C_185) = '#skF_1'(A_184,C_185,C_185)
      | ~ v5_orders_2(A_184)
      | v2_struct_0(A_184)
      | ~ m1_subset_1(C_185,u1_struct_0(A_184))
      | ~ v2_lattice3(A_184)
      | ~ l1_orders_2(A_184) ) ),
    inference(resolution,[status(thm)],[c_22,c_168])).

tff(c_185,plain,
    ( k11_lattice3('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_8'),'#skF_8') = '#skF_1'('#skF_6','#skF_8','#skF_8')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_173])).

tff(c_195,plain,
    ( k11_lattice3('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_8'),'#skF_8') = '#skF_1'('#skF_6','#skF_8','#skF_8')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_48,c_185])).

tff(c_212,plain,(
    v2_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v2_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_215,plain,
    ( ~ v2_lattice3('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_212,c_2])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_215])).

tff(c_221,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1142,plain,(
    ! [A_225,B_226,C_227] :
      ( k11_lattice3(A_225,'#skF_1'(A_225,B_226,C_227),B_226) = '#skF_1'(A_225,B_226,C_227)
      | ~ v5_orders_2(A_225)
      | v2_struct_0(A_225)
      | ~ r1_orders_2(A_225,'#skF_1'(A_225,B_226,C_227),B_226)
      | ~ m1_subset_1('#skF_1'(A_225,B_226,C_227),u1_struct_0(A_225))
      | ~ m1_subset_1(C_227,u1_struct_0(A_225))
      | ~ m1_subset_1(B_226,u1_struct_0(A_225))
      | ~ v2_lattice3(A_225)
      | ~ l1_orders_2(A_225) ) ),
    inference(resolution,[status(thm)],[c_18,c_143])).

tff(c_1177,plain,(
    ! [A_228,B_229,C_230] :
      ( k11_lattice3(A_228,'#skF_1'(A_228,B_229,C_230),B_229) = '#skF_1'(A_228,B_229,C_230)
      | ~ v5_orders_2(A_228)
      | v2_struct_0(A_228)
      | ~ m1_subset_1('#skF_1'(A_228,B_229,C_230),u1_struct_0(A_228))
      | ~ m1_subset_1(C_230,u1_struct_0(A_228))
      | ~ m1_subset_1(B_229,u1_struct_0(A_228))
      | ~ v2_lattice3(A_228)
      | ~ l1_orders_2(A_228) ) ),
    inference(resolution,[status(thm)],[c_20,c_1142])).

tff(c_1371,plain,(
    ! [A_236,B_237,C_238] :
      ( k11_lattice3(A_236,'#skF_1'(A_236,B_237,C_238),B_237) = '#skF_1'(A_236,B_237,C_238)
      | ~ v5_orders_2(A_236)
      | v2_struct_0(A_236)
      | ~ m1_subset_1(C_238,u1_struct_0(A_236))
      | ~ m1_subset_1(B_237,u1_struct_0(A_236))
      | ~ v2_lattice3(A_236)
      | ~ l1_orders_2(A_236) ) ),
    inference(resolution,[status(thm)],[c_22,c_1177])).

tff(c_1387,plain,(
    ! [B_237] :
      ( k11_lattice3('#skF_6','#skF_1'('#skF_6',B_237,'#skF_8'),B_237) = '#skF_1'('#skF_6',B_237,'#skF_8')
      | ~ v5_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(B_237,u1_struct_0('#skF_6'))
      | ~ v2_lattice3('#skF_6')
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_1371])).

tff(c_1405,plain,(
    ! [B_237] :
      ( k11_lattice3('#skF_6','#skF_1'('#skF_6',B_237,'#skF_8'),B_237) = '#skF_1'('#skF_6',B_237,'#skF_8')
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(B_237,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_48,c_1387])).

tff(c_1411,plain,(
    ! [B_239] :
      ( k11_lattice3('#skF_6','#skF_1'('#skF_6',B_239,'#skF_8'),B_239) = '#skF_1'('#skF_6',B_239,'#skF_8')
      | ~ m1_subset_1(B_239,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_1405])).

tff(c_1455,plain,(
    k11_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_7') = '#skF_1'('#skF_6','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_1411])).

tff(c_34,plain,(
    ! [A_59,B_83,C_95] :
      ( r1_orders_2(A_59,k11_lattice3(A_59,B_83,C_95),C_95)
      | ~ m1_subset_1(k11_lattice3(A_59,B_83,C_95),u1_struct_0(A_59))
      | ~ m1_subset_1(C_95,u1_struct_0(A_59))
      | ~ m1_subset_1(B_83,u1_struct_0(A_59))
      | ~ l1_orders_2(A_59)
      | ~ v2_lattice3(A_59)
      | ~ v5_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1460,plain,
    ( r1_orders_2('#skF_6',k11_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1455,c_34])).

tff(c_1469,plain,
    ( r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_7')
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_1455,c_1460])).

tff(c_1470,plain,
    ( r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_7')
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_1469])).

tff(c_1539,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1470])).

tff(c_1542,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ v2_lattice3('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_1539])).

tff(c_1546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_42,c_40,c_1542])).

tff(c_1548,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1470])).

tff(c_36,plain,(
    ! [A_59,B_83,C_95] :
      ( r1_orders_2(A_59,k11_lattice3(A_59,B_83,C_95),B_83)
      | ~ m1_subset_1(k11_lattice3(A_59,B_83,C_95),u1_struct_0(A_59))
      | ~ m1_subset_1(C_95,u1_struct_0(A_59))
      | ~ m1_subset_1(B_83,u1_struct_0(A_59))
      | ~ l1_orders_2(A_59)
      | ~ v2_lattice3(A_59)
      | ~ v5_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1462,plain,
    ( r1_orders_2('#skF_6',k11_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_7'),'#skF_1'('#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1455,c_36])).

tff(c_1472,plain,
    ( r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_1'('#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_1455,c_1462])).

tff(c_1473,plain,
    ( r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_1'('#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_1472])).

tff(c_1868,plain,(
    r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_1'('#skF_6','#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1548,c_1473])).

tff(c_124,plain,(
    ! [A_2,B_33,C_41] :
      ( k11_lattice3(A_2,'#skF_1'(A_2,B_33,C_41),C_41) = '#skF_1'(A_2,B_33,C_41)
      | ~ r1_orders_2(A_2,'#skF_1'(A_2,B_33,C_41),'#skF_1'(A_2,B_33,C_41))
      | ~ m1_subset_1('#skF_1'(A_2,B_33,C_41),u1_struct_0(A_2))
      | ~ v5_orders_2(A_2)
      | v2_struct_0(A_2)
      | ~ m1_subset_1(C_41,u1_struct_0(A_2))
      | ~ m1_subset_1(B_33,u1_struct_0(A_2))
      | ~ v2_lattice3(A_2)
      | ~ l1_orders_2(A_2) ) ),
    inference(resolution,[status(thm)],[c_18,c_104])).

tff(c_1875,plain,
    ( k11_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_8') = '#skF_1'('#skF_6','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ v2_lattice3('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_1868,c_124])).

tff(c_1890,plain,
    ( k11_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_8') = '#skF_1'('#skF_6','#skF_7','#skF_8')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_42,c_40,c_48,c_1548,c_1875])).

tff(c_1891,plain,(
    k11_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_8') = '#skF_1'('#skF_6','#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_1890])).

tff(c_1904,plain,
    ( r1_orders_2('#skF_6',k11_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_8'),'#skF_8')
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1891,c_34])).

tff(c_1913,plain,
    ( r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_8')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_1548,c_40,c_1548,c_1891,c_1904])).

tff(c_1914,plain,(
    r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_1913])).

tff(c_1547,plain,(
    r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1470])).

tff(c_30,plain,(
    ! [A_59,B_83,C_95,D_101] :
      ( m1_subset_1('#skF_5'(A_59,B_83,C_95,D_101),u1_struct_0(A_59))
      | k11_lattice3(A_59,B_83,C_95) = D_101
      | ~ r1_orders_2(A_59,D_101,C_95)
      | ~ r1_orders_2(A_59,D_101,B_83)
      | ~ m1_subset_1(D_101,u1_struct_0(A_59))
      | ~ m1_subset_1(C_95,u1_struct_0(A_59))
      | ~ m1_subset_1(B_83,u1_struct_0(A_59))
      | ~ l1_orders_2(A_59)
      | ~ v2_lattice3(A_59)
      | ~ v5_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_26,plain,(
    ! [A_59,B_83,C_95,D_101] :
      ( r1_orders_2(A_59,'#skF_5'(A_59,B_83,C_95,D_101),C_95)
      | k11_lattice3(A_59,B_83,C_95) = D_101
      | ~ r1_orders_2(A_59,D_101,C_95)
      | ~ r1_orders_2(A_59,D_101,B_83)
      | ~ m1_subset_1(D_101,u1_struct_0(A_59))
      | ~ m1_subset_1(C_95,u1_struct_0(A_59))
      | ~ m1_subset_1(B_83,u1_struct_0(A_59))
      | ~ l1_orders_2(A_59)
      | ~ v2_lattice3(A_59)
      | ~ v5_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_199,plain,(
    ! [C_187,C_188,B_190,B_186,A_189] :
      ( k11_lattice3(A_189,B_190,C_187) = '#skF_1'(A_189,B_186,C_188)
      | ~ r1_orders_2(A_189,'#skF_1'(A_189,B_186,C_188),C_187)
      | ~ r1_orders_2(A_189,'#skF_1'(A_189,B_186,C_188),B_190)
      | ~ m1_subset_1('#skF_1'(A_189,B_186,C_188),u1_struct_0(A_189))
      | ~ m1_subset_1(C_187,u1_struct_0(A_189))
      | ~ m1_subset_1(B_190,u1_struct_0(A_189))
      | ~ v5_orders_2(A_189)
      | v2_struct_0(A_189)
      | ~ r1_orders_2(A_189,'#skF_5'(A_189,B_190,C_187,'#skF_1'(A_189,B_186,C_188)),C_188)
      | ~ r1_orders_2(A_189,'#skF_5'(A_189,B_190,C_187,'#skF_1'(A_189,B_186,C_188)),B_186)
      | ~ m1_subset_1('#skF_5'(A_189,B_190,C_187,'#skF_1'(A_189,B_186,C_188)),u1_struct_0(A_189))
      | ~ m1_subset_1(C_188,u1_struct_0(A_189))
      | ~ m1_subset_1(B_186,u1_struct_0(A_189))
      | ~ v2_lattice3(A_189)
      | ~ l1_orders_2(A_189) ) ),
    inference(resolution,[status(thm)],[c_16,c_82])).

tff(c_714,plain,(
    ! [A_205,B_206,C_207,B_208] :
      ( ~ r1_orders_2(A_205,'#skF_5'(A_205,B_206,C_207,'#skF_1'(A_205,B_208,B_206)),B_208)
      | ~ m1_subset_1('#skF_5'(A_205,B_206,C_207,'#skF_1'(A_205,B_208,B_206)),u1_struct_0(A_205))
      | ~ m1_subset_1(B_208,u1_struct_0(A_205))
      | k11_lattice3(A_205,B_206,C_207) = '#skF_1'(A_205,B_208,B_206)
      | ~ r1_orders_2(A_205,'#skF_1'(A_205,B_208,B_206),C_207)
      | ~ r1_orders_2(A_205,'#skF_1'(A_205,B_208,B_206),B_206)
      | ~ m1_subset_1('#skF_1'(A_205,B_208,B_206),u1_struct_0(A_205))
      | ~ m1_subset_1(C_207,u1_struct_0(A_205))
      | ~ m1_subset_1(B_206,u1_struct_0(A_205))
      | ~ l1_orders_2(A_205)
      | ~ v2_lattice3(A_205)
      | ~ v5_orders_2(A_205)
      | v2_struct_0(A_205) ) ),
    inference(resolution,[status(thm)],[c_28,c_199])).

tff(c_1949,plain,(
    ! [A_247,B_248,C_249] :
      ( ~ m1_subset_1('#skF_5'(A_247,B_248,C_249,'#skF_1'(A_247,C_249,B_248)),u1_struct_0(A_247))
      | k11_lattice3(A_247,B_248,C_249) = '#skF_1'(A_247,C_249,B_248)
      | ~ r1_orders_2(A_247,'#skF_1'(A_247,C_249,B_248),C_249)
      | ~ r1_orders_2(A_247,'#skF_1'(A_247,C_249,B_248),B_248)
      | ~ m1_subset_1('#skF_1'(A_247,C_249,B_248),u1_struct_0(A_247))
      | ~ m1_subset_1(C_249,u1_struct_0(A_247))
      | ~ m1_subset_1(B_248,u1_struct_0(A_247))
      | ~ l1_orders_2(A_247)
      | ~ v2_lattice3(A_247)
      | ~ v5_orders_2(A_247)
      | v2_struct_0(A_247) ) ),
    inference(resolution,[status(thm)],[c_26,c_714])).

tff(c_6514,plain,(
    ! [A_340,B_341,C_342] :
      ( k11_lattice3(A_340,B_341,C_342) = '#skF_1'(A_340,C_342,B_341)
      | ~ r1_orders_2(A_340,'#skF_1'(A_340,C_342,B_341),C_342)
      | ~ r1_orders_2(A_340,'#skF_1'(A_340,C_342,B_341),B_341)
      | ~ m1_subset_1('#skF_1'(A_340,C_342,B_341),u1_struct_0(A_340))
      | ~ m1_subset_1(C_342,u1_struct_0(A_340))
      | ~ m1_subset_1(B_341,u1_struct_0(A_340))
      | ~ l1_orders_2(A_340)
      | ~ v2_lattice3(A_340)
      | ~ v5_orders_2(A_340)
      | v2_struct_0(A_340) ) ),
    inference(resolution,[status(thm)],[c_30,c_1949])).

tff(c_6546,plain,
    ( k11_lattice3('#skF_6','#skF_8','#skF_7') = '#skF_1'('#skF_6','#skF_7','#skF_8')
    | ~ r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_8')
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1547,c_6514])).

tff(c_6618,plain,
    ( k11_lattice3('#skF_6','#skF_8','#skF_7') = '#skF_1'('#skF_6','#skF_7','#skF_8')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_40,c_42,c_1548,c_1914,c_6546])).

tff(c_6619,plain,(
    k11_lattice3('#skF_6','#skF_8','#skF_7') = '#skF_1'('#skF_6','#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_6618])).

tff(c_1389,plain,(
    ! [B_237] :
      ( k11_lattice3('#skF_6','#skF_1'('#skF_6',B_237,'#skF_7'),B_237) = '#skF_1'('#skF_6',B_237,'#skF_7')
      | ~ v5_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(B_237,u1_struct_0('#skF_6'))
      | ~ v2_lattice3('#skF_6')
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_1371])).

tff(c_1409,plain,(
    ! [B_237] :
      ( k11_lattice3('#skF_6','#skF_1'('#skF_6',B_237,'#skF_7'),B_237) = '#skF_1'('#skF_6',B_237,'#skF_7')
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(B_237,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_48,c_1389])).

tff(c_1475,plain,(
    ! [B_240] :
      ( k11_lattice3('#skF_6','#skF_1'('#skF_6',B_240,'#skF_7'),B_240) = '#skF_1'('#skF_6',B_240,'#skF_7')
      | ~ m1_subset_1(B_240,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_1409])).

tff(c_1517,plain,(
    k11_lattice3('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_8') = '#skF_1'('#skF_6','#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_1475])).

tff(c_1524,plain,
    ( r1_orders_2('#skF_6',k11_lattice3('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_8'),'#skF_8')
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1517,c_34])).

tff(c_1533,plain,
    ( r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_8')
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_40,c_1517,c_1524])).

tff(c_1534,plain,
    ( r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_8')
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_1533])).

tff(c_1619,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1534])).

tff(c_1622,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ v2_lattice3('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_1619])).

tff(c_1626,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_40,c_42,c_1622])).

tff(c_1628,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1534])).

tff(c_1526,plain,
    ( r1_orders_2('#skF_6',k11_lattice3('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_8'),'#skF_1'('#skF_6','#skF_8','#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1517,c_36])).

tff(c_1536,plain,
    ( r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_1'('#skF_6','#skF_8','#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_40,c_1517,c_1526])).

tff(c_1537,plain,
    ( r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_1'('#skF_6','#skF_8','#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_1536])).

tff(c_1641,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1537])).

tff(c_1667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1628,c_1641])).

tff(c_1668,plain,(
    r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_1'('#skF_6','#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1537])).

tff(c_1701,plain,
    ( k11_lattice3('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_7') = '#skF_1'('#skF_6','#skF_8','#skF_7')
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6'))
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ v2_lattice3('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_1668,c_124])).

tff(c_1716,plain,
    ( k11_lattice3('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_7') = '#skF_1'('#skF_6','#skF_8','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_40,c_42,c_48,c_1628,c_1701])).

tff(c_1717,plain,(
    k11_lattice3('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_7') = '#skF_1'('#skF_6','#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_1716])).

tff(c_1764,plain,
    ( r1_orders_2('#skF_6',k11_lattice3('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1717,c_34])).

tff(c_1773,plain,
    ( r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_1628,c_42,c_1628,c_1717,c_1764])).

tff(c_1774,plain,(
    r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_1773])).

tff(c_1627,plain,(
    r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_1534])).

tff(c_6544,plain,
    ( k11_lattice3('#skF_6','#skF_7','#skF_8') = '#skF_1'('#skF_6','#skF_8','#skF_7')
    | ~ r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_8','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_8','#skF_7'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1627,c_6514])).

tff(c_6614,plain,
    ( k11_lattice3('#skF_6','#skF_7','#skF_8') = '#skF_1'('#skF_6','#skF_8','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_1628,c_1774,c_6544])).

tff(c_6615,plain,(
    k11_lattice3('#skF_6','#skF_7','#skF_8') = '#skF_1'('#skF_6','#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_6614])).

tff(c_38,plain,(
    k11_lattice3('#skF_6','#skF_7','#skF_8') != k11_lattice3('#skF_6','#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6637,plain,(
    k11_lattice3('#skF_6','#skF_8','#skF_7') != '#skF_1'('#skF_6','#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6615,c_38])).

tff(c_6676,plain,(
    '#skF_1'('#skF_6','#skF_7','#skF_8') != '#skF_1'('#skF_6','#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6619,c_6637])).

tff(c_864,plain,(
    ! [A_209,B_210,C_211,B_212] :
      ( ~ r1_orders_2(A_209,'#skF_5'(A_209,B_210,C_211,'#skF_1'(A_209,B_212,C_211)),B_212)
      | ~ m1_subset_1('#skF_5'(A_209,B_210,C_211,'#skF_1'(A_209,B_212,C_211)),u1_struct_0(A_209))
      | ~ m1_subset_1(B_212,u1_struct_0(A_209))
      | k11_lattice3(A_209,B_210,C_211) = '#skF_1'(A_209,B_212,C_211)
      | ~ r1_orders_2(A_209,'#skF_1'(A_209,B_212,C_211),C_211)
      | ~ r1_orders_2(A_209,'#skF_1'(A_209,B_212,C_211),B_210)
      | ~ m1_subset_1('#skF_1'(A_209,B_212,C_211),u1_struct_0(A_209))
      | ~ m1_subset_1(C_211,u1_struct_0(A_209))
      | ~ m1_subset_1(B_210,u1_struct_0(A_209))
      | ~ l1_orders_2(A_209)
      | ~ v2_lattice3(A_209)
      | ~ v5_orders_2(A_209)
      | v2_struct_0(A_209) ) ),
    inference(resolution,[status(thm)],[c_26,c_199])).

tff(c_2305,plain,(
    ! [A_257,B_258,C_259] :
      ( ~ m1_subset_1('#skF_5'(A_257,B_258,C_259,'#skF_1'(A_257,B_258,C_259)),u1_struct_0(A_257))
      | k11_lattice3(A_257,B_258,C_259) = '#skF_1'(A_257,B_258,C_259)
      | ~ r1_orders_2(A_257,'#skF_1'(A_257,B_258,C_259),C_259)
      | ~ r1_orders_2(A_257,'#skF_1'(A_257,B_258,C_259),B_258)
      | ~ m1_subset_1('#skF_1'(A_257,B_258,C_259),u1_struct_0(A_257))
      | ~ m1_subset_1(C_259,u1_struct_0(A_257))
      | ~ m1_subset_1(B_258,u1_struct_0(A_257))
      | ~ l1_orders_2(A_257)
      | ~ v2_lattice3(A_257)
      | ~ v5_orders_2(A_257)
      | v2_struct_0(A_257) ) ),
    inference(resolution,[status(thm)],[c_28,c_864])).

tff(c_7479,plain,(
    ! [A_343,B_344,C_345] :
      ( k11_lattice3(A_343,B_344,C_345) = '#skF_1'(A_343,B_344,C_345)
      | ~ r1_orders_2(A_343,'#skF_1'(A_343,B_344,C_345),C_345)
      | ~ r1_orders_2(A_343,'#skF_1'(A_343,B_344,C_345),B_344)
      | ~ m1_subset_1('#skF_1'(A_343,B_344,C_345),u1_struct_0(A_343))
      | ~ m1_subset_1(C_345,u1_struct_0(A_343))
      | ~ m1_subset_1(B_344,u1_struct_0(A_343))
      | ~ l1_orders_2(A_343)
      | ~ v2_lattice3(A_343)
      | ~ v5_orders_2(A_343)
      | v2_struct_0(A_343) ) ),
    inference(resolution,[status(thm)],[c_30,c_2305])).

tff(c_7511,plain,
    ( k11_lattice3('#skF_6','#skF_7','#skF_8') = '#skF_1'('#skF_6','#skF_7','#skF_8')
    | ~ r1_orders_2('#skF_6','#skF_1'('#skF_6','#skF_7','#skF_8'),'#skF_7')
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1914,c_7479])).

tff(c_7577,plain,
    ( '#skF_1'('#skF_6','#skF_7','#skF_8') = '#skF_1'('#skF_6','#skF_8','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_1548,c_1547,c_6615,c_7511])).

tff(c_7579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_6676,c_7577])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:23:41 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.75/3.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.75/3.61  
% 9.75/3.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.75/3.62  %$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v2_struct_0 > v2_lattice3 > l1_orders_2 > k11_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_5 > #skF_3 > #skF_4
% 9.75/3.62  
% 9.75/3.62  %Foreground sorts:
% 9.75/3.62  
% 9.75/3.62  
% 9.75/3.62  %Background operators:
% 9.75/3.62  
% 9.75/3.62  
% 9.75/3.62  %Foreground operators:
% 9.75/3.62  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.75/3.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.75/3.62  tff('#skF_2', type, '#skF_2': $i > $i).
% 9.75/3.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.75/3.62  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 9.75/3.62  tff('#skF_7', type, '#skF_7': $i).
% 9.75/3.62  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 9.75/3.62  tff('#skF_6', type, '#skF_6': $i).
% 9.75/3.62  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 9.75/3.62  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 9.75/3.62  tff('#skF_8', type, '#skF_8': $i).
% 9.75/3.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.75/3.62  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 9.75/3.62  tff('#skF_3', type, '#skF_3': $i > $i).
% 9.75/3.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.75/3.62  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 9.75/3.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.75/3.62  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.75/3.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.75/3.62  
% 10.00/3.64  tff(f_106, negated_conjecture, ~(![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k11_lattice3(A, B, C) = k11_lattice3(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_lattice3)).
% 10.00/3.64  tff(f_58, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (?[D]: (((m1_subset_1(D, u1_struct_0(A)) & r1_orders_2(A, D, B)) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_lattice3)).
% 10.00/3.64  tff(f_91, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l28_lattice3)).
% 10.00/3.64  tff(f_32, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 10.00/3.64  tff(c_44, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.00/3.64  tff(c_46, plain, (v2_lattice3('#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.00/3.64  tff(c_48, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.00/3.64  tff(c_40, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.00/3.64  tff(c_22, plain, (![A_2, B_33, C_41]: (m1_subset_1('#skF_1'(A_2, B_33, C_41), u1_struct_0(A_2)) | ~m1_subset_1(C_41, u1_struct_0(A_2)) | ~m1_subset_1(B_33, u1_struct_0(A_2)) | ~v2_lattice3(A_2) | ~l1_orders_2(A_2))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.00/3.64  tff(c_18, plain, (![A_2, B_33, C_41]: (r1_orders_2(A_2, '#skF_1'(A_2, B_33, C_41), C_41) | ~m1_subset_1(C_41, u1_struct_0(A_2)) | ~m1_subset_1(B_33, u1_struct_0(A_2)) | ~v2_lattice3(A_2) | ~l1_orders_2(A_2))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.00/3.64  tff(c_20, plain, (![A_2, B_33, C_41]: (r1_orders_2(A_2, '#skF_1'(A_2, B_33, C_41), B_33) | ~m1_subset_1(C_41, u1_struct_0(A_2)) | ~m1_subset_1(B_33, u1_struct_0(A_2)) | ~v2_lattice3(A_2) | ~l1_orders_2(A_2))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.00/3.64  tff(c_16, plain, (![A_2, E_46, B_33, C_41]: (r1_orders_2(A_2, E_46, '#skF_1'(A_2, B_33, C_41)) | ~r1_orders_2(A_2, E_46, C_41) | ~r1_orders_2(A_2, E_46, B_33) | ~m1_subset_1(E_46, u1_struct_0(A_2)) | ~m1_subset_1(C_41, u1_struct_0(A_2)) | ~m1_subset_1(B_33, u1_struct_0(A_2)) | ~v2_lattice3(A_2) | ~l1_orders_2(A_2))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.00/3.64  tff(c_28, plain, (![A_59, B_83, C_95, D_101]: (r1_orders_2(A_59, '#skF_5'(A_59, B_83, C_95, D_101), B_83) | k11_lattice3(A_59, B_83, C_95)=D_101 | ~r1_orders_2(A_59, D_101, C_95) | ~r1_orders_2(A_59, D_101, B_83) | ~m1_subset_1(D_101, u1_struct_0(A_59)) | ~m1_subset_1(C_95, u1_struct_0(A_59)) | ~m1_subset_1(B_83, u1_struct_0(A_59)) | ~l1_orders_2(A_59) | ~v2_lattice3(A_59) | ~v5_orders_2(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.00/3.64  tff(c_82, plain, (![A_153, B_154, C_155, D_156]: (~r1_orders_2(A_153, '#skF_5'(A_153, B_154, C_155, D_156), D_156) | k11_lattice3(A_153, B_154, C_155)=D_156 | ~r1_orders_2(A_153, D_156, C_155) | ~r1_orders_2(A_153, D_156, B_154) | ~m1_subset_1(D_156, u1_struct_0(A_153)) | ~m1_subset_1(C_155, u1_struct_0(A_153)) | ~m1_subset_1(B_154, u1_struct_0(A_153)) | ~l1_orders_2(A_153) | ~v2_lattice3(A_153) | ~v5_orders_2(A_153) | v2_struct_0(A_153))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.00/3.64  tff(c_104, plain, (![A_164, B_165, C_166]: (k11_lattice3(A_164, B_165, C_166)=B_165 | ~r1_orders_2(A_164, B_165, C_166) | ~r1_orders_2(A_164, B_165, B_165) | ~m1_subset_1(C_166, u1_struct_0(A_164)) | ~m1_subset_1(B_165, u1_struct_0(A_164)) | ~l1_orders_2(A_164) | ~v2_lattice3(A_164) | ~v5_orders_2(A_164) | v2_struct_0(A_164))), inference(resolution, [status(thm)], [c_28, c_82])).
% 10.00/3.64  tff(c_132, plain, (![A_170, B_171, C_172]: (k11_lattice3(A_170, '#skF_1'(A_170, B_171, C_172), B_171)='#skF_1'(A_170, B_171, C_172) | ~r1_orders_2(A_170, '#skF_1'(A_170, B_171, C_172), '#skF_1'(A_170, B_171, C_172)) | ~m1_subset_1('#skF_1'(A_170, B_171, C_172), u1_struct_0(A_170)) | ~v5_orders_2(A_170) | v2_struct_0(A_170) | ~m1_subset_1(C_172, u1_struct_0(A_170)) | ~m1_subset_1(B_171, u1_struct_0(A_170)) | ~v2_lattice3(A_170) | ~l1_orders_2(A_170))), inference(resolution, [status(thm)], [c_20, c_104])).
% 10.00/3.64  tff(c_143, plain, (![A_177, B_178, C_179]: (k11_lattice3(A_177, '#skF_1'(A_177, B_178, C_179), B_178)='#skF_1'(A_177, B_178, C_179) | ~v5_orders_2(A_177) | v2_struct_0(A_177) | ~r1_orders_2(A_177, '#skF_1'(A_177, B_178, C_179), C_179) | ~r1_orders_2(A_177, '#skF_1'(A_177, B_178, C_179), B_178) | ~m1_subset_1('#skF_1'(A_177, B_178, C_179), u1_struct_0(A_177)) | ~m1_subset_1(C_179, u1_struct_0(A_177)) | ~m1_subset_1(B_178, u1_struct_0(A_177)) | ~v2_lattice3(A_177) | ~l1_orders_2(A_177))), inference(resolution, [status(thm)], [c_16, c_132])).
% 10.00/3.64  tff(c_155, plain, (![A_180, B_181]: (k11_lattice3(A_180, '#skF_1'(A_180, B_181, B_181), B_181)='#skF_1'(A_180, B_181, B_181) | ~v5_orders_2(A_180) | v2_struct_0(A_180) | ~r1_orders_2(A_180, '#skF_1'(A_180, B_181, B_181), B_181) | ~m1_subset_1('#skF_1'(A_180, B_181, B_181), u1_struct_0(A_180)) | ~m1_subset_1(B_181, u1_struct_0(A_180)) | ~v2_lattice3(A_180) | ~l1_orders_2(A_180))), inference(resolution, [status(thm)], [c_20, c_143])).
% 10.00/3.64  tff(c_168, plain, (![A_182, C_183]: (k11_lattice3(A_182, '#skF_1'(A_182, C_183, C_183), C_183)='#skF_1'(A_182, C_183, C_183) | ~v5_orders_2(A_182) | v2_struct_0(A_182) | ~m1_subset_1('#skF_1'(A_182, C_183, C_183), u1_struct_0(A_182)) | ~m1_subset_1(C_183, u1_struct_0(A_182)) | ~v2_lattice3(A_182) | ~l1_orders_2(A_182))), inference(resolution, [status(thm)], [c_18, c_155])).
% 10.00/3.64  tff(c_173, plain, (![A_184, C_185]: (k11_lattice3(A_184, '#skF_1'(A_184, C_185, C_185), C_185)='#skF_1'(A_184, C_185, C_185) | ~v5_orders_2(A_184) | v2_struct_0(A_184) | ~m1_subset_1(C_185, u1_struct_0(A_184)) | ~v2_lattice3(A_184) | ~l1_orders_2(A_184))), inference(resolution, [status(thm)], [c_22, c_168])).
% 10.00/3.64  tff(c_185, plain, (k11_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_8'), '#skF_8')='#skF_1'('#skF_6', '#skF_8', '#skF_8') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~v2_lattice3('#skF_6') | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_40, c_173])).
% 10.00/3.64  tff(c_195, plain, (k11_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_8'), '#skF_8')='#skF_1'('#skF_6', '#skF_8', '#skF_8') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_48, c_185])).
% 10.00/3.64  tff(c_212, plain, (v2_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_195])).
% 10.00/3.64  tff(c_2, plain, (![A_1]: (~v2_struct_0(A_1) | ~v2_lattice3(A_1) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.00/3.64  tff(c_215, plain, (~v2_lattice3('#skF_6') | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_212, c_2])).
% 10.00/3.64  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_215])).
% 10.00/3.64  tff(c_221, plain, (~v2_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_195])).
% 10.00/3.64  tff(c_42, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.00/3.64  tff(c_1142, plain, (![A_225, B_226, C_227]: (k11_lattice3(A_225, '#skF_1'(A_225, B_226, C_227), B_226)='#skF_1'(A_225, B_226, C_227) | ~v5_orders_2(A_225) | v2_struct_0(A_225) | ~r1_orders_2(A_225, '#skF_1'(A_225, B_226, C_227), B_226) | ~m1_subset_1('#skF_1'(A_225, B_226, C_227), u1_struct_0(A_225)) | ~m1_subset_1(C_227, u1_struct_0(A_225)) | ~m1_subset_1(B_226, u1_struct_0(A_225)) | ~v2_lattice3(A_225) | ~l1_orders_2(A_225))), inference(resolution, [status(thm)], [c_18, c_143])).
% 10.00/3.64  tff(c_1177, plain, (![A_228, B_229, C_230]: (k11_lattice3(A_228, '#skF_1'(A_228, B_229, C_230), B_229)='#skF_1'(A_228, B_229, C_230) | ~v5_orders_2(A_228) | v2_struct_0(A_228) | ~m1_subset_1('#skF_1'(A_228, B_229, C_230), u1_struct_0(A_228)) | ~m1_subset_1(C_230, u1_struct_0(A_228)) | ~m1_subset_1(B_229, u1_struct_0(A_228)) | ~v2_lattice3(A_228) | ~l1_orders_2(A_228))), inference(resolution, [status(thm)], [c_20, c_1142])).
% 10.00/3.64  tff(c_1371, plain, (![A_236, B_237, C_238]: (k11_lattice3(A_236, '#skF_1'(A_236, B_237, C_238), B_237)='#skF_1'(A_236, B_237, C_238) | ~v5_orders_2(A_236) | v2_struct_0(A_236) | ~m1_subset_1(C_238, u1_struct_0(A_236)) | ~m1_subset_1(B_237, u1_struct_0(A_236)) | ~v2_lattice3(A_236) | ~l1_orders_2(A_236))), inference(resolution, [status(thm)], [c_22, c_1177])).
% 10.00/3.64  tff(c_1387, plain, (![B_237]: (k11_lattice3('#skF_6', '#skF_1'('#skF_6', B_237, '#skF_8'), B_237)='#skF_1'('#skF_6', B_237, '#skF_8') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~m1_subset_1(B_237, u1_struct_0('#skF_6')) | ~v2_lattice3('#skF_6') | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_1371])).
% 10.00/3.64  tff(c_1405, plain, (![B_237]: (k11_lattice3('#skF_6', '#skF_1'('#skF_6', B_237, '#skF_8'), B_237)='#skF_1'('#skF_6', B_237, '#skF_8') | v2_struct_0('#skF_6') | ~m1_subset_1(B_237, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_48, c_1387])).
% 10.00/3.64  tff(c_1411, plain, (![B_239]: (k11_lattice3('#skF_6', '#skF_1'('#skF_6', B_239, '#skF_8'), B_239)='#skF_1'('#skF_6', B_239, '#skF_8') | ~m1_subset_1(B_239, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_221, c_1405])).
% 10.00/3.64  tff(c_1455, plain, (k11_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_7')='#skF_1'('#skF_6', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_42, c_1411])).
% 10.00/3.64  tff(c_34, plain, (![A_59, B_83, C_95]: (r1_orders_2(A_59, k11_lattice3(A_59, B_83, C_95), C_95) | ~m1_subset_1(k11_lattice3(A_59, B_83, C_95), u1_struct_0(A_59)) | ~m1_subset_1(C_95, u1_struct_0(A_59)) | ~m1_subset_1(B_83, u1_struct_0(A_59)) | ~l1_orders_2(A_59) | ~v2_lattice3(A_59) | ~v5_orders_2(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.00/3.64  tff(c_1460, plain, (r1_orders_2('#skF_6', k11_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_7'), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v2_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1455, c_34])).
% 10.00/3.64  tff(c_1469, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_1455, c_1460])).
% 10.00/3.64  tff(c_1470, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_221, c_1469])).
% 10.00/3.64  tff(c_1539, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_1470])).
% 10.00/3.64  tff(c_1542, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~v2_lattice3('#skF_6') | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_22, c_1539])).
% 10.00/3.64  tff(c_1546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_42, c_40, c_1542])).
% 10.00/3.64  tff(c_1548, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_1470])).
% 10.00/3.64  tff(c_36, plain, (![A_59, B_83, C_95]: (r1_orders_2(A_59, k11_lattice3(A_59, B_83, C_95), B_83) | ~m1_subset_1(k11_lattice3(A_59, B_83, C_95), u1_struct_0(A_59)) | ~m1_subset_1(C_95, u1_struct_0(A_59)) | ~m1_subset_1(B_83, u1_struct_0(A_59)) | ~l1_orders_2(A_59) | ~v2_lattice3(A_59) | ~v5_orders_2(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.00/3.64  tff(c_1462, plain, (r1_orders_2('#skF_6', k11_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_7'), '#skF_1'('#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v2_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1455, c_36])).
% 10.00/3.64  tff(c_1472, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_1'('#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_1455, c_1462])).
% 10.00/3.64  tff(c_1473, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_1'('#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_221, c_1472])).
% 10.00/3.64  tff(c_1868, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_1'('#skF_6', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1548, c_1473])).
% 10.00/3.64  tff(c_124, plain, (![A_2, B_33, C_41]: (k11_lattice3(A_2, '#skF_1'(A_2, B_33, C_41), C_41)='#skF_1'(A_2, B_33, C_41) | ~r1_orders_2(A_2, '#skF_1'(A_2, B_33, C_41), '#skF_1'(A_2, B_33, C_41)) | ~m1_subset_1('#skF_1'(A_2, B_33, C_41), u1_struct_0(A_2)) | ~v5_orders_2(A_2) | v2_struct_0(A_2) | ~m1_subset_1(C_41, u1_struct_0(A_2)) | ~m1_subset_1(B_33, u1_struct_0(A_2)) | ~v2_lattice3(A_2) | ~l1_orders_2(A_2))), inference(resolution, [status(thm)], [c_18, c_104])).
% 10.00/3.64  tff(c_1875, plain, (k11_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_8')='#skF_1'('#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~v2_lattice3('#skF_6') | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_1868, c_124])).
% 10.00/3.64  tff(c_1890, plain, (k11_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_8')='#skF_1'('#skF_6', '#skF_7', '#skF_8') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_42, c_40, c_48, c_1548, c_1875])).
% 10.00/3.64  tff(c_1891, plain, (k11_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_8')='#skF_1'('#skF_6', '#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_221, c_1890])).
% 10.00/3.64  tff(c_1904, plain, (r1_orders_2('#skF_6', k11_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_8'), '#skF_8') | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v2_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1891, c_34])).
% 10.00/3.64  tff(c_1913, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_8') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_1548, c_40, c_1548, c_1891, c_1904])).
% 10.00/3.64  tff(c_1914, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_221, c_1913])).
% 10.00/3.64  tff(c_1547, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_1470])).
% 10.00/3.64  tff(c_30, plain, (![A_59, B_83, C_95, D_101]: (m1_subset_1('#skF_5'(A_59, B_83, C_95, D_101), u1_struct_0(A_59)) | k11_lattice3(A_59, B_83, C_95)=D_101 | ~r1_orders_2(A_59, D_101, C_95) | ~r1_orders_2(A_59, D_101, B_83) | ~m1_subset_1(D_101, u1_struct_0(A_59)) | ~m1_subset_1(C_95, u1_struct_0(A_59)) | ~m1_subset_1(B_83, u1_struct_0(A_59)) | ~l1_orders_2(A_59) | ~v2_lattice3(A_59) | ~v5_orders_2(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.00/3.64  tff(c_26, plain, (![A_59, B_83, C_95, D_101]: (r1_orders_2(A_59, '#skF_5'(A_59, B_83, C_95, D_101), C_95) | k11_lattice3(A_59, B_83, C_95)=D_101 | ~r1_orders_2(A_59, D_101, C_95) | ~r1_orders_2(A_59, D_101, B_83) | ~m1_subset_1(D_101, u1_struct_0(A_59)) | ~m1_subset_1(C_95, u1_struct_0(A_59)) | ~m1_subset_1(B_83, u1_struct_0(A_59)) | ~l1_orders_2(A_59) | ~v2_lattice3(A_59) | ~v5_orders_2(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.00/3.64  tff(c_199, plain, (![C_187, C_188, B_190, B_186, A_189]: (k11_lattice3(A_189, B_190, C_187)='#skF_1'(A_189, B_186, C_188) | ~r1_orders_2(A_189, '#skF_1'(A_189, B_186, C_188), C_187) | ~r1_orders_2(A_189, '#skF_1'(A_189, B_186, C_188), B_190) | ~m1_subset_1('#skF_1'(A_189, B_186, C_188), u1_struct_0(A_189)) | ~m1_subset_1(C_187, u1_struct_0(A_189)) | ~m1_subset_1(B_190, u1_struct_0(A_189)) | ~v5_orders_2(A_189) | v2_struct_0(A_189) | ~r1_orders_2(A_189, '#skF_5'(A_189, B_190, C_187, '#skF_1'(A_189, B_186, C_188)), C_188) | ~r1_orders_2(A_189, '#skF_5'(A_189, B_190, C_187, '#skF_1'(A_189, B_186, C_188)), B_186) | ~m1_subset_1('#skF_5'(A_189, B_190, C_187, '#skF_1'(A_189, B_186, C_188)), u1_struct_0(A_189)) | ~m1_subset_1(C_188, u1_struct_0(A_189)) | ~m1_subset_1(B_186, u1_struct_0(A_189)) | ~v2_lattice3(A_189) | ~l1_orders_2(A_189))), inference(resolution, [status(thm)], [c_16, c_82])).
% 10.00/3.64  tff(c_714, plain, (![A_205, B_206, C_207, B_208]: (~r1_orders_2(A_205, '#skF_5'(A_205, B_206, C_207, '#skF_1'(A_205, B_208, B_206)), B_208) | ~m1_subset_1('#skF_5'(A_205, B_206, C_207, '#skF_1'(A_205, B_208, B_206)), u1_struct_0(A_205)) | ~m1_subset_1(B_208, u1_struct_0(A_205)) | k11_lattice3(A_205, B_206, C_207)='#skF_1'(A_205, B_208, B_206) | ~r1_orders_2(A_205, '#skF_1'(A_205, B_208, B_206), C_207) | ~r1_orders_2(A_205, '#skF_1'(A_205, B_208, B_206), B_206) | ~m1_subset_1('#skF_1'(A_205, B_208, B_206), u1_struct_0(A_205)) | ~m1_subset_1(C_207, u1_struct_0(A_205)) | ~m1_subset_1(B_206, u1_struct_0(A_205)) | ~l1_orders_2(A_205) | ~v2_lattice3(A_205) | ~v5_orders_2(A_205) | v2_struct_0(A_205))), inference(resolution, [status(thm)], [c_28, c_199])).
% 10.00/3.64  tff(c_1949, plain, (![A_247, B_248, C_249]: (~m1_subset_1('#skF_5'(A_247, B_248, C_249, '#skF_1'(A_247, C_249, B_248)), u1_struct_0(A_247)) | k11_lattice3(A_247, B_248, C_249)='#skF_1'(A_247, C_249, B_248) | ~r1_orders_2(A_247, '#skF_1'(A_247, C_249, B_248), C_249) | ~r1_orders_2(A_247, '#skF_1'(A_247, C_249, B_248), B_248) | ~m1_subset_1('#skF_1'(A_247, C_249, B_248), u1_struct_0(A_247)) | ~m1_subset_1(C_249, u1_struct_0(A_247)) | ~m1_subset_1(B_248, u1_struct_0(A_247)) | ~l1_orders_2(A_247) | ~v2_lattice3(A_247) | ~v5_orders_2(A_247) | v2_struct_0(A_247))), inference(resolution, [status(thm)], [c_26, c_714])).
% 10.00/3.64  tff(c_6514, plain, (![A_340, B_341, C_342]: (k11_lattice3(A_340, B_341, C_342)='#skF_1'(A_340, C_342, B_341) | ~r1_orders_2(A_340, '#skF_1'(A_340, C_342, B_341), C_342) | ~r1_orders_2(A_340, '#skF_1'(A_340, C_342, B_341), B_341) | ~m1_subset_1('#skF_1'(A_340, C_342, B_341), u1_struct_0(A_340)) | ~m1_subset_1(C_342, u1_struct_0(A_340)) | ~m1_subset_1(B_341, u1_struct_0(A_340)) | ~l1_orders_2(A_340) | ~v2_lattice3(A_340) | ~v5_orders_2(A_340) | v2_struct_0(A_340))), inference(resolution, [status(thm)], [c_30, c_1949])).
% 10.00/3.64  tff(c_6546, plain, (k11_lattice3('#skF_6', '#skF_8', '#skF_7')='#skF_1'('#skF_6', '#skF_7', '#skF_8') | ~r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_8') | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v2_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1547, c_6514])).
% 10.00/3.64  tff(c_6618, plain, (k11_lattice3('#skF_6', '#skF_8', '#skF_7')='#skF_1'('#skF_6', '#skF_7', '#skF_8') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_40, c_42, c_1548, c_1914, c_6546])).
% 10.00/3.64  tff(c_6619, plain, (k11_lattice3('#skF_6', '#skF_8', '#skF_7')='#skF_1'('#skF_6', '#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_221, c_6618])).
% 10.00/3.64  tff(c_1389, plain, (![B_237]: (k11_lattice3('#skF_6', '#skF_1'('#skF_6', B_237, '#skF_7'), B_237)='#skF_1'('#skF_6', B_237, '#skF_7') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~m1_subset_1(B_237, u1_struct_0('#skF_6')) | ~v2_lattice3('#skF_6') | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_42, c_1371])).
% 10.00/3.64  tff(c_1409, plain, (![B_237]: (k11_lattice3('#skF_6', '#skF_1'('#skF_6', B_237, '#skF_7'), B_237)='#skF_1'('#skF_6', B_237, '#skF_7') | v2_struct_0('#skF_6') | ~m1_subset_1(B_237, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_48, c_1389])).
% 10.00/3.64  tff(c_1475, plain, (![B_240]: (k11_lattice3('#skF_6', '#skF_1'('#skF_6', B_240, '#skF_7'), B_240)='#skF_1'('#skF_6', B_240, '#skF_7') | ~m1_subset_1(B_240, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_221, c_1409])).
% 10.00/3.64  tff(c_1517, plain, (k11_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_8')='#skF_1'('#skF_6', '#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_40, c_1475])).
% 10.00/3.64  tff(c_1524, plain, (r1_orders_2('#skF_6', k11_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_8'), '#skF_8') | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v2_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1517, c_34])).
% 10.00/3.64  tff(c_1533, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_8') | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_40, c_1517, c_1524])).
% 10.00/3.64  tff(c_1534, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_8') | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_221, c_1533])).
% 10.00/3.64  tff(c_1619, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_1534])).
% 10.00/3.64  tff(c_1622, plain, (~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~v2_lattice3('#skF_6') | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_22, c_1619])).
% 10.00/3.64  tff(c_1626, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_40, c_42, c_1622])).
% 10.00/3.64  tff(c_1628, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_1534])).
% 10.00/3.64  tff(c_1526, plain, (r1_orders_2('#skF_6', k11_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_8'), '#skF_1'('#skF_6', '#skF_8', '#skF_7')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v2_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1517, c_36])).
% 10.00/3.64  tff(c_1536, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_1'('#skF_6', '#skF_8', '#skF_7')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_40, c_1517, c_1526])).
% 10.00/3.64  tff(c_1537, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_1'('#skF_6', '#skF_8', '#skF_7')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_221, c_1536])).
% 10.00/3.64  tff(c_1641, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_1537])).
% 10.00/3.64  tff(c_1667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1628, c_1641])).
% 10.00/3.64  tff(c_1668, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_1'('#skF_6', '#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_1537])).
% 10.00/3.64  tff(c_1701, plain, (k11_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_7')='#skF_1'('#skF_6', '#skF_8', '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6')) | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~v2_lattice3('#skF_6') | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_1668, c_124])).
% 10.00/3.64  tff(c_1716, plain, (k11_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_7')='#skF_1'('#skF_6', '#skF_8', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_40, c_42, c_48, c_1628, c_1701])).
% 10.00/3.64  tff(c_1717, plain, (k11_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_7')='#skF_1'('#skF_6', '#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_221, c_1716])).
% 10.00/3.64  tff(c_1764, plain, (r1_orders_2('#skF_6', k11_lattice3('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_7'), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v2_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1717, c_34])).
% 10.00/3.64  tff(c_1773, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_1628, c_42, c_1628, c_1717, c_1764])).
% 10.00/3.64  tff(c_1774, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_221, c_1773])).
% 10.00/3.64  tff(c_1627, plain, (r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_1534])).
% 10.00/3.64  tff(c_6544, plain, (k11_lattice3('#skF_6', '#skF_7', '#skF_8')='#skF_1'('#skF_6', '#skF_8', '#skF_7') | ~r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_8', '#skF_7'), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', '#skF_8', '#skF_7'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v2_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1627, c_6514])).
% 10.00/3.64  tff(c_6614, plain, (k11_lattice3('#skF_6', '#skF_7', '#skF_8')='#skF_1'('#skF_6', '#skF_8', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_1628, c_1774, c_6544])).
% 10.00/3.64  tff(c_6615, plain, (k11_lattice3('#skF_6', '#skF_7', '#skF_8')='#skF_1'('#skF_6', '#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_221, c_6614])).
% 10.00/3.64  tff(c_38, plain, (k11_lattice3('#skF_6', '#skF_7', '#skF_8')!=k11_lattice3('#skF_6', '#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.00/3.64  tff(c_6637, plain, (k11_lattice3('#skF_6', '#skF_8', '#skF_7')!='#skF_1'('#skF_6', '#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6615, c_38])).
% 10.00/3.64  tff(c_6676, plain, ('#skF_1'('#skF_6', '#skF_7', '#skF_8')!='#skF_1'('#skF_6', '#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6619, c_6637])).
% 10.00/3.64  tff(c_864, plain, (![A_209, B_210, C_211, B_212]: (~r1_orders_2(A_209, '#skF_5'(A_209, B_210, C_211, '#skF_1'(A_209, B_212, C_211)), B_212) | ~m1_subset_1('#skF_5'(A_209, B_210, C_211, '#skF_1'(A_209, B_212, C_211)), u1_struct_0(A_209)) | ~m1_subset_1(B_212, u1_struct_0(A_209)) | k11_lattice3(A_209, B_210, C_211)='#skF_1'(A_209, B_212, C_211) | ~r1_orders_2(A_209, '#skF_1'(A_209, B_212, C_211), C_211) | ~r1_orders_2(A_209, '#skF_1'(A_209, B_212, C_211), B_210) | ~m1_subset_1('#skF_1'(A_209, B_212, C_211), u1_struct_0(A_209)) | ~m1_subset_1(C_211, u1_struct_0(A_209)) | ~m1_subset_1(B_210, u1_struct_0(A_209)) | ~l1_orders_2(A_209) | ~v2_lattice3(A_209) | ~v5_orders_2(A_209) | v2_struct_0(A_209))), inference(resolution, [status(thm)], [c_26, c_199])).
% 10.00/3.64  tff(c_2305, plain, (![A_257, B_258, C_259]: (~m1_subset_1('#skF_5'(A_257, B_258, C_259, '#skF_1'(A_257, B_258, C_259)), u1_struct_0(A_257)) | k11_lattice3(A_257, B_258, C_259)='#skF_1'(A_257, B_258, C_259) | ~r1_orders_2(A_257, '#skF_1'(A_257, B_258, C_259), C_259) | ~r1_orders_2(A_257, '#skF_1'(A_257, B_258, C_259), B_258) | ~m1_subset_1('#skF_1'(A_257, B_258, C_259), u1_struct_0(A_257)) | ~m1_subset_1(C_259, u1_struct_0(A_257)) | ~m1_subset_1(B_258, u1_struct_0(A_257)) | ~l1_orders_2(A_257) | ~v2_lattice3(A_257) | ~v5_orders_2(A_257) | v2_struct_0(A_257))), inference(resolution, [status(thm)], [c_28, c_864])).
% 10.00/3.64  tff(c_7479, plain, (![A_343, B_344, C_345]: (k11_lattice3(A_343, B_344, C_345)='#skF_1'(A_343, B_344, C_345) | ~r1_orders_2(A_343, '#skF_1'(A_343, B_344, C_345), C_345) | ~r1_orders_2(A_343, '#skF_1'(A_343, B_344, C_345), B_344) | ~m1_subset_1('#skF_1'(A_343, B_344, C_345), u1_struct_0(A_343)) | ~m1_subset_1(C_345, u1_struct_0(A_343)) | ~m1_subset_1(B_344, u1_struct_0(A_343)) | ~l1_orders_2(A_343) | ~v2_lattice3(A_343) | ~v5_orders_2(A_343) | v2_struct_0(A_343))), inference(resolution, [status(thm)], [c_30, c_2305])).
% 10.00/3.64  tff(c_7511, plain, (k11_lattice3('#skF_6', '#skF_7', '#skF_8')='#skF_1'('#skF_6', '#skF_7', '#skF_8') | ~r1_orders_2('#skF_6', '#skF_1'('#skF_6', '#skF_7', '#skF_8'), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v2_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1914, c_7479])).
% 10.00/3.64  tff(c_7577, plain, ('#skF_1'('#skF_6', '#skF_7', '#skF_8')='#skF_1'('#skF_6', '#skF_8', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_1548, c_1547, c_6615, c_7511])).
% 10.00/3.64  tff(c_7579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_221, c_6676, c_7577])).
% 10.00/3.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.00/3.64  
% 10.00/3.64  Inference rules
% 10.00/3.64  ----------------------
% 10.00/3.64  #Ref     : 0
% 10.00/3.64  #Sup     : 1454
% 10.00/3.64  #Fact    : 0
% 10.00/3.64  #Define  : 0
% 10.00/3.64  #Split   : 27
% 10.00/3.64  #Chain   : 0
% 10.00/3.64  #Close   : 0
% 10.00/3.64  
% 10.00/3.64  Ordering : KBO
% 10.00/3.64  
% 10.00/3.64  Simplification rules
% 10.00/3.64  ----------------------
% 10.00/3.64  #Subsume      : 96
% 10.00/3.64  #Demod        : 7980
% 10.00/3.64  #Tautology    : 823
% 10.00/3.64  #SimpNegUnit  : 871
% 10.00/3.64  #BackRed      : 72
% 10.00/3.64  
% 10.00/3.64  #Partial instantiations: 0
% 10.00/3.64  #Strategies tried      : 1
% 10.00/3.64  
% 10.00/3.64  Timing (in seconds)
% 10.00/3.64  ----------------------
% 10.00/3.64  Preprocessing        : 0.33
% 10.00/3.64  Parsing              : 0.16
% 10.00/3.64  CNF conversion       : 0.03
% 10.00/3.64  Main loop            : 2.54
% 10.00/3.64  Inferencing          : 0.54
% 10.00/3.65  Reduction            : 0.95
% 10.00/3.65  Demodulation         : 0.79
% 10.00/3.65  BG Simplification    : 0.06
% 10.00/3.65  Subsumption          : 0.90
% 10.00/3.65  Abstraction          : 0.10
% 10.00/3.65  MUC search           : 0.00
% 10.00/3.65  Cooper               : 0.00
% 10.00/3.65  Total                : 2.92
% 10.00/3.65  Index Insertion      : 0.00
% 10.00/3.65  Index Deletion       : 0.00
% 10.00/3.65  Index Matching       : 0.00
% 10.00/3.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
