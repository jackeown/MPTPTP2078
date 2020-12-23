%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1526+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:59 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 215 expanded)
%              Number of leaves         :   22 (  89 expanded)
%              Depth                    :   12
%              Number of atoms          :  328 ( 966 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > v4_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( v4_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r1_orders_2(A,B,C)
                 => ! [D] :
                      ( ( r1_lattice3(A,D,C)
                       => r1_lattice3(A,D,B) )
                      & ( r2_lattice3(A,D,B)
                       => r2_lattice3(A,D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_0)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r1_orders_2(A,B,C)
                      & r1_orders_2(A,C,D) )
                   => r1_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

tff(c_30,plain,
    ( ~ r2_lattice3('#skF_3','#skF_6','#skF_5')
    | ~ r1_lattice3('#skF_3','#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_37,plain,(
    ~ r1_lattice3('#skF_3','#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,
    ( r2_lattice3('#skF_3','#skF_6','#skF_4')
    | r1_lattice3('#skF_3','#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_39,plain,(
    r1_lattice3('#skF_3','#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_8,plain,(
    ! [A_1,B_8,C_9] :
      ( m1_subset_1('#skF_1'(A_1,B_8,C_9),u1_struct_0(A_1))
      | r1_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_20,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6,plain,(
    ! [A_1,B_8,C_9] :
      ( r2_hidden('#skF_1'(A_1,B_8,C_9),B_8)
      | r1_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_46,plain,(
    ! [A_69,C_70,D_71,B_72] :
      ( r1_orders_2(A_69,C_70,D_71)
      | ~ r2_hidden(D_71,B_72)
      | ~ m1_subset_1(D_71,u1_struct_0(A_69))
      | ~ r1_lattice3(A_69,B_72,C_70)
      | ~ m1_subset_1(C_70,u1_struct_0(A_69))
      | ~ l1_orders_2(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_131,plain,(
    ! [C_102,A_101,B_99,A_103,C_100] :
      ( r1_orders_2(A_101,C_102,'#skF_1'(A_103,B_99,C_100))
      | ~ m1_subset_1('#skF_1'(A_103,B_99,C_100),u1_struct_0(A_101))
      | ~ r1_lattice3(A_101,B_99,C_102)
      | ~ m1_subset_1(C_102,u1_struct_0(A_101))
      | ~ l1_orders_2(A_101)
      | r1_lattice3(A_103,B_99,C_100)
      | ~ m1_subset_1(C_100,u1_struct_0(A_103))
      | ~ l1_orders_2(A_103) ) ),
    inference(resolution,[status(thm)],[c_6,c_46])).

tff(c_135,plain,(
    ! [A_104,C_105,B_106,C_107] :
      ( r1_orders_2(A_104,C_105,'#skF_1'(A_104,B_106,C_107))
      | ~ r1_lattice3(A_104,B_106,C_105)
      | ~ m1_subset_1(C_105,u1_struct_0(A_104))
      | r1_lattice3(A_104,B_106,C_107)
      | ~ m1_subset_1(C_107,u1_struct_0(A_104))
      | ~ l1_orders_2(A_104) ) ),
    inference(resolution,[status(thm)],[c_8,c_131])).

tff(c_18,plain,(
    ! [A_25,B_33,D_39,C_37] :
      ( r1_orders_2(A_25,B_33,D_39)
      | ~ r1_orders_2(A_25,C_37,D_39)
      | ~ r1_orders_2(A_25,B_33,C_37)
      | ~ m1_subset_1(D_39,u1_struct_0(A_25))
      | ~ m1_subset_1(C_37,u1_struct_0(A_25))
      | ~ m1_subset_1(B_33,u1_struct_0(A_25))
      | ~ l1_orders_2(A_25)
      | ~ v4_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_251,plain,(
    ! [B_143,A_144,C_142,B_145,C_146] :
      ( r1_orders_2(A_144,B_143,'#skF_1'(A_144,B_145,C_146))
      | ~ r1_orders_2(A_144,B_143,C_142)
      | ~ m1_subset_1('#skF_1'(A_144,B_145,C_146),u1_struct_0(A_144))
      | ~ m1_subset_1(B_143,u1_struct_0(A_144))
      | ~ v4_orders_2(A_144)
      | ~ r1_lattice3(A_144,B_145,C_142)
      | ~ m1_subset_1(C_142,u1_struct_0(A_144))
      | r1_lattice3(A_144,B_145,C_146)
      | ~ m1_subset_1(C_146,u1_struct_0(A_144))
      | ~ l1_orders_2(A_144) ) ),
    inference(resolution,[status(thm)],[c_135,c_18])).

tff(c_265,plain,(
    ! [B_145,C_146] :
      ( r1_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3',B_145,C_146))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_145,C_146),u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ v4_orders_2('#skF_3')
      | ~ r1_lattice3('#skF_3',B_145,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | r1_lattice3('#skF_3',B_145,C_146)
      | ~ m1_subset_1(C_146,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_251])).

tff(c_279,plain,(
    ! [B_147,C_148] :
      ( r1_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3',B_147,C_148))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_147,C_148),u1_struct_0('#skF_3'))
      | ~ r1_lattice3('#skF_3',B_147,'#skF_5')
      | r1_lattice3('#skF_3',B_147,C_148)
      | ~ m1_subset_1(C_148,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_28,c_24,c_265])).

tff(c_283,plain,(
    ! [B_8,C_9] :
      ( r1_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3',B_8,C_9))
      | ~ r1_lattice3('#skF_3',B_8,'#skF_5')
      | r1_lattice3('#skF_3',B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_279])).

tff(c_287,plain,(
    ! [B_149,C_150] :
      ( r1_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3',B_149,C_150))
      | ~ r1_lattice3('#skF_3',B_149,'#skF_5')
      | r1_lattice3('#skF_3',B_149,C_150)
      | ~ m1_subset_1(C_150,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_283])).

tff(c_4,plain,(
    ! [A_1,C_9,B_8] :
      ( ~ r1_orders_2(A_1,C_9,'#skF_1'(A_1,B_8,C_9))
      | r1_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_297,plain,(
    ! [B_149] :
      ( ~ l1_orders_2('#skF_3')
      | ~ r1_lattice3('#skF_3',B_149,'#skF_5')
      | r1_lattice3('#skF_3',B_149,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_287,c_4])).

tff(c_310,plain,(
    ! [B_151] :
      ( ~ r1_lattice3('#skF_3',B_151,'#skF_5')
      | r1_lattice3('#skF_3',B_151,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_297])).

tff(c_313,plain,(
    r1_lattice3('#skF_3','#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_39,c_310])).

tff(c_317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_313])).

tff(c_318,plain,(
    r2_lattice3('#skF_3','#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_16,plain,(
    ! [A_13,B_20,C_21] :
      ( m1_subset_1('#skF_2'(A_13,B_20,C_21),u1_struct_0(A_13))
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_13,B_20,C_21] :
      ( r2_hidden('#skF_2'(A_13,B_20,C_21),B_20)
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_333,plain,(
    ! [A_174,D_175,C_176,B_177] :
      ( r1_orders_2(A_174,D_175,C_176)
      | ~ r2_hidden(D_175,B_177)
      | ~ m1_subset_1(D_175,u1_struct_0(A_174))
      | ~ r2_lattice3(A_174,B_177,C_176)
      | ~ m1_subset_1(C_176,u1_struct_0(A_174))
      | ~ l1_orders_2(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_404,plain,(
    ! [B_199,A_200,C_197,A_198,C_201] :
      ( r1_orders_2(A_198,'#skF_2'(A_200,B_199,C_197),C_201)
      | ~ m1_subset_1('#skF_2'(A_200,B_199,C_197),u1_struct_0(A_198))
      | ~ r2_lattice3(A_198,B_199,C_201)
      | ~ m1_subset_1(C_201,u1_struct_0(A_198))
      | ~ l1_orders_2(A_198)
      | r2_lattice3(A_200,B_199,C_197)
      | ~ m1_subset_1(C_197,u1_struct_0(A_200))
      | ~ l1_orders_2(A_200) ) ),
    inference(resolution,[status(thm)],[c_14,c_333])).

tff(c_409,plain,(
    ! [A_205,B_206,C_207,C_208] :
      ( r1_orders_2(A_205,'#skF_2'(A_205,B_206,C_207),C_208)
      | ~ r2_lattice3(A_205,B_206,C_208)
      | ~ m1_subset_1(C_208,u1_struct_0(A_205))
      | r2_lattice3(A_205,B_206,C_207)
      | ~ m1_subset_1(C_207,u1_struct_0(A_205))
      | ~ l1_orders_2(A_205) ) ),
    inference(resolution,[status(thm)],[c_16,c_404])).

tff(c_340,plain,(
    ! [A_178,B_179,D_180,C_181] :
      ( r1_orders_2(A_178,B_179,D_180)
      | ~ r1_orders_2(A_178,C_181,D_180)
      | ~ r1_orders_2(A_178,B_179,C_181)
      | ~ m1_subset_1(D_180,u1_struct_0(A_178))
      | ~ m1_subset_1(C_181,u1_struct_0(A_178))
      | ~ m1_subset_1(B_179,u1_struct_0(A_178))
      | ~ l1_orders_2(A_178)
      | ~ v4_orders_2(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_342,plain,(
    ! [B_179] :
      ( r1_orders_2('#skF_3',B_179,'#skF_5')
      | ~ r1_orders_2('#skF_3',B_179,'#skF_4')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_179,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_340])).

tff(c_346,plain,(
    ! [B_182] :
      ( r1_orders_2('#skF_3',B_182,'#skF_5')
      | ~ r1_orders_2('#skF_3',B_182,'#skF_4')
      | ~ m1_subset_1(B_182,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_22,c_342])).

tff(c_350,plain,(
    ! [B_20,C_21] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_3',B_20,C_21),'#skF_5')
      | ~ r1_orders_2('#skF_3','#skF_2'('#skF_3',B_20,C_21),'#skF_4')
      | r2_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_346])).

tff(c_371,plain,(
    ! [B_183,C_184] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_3',B_183,C_184),'#skF_5')
      | ~ r1_orders_2('#skF_3','#skF_2'('#skF_3',B_183,C_184),'#skF_4')
      | r2_lattice3('#skF_3',B_183,C_184)
      | ~ m1_subset_1(C_184,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_350])).

tff(c_12,plain,(
    ! [A_13,B_20,C_21] :
      ( ~ r1_orders_2(A_13,'#skF_2'(A_13,B_20,C_21),C_21)
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_377,plain,(
    ! [B_183] :
      ( ~ l1_orders_2('#skF_3')
      | ~ r1_orders_2('#skF_3','#skF_2'('#skF_3',B_183,'#skF_5'),'#skF_4')
      | r2_lattice3('#skF_3',B_183,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_371,c_12])).

tff(c_383,plain,(
    ! [B_183] :
      ( ~ r1_orders_2('#skF_3','#skF_2'('#skF_3',B_183,'#skF_5'),'#skF_4')
      | r2_lattice3('#skF_3',B_183,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26,c_377])).

tff(c_416,plain,(
    ! [B_206] :
      ( ~ r2_lattice3('#skF_3',B_206,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | r2_lattice3('#skF_3',B_206,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_409,c_383])).

tff(c_436,plain,(
    ! [B_209] :
      ( ~ r2_lattice3('#skF_3',B_209,'#skF_4')
      | r2_lattice3('#skF_3',B_209,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_24,c_416])).

tff(c_34,plain,
    ( ~ r2_lattice3('#skF_3','#skF_6','#skF_5')
    | r1_lattice3('#skF_3','#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_38,plain,(
    ~ r2_lattice3('#skF_3','#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_439,plain,(
    ~ r2_lattice3('#skF_3','#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_436,c_38])).

tff(c_443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_439])).

tff(c_444,plain,(
    r1_lattice3('#skF_3','#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_453,plain,(
    ! [A_228,C_229,D_230,B_231] :
      ( r1_orders_2(A_228,C_229,D_230)
      | ~ r2_hidden(D_230,B_231)
      | ~ m1_subset_1(D_230,u1_struct_0(A_228))
      | ~ r1_lattice3(A_228,B_231,C_229)
      | ~ m1_subset_1(C_229,u1_struct_0(A_228))
      | ~ l1_orders_2(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_518,plain,(
    ! [C_248,A_250,B_247,C_246,A_249] :
      ( r1_orders_2(A_249,C_246,'#skF_1'(A_250,B_247,C_248))
      | ~ m1_subset_1('#skF_1'(A_250,B_247,C_248),u1_struct_0(A_249))
      | ~ r1_lattice3(A_249,B_247,C_246)
      | ~ m1_subset_1(C_246,u1_struct_0(A_249))
      | ~ l1_orders_2(A_249)
      | r1_lattice3(A_250,B_247,C_248)
      | ~ m1_subset_1(C_248,u1_struct_0(A_250))
      | ~ l1_orders_2(A_250) ) ),
    inference(resolution,[status(thm)],[c_6,c_453])).

tff(c_522,plain,(
    ! [A_251,C_252,B_253,C_254] :
      ( r1_orders_2(A_251,C_252,'#skF_1'(A_251,B_253,C_254))
      | ~ r1_lattice3(A_251,B_253,C_252)
      | ~ m1_subset_1(C_252,u1_struct_0(A_251))
      | r1_lattice3(A_251,B_253,C_254)
      | ~ m1_subset_1(C_254,u1_struct_0(A_251))
      | ~ l1_orders_2(A_251) ) ),
    inference(resolution,[status(thm)],[c_8,c_518])).

tff(c_902,plain,(
    ! [A_375,B_374,C_371,C_372,B_373] :
      ( r1_orders_2(A_375,B_373,'#skF_1'(A_375,B_374,C_372))
      | ~ r1_orders_2(A_375,B_373,C_371)
      | ~ m1_subset_1('#skF_1'(A_375,B_374,C_372),u1_struct_0(A_375))
      | ~ m1_subset_1(B_373,u1_struct_0(A_375))
      | ~ v4_orders_2(A_375)
      | ~ r1_lattice3(A_375,B_374,C_371)
      | ~ m1_subset_1(C_371,u1_struct_0(A_375))
      | r1_lattice3(A_375,B_374,C_372)
      | ~ m1_subset_1(C_372,u1_struct_0(A_375))
      | ~ l1_orders_2(A_375) ) ),
    inference(resolution,[status(thm)],[c_522,c_18])).

tff(c_920,plain,(
    ! [B_374,C_372] :
      ( r1_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3',B_374,C_372))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_374,C_372),u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ v4_orders_2('#skF_3')
      | ~ r1_lattice3('#skF_3',B_374,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | r1_lattice3('#skF_3',B_374,C_372)
      | ~ m1_subset_1(C_372,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_902])).

tff(c_1127,plain,(
    ! [B_394,C_395] :
      ( r1_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3',B_394,C_395))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_394,C_395),u1_struct_0('#skF_3'))
      | ~ r1_lattice3('#skF_3',B_394,'#skF_5')
      | r1_lattice3('#skF_3',B_394,C_395)
      | ~ m1_subset_1(C_395,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_28,c_24,c_920])).

tff(c_1131,plain,(
    ! [B_8,C_9] :
      ( r1_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3',B_8,C_9))
      | ~ r1_lattice3('#skF_3',B_8,'#skF_5')
      | r1_lattice3('#skF_3',B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_1127])).

tff(c_1135,plain,(
    ! [B_396,C_397] :
      ( r1_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3',B_396,C_397))
      | ~ r1_lattice3('#skF_3',B_396,'#skF_5')
      | r1_lattice3('#skF_3',B_396,C_397)
      | ~ m1_subset_1(C_397,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1131])).

tff(c_1149,plain,(
    ! [B_396] :
      ( ~ l1_orders_2('#skF_3')
      | ~ r1_lattice3('#skF_3',B_396,'#skF_5')
      | r1_lattice3('#skF_3',B_396,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1135,c_4])).

tff(c_1176,plain,(
    ! [B_400] :
      ( ~ r1_lattice3('#skF_3',B_400,'#skF_5')
      | r1_lattice3('#skF_3',B_400,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_1149])).

tff(c_1182,plain,(
    r1_lattice3('#skF_3','#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_444,c_1176])).

tff(c_1188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_1182])).

tff(c_1190,plain,(
    r1_lattice3('#skF_3','#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( r2_lattice3('#skF_3','#skF_6','#skF_4')
    | ~ r1_lattice3('#skF_3','#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1193,plain,(
    r2_lattice3('#skF_3','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1190,c_32])).

tff(c_1200,plain,(
    ! [A_419,D_420,C_421,B_422] :
      ( r1_orders_2(A_419,D_420,C_421)
      | ~ r2_hidden(D_420,B_422)
      | ~ m1_subset_1(D_420,u1_struct_0(A_419))
      | ~ r2_lattice3(A_419,B_422,C_421)
      | ~ m1_subset_1(C_421,u1_struct_0(A_419))
      | ~ l1_orders_2(A_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1282,plain,(
    ! [A_455,C_452,A_453,B_454,C_451] :
      ( r1_orders_2(A_453,'#skF_2'(A_455,B_454,C_451),C_452)
      | ~ m1_subset_1('#skF_2'(A_455,B_454,C_451),u1_struct_0(A_453))
      | ~ r2_lattice3(A_453,B_454,C_452)
      | ~ m1_subset_1(C_452,u1_struct_0(A_453))
      | ~ l1_orders_2(A_453)
      | r2_lattice3(A_455,B_454,C_451)
      | ~ m1_subset_1(C_451,u1_struct_0(A_455))
      | ~ l1_orders_2(A_455) ) ),
    inference(resolution,[status(thm)],[c_14,c_1200])).

tff(c_1295,plain,(
    ! [A_460,B_461,C_462,C_463] :
      ( r1_orders_2(A_460,'#skF_2'(A_460,B_461,C_462),C_463)
      | ~ r2_lattice3(A_460,B_461,C_463)
      | ~ m1_subset_1(C_463,u1_struct_0(A_460))
      | r2_lattice3(A_460,B_461,C_462)
      | ~ m1_subset_1(C_462,u1_struct_0(A_460))
      | ~ l1_orders_2(A_460) ) ),
    inference(resolution,[status(thm)],[c_16,c_1282])).

tff(c_1214,plain,(
    ! [A_427,B_428,D_429,C_430] :
      ( r1_orders_2(A_427,B_428,D_429)
      | ~ r1_orders_2(A_427,C_430,D_429)
      | ~ r1_orders_2(A_427,B_428,C_430)
      | ~ m1_subset_1(D_429,u1_struct_0(A_427))
      | ~ m1_subset_1(C_430,u1_struct_0(A_427))
      | ~ m1_subset_1(B_428,u1_struct_0(A_427))
      | ~ l1_orders_2(A_427)
      | ~ v4_orders_2(A_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1216,plain,(
    ! [B_428] :
      ( r1_orders_2('#skF_3',B_428,'#skF_5')
      | ~ r1_orders_2('#skF_3',B_428,'#skF_4')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_428,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_1214])).

tff(c_1220,plain,(
    ! [B_431] :
      ( r1_orders_2('#skF_3',B_431,'#skF_5')
      | ~ r1_orders_2('#skF_3',B_431,'#skF_4')
      | ~ m1_subset_1(B_431,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_22,c_1216])).

tff(c_1228,plain,(
    ! [B_20,C_21] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_3',B_20,C_21),'#skF_5')
      | ~ r1_orders_2('#skF_3','#skF_2'('#skF_3',B_20,C_21),'#skF_4')
      | r2_lattice3('#skF_3',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_1220])).

tff(c_1251,plain,(
    ! [B_434,C_435] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_3',B_434,C_435),'#skF_5')
      | ~ r1_orders_2('#skF_3','#skF_2'('#skF_3',B_434,C_435),'#skF_4')
      | r2_lattice3('#skF_3',B_434,C_435)
      | ~ m1_subset_1(C_435,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1228])).

tff(c_1257,plain,(
    ! [B_434] :
      ( ~ l1_orders_2('#skF_3')
      | ~ r1_orders_2('#skF_3','#skF_2'('#skF_3',B_434,'#skF_5'),'#skF_4')
      | r2_lattice3('#skF_3',B_434,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1251,c_12])).

tff(c_1263,plain,(
    ! [B_434] :
      ( ~ r1_orders_2('#skF_3','#skF_2'('#skF_3',B_434,'#skF_5'),'#skF_4')
      | r2_lattice3('#skF_3',B_434,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26,c_1257])).

tff(c_1299,plain,(
    ! [B_461] :
      ( ~ r2_lattice3('#skF_3',B_461,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | r2_lattice3('#skF_3',B_461,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1295,c_1263])).

tff(c_1316,plain,(
    ! [B_464] :
      ( ~ r2_lattice3('#skF_3',B_464,'#skF_4')
      | r2_lattice3('#skF_3',B_464,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_24,c_1299])).

tff(c_1189,plain,(
    ~ r2_lattice3('#skF_3','#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1319,plain,(
    ~ r2_lattice3('#skF_3','#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_1316,c_1189])).

tff(c_1323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1193,c_1319])).

%------------------------------------------------------------------------------
