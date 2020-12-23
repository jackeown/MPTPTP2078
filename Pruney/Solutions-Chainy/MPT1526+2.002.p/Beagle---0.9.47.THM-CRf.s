%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:56 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 3.94s
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

tff(f_94,negated_conjecture,(
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

tff(f_58,axiom,(
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

tff(f_44,axiom,(
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

tff(f_72,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_37,plain,(
    ~ r1_lattice3('#skF_3','#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,
    ( r2_lattice3('#skF_3','#skF_6','#skF_4')
    | r1_lattice3('#skF_3','#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_39,plain,(
    r1_lattice3('#skF_3','#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_26,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_10,plain,(
    ! [A_16,B_23,C_24] :
      ( m1_subset_1('#skF_1'(A_16,B_23,C_24),u1_struct_0(A_16))
      | r1_lattice3(A_16,B_23,C_24)
      | ~ m1_subset_1(C_24,u1_struct_0(A_16))
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_20,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_8,plain,(
    ! [A_16,B_23,C_24] :
      ( r2_hidden('#skF_1'(A_16,B_23,C_24),B_23)
      | r1_lattice3(A_16,B_23,C_24)
      | ~ m1_subset_1(C_24,u1_struct_0(A_16))
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_53,plain,(
    ! [A_73,C_74,D_75,B_76] :
      ( r1_orders_2(A_73,C_74,D_75)
      | ~ r2_hidden(D_75,B_76)
      | ~ m1_subset_1(D_75,u1_struct_0(A_73))
      | ~ r1_lattice3(A_73,B_76,C_74)
      | ~ m1_subset_1(C_74,u1_struct_0(A_73))
      | ~ l1_orders_2(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_171,plain,(
    ! [C_115,C_114,A_116,A_118,B_117] :
      ( r1_orders_2(A_118,C_115,'#skF_1'(A_116,B_117,C_114))
      | ~ m1_subset_1('#skF_1'(A_116,B_117,C_114),u1_struct_0(A_118))
      | ~ r1_lattice3(A_118,B_117,C_115)
      | ~ m1_subset_1(C_115,u1_struct_0(A_118))
      | ~ l1_orders_2(A_118)
      | r1_lattice3(A_116,B_117,C_114)
      | ~ m1_subset_1(C_114,u1_struct_0(A_116))
      | ~ l1_orders_2(A_116) ) ),
    inference(resolution,[status(thm)],[c_8,c_53])).

tff(c_190,plain,(
    ! [A_123,C_124,B_125,C_126] :
      ( r1_orders_2(A_123,C_124,'#skF_1'(A_123,B_125,C_126))
      | ~ r1_lattice3(A_123,B_125,C_124)
      | ~ m1_subset_1(C_124,u1_struct_0(A_123))
      | r1_lattice3(A_123,B_125,C_126)
      | ~ m1_subset_1(C_126,u1_struct_0(A_123))
      | ~ l1_orders_2(A_123) ) ),
    inference(resolution,[status(thm)],[c_10,c_171])).

tff(c_2,plain,(
    ! [A_1,B_9,D_15,C_13] :
      ( r1_orders_2(A_1,B_9,D_15)
      | ~ r1_orders_2(A_1,C_13,D_15)
      | ~ r1_orders_2(A_1,B_9,C_13)
      | ~ m1_subset_1(D_15,u1_struct_0(A_1))
      | ~ m1_subset_1(C_13,u1_struct_0(A_1))
      | ~ m1_subset_1(B_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1)
      | ~ v4_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_251,plain,(
    ! [B_143,C_144,A_142,B_145,C_146] :
      ( r1_orders_2(A_142,B_145,'#skF_1'(A_142,B_143,C_144))
      | ~ r1_orders_2(A_142,B_145,C_146)
      | ~ m1_subset_1('#skF_1'(A_142,B_143,C_144),u1_struct_0(A_142))
      | ~ m1_subset_1(B_145,u1_struct_0(A_142))
      | ~ v4_orders_2(A_142)
      | ~ r1_lattice3(A_142,B_143,C_146)
      | ~ m1_subset_1(C_146,u1_struct_0(A_142))
      | r1_lattice3(A_142,B_143,C_144)
      | ~ m1_subset_1(C_144,u1_struct_0(A_142))
      | ~ l1_orders_2(A_142) ) ),
    inference(resolution,[status(thm)],[c_190,c_2])).

tff(c_265,plain,(
    ! [B_143,C_144] :
      ( r1_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3',B_143,C_144))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_143,C_144),u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ v4_orders_2('#skF_3')
      | ~ r1_lattice3('#skF_3',B_143,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | r1_lattice3('#skF_3',B_143,C_144)
      | ~ m1_subset_1(C_144,u1_struct_0('#skF_3'))
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
    ! [B_23,C_24] :
      ( r1_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3',B_23,C_24))
      | ~ r1_lattice3('#skF_3',B_23,'#skF_5')
      | r1_lattice3('#skF_3',B_23,C_24)
      | ~ m1_subset_1(C_24,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_279])).

tff(c_287,plain,(
    ! [B_149,C_150] :
      ( r1_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3',B_149,C_150))
      | ~ r1_lattice3('#skF_3',B_149,'#skF_5')
      | r1_lattice3('#skF_3',B_149,C_150)
      | ~ m1_subset_1(C_150,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_283])).

tff(c_6,plain,(
    ! [A_16,C_24,B_23] :
      ( ~ r1_orders_2(A_16,C_24,'#skF_1'(A_16,B_23,C_24))
      | r1_lattice3(A_16,B_23,C_24)
      | ~ m1_subset_1(C_24,u1_struct_0(A_16))
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_297,plain,(
    ! [B_149] :
      ( ~ l1_orders_2('#skF_3')
      | ~ r1_lattice3('#skF_3',B_149,'#skF_5')
      | r1_lattice3('#skF_3',B_149,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_287,c_6])).

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

tff(c_18,plain,(
    ! [A_28,B_35,C_36] :
      ( m1_subset_1('#skF_2'(A_28,B_35,C_36),u1_struct_0(A_28))
      | r2_lattice3(A_28,B_35,C_36)
      | ~ m1_subset_1(C_36,u1_struct_0(A_28))
      | ~ l1_orders_2(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    ! [A_28,B_35,C_36] :
      ( r2_hidden('#skF_2'(A_28,B_35,C_36),B_35)
      | r2_lattice3(A_28,B_35,C_36)
      | ~ m1_subset_1(C_36,u1_struct_0(A_28))
      | ~ l1_orders_2(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_326,plain,(
    ! [A_170,D_171,C_172,B_173] :
      ( r1_orders_2(A_170,D_171,C_172)
      | ~ r2_hidden(D_171,B_173)
      | ~ m1_subset_1(D_171,u1_struct_0(A_170))
      | ~ r2_lattice3(A_170,B_173,C_172)
      | ~ m1_subset_1(C_172,u1_struct_0(A_170))
      | ~ l1_orders_2(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_435,plain,(
    ! [B_211,A_209,C_213,A_210,C_212] :
      ( r1_orders_2(A_209,'#skF_2'(A_210,B_211,C_213),C_212)
      | ~ m1_subset_1('#skF_2'(A_210,B_211,C_213),u1_struct_0(A_209))
      | ~ r2_lattice3(A_209,B_211,C_212)
      | ~ m1_subset_1(C_212,u1_struct_0(A_209))
      | ~ l1_orders_2(A_209)
      | r2_lattice3(A_210,B_211,C_213)
      | ~ m1_subset_1(C_213,u1_struct_0(A_210))
      | ~ l1_orders_2(A_210) ) ),
    inference(resolution,[status(thm)],[c_16,c_326])).

tff(c_439,plain,(
    ! [A_214,B_215,C_216,C_217] :
      ( r1_orders_2(A_214,'#skF_2'(A_214,B_215,C_216),C_217)
      | ~ r2_lattice3(A_214,B_215,C_217)
      | ~ m1_subset_1(C_217,u1_struct_0(A_214))
      | r2_lattice3(A_214,B_215,C_216)
      | ~ m1_subset_1(C_216,u1_struct_0(A_214))
      | ~ l1_orders_2(A_214) ) ),
    inference(resolution,[status(thm)],[c_18,c_435])).

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
    inference(cnfTransformation,[status(thm)],[f_44])).

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
    ! [B_35,C_36] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_3',B_35,C_36),'#skF_5')
      | ~ r1_orders_2('#skF_3','#skF_2'('#skF_3',B_35,C_36),'#skF_4')
      | r2_lattice3('#skF_3',B_35,C_36)
      | ~ m1_subset_1(C_36,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_346])).

tff(c_371,plain,(
    ! [B_183,C_184] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_3',B_183,C_184),'#skF_5')
      | ~ r1_orders_2('#skF_3','#skF_2'('#skF_3',B_183,C_184),'#skF_4')
      | r2_lattice3('#skF_3',B_183,C_184)
      | ~ m1_subset_1(C_184,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_350])).

tff(c_14,plain,(
    ! [A_28,B_35,C_36] :
      ( ~ r1_orders_2(A_28,'#skF_2'(A_28,B_35,C_36),C_36)
      | r2_lattice3(A_28,B_35,C_36)
      | ~ m1_subset_1(C_36,u1_struct_0(A_28))
      | ~ l1_orders_2(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_377,plain,(
    ! [B_183] :
      ( ~ l1_orders_2('#skF_3')
      | ~ r1_orders_2('#skF_3','#skF_2'('#skF_3',B_183,'#skF_5'),'#skF_4')
      | r2_lattice3('#skF_3',B_183,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_371,c_14])).

tff(c_383,plain,(
    ! [B_183] :
      ( ~ r1_orders_2('#skF_3','#skF_2'('#skF_3',B_183,'#skF_5'),'#skF_4')
      | r2_lattice3('#skF_3',B_183,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26,c_377])).

tff(c_446,plain,(
    ! [B_215] :
      ( ~ r2_lattice3('#skF_3',B_215,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | r2_lattice3('#skF_3',B_215,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_439,c_383])).

tff(c_466,plain,(
    ! [B_218] :
      ( ~ r2_lattice3('#skF_3',B_218,'#skF_4')
      | r2_lattice3('#skF_3',B_218,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_24,c_446])).

tff(c_34,plain,
    ( ~ r2_lattice3('#skF_3','#skF_6','#skF_5')
    | r1_lattice3('#skF_3','#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,(
    ~ r2_lattice3('#skF_3','#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_469,plain,(
    ~ r2_lattice3('#skF_3','#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_466,c_38])).

tff(c_473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_469])).

tff(c_474,plain,(
    r1_lattice3('#skF_3','#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_483,plain,(
    ! [A_237,C_238,D_239,B_240] :
      ( r1_orders_2(A_237,C_238,D_239)
      | ~ r2_hidden(D_239,B_240)
      | ~ m1_subset_1(D_239,u1_struct_0(A_237))
      | ~ r1_lattice3(A_237,B_240,C_238)
      | ~ m1_subset_1(C_238,u1_struct_0(A_237))
      | ~ l1_orders_2(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_573,plain,(
    ! [B_267,A_266,C_264,A_265,C_268] :
      ( r1_orders_2(A_265,C_268,'#skF_1'(A_266,B_267,C_264))
      | ~ m1_subset_1('#skF_1'(A_266,B_267,C_264),u1_struct_0(A_265))
      | ~ r1_lattice3(A_265,B_267,C_268)
      | ~ m1_subset_1(C_268,u1_struct_0(A_265))
      | ~ l1_orders_2(A_265)
      | r1_lattice3(A_266,B_267,C_264)
      | ~ m1_subset_1(C_264,u1_struct_0(A_266))
      | ~ l1_orders_2(A_266) ) ),
    inference(resolution,[status(thm)],[c_8,c_483])).

tff(c_578,plain,(
    ! [A_270,C_271,B_272,C_273] :
      ( r1_orders_2(A_270,C_271,'#skF_1'(A_270,B_272,C_273))
      | ~ r1_lattice3(A_270,B_272,C_271)
      | ~ m1_subset_1(C_271,u1_struct_0(A_270))
      | r1_lattice3(A_270,B_272,C_273)
      | ~ m1_subset_1(C_273,u1_struct_0(A_270))
      | ~ l1_orders_2(A_270) ) ),
    inference(resolution,[status(thm)],[c_10,c_573])).

tff(c_978,plain,(
    ! [B_380,C_379,C_378,A_381,B_377] :
      ( r1_orders_2(A_381,B_380,'#skF_1'(A_381,B_377,C_379))
      | ~ r1_orders_2(A_381,B_380,C_378)
      | ~ m1_subset_1('#skF_1'(A_381,B_377,C_379),u1_struct_0(A_381))
      | ~ m1_subset_1(B_380,u1_struct_0(A_381))
      | ~ v4_orders_2(A_381)
      | ~ r1_lattice3(A_381,B_377,C_378)
      | ~ m1_subset_1(C_378,u1_struct_0(A_381))
      | r1_lattice3(A_381,B_377,C_379)
      | ~ m1_subset_1(C_379,u1_struct_0(A_381))
      | ~ l1_orders_2(A_381) ) ),
    inference(resolution,[status(thm)],[c_578,c_2])).

tff(c_996,plain,(
    ! [B_377,C_379] :
      ( r1_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3',B_377,C_379))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_377,C_379),u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ v4_orders_2('#skF_3')
      | ~ r1_lattice3('#skF_3',B_377,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | r1_lattice3('#skF_3',B_377,C_379)
      | ~ m1_subset_1(C_379,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_978])).

tff(c_1038,plain,(
    ! [B_386,C_387] :
      ( r1_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3',B_386,C_387))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_386,C_387),u1_struct_0('#skF_3'))
      | ~ r1_lattice3('#skF_3',B_386,'#skF_5')
      | r1_lattice3('#skF_3',B_386,C_387)
      | ~ m1_subset_1(C_387,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_28,c_24,c_996])).

tff(c_1042,plain,(
    ! [B_23,C_24] :
      ( r1_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3',B_23,C_24))
      | ~ r1_lattice3('#skF_3',B_23,'#skF_5')
      | r1_lattice3('#skF_3',B_23,C_24)
      | ~ m1_subset_1(C_24,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_1038])).

tff(c_1046,plain,(
    ! [B_388,C_389] :
      ( r1_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3',B_388,C_389))
      | ~ r1_lattice3('#skF_3',B_388,'#skF_5')
      | r1_lattice3('#skF_3',B_388,C_389)
      | ~ m1_subset_1(C_389,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1042])).

tff(c_1060,plain,(
    ! [B_388] :
      ( ~ l1_orders_2('#skF_3')
      | ~ r1_lattice3('#skF_3',B_388,'#skF_5')
      | r1_lattice3('#skF_3',B_388,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1046,c_6])).

tff(c_1079,plain,(
    ! [B_390] :
      ( ~ r1_lattice3('#skF_3',B_390,'#skF_5')
      | r1_lattice3('#skF_3',B_390,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_1060])).

tff(c_1085,plain,(
    r1_lattice3('#skF_3','#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_474,c_1079])).

tff(c_1091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_1085])).

tff(c_1093,plain,(
    r1_lattice3('#skF_3','#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( r2_lattice3('#skF_3','#skF_6','#skF_4')
    | ~ r1_lattice3('#skF_3','#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1096,plain,(
    r2_lattice3('#skF_3','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1093,c_32])).

tff(c_1110,plain,(
    ! [A_413,D_414,C_415,B_416] :
      ( r1_orders_2(A_413,D_414,C_415)
      | ~ r2_hidden(D_414,B_416)
      | ~ m1_subset_1(D_414,u1_struct_0(A_413))
      | ~ r2_lattice3(A_413,B_416,C_415)
      | ~ m1_subset_1(C_415,u1_struct_0(A_413))
      | ~ l1_orders_2(A_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1168,plain,(
    ! [C_427,C_431,A_429,A_428,B_430] :
      ( r1_orders_2(A_428,'#skF_2'(A_429,B_430,C_431),C_427)
      | ~ m1_subset_1('#skF_2'(A_429,B_430,C_431),u1_struct_0(A_428))
      | ~ r2_lattice3(A_428,B_430,C_427)
      | ~ m1_subset_1(C_427,u1_struct_0(A_428))
      | ~ l1_orders_2(A_428)
      | r2_lattice3(A_429,B_430,C_431)
      | ~ m1_subset_1(C_431,u1_struct_0(A_429))
      | ~ l1_orders_2(A_429) ) ),
    inference(resolution,[status(thm)],[c_16,c_1110])).

tff(c_1172,plain,(
    ! [A_432,B_433,C_434,C_435] :
      ( r1_orders_2(A_432,'#skF_2'(A_432,B_433,C_434),C_435)
      | ~ r2_lattice3(A_432,B_433,C_435)
      | ~ m1_subset_1(C_435,u1_struct_0(A_432))
      | r2_lattice3(A_432,B_433,C_434)
      | ~ m1_subset_1(C_434,u1_struct_0(A_432))
      | ~ l1_orders_2(A_432) ) ),
    inference(resolution,[status(thm)],[c_18,c_1168])).

tff(c_1117,plain,(
    ! [A_417,B_418,D_419,C_420] :
      ( r1_orders_2(A_417,B_418,D_419)
      | ~ r1_orders_2(A_417,C_420,D_419)
      | ~ r1_orders_2(A_417,B_418,C_420)
      | ~ m1_subset_1(D_419,u1_struct_0(A_417))
      | ~ m1_subset_1(C_420,u1_struct_0(A_417))
      | ~ m1_subset_1(B_418,u1_struct_0(A_417))
      | ~ l1_orders_2(A_417)
      | ~ v4_orders_2(A_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1119,plain,(
    ! [B_418] :
      ( r1_orders_2('#skF_3',B_418,'#skF_5')
      | ~ r1_orders_2('#skF_3',B_418,'#skF_4')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_418,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_1117])).

tff(c_1123,plain,(
    ! [B_421] :
      ( r1_orders_2('#skF_3',B_421,'#skF_5')
      | ~ r1_orders_2('#skF_3',B_421,'#skF_4')
      | ~ m1_subset_1(B_421,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_22,c_1119])).

tff(c_1127,plain,(
    ! [B_35,C_36] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_3',B_35,C_36),'#skF_5')
      | ~ r1_orders_2('#skF_3','#skF_2'('#skF_3',B_35,C_36),'#skF_4')
      | r2_lattice3('#skF_3',B_35,C_36)
      | ~ m1_subset_1(C_36,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_1123])).

tff(c_1154,plain,(
    ! [B_424,C_425] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_3',B_424,C_425),'#skF_5')
      | ~ r1_orders_2('#skF_3','#skF_2'('#skF_3',B_424,C_425),'#skF_4')
      | r2_lattice3('#skF_3',B_424,C_425)
      | ~ m1_subset_1(C_425,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1127])).

tff(c_1160,plain,(
    ! [B_424] :
      ( ~ l1_orders_2('#skF_3')
      | ~ r1_orders_2('#skF_3','#skF_2'('#skF_3',B_424,'#skF_5'),'#skF_4')
      | r2_lattice3('#skF_3',B_424,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1154,c_14])).

tff(c_1166,plain,(
    ! [B_424] :
      ( ~ r1_orders_2('#skF_3','#skF_2'('#skF_3',B_424,'#skF_5'),'#skF_4')
      | r2_lattice3('#skF_3',B_424,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26,c_1160])).

tff(c_1176,plain,(
    ! [B_433] :
      ( ~ r2_lattice3('#skF_3',B_433,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | r2_lattice3('#skF_3',B_433,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1172,c_1166])).

tff(c_1197,plain,(
    ! [B_441] :
      ( ~ r2_lattice3('#skF_3',B_441,'#skF_4')
      | r2_lattice3('#skF_3',B_441,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_24,c_1176])).

tff(c_1092,plain,(
    ~ r2_lattice3('#skF_3','#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1200,plain,(
    ~ r2_lattice3('#skF_3','#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_1197,c_1092])).

tff(c_1204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1096,c_1200])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.94/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/1.74  
% 3.94/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/1.74  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > v4_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.94/1.74  
% 3.94/1.74  %Foreground sorts:
% 3.94/1.74  
% 3.94/1.74  
% 3.94/1.74  %Background operators:
% 3.94/1.74  
% 3.94/1.74  
% 3.94/1.74  %Foreground operators:
% 3.94/1.74  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.94/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.94/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.94/1.74  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.94/1.74  tff('#skF_7', type, '#skF_7': $i).
% 3.94/1.74  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 3.94/1.74  tff('#skF_5', type, '#skF_5': $i).
% 3.94/1.74  tff('#skF_6', type, '#skF_6': $i).
% 3.94/1.74  tff('#skF_3', type, '#skF_3': $i).
% 3.94/1.74  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.94/1.74  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 3.94/1.74  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.94/1.74  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.94/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.94/1.74  tff('#skF_4', type, '#skF_4': $i).
% 3.94/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.94/1.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.94/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.94/1.74  
% 3.94/1.77  tff(f_94, negated_conjecture, ~(![A]: ((v4_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) => (![D]: ((r1_lattice3(A, D, C) => r1_lattice3(A, D, B)) & (r2_lattice3(A, D, B) => r2_lattice3(A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_0)).
% 3.94/1.77  tff(f_58, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 3.94/1.77  tff(f_44, axiom, (![A]: ((v4_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, D)) => r1_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_orders_2)).
% 3.94/1.77  tff(f_72, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 3.94/1.77  tff(c_30, plain, (~r2_lattice3('#skF_3', '#skF_6', '#skF_5') | ~r1_lattice3('#skF_3', '#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.94/1.77  tff(c_37, plain, (~r1_lattice3('#skF_3', '#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_30])).
% 3.94/1.77  tff(c_36, plain, (r2_lattice3('#skF_3', '#skF_6', '#skF_4') | r1_lattice3('#skF_3', '#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.94/1.77  tff(c_39, plain, (r1_lattice3('#skF_3', '#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_36])).
% 3.94/1.77  tff(c_24, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.94/1.77  tff(c_26, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.94/1.77  tff(c_10, plain, (![A_16, B_23, C_24]: (m1_subset_1('#skF_1'(A_16, B_23, C_24), u1_struct_0(A_16)) | r1_lattice3(A_16, B_23, C_24) | ~m1_subset_1(C_24, u1_struct_0(A_16)) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.94/1.77  tff(c_22, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.94/1.77  tff(c_28, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.94/1.77  tff(c_20, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.94/1.77  tff(c_8, plain, (![A_16, B_23, C_24]: (r2_hidden('#skF_1'(A_16, B_23, C_24), B_23) | r1_lattice3(A_16, B_23, C_24) | ~m1_subset_1(C_24, u1_struct_0(A_16)) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.94/1.77  tff(c_53, plain, (![A_73, C_74, D_75, B_76]: (r1_orders_2(A_73, C_74, D_75) | ~r2_hidden(D_75, B_76) | ~m1_subset_1(D_75, u1_struct_0(A_73)) | ~r1_lattice3(A_73, B_76, C_74) | ~m1_subset_1(C_74, u1_struct_0(A_73)) | ~l1_orders_2(A_73))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.94/1.77  tff(c_171, plain, (![C_115, C_114, A_116, A_118, B_117]: (r1_orders_2(A_118, C_115, '#skF_1'(A_116, B_117, C_114)) | ~m1_subset_1('#skF_1'(A_116, B_117, C_114), u1_struct_0(A_118)) | ~r1_lattice3(A_118, B_117, C_115) | ~m1_subset_1(C_115, u1_struct_0(A_118)) | ~l1_orders_2(A_118) | r1_lattice3(A_116, B_117, C_114) | ~m1_subset_1(C_114, u1_struct_0(A_116)) | ~l1_orders_2(A_116))), inference(resolution, [status(thm)], [c_8, c_53])).
% 3.94/1.77  tff(c_190, plain, (![A_123, C_124, B_125, C_126]: (r1_orders_2(A_123, C_124, '#skF_1'(A_123, B_125, C_126)) | ~r1_lattice3(A_123, B_125, C_124) | ~m1_subset_1(C_124, u1_struct_0(A_123)) | r1_lattice3(A_123, B_125, C_126) | ~m1_subset_1(C_126, u1_struct_0(A_123)) | ~l1_orders_2(A_123))), inference(resolution, [status(thm)], [c_10, c_171])).
% 3.94/1.77  tff(c_2, plain, (![A_1, B_9, D_15, C_13]: (r1_orders_2(A_1, B_9, D_15) | ~r1_orders_2(A_1, C_13, D_15) | ~r1_orders_2(A_1, B_9, C_13) | ~m1_subset_1(D_15, u1_struct_0(A_1)) | ~m1_subset_1(C_13, u1_struct_0(A_1)) | ~m1_subset_1(B_9, u1_struct_0(A_1)) | ~l1_orders_2(A_1) | ~v4_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.94/1.77  tff(c_251, plain, (![B_143, C_144, A_142, B_145, C_146]: (r1_orders_2(A_142, B_145, '#skF_1'(A_142, B_143, C_144)) | ~r1_orders_2(A_142, B_145, C_146) | ~m1_subset_1('#skF_1'(A_142, B_143, C_144), u1_struct_0(A_142)) | ~m1_subset_1(B_145, u1_struct_0(A_142)) | ~v4_orders_2(A_142) | ~r1_lattice3(A_142, B_143, C_146) | ~m1_subset_1(C_146, u1_struct_0(A_142)) | r1_lattice3(A_142, B_143, C_144) | ~m1_subset_1(C_144, u1_struct_0(A_142)) | ~l1_orders_2(A_142))), inference(resolution, [status(thm)], [c_190, c_2])).
% 3.94/1.77  tff(c_265, plain, (![B_143, C_144]: (r1_orders_2('#skF_3', '#skF_4', '#skF_1'('#skF_3', B_143, C_144)) | ~m1_subset_1('#skF_1'('#skF_3', B_143, C_144), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v4_orders_2('#skF_3') | ~r1_lattice3('#skF_3', B_143, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | r1_lattice3('#skF_3', B_143, C_144) | ~m1_subset_1(C_144, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_251])).
% 3.94/1.77  tff(c_279, plain, (![B_147, C_148]: (r1_orders_2('#skF_3', '#skF_4', '#skF_1'('#skF_3', B_147, C_148)) | ~m1_subset_1('#skF_1'('#skF_3', B_147, C_148), u1_struct_0('#skF_3')) | ~r1_lattice3('#skF_3', B_147, '#skF_5') | r1_lattice3('#skF_3', B_147, C_148) | ~m1_subset_1(C_148, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_28, c_24, c_265])).
% 3.94/1.77  tff(c_283, plain, (![B_23, C_24]: (r1_orders_2('#skF_3', '#skF_4', '#skF_1'('#skF_3', B_23, C_24)) | ~r1_lattice3('#skF_3', B_23, '#skF_5') | r1_lattice3('#skF_3', B_23, C_24) | ~m1_subset_1(C_24, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_279])).
% 3.94/1.77  tff(c_287, plain, (![B_149, C_150]: (r1_orders_2('#skF_3', '#skF_4', '#skF_1'('#skF_3', B_149, C_150)) | ~r1_lattice3('#skF_3', B_149, '#skF_5') | r1_lattice3('#skF_3', B_149, C_150) | ~m1_subset_1(C_150, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_283])).
% 3.94/1.77  tff(c_6, plain, (![A_16, C_24, B_23]: (~r1_orders_2(A_16, C_24, '#skF_1'(A_16, B_23, C_24)) | r1_lattice3(A_16, B_23, C_24) | ~m1_subset_1(C_24, u1_struct_0(A_16)) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.94/1.77  tff(c_297, plain, (![B_149]: (~l1_orders_2('#skF_3') | ~r1_lattice3('#skF_3', B_149, '#skF_5') | r1_lattice3('#skF_3', B_149, '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_287, c_6])).
% 3.94/1.77  tff(c_310, plain, (![B_151]: (~r1_lattice3('#skF_3', B_151, '#skF_5') | r1_lattice3('#skF_3', B_151, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_297])).
% 3.94/1.77  tff(c_313, plain, (r1_lattice3('#skF_3', '#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_39, c_310])).
% 3.94/1.77  tff(c_317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_313])).
% 3.94/1.77  tff(c_318, plain, (r2_lattice3('#skF_3', '#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_36])).
% 3.94/1.77  tff(c_18, plain, (![A_28, B_35, C_36]: (m1_subset_1('#skF_2'(A_28, B_35, C_36), u1_struct_0(A_28)) | r2_lattice3(A_28, B_35, C_36) | ~m1_subset_1(C_36, u1_struct_0(A_28)) | ~l1_orders_2(A_28))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.94/1.77  tff(c_16, plain, (![A_28, B_35, C_36]: (r2_hidden('#skF_2'(A_28, B_35, C_36), B_35) | r2_lattice3(A_28, B_35, C_36) | ~m1_subset_1(C_36, u1_struct_0(A_28)) | ~l1_orders_2(A_28))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.94/1.77  tff(c_326, plain, (![A_170, D_171, C_172, B_173]: (r1_orders_2(A_170, D_171, C_172) | ~r2_hidden(D_171, B_173) | ~m1_subset_1(D_171, u1_struct_0(A_170)) | ~r2_lattice3(A_170, B_173, C_172) | ~m1_subset_1(C_172, u1_struct_0(A_170)) | ~l1_orders_2(A_170))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.94/1.77  tff(c_435, plain, (![B_211, A_209, C_213, A_210, C_212]: (r1_orders_2(A_209, '#skF_2'(A_210, B_211, C_213), C_212) | ~m1_subset_1('#skF_2'(A_210, B_211, C_213), u1_struct_0(A_209)) | ~r2_lattice3(A_209, B_211, C_212) | ~m1_subset_1(C_212, u1_struct_0(A_209)) | ~l1_orders_2(A_209) | r2_lattice3(A_210, B_211, C_213) | ~m1_subset_1(C_213, u1_struct_0(A_210)) | ~l1_orders_2(A_210))), inference(resolution, [status(thm)], [c_16, c_326])).
% 3.94/1.77  tff(c_439, plain, (![A_214, B_215, C_216, C_217]: (r1_orders_2(A_214, '#skF_2'(A_214, B_215, C_216), C_217) | ~r2_lattice3(A_214, B_215, C_217) | ~m1_subset_1(C_217, u1_struct_0(A_214)) | r2_lattice3(A_214, B_215, C_216) | ~m1_subset_1(C_216, u1_struct_0(A_214)) | ~l1_orders_2(A_214))), inference(resolution, [status(thm)], [c_18, c_435])).
% 3.94/1.77  tff(c_340, plain, (![A_178, B_179, D_180, C_181]: (r1_orders_2(A_178, B_179, D_180) | ~r1_orders_2(A_178, C_181, D_180) | ~r1_orders_2(A_178, B_179, C_181) | ~m1_subset_1(D_180, u1_struct_0(A_178)) | ~m1_subset_1(C_181, u1_struct_0(A_178)) | ~m1_subset_1(B_179, u1_struct_0(A_178)) | ~l1_orders_2(A_178) | ~v4_orders_2(A_178))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.94/1.77  tff(c_342, plain, (![B_179]: (r1_orders_2('#skF_3', B_179, '#skF_5') | ~r1_orders_2('#skF_3', B_179, '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(B_179, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v4_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_340])).
% 3.94/1.77  tff(c_346, plain, (![B_182]: (r1_orders_2('#skF_3', B_182, '#skF_5') | ~r1_orders_2('#skF_3', B_182, '#skF_4') | ~m1_subset_1(B_182, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_22, c_342])).
% 3.94/1.77  tff(c_350, plain, (![B_35, C_36]: (r1_orders_2('#skF_3', '#skF_2'('#skF_3', B_35, C_36), '#skF_5') | ~r1_orders_2('#skF_3', '#skF_2'('#skF_3', B_35, C_36), '#skF_4') | r2_lattice3('#skF_3', B_35, C_36) | ~m1_subset_1(C_36, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_346])).
% 3.94/1.77  tff(c_371, plain, (![B_183, C_184]: (r1_orders_2('#skF_3', '#skF_2'('#skF_3', B_183, C_184), '#skF_5') | ~r1_orders_2('#skF_3', '#skF_2'('#skF_3', B_183, C_184), '#skF_4') | r2_lattice3('#skF_3', B_183, C_184) | ~m1_subset_1(C_184, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_350])).
% 3.94/1.77  tff(c_14, plain, (![A_28, B_35, C_36]: (~r1_orders_2(A_28, '#skF_2'(A_28, B_35, C_36), C_36) | r2_lattice3(A_28, B_35, C_36) | ~m1_subset_1(C_36, u1_struct_0(A_28)) | ~l1_orders_2(A_28))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.94/1.77  tff(c_377, plain, (![B_183]: (~l1_orders_2('#skF_3') | ~r1_orders_2('#skF_3', '#skF_2'('#skF_3', B_183, '#skF_5'), '#skF_4') | r2_lattice3('#skF_3', B_183, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_371, c_14])).
% 3.94/1.77  tff(c_383, plain, (![B_183]: (~r1_orders_2('#skF_3', '#skF_2'('#skF_3', B_183, '#skF_5'), '#skF_4') | r2_lattice3('#skF_3', B_183, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26, c_377])).
% 3.94/1.77  tff(c_446, plain, (![B_215]: (~r2_lattice3('#skF_3', B_215, '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | r2_lattice3('#skF_3', B_215, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_439, c_383])).
% 3.94/1.77  tff(c_466, plain, (![B_218]: (~r2_lattice3('#skF_3', B_218, '#skF_4') | r2_lattice3('#skF_3', B_218, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_24, c_446])).
% 3.94/1.77  tff(c_34, plain, (~r2_lattice3('#skF_3', '#skF_6', '#skF_5') | r1_lattice3('#skF_3', '#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.94/1.77  tff(c_38, plain, (~r2_lattice3('#skF_3', '#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_34])).
% 3.94/1.77  tff(c_469, plain, (~r2_lattice3('#skF_3', '#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_466, c_38])).
% 3.94/1.77  tff(c_473, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_318, c_469])).
% 3.94/1.77  tff(c_474, plain, (r1_lattice3('#skF_3', '#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_34])).
% 3.94/1.77  tff(c_483, plain, (![A_237, C_238, D_239, B_240]: (r1_orders_2(A_237, C_238, D_239) | ~r2_hidden(D_239, B_240) | ~m1_subset_1(D_239, u1_struct_0(A_237)) | ~r1_lattice3(A_237, B_240, C_238) | ~m1_subset_1(C_238, u1_struct_0(A_237)) | ~l1_orders_2(A_237))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.94/1.77  tff(c_573, plain, (![B_267, A_266, C_264, A_265, C_268]: (r1_orders_2(A_265, C_268, '#skF_1'(A_266, B_267, C_264)) | ~m1_subset_1('#skF_1'(A_266, B_267, C_264), u1_struct_0(A_265)) | ~r1_lattice3(A_265, B_267, C_268) | ~m1_subset_1(C_268, u1_struct_0(A_265)) | ~l1_orders_2(A_265) | r1_lattice3(A_266, B_267, C_264) | ~m1_subset_1(C_264, u1_struct_0(A_266)) | ~l1_orders_2(A_266))), inference(resolution, [status(thm)], [c_8, c_483])).
% 3.94/1.77  tff(c_578, plain, (![A_270, C_271, B_272, C_273]: (r1_orders_2(A_270, C_271, '#skF_1'(A_270, B_272, C_273)) | ~r1_lattice3(A_270, B_272, C_271) | ~m1_subset_1(C_271, u1_struct_0(A_270)) | r1_lattice3(A_270, B_272, C_273) | ~m1_subset_1(C_273, u1_struct_0(A_270)) | ~l1_orders_2(A_270))), inference(resolution, [status(thm)], [c_10, c_573])).
% 3.94/1.77  tff(c_978, plain, (![B_380, C_379, C_378, A_381, B_377]: (r1_orders_2(A_381, B_380, '#skF_1'(A_381, B_377, C_379)) | ~r1_orders_2(A_381, B_380, C_378) | ~m1_subset_1('#skF_1'(A_381, B_377, C_379), u1_struct_0(A_381)) | ~m1_subset_1(B_380, u1_struct_0(A_381)) | ~v4_orders_2(A_381) | ~r1_lattice3(A_381, B_377, C_378) | ~m1_subset_1(C_378, u1_struct_0(A_381)) | r1_lattice3(A_381, B_377, C_379) | ~m1_subset_1(C_379, u1_struct_0(A_381)) | ~l1_orders_2(A_381))), inference(resolution, [status(thm)], [c_578, c_2])).
% 3.94/1.77  tff(c_996, plain, (![B_377, C_379]: (r1_orders_2('#skF_3', '#skF_4', '#skF_1'('#skF_3', B_377, C_379)) | ~m1_subset_1('#skF_1'('#skF_3', B_377, C_379), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v4_orders_2('#skF_3') | ~r1_lattice3('#skF_3', B_377, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | r1_lattice3('#skF_3', B_377, C_379) | ~m1_subset_1(C_379, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_978])).
% 3.94/1.77  tff(c_1038, plain, (![B_386, C_387]: (r1_orders_2('#skF_3', '#skF_4', '#skF_1'('#skF_3', B_386, C_387)) | ~m1_subset_1('#skF_1'('#skF_3', B_386, C_387), u1_struct_0('#skF_3')) | ~r1_lattice3('#skF_3', B_386, '#skF_5') | r1_lattice3('#skF_3', B_386, C_387) | ~m1_subset_1(C_387, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_28, c_24, c_996])).
% 3.94/1.77  tff(c_1042, plain, (![B_23, C_24]: (r1_orders_2('#skF_3', '#skF_4', '#skF_1'('#skF_3', B_23, C_24)) | ~r1_lattice3('#skF_3', B_23, '#skF_5') | r1_lattice3('#skF_3', B_23, C_24) | ~m1_subset_1(C_24, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_1038])).
% 3.94/1.77  tff(c_1046, plain, (![B_388, C_389]: (r1_orders_2('#skF_3', '#skF_4', '#skF_1'('#skF_3', B_388, C_389)) | ~r1_lattice3('#skF_3', B_388, '#skF_5') | r1_lattice3('#skF_3', B_388, C_389) | ~m1_subset_1(C_389, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1042])).
% 3.94/1.77  tff(c_1060, plain, (![B_388]: (~l1_orders_2('#skF_3') | ~r1_lattice3('#skF_3', B_388, '#skF_5') | r1_lattice3('#skF_3', B_388, '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1046, c_6])).
% 3.94/1.77  tff(c_1079, plain, (![B_390]: (~r1_lattice3('#skF_3', B_390, '#skF_5') | r1_lattice3('#skF_3', B_390, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_1060])).
% 3.94/1.77  tff(c_1085, plain, (r1_lattice3('#skF_3', '#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_474, c_1079])).
% 3.94/1.77  tff(c_1091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_1085])).
% 3.94/1.77  tff(c_1093, plain, (r1_lattice3('#skF_3', '#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_30])).
% 3.94/1.77  tff(c_32, plain, (r2_lattice3('#skF_3', '#skF_6', '#skF_4') | ~r1_lattice3('#skF_3', '#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.94/1.77  tff(c_1096, plain, (r2_lattice3('#skF_3', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1093, c_32])).
% 3.94/1.77  tff(c_1110, plain, (![A_413, D_414, C_415, B_416]: (r1_orders_2(A_413, D_414, C_415) | ~r2_hidden(D_414, B_416) | ~m1_subset_1(D_414, u1_struct_0(A_413)) | ~r2_lattice3(A_413, B_416, C_415) | ~m1_subset_1(C_415, u1_struct_0(A_413)) | ~l1_orders_2(A_413))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.94/1.77  tff(c_1168, plain, (![C_427, C_431, A_429, A_428, B_430]: (r1_orders_2(A_428, '#skF_2'(A_429, B_430, C_431), C_427) | ~m1_subset_1('#skF_2'(A_429, B_430, C_431), u1_struct_0(A_428)) | ~r2_lattice3(A_428, B_430, C_427) | ~m1_subset_1(C_427, u1_struct_0(A_428)) | ~l1_orders_2(A_428) | r2_lattice3(A_429, B_430, C_431) | ~m1_subset_1(C_431, u1_struct_0(A_429)) | ~l1_orders_2(A_429))), inference(resolution, [status(thm)], [c_16, c_1110])).
% 3.94/1.77  tff(c_1172, plain, (![A_432, B_433, C_434, C_435]: (r1_orders_2(A_432, '#skF_2'(A_432, B_433, C_434), C_435) | ~r2_lattice3(A_432, B_433, C_435) | ~m1_subset_1(C_435, u1_struct_0(A_432)) | r2_lattice3(A_432, B_433, C_434) | ~m1_subset_1(C_434, u1_struct_0(A_432)) | ~l1_orders_2(A_432))), inference(resolution, [status(thm)], [c_18, c_1168])).
% 3.94/1.77  tff(c_1117, plain, (![A_417, B_418, D_419, C_420]: (r1_orders_2(A_417, B_418, D_419) | ~r1_orders_2(A_417, C_420, D_419) | ~r1_orders_2(A_417, B_418, C_420) | ~m1_subset_1(D_419, u1_struct_0(A_417)) | ~m1_subset_1(C_420, u1_struct_0(A_417)) | ~m1_subset_1(B_418, u1_struct_0(A_417)) | ~l1_orders_2(A_417) | ~v4_orders_2(A_417))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.94/1.77  tff(c_1119, plain, (![B_418]: (r1_orders_2('#skF_3', B_418, '#skF_5') | ~r1_orders_2('#skF_3', B_418, '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(B_418, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v4_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_1117])).
% 3.94/1.77  tff(c_1123, plain, (![B_421]: (r1_orders_2('#skF_3', B_421, '#skF_5') | ~r1_orders_2('#skF_3', B_421, '#skF_4') | ~m1_subset_1(B_421, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_22, c_1119])).
% 3.94/1.77  tff(c_1127, plain, (![B_35, C_36]: (r1_orders_2('#skF_3', '#skF_2'('#skF_3', B_35, C_36), '#skF_5') | ~r1_orders_2('#skF_3', '#skF_2'('#skF_3', B_35, C_36), '#skF_4') | r2_lattice3('#skF_3', B_35, C_36) | ~m1_subset_1(C_36, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_1123])).
% 3.94/1.77  tff(c_1154, plain, (![B_424, C_425]: (r1_orders_2('#skF_3', '#skF_2'('#skF_3', B_424, C_425), '#skF_5') | ~r1_orders_2('#skF_3', '#skF_2'('#skF_3', B_424, C_425), '#skF_4') | r2_lattice3('#skF_3', B_424, C_425) | ~m1_subset_1(C_425, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1127])).
% 3.94/1.77  tff(c_1160, plain, (![B_424]: (~l1_orders_2('#skF_3') | ~r1_orders_2('#skF_3', '#skF_2'('#skF_3', B_424, '#skF_5'), '#skF_4') | r2_lattice3('#skF_3', B_424, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1154, c_14])).
% 3.94/1.77  tff(c_1166, plain, (![B_424]: (~r1_orders_2('#skF_3', '#skF_2'('#skF_3', B_424, '#skF_5'), '#skF_4') | r2_lattice3('#skF_3', B_424, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26, c_1160])).
% 3.94/1.77  tff(c_1176, plain, (![B_433]: (~r2_lattice3('#skF_3', B_433, '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | r2_lattice3('#skF_3', B_433, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_1172, c_1166])).
% 3.94/1.77  tff(c_1197, plain, (![B_441]: (~r2_lattice3('#skF_3', B_441, '#skF_4') | r2_lattice3('#skF_3', B_441, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_24, c_1176])).
% 3.94/1.77  tff(c_1092, plain, (~r2_lattice3('#skF_3', '#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_30])).
% 3.94/1.77  tff(c_1200, plain, (~r2_lattice3('#skF_3', '#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_1197, c_1092])).
% 3.94/1.77  tff(c_1204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1096, c_1200])).
% 3.94/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/1.77  
% 3.94/1.77  Inference rules
% 3.94/1.77  ----------------------
% 3.94/1.77  #Ref     : 0
% 3.94/1.77  #Sup     : 214
% 3.94/1.77  #Fact    : 0
% 3.94/1.77  #Define  : 0
% 3.94/1.77  #Split   : 12
% 3.94/1.77  #Chain   : 0
% 3.94/1.77  #Close   : 0
% 3.94/1.77  
% 3.94/1.77  Ordering : KBO
% 3.94/1.77  
% 3.94/1.77  Simplification rules
% 3.94/1.77  ----------------------
% 3.94/1.77  #Subsume      : 33
% 3.94/1.77  #Demod        : 240
% 3.94/1.77  #Tautology    : 18
% 3.94/1.77  #SimpNegUnit  : 2
% 3.94/1.77  #BackRed      : 0
% 3.94/1.77  
% 3.94/1.77  #Partial instantiations: 0
% 3.94/1.77  #Strategies tried      : 1
% 3.94/1.77  
% 3.94/1.77  Timing (in seconds)
% 3.94/1.77  ----------------------
% 3.94/1.77  Preprocessing        : 0.32
% 3.94/1.77  Parsing              : 0.18
% 3.94/1.77  CNF conversion       : 0.03
% 3.94/1.77  Main loop            : 0.60
% 3.94/1.77  Inferencing          : 0.25
% 3.94/1.77  Reduction            : 0.15
% 3.94/1.77  Demodulation         : 0.10
% 3.94/1.77  BG Simplification    : 0.03
% 3.94/1.77  Subsumption          : 0.13
% 3.94/1.77  Abstraction          : 0.02
% 3.94/1.77  MUC search           : 0.00
% 3.94/1.77  Cooper               : 0.00
% 3.94/1.77  Total                : 0.97
% 3.94/1.77  Index Insertion      : 0.00
% 3.94/1.77  Index Deletion       : 0.00
% 3.94/1.77  Index Matching       : 0.00
% 3.94/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
