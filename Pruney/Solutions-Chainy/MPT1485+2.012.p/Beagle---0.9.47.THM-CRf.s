%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:42 EST 2020

% Result     : Theorem 34.78s
% Output     : CNFRefutation 35.12s
% Verified   : 
% Statistics : Number of formulae       :  166 (42127 expanded)
%              Number of leaves         :   33 (15590 expanded)
%              Depth                    :   43
%              Number of atoms          :  587 (206350 expanded)
%              Number of equality atoms :   77 (18483 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k13_lattice3,type,(
    k13_lattice3: ( $i * $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k10_lattice3,type,(
    k10_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(f_179,negated_conjecture,(
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

tff(f_70,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_lattice3)).

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

tff(f_136,axiom,(
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

tff(f_148,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_103,axiom,(
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

tff(f_160,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(c_64,plain,(
    l1_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_68,plain,(
    v1_lattice3('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_62,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_60,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_24,plain,(
    ! [A_5,B_36,C_44] :
      ( m1_subset_1('#skF_1'(A_5,B_36,C_44),u1_struct_0(A_5))
      | ~ m1_subset_1(C_44,u1_struct_0(A_5))
      | ~ m1_subset_1(B_36,u1_struct_0(A_5))
      | ~ v1_lattice3(A_5)
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_72,plain,(
    v3_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_76,plain,(
    ! [A_167,B_168] :
      ( r1_orders_2(A_167,B_168,B_168)
      | ~ m1_subset_1(B_168,u1_struct_0(A_167))
      | ~ l1_orders_2(A_167)
      | ~ v3_orders_2(A_167)
      | v2_struct_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_82,plain,
    ( r1_orders_2('#skF_7','#skF_9','#skF_9')
    | ~ l1_orders_2('#skF_7')
    | ~ v3_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_76])).

tff(c_89,plain,
    ( r1_orders_2('#skF_7','#skF_9','#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_64,c_82])).

tff(c_93,plain,(
    v2_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_4,plain,(
    ! [A_4] :
      ( ~ v2_struct_0(A_4)
      | ~ v1_lattice3(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_96,plain,
    ( ~ v1_lattice3('#skF_7')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_93,c_4])).

tff(c_100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_96])).

tff(c_102,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_70,plain,(
    v5_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_66,plain,(
    v2_lattice3('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_22,plain,(
    ! [A_5,B_36,C_44] :
      ( r1_orders_2(A_5,B_36,'#skF_1'(A_5,B_36,C_44))
      | ~ m1_subset_1(C_44,u1_struct_0(A_5))
      | ~ m1_subset_1(B_36,u1_struct_0(A_5))
      | ~ v1_lattice3(A_5)
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_84,plain,
    ( r1_orders_2('#skF_7','#skF_8','#skF_8')
    | ~ l1_orders_2('#skF_7')
    | ~ v3_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_76])).

tff(c_92,plain,
    ( r1_orders_2('#skF_7','#skF_8','#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_64,c_84])).

tff(c_104,plain,(
    r1_orders_2('#skF_7','#skF_8','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_92])).

tff(c_2600,plain,(
    ! [A_366,B_367,C_368,D_369] :
      ( r1_orders_2(A_366,'#skF_6'(A_366,B_367,C_368,D_369),C_368)
      | k11_lattice3(A_366,B_367,C_368) = D_369
      | ~ r1_orders_2(A_366,D_369,C_368)
      | ~ r1_orders_2(A_366,D_369,B_367)
      | ~ m1_subset_1(D_369,u1_struct_0(A_366))
      | ~ m1_subset_1(C_368,u1_struct_0(A_366))
      | ~ m1_subset_1(B_367,u1_struct_0(A_366))
      | ~ l1_orders_2(A_366)
      | ~ v2_lattice3(A_366)
      | ~ v5_orders_2(A_366)
      | v2_struct_0(A_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_40,plain,(
    ! [A_108,B_132,C_144,D_150] :
      ( ~ r1_orders_2(A_108,'#skF_6'(A_108,B_132,C_144,D_150),D_150)
      | k11_lattice3(A_108,B_132,C_144) = D_150
      | ~ r1_orders_2(A_108,D_150,C_144)
      | ~ r1_orders_2(A_108,D_150,B_132)
      | ~ m1_subset_1(D_150,u1_struct_0(A_108))
      | ~ m1_subset_1(C_144,u1_struct_0(A_108))
      | ~ m1_subset_1(B_132,u1_struct_0(A_108))
      | ~ l1_orders_2(A_108)
      | ~ v2_lattice3(A_108)
      | ~ v5_orders_2(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3241,plain,(
    ! [A_383,B_384,C_385] :
      ( k11_lattice3(A_383,B_384,C_385) = C_385
      | ~ r1_orders_2(A_383,C_385,C_385)
      | ~ r1_orders_2(A_383,C_385,B_384)
      | ~ m1_subset_1(C_385,u1_struct_0(A_383))
      | ~ m1_subset_1(B_384,u1_struct_0(A_383))
      | ~ l1_orders_2(A_383)
      | ~ v2_lattice3(A_383)
      | ~ v5_orders_2(A_383)
      | v2_struct_0(A_383) ) ),
    inference(resolution,[status(thm)],[c_2600,c_40])).

tff(c_3256,plain,(
    ! [B_384] :
      ( k11_lattice3('#skF_7',B_384,'#skF_8') = '#skF_8'
      | ~ r1_orders_2('#skF_7','#skF_8',B_384)
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_384,u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ v2_lattice3('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_104,c_3241])).

tff(c_3270,plain,(
    ! [B_384] :
      ( k11_lattice3('#skF_7',B_384,'#skF_8') = '#skF_8'
      | ~ r1_orders_2('#skF_7','#skF_8',B_384)
      | ~ m1_subset_1(B_384,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_62,c_3256])).

tff(c_3276,plain,(
    ! [B_386] :
      ( k11_lattice3('#skF_7',B_386,'#skF_8') = '#skF_8'
      | ~ r1_orders_2('#skF_7','#skF_8',B_386)
      | ~ m1_subset_1(B_386,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_3270])).

tff(c_3295,plain,(
    ! [B_36,C_44] :
      ( k11_lattice3('#skF_7','#skF_1'('#skF_7',B_36,C_44),'#skF_8') = '#skF_8'
      | ~ r1_orders_2('#skF_7','#skF_8','#skF_1'('#skF_7',B_36,C_44))
      | ~ m1_subset_1(C_44,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_36,u1_struct_0('#skF_7'))
      | ~ v1_lattice3('#skF_7')
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_24,c_3276])).

tff(c_3708,plain,(
    ! [B_395,C_396] :
      ( k11_lattice3('#skF_7','#skF_1'('#skF_7',B_395,C_396),'#skF_8') = '#skF_8'
      | ~ r1_orders_2('#skF_7','#skF_8','#skF_1'('#skF_7',B_395,C_396))
      | ~ m1_subset_1(C_396,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_395,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_3295])).

tff(c_3719,plain,(
    ! [C_44] :
      ( k11_lattice3('#skF_7','#skF_1'('#skF_7','#skF_8',C_44),'#skF_8') = '#skF_8'
      | ~ m1_subset_1(C_44,u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
      | ~ v1_lattice3('#skF_7')
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_22,c_3708])).

tff(c_3842,plain,(
    ! [C_402] :
      ( k11_lattice3('#skF_7','#skF_1'('#skF_7','#skF_8',C_402),'#skF_8') = '#skF_8'
      | ~ m1_subset_1(C_402,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_62,c_3719])).

tff(c_3893,plain,(
    k11_lattice3('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_60,c_3842])).

tff(c_52,plain,(
    ! [A_108,B_132,C_144] :
      ( r1_orders_2(A_108,k11_lattice3(A_108,B_132,C_144),B_132)
      | ~ m1_subset_1(k11_lattice3(A_108,B_132,C_144),u1_struct_0(A_108))
      | ~ m1_subset_1(C_144,u1_struct_0(A_108))
      | ~ m1_subset_1(B_132,u1_struct_0(A_108))
      | ~ l1_orders_2(A_108)
      | ~ v2_lattice3(A_108)
      | ~ v5_orders_2(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3901,plain,
    ( r1_orders_2('#skF_7',k11_lattice3('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_8'),'#skF_1'('#skF_7','#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7')
    | ~ v2_lattice3('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3893,c_52])).

tff(c_3910,plain,
    ( r1_orders_2('#skF_7','#skF_8','#skF_1'('#skF_7','#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_62,c_62,c_3893,c_3901])).

tff(c_3911,plain,
    ( r1_orders_2('#skF_7','#skF_8','#skF_1'('#skF_7','#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_3910])).

tff(c_4245,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_3911])).

tff(c_4248,plain,
    ( ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v1_lattice3('#skF_7')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_4245])).

tff(c_4252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_62,c_60,c_4248])).

tff(c_4254,plain,(
    m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_3911])).

tff(c_4253,plain,(
    r1_orders_2('#skF_7','#skF_8','#skF_1'('#skF_7','#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_3911])).

tff(c_1818,plain,(
    ! [A_327,B_328,C_329,D_330] :
      ( r1_orders_2(A_327,'#skF_6'(A_327,B_328,C_329,D_330),B_328)
      | k11_lattice3(A_327,B_328,C_329) = D_330
      | ~ r1_orders_2(A_327,D_330,C_329)
      | ~ r1_orders_2(A_327,D_330,B_328)
      | ~ m1_subset_1(D_330,u1_struct_0(A_327))
      | ~ m1_subset_1(C_329,u1_struct_0(A_327))
      | ~ m1_subset_1(B_328,u1_struct_0(A_327))
      | ~ l1_orders_2(A_327)
      | ~ v2_lattice3(A_327)
      | ~ v5_orders_2(A_327)
      | v2_struct_0(A_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1826,plain,(
    ! [A_327,B_328,C_329] :
      ( k11_lattice3(A_327,B_328,C_329) = B_328
      | ~ r1_orders_2(A_327,B_328,C_329)
      | ~ r1_orders_2(A_327,B_328,B_328)
      | ~ m1_subset_1(C_329,u1_struct_0(A_327))
      | ~ m1_subset_1(B_328,u1_struct_0(A_327))
      | ~ l1_orders_2(A_327)
      | ~ v2_lattice3(A_327)
      | ~ v5_orders_2(A_327)
      | v2_struct_0(A_327) ) ),
    inference(resolution,[status(thm)],[c_1818,c_40])).

tff(c_4259,plain,
    ( k11_lattice3('#skF_7','#skF_8','#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_8'
    | ~ r1_orders_2('#skF_7','#skF_8','#skF_8')
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7')
    | ~ v2_lattice3('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4253,c_1826])).

tff(c_4267,plain,
    ( k11_lattice3('#skF_7','#skF_8','#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_8'
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_62,c_104,c_4259])).

tff(c_4268,plain,
    ( k11_lattice3('#skF_7','#skF_8','#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_8'
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_4267])).

tff(c_5268,plain,(
    k11_lattice3('#skF_7','#skF_8','#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4254,c_4268])).

tff(c_166,plain,(
    ! [A_184,B_185,C_186] :
      ( k12_lattice3(A_184,B_185,C_186) = k11_lattice3(A_184,B_185,C_186)
      | ~ m1_subset_1(C_186,u1_struct_0(A_184))
      | ~ m1_subset_1(B_185,u1_struct_0(A_184))
      | ~ l1_orders_2(A_184)
      | ~ v2_lattice3(A_184)
      | ~ v5_orders_2(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1648,plain,(
    ! [A_319,B_320,B_321,C_322] :
      ( k12_lattice3(A_319,B_320,'#skF_1'(A_319,B_321,C_322)) = k11_lattice3(A_319,B_320,'#skF_1'(A_319,B_321,C_322))
      | ~ m1_subset_1(B_320,u1_struct_0(A_319))
      | ~ v2_lattice3(A_319)
      | ~ v5_orders_2(A_319)
      | ~ m1_subset_1(C_322,u1_struct_0(A_319))
      | ~ m1_subset_1(B_321,u1_struct_0(A_319))
      | ~ v1_lattice3(A_319)
      | ~ l1_orders_2(A_319) ) ),
    inference(resolution,[status(thm)],[c_24,c_166])).

tff(c_1662,plain,(
    ! [B_321,C_322] :
      ( k12_lattice3('#skF_7','#skF_8','#skF_1'('#skF_7',B_321,C_322)) = k11_lattice3('#skF_7','#skF_8','#skF_1'('#skF_7',B_321,C_322))
      | ~ v2_lattice3('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | ~ m1_subset_1(C_322,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_321,u1_struct_0('#skF_7'))
      | ~ v1_lattice3('#skF_7')
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_62,c_1648])).

tff(c_1827,plain,(
    ! [B_331,C_332] :
      ( k12_lattice3('#skF_7','#skF_8','#skF_1'('#skF_7',B_331,C_332)) = k11_lattice3('#skF_7','#skF_8','#skF_1'('#skF_7',B_331,C_332))
      | ~ m1_subset_1(C_332,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_331,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_70,c_66,c_1662])).

tff(c_1865,plain,(
    ! [B_333] :
      ( k12_lattice3('#skF_7','#skF_8','#skF_1'('#skF_7',B_333,'#skF_9')) = k11_lattice3('#skF_7','#skF_8','#skF_1'('#skF_7',B_333,'#skF_9'))
      | ~ m1_subset_1(B_333,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_60,c_1827])).

tff(c_1909,plain,(
    k12_lattice3('#skF_7','#skF_8','#skF_1'('#skF_7','#skF_8','#skF_9')) = k11_lattice3('#skF_7','#skF_8','#skF_1'('#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_62,c_1865])).

tff(c_5269,plain,(
    k12_lattice3('#skF_7','#skF_8','#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5268,c_1909])).

tff(c_20,plain,(
    ! [A_5,C_44,B_36] :
      ( r1_orders_2(A_5,C_44,'#skF_1'(A_5,B_36,C_44))
      | ~ m1_subset_1(C_44,u1_struct_0(A_5))
      | ~ m1_subset_1(B_36,u1_struct_0(A_5))
      | ~ v1_lattice3(A_5)
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_101,plain,(
    r1_orders_2('#skF_7','#skF_9','#skF_9') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_3258,plain,(
    ! [B_384] :
      ( k11_lattice3('#skF_7',B_384,'#skF_9') = '#skF_9'
      | ~ r1_orders_2('#skF_7','#skF_9',B_384)
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_384,u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ v2_lattice3('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_101,c_3241])).

tff(c_3274,plain,(
    ! [B_384] :
      ( k11_lattice3('#skF_7',B_384,'#skF_9') = '#skF_9'
      | ~ r1_orders_2('#skF_7','#skF_9',B_384)
      | ~ m1_subset_1(B_384,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_3258])).

tff(c_3275,plain,(
    ! [B_384] :
      ( k11_lattice3('#skF_7',B_384,'#skF_9') = '#skF_9'
      | ~ r1_orders_2('#skF_7','#skF_9',B_384)
      | ~ m1_subset_1(B_384,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_3274])).

tff(c_4399,plain,
    ( k11_lattice3('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9'
    | ~ r1_orders_2('#skF_7','#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_4254,c_3275])).

tff(c_5045,plain,(
    ~ r1_orders_2('#skF_7','#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_4399])).

tff(c_5097,plain,
    ( ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v1_lattice3('#skF_7')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_5045])).

tff(c_5101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_62,c_60,c_5097])).

tff(c_5103,plain,(
    r1_orders_2('#skF_7','#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_4399])).

tff(c_32,plain,(
    ! [A_62,B_86,C_98,D_104] :
      ( m1_subset_1('#skF_5'(A_62,B_86,C_98,D_104),u1_struct_0(A_62))
      | k10_lattice3(A_62,B_86,C_98) = D_104
      | ~ r1_orders_2(A_62,C_98,D_104)
      | ~ r1_orders_2(A_62,B_86,D_104)
      | ~ m1_subset_1(D_104,u1_struct_0(A_62))
      | ~ m1_subset_1(C_98,u1_struct_0(A_62))
      | ~ m1_subset_1(B_86,u1_struct_0(A_62))
      | ~ l1_orders_2(A_62)
      | ~ v1_lattice3(A_62)
      | ~ v5_orders_2(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3715,plain,(
    ! [B_36] :
      ( k11_lattice3('#skF_7','#skF_1'('#skF_7',B_36,'#skF_8'),'#skF_8') = '#skF_8'
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_36,u1_struct_0('#skF_7'))
      | ~ v1_lattice3('#skF_7')
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_20,c_3708])).

tff(c_3728,plain,(
    ! [B_397] :
      ( k11_lattice3('#skF_7','#skF_1'('#skF_7',B_397,'#skF_8'),'#skF_8') = '#skF_8'
      | ~ m1_subset_1(B_397,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_62,c_3715])).

tff(c_3779,plain,(
    k11_lattice3('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_60,c_3728])).

tff(c_3786,plain,
    ( r1_orders_2('#skF_7',k11_lattice3('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_8'),'#skF_1'('#skF_7','#skF_9','#skF_8'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_9','#skF_8'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7')
    | ~ v2_lattice3('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3779,c_52])).

tff(c_3795,plain,
    ( r1_orders_2('#skF_7','#skF_8','#skF_1'('#skF_7','#skF_9','#skF_8'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_9','#skF_8'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_62,c_62,c_3779,c_3786])).

tff(c_3796,plain,
    ( r1_orders_2('#skF_7','#skF_8','#skF_1'('#skF_7','#skF_9','#skF_8'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_9','#skF_8'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_3795])).

tff(c_3920,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7','#skF_9','#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_3796])).

tff(c_3923,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ v1_lattice3('#skF_7')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_3920])).

tff(c_3927,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_60,c_62,c_3923])).

tff(c_3928,plain,(
    r1_orders_2('#skF_7','#skF_8','#skF_1'('#skF_7','#skF_9','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_3796])).

tff(c_3929,plain,(
    m1_subset_1('#skF_1'('#skF_7','#skF_9','#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_3796])).

tff(c_4068,plain,
    ( k11_lattice3('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_9') = '#skF_9'
    | ~ r1_orders_2('#skF_7','#skF_9','#skF_1'('#skF_7','#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_3929,c_3275])).

tff(c_5654,plain,(
    ~ r1_orders_2('#skF_7','#skF_9','#skF_1'('#skF_7','#skF_9','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_4068])).

tff(c_5662,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ v1_lattice3('#skF_7')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_22,c_5654])).

tff(c_5666,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_60,c_62,c_5662])).

tff(c_5668,plain,(
    r1_orders_2('#skF_7','#skF_9','#skF_1'('#skF_7','#skF_9','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_4068])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( r1_orders_2(A_1,B_3,B_3)
      | ~ m1_subset_1(B_3,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4062,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_1'('#skF_7','#skF_9','#skF_8'))
    | ~ l1_orders_2('#skF_7')
    | ~ v3_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_3929,c_2])).

tff(c_4128,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_1'('#skF_7','#skF_9','#skF_8'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_64,c_4062])).

tff(c_4129,plain,(
    r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_1'('#skF_7','#skF_9','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_4128])).

tff(c_18,plain,(
    ! [A_5,B_36,C_44,E_49] :
      ( r1_orders_2(A_5,'#skF_1'(A_5,B_36,C_44),E_49)
      | ~ r1_orders_2(A_5,C_44,E_49)
      | ~ r1_orders_2(A_5,B_36,E_49)
      | ~ m1_subset_1(E_49,u1_struct_0(A_5))
      | ~ m1_subset_1(C_44,u1_struct_0(A_5))
      | ~ m1_subset_1(B_36,u1_struct_0(A_5))
      | ~ v1_lattice3(A_5)
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2611,plain,(
    ! [A_366,B_367,C_368] :
      ( k11_lattice3(A_366,B_367,C_368) = C_368
      | ~ r1_orders_2(A_366,C_368,C_368)
      | ~ r1_orders_2(A_366,C_368,B_367)
      | ~ m1_subset_1(C_368,u1_struct_0(A_366))
      | ~ m1_subset_1(B_367,u1_struct_0(A_366))
      | ~ l1_orders_2(A_366)
      | ~ v2_lattice3(A_366)
      | ~ v5_orders_2(A_366)
      | v2_struct_0(A_366) ) ),
    inference(resolution,[status(thm)],[c_2600,c_40])).

tff(c_4168,plain,(
    ! [B_367] :
      ( k11_lattice3('#skF_7',B_367,'#skF_1'('#skF_7','#skF_9','#skF_8')) = '#skF_1'('#skF_7','#skF_9','#skF_8')
      | ~ r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),B_367)
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_9','#skF_8'),u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_367,u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ v2_lattice3('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4129,c_2611])).

tff(c_4177,plain,(
    ! [B_367] :
      ( k11_lattice3('#skF_7',B_367,'#skF_1'('#skF_7','#skF_9','#skF_8')) = '#skF_1'('#skF_7','#skF_9','#skF_8')
      | ~ r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),B_367)
      | ~ m1_subset_1(B_367,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_3929,c_4168])).

tff(c_10444,plain,(
    ! [B_520] :
      ( k11_lattice3('#skF_7',B_520,'#skF_1'('#skF_7','#skF_9','#skF_8')) = '#skF_1'('#skF_7','#skF_9','#skF_8')
      | ~ r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),B_520)
      | ~ m1_subset_1(B_520,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_4177])).

tff(c_10465,plain,(
    ! [E_49] :
      ( k11_lattice3('#skF_7',E_49,'#skF_1'('#skF_7','#skF_9','#skF_8')) = '#skF_1'('#skF_7','#skF_9','#skF_8')
      | ~ r1_orders_2('#skF_7','#skF_8',E_49)
      | ~ r1_orders_2('#skF_7','#skF_9',E_49)
      | ~ m1_subset_1(E_49,u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
      | ~ v1_lattice3('#skF_7')
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_18,c_10444])).

tff(c_17640,plain,(
    ! [E_634] :
      ( k11_lattice3('#skF_7',E_634,'#skF_1'('#skF_7','#skF_9','#skF_8')) = '#skF_1'('#skF_7','#skF_9','#skF_8')
      | ~ r1_orders_2('#skF_7','#skF_8',E_634)
      | ~ r1_orders_2('#skF_7','#skF_9',E_634)
      | ~ m1_subset_1(E_634,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_60,c_62,c_10465])).

tff(c_17667,plain,
    ( k11_lattice3('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_1'('#skF_7','#skF_9','#skF_8')) = '#skF_1'('#skF_7','#skF_9','#skF_8')
    | ~ r1_orders_2('#skF_7','#skF_8','#skF_1'('#skF_7','#skF_8','#skF_9'))
    | ~ r1_orders_2('#skF_7','#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_4254,c_17640])).

tff(c_17727,plain,(
    k11_lattice3('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_1'('#skF_7','#skF_9','#skF_8')) = '#skF_1'('#skF_7','#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5103,c_4253,c_17667])).

tff(c_17762,plain,
    ( r1_orders_2('#skF_7',k11_lattice3('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_1'('#skF_7','#skF_9','#skF_8')),'#skF_1'('#skF_7','#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_9','#skF_8'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_9','#skF_8'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7')
    | ~ v2_lattice3('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_17727,c_52])).

tff(c_17771,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_1'('#skF_7','#skF_8','#skF_9'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_4254,c_3929,c_3929,c_17727,c_17762])).

tff(c_17772,plain,(
    r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_1'('#skF_7','#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_17771])).

tff(c_17788,plain,
    ( k11_lattice3('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_1'('#skF_7','#skF_9','#skF_8')
    | ~ r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_1'('#skF_7','#skF_9','#skF_8'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_9','#skF_8'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7')
    | ~ v2_lattice3('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_17772,c_1826])).

tff(c_17807,plain,
    ( k11_lattice3('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_1'('#skF_7','#skF_9','#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_3929,c_4254,c_4129,c_17788])).

tff(c_17808,plain,(
    k11_lattice3('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_1'('#skF_7','#skF_9','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_17807])).

tff(c_4389,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_1'('#skF_7','#skF_8','#skF_9'))
    | ~ l1_orders_2('#skF_7')
    | ~ v3_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4254,c_2])).

tff(c_4459,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_1'('#skF_7','#skF_8','#skF_9'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_64,c_4389])).

tff(c_4460,plain,(
    r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_1'('#skF_7','#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_4459])).

tff(c_4462,plain,(
    ! [B_367] :
      ( k11_lattice3('#skF_7',B_367,'#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_1'('#skF_7','#skF_8','#skF_9')
      | ~ r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),B_367)
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_367,u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ v2_lattice3('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4460,c_2611])).

tff(c_4471,plain,(
    ! [B_367] :
      ( k11_lattice3('#skF_7',B_367,'#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_1'('#skF_7','#skF_8','#skF_9')
      | ~ r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),B_367)
      | ~ m1_subset_1(B_367,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_4254,c_4462])).

tff(c_10099,plain,(
    ! [B_513] :
      ( k11_lattice3('#skF_7',B_513,'#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_1'('#skF_7','#skF_8','#skF_9')
      | ~ r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),B_513)
      | ~ m1_subset_1(B_513,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_4471])).

tff(c_10120,plain,(
    ! [E_49] :
      ( k11_lattice3('#skF_7',E_49,'#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_1'('#skF_7','#skF_8','#skF_9')
      | ~ r1_orders_2('#skF_7','#skF_9',E_49)
      | ~ r1_orders_2('#skF_7','#skF_8',E_49)
      | ~ m1_subset_1(E_49,u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
      | ~ v1_lattice3('#skF_7')
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_18,c_10099])).

tff(c_18028,plain,(
    ! [E_640] :
      ( k11_lattice3('#skF_7',E_640,'#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_1'('#skF_7','#skF_8','#skF_9')
      | ~ r1_orders_2('#skF_7','#skF_9',E_640)
      | ~ r1_orders_2('#skF_7','#skF_8',E_640)
      | ~ m1_subset_1(E_640,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_62,c_60,c_10120])).

tff(c_18058,plain,
    ( k11_lattice3('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_1'('#skF_7','#skF_8','#skF_9')
    | ~ r1_orders_2('#skF_7','#skF_9','#skF_1'('#skF_7','#skF_9','#skF_8'))
    | ~ r1_orders_2('#skF_7','#skF_8','#skF_1'('#skF_7','#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_3929,c_18028])).

tff(c_18118,plain,(
    '#skF_1'('#skF_7','#skF_9','#skF_8') = '#skF_1'('#skF_7','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3928,c_5668,c_17808,c_18058])).

tff(c_28,plain,(
    ! [A_62,C_98,B_86,D_104] :
      ( r1_orders_2(A_62,C_98,'#skF_5'(A_62,B_86,C_98,D_104))
      | k10_lattice3(A_62,B_86,C_98) = D_104
      | ~ r1_orders_2(A_62,C_98,D_104)
      | ~ r1_orders_2(A_62,B_86,D_104)
      | ~ m1_subset_1(D_104,u1_struct_0(A_62))
      | ~ m1_subset_1(C_98,u1_struct_0(A_62))
      | ~ m1_subset_1(B_86,u1_struct_0(A_62))
      | ~ l1_orders_2(A_62)
      | ~ v1_lattice3(A_62)
      | ~ v5_orders_2(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_30,plain,(
    ! [A_62,B_86,C_98,D_104] :
      ( r1_orders_2(A_62,B_86,'#skF_5'(A_62,B_86,C_98,D_104))
      | k10_lattice3(A_62,B_86,C_98) = D_104
      | ~ r1_orders_2(A_62,C_98,D_104)
      | ~ r1_orders_2(A_62,B_86,D_104)
      | ~ m1_subset_1(D_104,u1_struct_0(A_62))
      | ~ m1_subset_1(C_98,u1_struct_0(A_62))
      | ~ m1_subset_1(B_86,u1_struct_0(A_62))
      | ~ l1_orders_2(A_62)
      | ~ v1_lattice3(A_62)
      | ~ v5_orders_2(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1232,plain,(
    ! [A_280,D_281,B_282,C_283] :
      ( ~ r1_orders_2(A_280,D_281,'#skF_5'(A_280,B_282,C_283,D_281))
      | k10_lattice3(A_280,B_282,C_283) = D_281
      | ~ r1_orders_2(A_280,C_283,D_281)
      | ~ r1_orders_2(A_280,B_282,D_281)
      | ~ m1_subset_1(D_281,u1_struct_0(A_280))
      | ~ m1_subset_1(C_283,u1_struct_0(A_280))
      | ~ m1_subset_1(B_282,u1_struct_0(A_280))
      | ~ l1_orders_2(A_280)
      | ~ v1_lattice3(A_280)
      | ~ v5_orders_2(A_280)
      | v2_struct_0(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5316,plain,(
    ! [C_432,C_431,B_428,A_429,B_430] :
      ( k10_lattice3(A_429,B_428,C_431) = '#skF_1'(A_429,B_430,C_432)
      | ~ r1_orders_2(A_429,C_431,'#skF_1'(A_429,B_430,C_432))
      | ~ r1_orders_2(A_429,B_428,'#skF_1'(A_429,B_430,C_432))
      | ~ m1_subset_1('#skF_1'(A_429,B_430,C_432),u1_struct_0(A_429))
      | ~ m1_subset_1(C_431,u1_struct_0(A_429))
      | ~ m1_subset_1(B_428,u1_struct_0(A_429))
      | ~ v5_orders_2(A_429)
      | v2_struct_0(A_429)
      | ~ r1_orders_2(A_429,C_432,'#skF_5'(A_429,B_428,C_431,'#skF_1'(A_429,B_430,C_432)))
      | ~ r1_orders_2(A_429,B_430,'#skF_5'(A_429,B_428,C_431,'#skF_1'(A_429,B_430,C_432)))
      | ~ m1_subset_1('#skF_5'(A_429,B_428,C_431,'#skF_1'(A_429,B_430,C_432)),u1_struct_0(A_429))
      | ~ m1_subset_1(C_432,u1_struct_0(A_429))
      | ~ m1_subset_1(B_430,u1_struct_0(A_429))
      | ~ v1_lattice3(A_429)
      | ~ l1_orders_2(A_429) ) ),
    inference(resolution,[status(thm)],[c_18,c_1232])).

tff(c_23655,plain,(
    ! [A_831,B_832,B_833,C_834] :
      ( ~ r1_orders_2(A_831,B_832,'#skF_5'(A_831,B_833,C_834,'#skF_1'(A_831,B_832,B_833)))
      | ~ m1_subset_1('#skF_5'(A_831,B_833,C_834,'#skF_1'(A_831,B_832,B_833)),u1_struct_0(A_831))
      | ~ m1_subset_1(B_832,u1_struct_0(A_831))
      | k10_lattice3(A_831,B_833,C_834) = '#skF_1'(A_831,B_832,B_833)
      | ~ r1_orders_2(A_831,C_834,'#skF_1'(A_831,B_832,B_833))
      | ~ r1_orders_2(A_831,B_833,'#skF_1'(A_831,B_832,B_833))
      | ~ m1_subset_1('#skF_1'(A_831,B_832,B_833),u1_struct_0(A_831))
      | ~ m1_subset_1(C_834,u1_struct_0(A_831))
      | ~ m1_subset_1(B_833,u1_struct_0(A_831))
      | ~ l1_orders_2(A_831)
      | ~ v1_lattice3(A_831)
      | ~ v5_orders_2(A_831)
      | v2_struct_0(A_831) ) ),
    inference(resolution,[status(thm)],[c_30,c_5316])).

tff(c_52401,plain,(
    ! [A_1237,B_1238,C_1239] :
      ( ~ m1_subset_1('#skF_5'(A_1237,B_1238,C_1239,'#skF_1'(A_1237,C_1239,B_1238)),u1_struct_0(A_1237))
      | k10_lattice3(A_1237,B_1238,C_1239) = '#skF_1'(A_1237,C_1239,B_1238)
      | ~ r1_orders_2(A_1237,C_1239,'#skF_1'(A_1237,C_1239,B_1238))
      | ~ r1_orders_2(A_1237,B_1238,'#skF_1'(A_1237,C_1239,B_1238))
      | ~ m1_subset_1('#skF_1'(A_1237,C_1239,B_1238),u1_struct_0(A_1237))
      | ~ m1_subset_1(C_1239,u1_struct_0(A_1237))
      | ~ m1_subset_1(B_1238,u1_struct_0(A_1237))
      | ~ l1_orders_2(A_1237)
      | ~ v1_lattice3(A_1237)
      | ~ v5_orders_2(A_1237)
      | v2_struct_0(A_1237) ) ),
    inference(resolution,[status(thm)],[c_28,c_23655])).

tff(c_52404,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_7','#skF_8','#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')),u1_struct_0('#skF_7'))
    | k10_lattice3('#skF_7','#skF_8','#skF_9') = '#skF_1'('#skF_7','#skF_9','#skF_8')
    | ~ r1_orders_2('#skF_7','#skF_9','#skF_1'('#skF_7','#skF_9','#skF_8'))
    | ~ r1_orders_2('#skF_7','#skF_8','#skF_1'('#skF_7','#skF_9','#skF_8'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_9','#skF_8'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7')
    | ~ v1_lattice3('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_18118,c_52401])).

tff(c_52416,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_7','#skF_8','#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')),u1_struct_0('#skF_7'))
    | k10_lattice3('#skF_7','#skF_8','#skF_9') = '#skF_1'('#skF_7','#skF_8','#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_60,c_4254,c_18118,c_4253,c_18118,c_5103,c_18118,c_18118,c_52404])).

tff(c_52417,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_7','#skF_8','#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')),u1_struct_0('#skF_7'))
    | k10_lattice3('#skF_7','#skF_8','#skF_9') = '#skF_1'('#skF_7','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_52416])).

tff(c_52425,plain,(
    ~ m1_subset_1('#skF_5'('#skF_7','#skF_8','#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_52417])).

tff(c_52428,plain,
    ( k10_lattice3('#skF_7','#skF_8','#skF_9') = '#skF_1'('#skF_7','#skF_8','#skF_9')
    | ~ r1_orders_2('#skF_7','#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9'))
    | ~ r1_orders_2('#skF_7','#skF_8','#skF_1'('#skF_7','#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7')
    | ~ v1_lattice3('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_52425])).

tff(c_52431,plain,
    ( k10_lattice3('#skF_7','#skF_8','#skF_9') = '#skF_1'('#skF_7','#skF_8','#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_60,c_4254,c_4253,c_5103,c_52428])).

tff(c_52432,plain,(
    k10_lattice3('#skF_7','#skF_8','#skF_9') = '#skF_1'('#skF_7','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_52431])).

tff(c_112,plain,(
    ! [A_180,B_181,C_182] :
      ( k13_lattice3(A_180,B_181,C_182) = k10_lattice3(A_180,B_181,C_182)
      | ~ m1_subset_1(C_182,u1_struct_0(A_180))
      | ~ m1_subset_1(B_181,u1_struct_0(A_180))
      | ~ l1_orders_2(A_180)
      | ~ v1_lattice3(A_180)
      | ~ v5_orders_2(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_120,plain,(
    ! [B_181] :
      ( k13_lattice3('#skF_7',B_181,'#skF_9') = k10_lattice3('#skF_7',B_181,'#skF_9')
      | ~ m1_subset_1(B_181,u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ v1_lattice3('#skF_7')
      | ~ v5_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_60,c_112])).

tff(c_132,plain,(
    ! [B_183] :
      ( k13_lattice3('#skF_7',B_183,'#skF_9') = k10_lattice3('#skF_7',B_183,'#skF_9')
      | ~ m1_subset_1(B_183,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_120])).

tff(c_161,plain,(
    k13_lattice3('#skF_7','#skF_8','#skF_9') = k10_lattice3('#skF_7','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_62,c_132])).

tff(c_58,plain,(
    k12_lattice3('#skF_7','#skF_8',k13_lattice3('#skF_7','#skF_8','#skF_9')) != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_186,plain,(
    k12_lattice3('#skF_7','#skF_8',k10_lattice3('#skF_7','#skF_8','#skF_9')) != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_58])).

tff(c_52433,plain,(
    k12_lattice3('#skF_7','#skF_8','#skF_1'('#skF_7','#skF_8','#skF_9')) != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52432,c_186])).

tff(c_52437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5269,c_52433])).

tff(c_52438,plain,(
    k10_lattice3('#skF_7','#skF_8','#skF_9') = '#skF_1'('#skF_7','#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_52417])).

tff(c_52456,plain,(
    k12_lattice3('#skF_7','#skF_8','#skF_1'('#skF_7','#skF_8','#skF_9')) != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52438,c_186])).

tff(c_52460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5269,c_52456])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 34.78/23.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 34.78/23.21  
% 34.78/23.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 34.78/23.21  %$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_4
% 34.78/23.21  
% 34.78/23.21  %Foreground sorts:
% 34.78/23.21  
% 34.78/23.21  
% 34.78/23.21  %Background operators:
% 34.78/23.21  
% 34.78/23.21  
% 34.78/23.21  %Foreground operators:
% 34.78/23.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 34.78/23.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 34.78/23.21  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 34.78/23.21  tff('#skF_2', type, '#skF_2': $i > $i).
% 34.78/23.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 34.78/23.21  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 34.78/23.21  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 34.78/23.21  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 34.78/23.21  tff('#skF_7', type, '#skF_7': $i).
% 34.78/23.21  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 34.78/23.21  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 34.78/23.21  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 34.78/23.21  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 34.78/23.21  tff('#skF_9', type, '#skF_9': $i).
% 34.78/23.21  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 34.78/23.21  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 34.78/23.21  tff('#skF_8', type, '#skF_8': $i).
% 34.78/23.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 34.78/23.21  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 34.78/23.21  tff('#skF_3', type, '#skF_3': $i > $i).
% 34.78/23.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 34.78/23.21  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 34.78/23.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 34.78/23.21  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 34.78/23.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 34.78/23.21  
% 35.12/23.24  tff(f_179, negated_conjecture, ~(![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k12_lattice3(A, B, k13_lattice3(A, B, C)) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_lattice3)).
% 35.12/23.24  tff(f_70, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (?[D]: (((m1_subset_1(D, u1_struct_0(A)) & r1_orders_2(A, B, D)) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_lattice3)).
% 35.12/23.24  tff(f_37, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 35.12/23.24  tff(f_44, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 35.12/23.24  tff(f_136, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 35.12/23.24  tff(f_148, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 35.12/23.24  tff(f_103, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l26_lattice3)).
% 35.12/23.24  tff(f_160, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 35.12/23.24  tff(c_64, plain, (l1_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_179])).
% 35.12/23.24  tff(c_68, plain, (v1_lattice3('#skF_7')), inference(cnfTransformation, [status(thm)], [f_179])).
% 35.12/23.24  tff(c_62, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 35.12/23.24  tff(c_60, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 35.12/23.24  tff(c_24, plain, (![A_5, B_36, C_44]: (m1_subset_1('#skF_1'(A_5, B_36, C_44), u1_struct_0(A_5)) | ~m1_subset_1(C_44, u1_struct_0(A_5)) | ~m1_subset_1(B_36, u1_struct_0(A_5)) | ~v1_lattice3(A_5) | ~l1_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_70])).
% 35.12/23.24  tff(c_72, plain, (v3_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_179])).
% 35.12/23.24  tff(c_76, plain, (![A_167, B_168]: (r1_orders_2(A_167, B_168, B_168) | ~m1_subset_1(B_168, u1_struct_0(A_167)) | ~l1_orders_2(A_167) | ~v3_orders_2(A_167) | v2_struct_0(A_167))), inference(cnfTransformation, [status(thm)], [f_37])).
% 35.12/23.24  tff(c_82, plain, (r1_orders_2('#skF_7', '#skF_9', '#skF_9') | ~l1_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_60, c_76])).
% 35.12/23.24  tff(c_89, plain, (r1_orders_2('#skF_7', '#skF_9', '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_64, c_82])).
% 35.12/23.24  tff(c_93, plain, (v2_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_89])).
% 35.12/23.24  tff(c_4, plain, (![A_4]: (~v2_struct_0(A_4) | ~v1_lattice3(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 35.12/23.24  tff(c_96, plain, (~v1_lattice3('#skF_7') | ~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_93, c_4])).
% 35.12/23.24  tff(c_100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_96])).
% 35.12/23.24  tff(c_102, plain, (~v2_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_89])).
% 35.12/23.24  tff(c_70, plain, (v5_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_179])).
% 35.12/23.24  tff(c_66, plain, (v2_lattice3('#skF_7')), inference(cnfTransformation, [status(thm)], [f_179])).
% 35.12/23.24  tff(c_22, plain, (![A_5, B_36, C_44]: (r1_orders_2(A_5, B_36, '#skF_1'(A_5, B_36, C_44)) | ~m1_subset_1(C_44, u1_struct_0(A_5)) | ~m1_subset_1(B_36, u1_struct_0(A_5)) | ~v1_lattice3(A_5) | ~l1_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_70])).
% 35.12/23.24  tff(c_84, plain, (r1_orders_2('#skF_7', '#skF_8', '#skF_8') | ~l1_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_62, c_76])).
% 35.12/23.24  tff(c_92, plain, (r1_orders_2('#skF_7', '#skF_8', '#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_64, c_84])).
% 35.12/23.24  tff(c_104, plain, (r1_orders_2('#skF_7', '#skF_8', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_102, c_92])).
% 35.12/23.24  tff(c_2600, plain, (![A_366, B_367, C_368, D_369]: (r1_orders_2(A_366, '#skF_6'(A_366, B_367, C_368, D_369), C_368) | k11_lattice3(A_366, B_367, C_368)=D_369 | ~r1_orders_2(A_366, D_369, C_368) | ~r1_orders_2(A_366, D_369, B_367) | ~m1_subset_1(D_369, u1_struct_0(A_366)) | ~m1_subset_1(C_368, u1_struct_0(A_366)) | ~m1_subset_1(B_367, u1_struct_0(A_366)) | ~l1_orders_2(A_366) | ~v2_lattice3(A_366) | ~v5_orders_2(A_366) | v2_struct_0(A_366))), inference(cnfTransformation, [status(thm)], [f_136])).
% 35.12/23.24  tff(c_40, plain, (![A_108, B_132, C_144, D_150]: (~r1_orders_2(A_108, '#skF_6'(A_108, B_132, C_144, D_150), D_150) | k11_lattice3(A_108, B_132, C_144)=D_150 | ~r1_orders_2(A_108, D_150, C_144) | ~r1_orders_2(A_108, D_150, B_132) | ~m1_subset_1(D_150, u1_struct_0(A_108)) | ~m1_subset_1(C_144, u1_struct_0(A_108)) | ~m1_subset_1(B_132, u1_struct_0(A_108)) | ~l1_orders_2(A_108) | ~v2_lattice3(A_108) | ~v5_orders_2(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_136])).
% 35.12/23.24  tff(c_3241, plain, (![A_383, B_384, C_385]: (k11_lattice3(A_383, B_384, C_385)=C_385 | ~r1_orders_2(A_383, C_385, C_385) | ~r1_orders_2(A_383, C_385, B_384) | ~m1_subset_1(C_385, u1_struct_0(A_383)) | ~m1_subset_1(B_384, u1_struct_0(A_383)) | ~l1_orders_2(A_383) | ~v2_lattice3(A_383) | ~v5_orders_2(A_383) | v2_struct_0(A_383))), inference(resolution, [status(thm)], [c_2600, c_40])).
% 35.12/23.24  tff(c_3256, plain, (![B_384]: (k11_lattice3('#skF_7', B_384, '#skF_8')='#skF_8' | ~r1_orders_2('#skF_7', '#skF_8', B_384) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1(B_384, u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v2_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_104, c_3241])).
% 35.12/23.24  tff(c_3270, plain, (![B_384]: (k11_lattice3('#skF_7', B_384, '#skF_8')='#skF_8' | ~r1_orders_2('#skF_7', '#skF_8', B_384) | ~m1_subset_1(B_384, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_62, c_3256])).
% 35.12/23.24  tff(c_3276, plain, (![B_386]: (k11_lattice3('#skF_7', B_386, '#skF_8')='#skF_8' | ~r1_orders_2('#skF_7', '#skF_8', B_386) | ~m1_subset_1(B_386, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_102, c_3270])).
% 35.12/23.24  tff(c_3295, plain, (![B_36, C_44]: (k11_lattice3('#skF_7', '#skF_1'('#skF_7', B_36, C_44), '#skF_8')='#skF_8' | ~r1_orders_2('#skF_7', '#skF_8', '#skF_1'('#skF_7', B_36, C_44)) | ~m1_subset_1(C_44, u1_struct_0('#skF_7')) | ~m1_subset_1(B_36, u1_struct_0('#skF_7')) | ~v1_lattice3('#skF_7') | ~l1_orders_2('#skF_7'))), inference(resolution, [status(thm)], [c_24, c_3276])).
% 35.12/23.24  tff(c_3708, plain, (![B_395, C_396]: (k11_lattice3('#skF_7', '#skF_1'('#skF_7', B_395, C_396), '#skF_8')='#skF_8' | ~r1_orders_2('#skF_7', '#skF_8', '#skF_1'('#skF_7', B_395, C_396)) | ~m1_subset_1(C_396, u1_struct_0('#skF_7')) | ~m1_subset_1(B_395, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_3295])).
% 35.12/23.24  tff(c_3719, plain, (![C_44]: (k11_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_8', C_44), '#skF_8')='#skF_8' | ~m1_subset_1(C_44, u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v1_lattice3('#skF_7') | ~l1_orders_2('#skF_7'))), inference(resolution, [status(thm)], [c_22, c_3708])).
% 35.12/23.24  tff(c_3842, plain, (![C_402]: (k11_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_8', C_402), '#skF_8')='#skF_8' | ~m1_subset_1(C_402, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_62, c_3719])).
% 35.12/23.24  tff(c_3893, plain, (k11_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_60, c_3842])).
% 35.12/23.24  tff(c_52, plain, (![A_108, B_132, C_144]: (r1_orders_2(A_108, k11_lattice3(A_108, B_132, C_144), B_132) | ~m1_subset_1(k11_lattice3(A_108, B_132, C_144), u1_struct_0(A_108)) | ~m1_subset_1(C_144, u1_struct_0(A_108)) | ~m1_subset_1(B_132, u1_struct_0(A_108)) | ~l1_orders_2(A_108) | ~v2_lattice3(A_108) | ~v5_orders_2(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_136])).
% 35.12/23.24  tff(c_3901, plain, (r1_orders_2('#skF_7', k11_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_8'), '#skF_1'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v2_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3893, c_52])).
% 35.12/23.24  tff(c_3910, plain, (r1_orders_2('#skF_7', '#skF_8', '#skF_1'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_62, c_62, c_3893, c_3901])).
% 35.12/23.24  tff(c_3911, plain, (r1_orders_2('#skF_7', '#skF_8', '#skF_1'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_102, c_3910])).
% 35.12/23.24  tff(c_4245, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_3911])).
% 35.12/23.24  tff(c_4248, plain, (~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v1_lattice3('#skF_7') | ~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_24, c_4245])).
% 35.12/23.24  tff(c_4252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_62, c_60, c_4248])).
% 35.12/23.24  tff(c_4254, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_3911])).
% 35.12/23.24  tff(c_4253, plain, (r1_orders_2('#skF_7', '#skF_8', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_3911])).
% 35.12/23.24  tff(c_1818, plain, (![A_327, B_328, C_329, D_330]: (r1_orders_2(A_327, '#skF_6'(A_327, B_328, C_329, D_330), B_328) | k11_lattice3(A_327, B_328, C_329)=D_330 | ~r1_orders_2(A_327, D_330, C_329) | ~r1_orders_2(A_327, D_330, B_328) | ~m1_subset_1(D_330, u1_struct_0(A_327)) | ~m1_subset_1(C_329, u1_struct_0(A_327)) | ~m1_subset_1(B_328, u1_struct_0(A_327)) | ~l1_orders_2(A_327) | ~v2_lattice3(A_327) | ~v5_orders_2(A_327) | v2_struct_0(A_327))), inference(cnfTransformation, [status(thm)], [f_136])).
% 35.12/23.24  tff(c_1826, plain, (![A_327, B_328, C_329]: (k11_lattice3(A_327, B_328, C_329)=B_328 | ~r1_orders_2(A_327, B_328, C_329) | ~r1_orders_2(A_327, B_328, B_328) | ~m1_subset_1(C_329, u1_struct_0(A_327)) | ~m1_subset_1(B_328, u1_struct_0(A_327)) | ~l1_orders_2(A_327) | ~v2_lattice3(A_327) | ~v5_orders_2(A_327) | v2_struct_0(A_327))), inference(resolution, [status(thm)], [c_1818, c_40])).
% 35.12/23.24  tff(c_4259, plain, (k11_lattice3('#skF_7', '#skF_8', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_8' | ~r1_orders_2('#skF_7', '#skF_8', '#skF_8') | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v2_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_4253, c_1826])).
% 35.12/23.24  tff(c_4267, plain, (k11_lattice3('#skF_7', '#skF_8', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_8' | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_62, c_104, c_4259])).
% 35.12/23.24  tff(c_4268, plain, (k11_lattice3('#skF_7', '#skF_8', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_8' | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_102, c_4267])).
% 35.12/23.24  tff(c_5268, plain, (k11_lattice3('#skF_7', '#skF_8', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4254, c_4268])).
% 35.12/23.24  tff(c_166, plain, (![A_184, B_185, C_186]: (k12_lattice3(A_184, B_185, C_186)=k11_lattice3(A_184, B_185, C_186) | ~m1_subset_1(C_186, u1_struct_0(A_184)) | ~m1_subset_1(B_185, u1_struct_0(A_184)) | ~l1_orders_2(A_184) | ~v2_lattice3(A_184) | ~v5_orders_2(A_184))), inference(cnfTransformation, [status(thm)], [f_148])).
% 35.12/23.24  tff(c_1648, plain, (![A_319, B_320, B_321, C_322]: (k12_lattice3(A_319, B_320, '#skF_1'(A_319, B_321, C_322))=k11_lattice3(A_319, B_320, '#skF_1'(A_319, B_321, C_322)) | ~m1_subset_1(B_320, u1_struct_0(A_319)) | ~v2_lattice3(A_319) | ~v5_orders_2(A_319) | ~m1_subset_1(C_322, u1_struct_0(A_319)) | ~m1_subset_1(B_321, u1_struct_0(A_319)) | ~v1_lattice3(A_319) | ~l1_orders_2(A_319))), inference(resolution, [status(thm)], [c_24, c_166])).
% 35.12/23.24  tff(c_1662, plain, (![B_321, C_322]: (k12_lattice3('#skF_7', '#skF_8', '#skF_1'('#skF_7', B_321, C_322))=k11_lattice3('#skF_7', '#skF_8', '#skF_1'('#skF_7', B_321, C_322)) | ~v2_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | ~m1_subset_1(C_322, u1_struct_0('#skF_7')) | ~m1_subset_1(B_321, u1_struct_0('#skF_7')) | ~v1_lattice3('#skF_7') | ~l1_orders_2('#skF_7'))), inference(resolution, [status(thm)], [c_62, c_1648])).
% 35.12/23.24  tff(c_1827, plain, (![B_331, C_332]: (k12_lattice3('#skF_7', '#skF_8', '#skF_1'('#skF_7', B_331, C_332))=k11_lattice3('#skF_7', '#skF_8', '#skF_1'('#skF_7', B_331, C_332)) | ~m1_subset_1(C_332, u1_struct_0('#skF_7')) | ~m1_subset_1(B_331, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_70, c_66, c_1662])).
% 35.12/23.24  tff(c_1865, plain, (![B_333]: (k12_lattice3('#skF_7', '#skF_8', '#skF_1'('#skF_7', B_333, '#skF_9'))=k11_lattice3('#skF_7', '#skF_8', '#skF_1'('#skF_7', B_333, '#skF_9')) | ~m1_subset_1(B_333, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_60, c_1827])).
% 35.12/23.24  tff(c_1909, plain, (k12_lattice3('#skF_7', '#skF_8', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))=k11_lattice3('#skF_7', '#skF_8', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_62, c_1865])).
% 35.12/23.24  tff(c_5269, plain, (k12_lattice3('#skF_7', '#skF_8', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5268, c_1909])).
% 35.12/23.24  tff(c_20, plain, (![A_5, C_44, B_36]: (r1_orders_2(A_5, C_44, '#skF_1'(A_5, B_36, C_44)) | ~m1_subset_1(C_44, u1_struct_0(A_5)) | ~m1_subset_1(B_36, u1_struct_0(A_5)) | ~v1_lattice3(A_5) | ~l1_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_70])).
% 35.12/23.24  tff(c_101, plain, (r1_orders_2('#skF_7', '#skF_9', '#skF_9')), inference(splitRight, [status(thm)], [c_89])).
% 35.12/23.24  tff(c_3258, plain, (![B_384]: (k11_lattice3('#skF_7', B_384, '#skF_9')='#skF_9' | ~r1_orders_2('#skF_7', '#skF_9', B_384) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_subset_1(B_384, u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v2_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_101, c_3241])).
% 35.12/23.24  tff(c_3274, plain, (![B_384]: (k11_lattice3('#skF_7', B_384, '#skF_9')='#skF_9' | ~r1_orders_2('#skF_7', '#skF_9', B_384) | ~m1_subset_1(B_384, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_3258])).
% 35.12/23.24  tff(c_3275, plain, (![B_384]: (k11_lattice3('#skF_7', B_384, '#skF_9')='#skF_9' | ~r1_orders_2('#skF_7', '#skF_9', B_384) | ~m1_subset_1(B_384, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_102, c_3274])).
% 35.12/23.24  tff(c_4399, plain, (k11_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9' | ~r1_orders_2('#skF_7', '#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_4254, c_3275])).
% 35.12/23.24  tff(c_5045, plain, (~r1_orders_2('#skF_7', '#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_4399])).
% 35.12/23.24  tff(c_5097, plain, (~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v1_lattice3('#skF_7') | ~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_20, c_5045])).
% 35.12/23.24  tff(c_5101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_62, c_60, c_5097])).
% 35.12/23.24  tff(c_5103, plain, (r1_orders_2('#skF_7', '#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_4399])).
% 35.12/23.24  tff(c_32, plain, (![A_62, B_86, C_98, D_104]: (m1_subset_1('#skF_5'(A_62, B_86, C_98, D_104), u1_struct_0(A_62)) | k10_lattice3(A_62, B_86, C_98)=D_104 | ~r1_orders_2(A_62, C_98, D_104) | ~r1_orders_2(A_62, B_86, D_104) | ~m1_subset_1(D_104, u1_struct_0(A_62)) | ~m1_subset_1(C_98, u1_struct_0(A_62)) | ~m1_subset_1(B_86, u1_struct_0(A_62)) | ~l1_orders_2(A_62) | ~v1_lattice3(A_62) | ~v5_orders_2(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_103])).
% 35.12/23.24  tff(c_3715, plain, (![B_36]: (k11_lattice3('#skF_7', '#skF_1'('#skF_7', B_36, '#skF_8'), '#skF_8')='#skF_8' | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1(B_36, u1_struct_0('#skF_7')) | ~v1_lattice3('#skF_7') | ~l1_orders_2('#skF_7'))), inference(resolution, [status(thm)], [c_20, c_3708])).
% 35.12/23.24  tff(c_3728, plain, (![B_397]: (k11_lattice3('#skF_7', '#skF_1'('#skF_7', B_397, '#skF_8'), '#skF_8')='#skF_8' | ~m1_subset_1(B_397, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_62, c_3715])).
% 35.12/23.24  tff(c_3779, plain, (k11_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_60, c_3728])).
% 35.12/23.24  tff(c_3786, plain, (r1_orders_2('#skF_7', k11_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_8'), '#skF_1'('#skF_7', '#skF_9', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_9', '#skF_8'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v2_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3779, c_52])).
% 35.12/23.24  tff(c_3795, plain, (r1_orders_2('#skF_7', '#skF_8', '#skF_1'('#skF_7', '#skF_9', '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_9', '#skF_8'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_62, c_62, c_3779, c_3786])).
% 35.12/23.24  tff(c_3796, plain, (r1_orders_2('#skF_7', '#skF_8', '#skF_1'('#skF_7', '#skF_9', '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_9', '#skF_8'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_102, c_3795])).
% 35.12/23.24  tff(c_3920, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_9', '#skF_8'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_3796])).
% 35.12/23.24  tff(c_3923, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~v1_lattice3('#skF_7') | ~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_24, c_3920])).
% 35.12/23.24  tff(c_3927, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_60, c_62, c_3923])).
% 35.12/23.24  tff(c_3928, plain, (r1_orders_2('#skF_7', '#skF_8', '#skF_1'('#skF_7', '#skF_9', '#skF_8'))), inference(splitRight, [status(thm)], [c_3796])).
% 35.12/23.24  tff(c_3929, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_9', '#skF_8'), u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_3796])).
% 35.12/23.24  tff(c_4068, plain, (k11_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_9')='#skF_9' | ~r1_orders_2('#skF_7', '#skF_9', '#skF_1'('#skF_7', '#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_3929, c_3275])).
% 35.12/23.24  tff(c_5654, plain, (~r1_orders_2('#skF_7', '#skF_9', '#skF_1'('#skF_7', '#skF_9', '#skF_8'))), inference(splitLeft, [status(thm)], [c_4068])).
% 35.12/23.24  tff(c_5662, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~v1_lattice3('#skF_7') | ~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_22, c_5654])).
% 35.12/23.24  tff(c_5666, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_60, c_62, c_5662])).
% 35.12/23.24  tff(c_5668, plain, (r1_orders_2('#skF_7', '#skF_9', '#skF_1'('#skF_7', '#skF_9', '#skF_8'))), inference(splitRight, [status(thm)], [c_4068])).
% 35.12/23.24  tff(c_2, plain, (![A_1, B_3]: (r1_orders_2(A_1, B_3, B_3) | ~m1_subset_1(B_3, u1_struct_0(A_1)) | ~l1_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 35.12/23.24  tff(c_4062, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_1'('#skF_7', '#skF_9', '#skF_8')) | ~l1_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_3929, c_2])).
% 35.12/23.24  tff(c_4128, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_1'('#skF_7', '#skF_9', '#skF_8')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_64, c_4062])).
% 35.12/23.24  tff(c_4129, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_1'('#skF_7', '#skF_9', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_102, c_4128])).
% 35.12/23.24  tff(c_18, plain, (![A_5, B_36, C_44, E_49]: (r1_orders_2(A_5, '#skF_1'(A_5, B_36, C_44), E_49) | ~r1_orders_2(A_5, C_44, E_49) | ~r1_orders_2(A_5, B_36, E_49) | ~m1_subset_1(E_49, u1_struct_0(A_5)) | ~m1_subset_1(C_44, u1_struct_0(A_5)) | ~m1_subset_1(B_36, u1_struct_0(A_5)) | ~v1_lattice3(A_5) | ~l1_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_70])).
% 35.12/23.24  tff(c_2611, plain, (![A_366, B_367, C_368]: (k11_lattice3(A_366, B_367, C_368)=C_368 | ~r1_orders_2(A_366, C_368, C_368) | ~r1_orders_2(A_366, C_368, B_367) | ~m1_subset_1(C_368, u1_struct_0(A_366)) | ~m1_subset_1(B_367, u1_struct_0(A_366)) | ~l1_orders_2(A_366) | ~v2_lattice3(A_366) | ~v5_orders_2(A_366) | v2_struct_0(A_366))), inference(resolution, [status(thm)], [c_2600, c_40])).
% 35.12/23.24  tff(c_4168, plain, (![B_367]: (k11_lattice3('#skF_7', B_367, '#skF_1'('#skF_7', '#skF_9', '#skF_8'))='#skF_1'('#skF_7', '#skF_9', '#skF_8') | ~r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), B_367) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_9', '#skF_8'), u1_struct_0('#skF_7')) | ~m1_subset_1(B_367, u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v2_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_4129, c_2611])).
% 35.12/23.24  tff(c_4177, plain, (![B_367]: (k11_lattice3('#skF_7', B_367, '#skF_1'('#skF_7', '#skF_9', '#skF_8'))='#skF_1'('#skF_7', '#skF_9', '#skF_8') | ~r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), B_367) | ~m1_subset_1(B_367, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_3929, c_4168])).
% 35.12/23.24  tff(c_10444, plain, (![B_520]: (k11_lattice3('#skF_7', B_520, '#skF_1'('#skF_7', '#skF_9', '#skF_8'))='#skF_1'('#skF_7', '#skF_9', '#skF_8') | ~r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), B_520) | ~m1_subset_1(B_520, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_102, c_4177])).
% 35.12/23.24  tff(c_10465, plain, (![E_49]: (k11_lattice3('#skF_7', E_49, '#skF_1'('#skF_7', '#skF_9', '#skF_8'))='#skF_1'('#skF_7', '#skF_9', '#skF_8') | ~r1_orders_2('#skF_7', '#skF_8', E_49) | ~r1_orders_2('#skF_7', '#skF_9', E_49) | ~m1_subset_1(E_49, u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~v1_lattice3('#skF_7') | ~l1_orders_2('#skF_7'))), inference(resolution, [status(thm)], [c_18, c_10444])).
% 35.12/23.24  tff(c_17640, plain, (![E_634]: (k11_lattice3('#skF_7', E_634, '#skF_1'('#skF_7', '#skF_9', '#skF_8'))='#skF_1'('#skF_7', '#skF_9', '#skF_8') | ~r1_orders_2('#skF_7', '#skF_8', E_634) | ~r1_orders_2('#skF_7', '#skF_9', E_634) | ~m1_subset_1(E_634, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_60, c_62, c_10465])).
% 35.12/23.24  tff(c_17667, plain, (k11_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'('#skF_7', '#skF_9', '#skF_8'))='#skF_1'('#skF_7', '#skF_9', '#skF_8') | ~r1_orders_2('#skF_7', '#skF_8', '#skF_1'('#skF_7', '#skF_8', '#skF_9')) | ~r1_orders_2('#skF_7', '#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_4254, c_17640])).
% 35.12/23.24  tff(c_17727, plain, (k11_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'('#skF_7', '#skF_9', '#skF_8'))='#skF_1'('#skF_7', '#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5103, c_4253, c_17667])).
% 35.12/23.24  tff(c_17762, plain, (r1_orders_2('#skF_7', k11_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'('#skF_7', '#skF_9', '#skF_8')), '#skF_1'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_9', '#skF_8'), u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_9', '#skF_8'), u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v2_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_17727, c_52])).
% 35.12/23.24  tff(c_17771, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_1'('#skF_7', '#skF_8', '#skF_9')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_4254, c_3929, c_3929, c_17727, c_17762])).
% 35.12/23.24  tff(c_17772, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_1'('#skF_7', '#skF_8', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_102, c_17771])).
% 35.12/23.24  tff(c_17788, plain, (k11_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_1'('#skF_7', '#skF_9', '#skF_8') | ~r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_1'('#skF_7', '#skF_9', '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_9', '#skF_8'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v2_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_17772, c_1826])).
% 35.12/23.24  tff(c_17807, plain, (k11_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_1'('#skF_7', '#skF_9', '#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_3929, c_4254, c_4129, c_17788])).
% 35.12/23.24  tff(c_17808, plain, (k11_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_1'('#skF_7', '#skF_9', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_102, c_17807])).
% 35.12/23.24  tff(c_4389, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'('#skF_7', '#skF_8', '#skF_9')) | ~l1_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_4254, c_2])).
% 35.12/23.24  tff(c_4459, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'('#skF_7', '#skF_8', '#skF_9')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_64, c_4389])).
% 35.12/23.24  tff(c_4460, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'('#skF_7', '#skF_8', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_102, c_4459])).
% 35.12/23.24  tff(c_4462, plain, (![B_367]: (k11_lattice3('#skF_7', B_367, '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_1'('#skF_7', '#skF_8', '#skF_9') | ~r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), B_367) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~m1_subset_1(B_367, u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v2_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_4460, c_2611])).
% 35.12/23.24  tff(c_4471, plain, (![B_367]: (k11_lattice3('#skF_7', B_367, '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_1'('#skF_7', '#skF_8', '#skF_9') | ~r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), B_367) | ~m1_subset_1(B_367, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_4254, c_4462])).
% 35.12/23.24  tff(c_10099, plain, (![B_513]: (k11_lattice3('#skF_7', B_513, '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_1'('#skF_7', '#skF_8', '#skF_9') | ~r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), B_513) | ~m1_subset_1(B_513, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_102, c_4471])).
% 35.12/23.24  tff(c_10120, plain, (![E_49]: (k11_lattice3('#skF_7', E_49, '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_1'('#skF_7', '#skF_8', '#skF_9') | ~r1_orders_2('#skF_7', '#skF_9', E_49) | ~r1_orders_2('#skF_7', '#skF_8', E_49) | ~m1_subset_1(E_49, u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v1_lattice3('#skF_7') | ~l1_orders_2('#skF_7'))), inference(resolution, [status(thm)], [c_18, c_10099])).
% 35.12/23.24  tff(c_18028, plain, (![E_640]: (k11_lattice3('#skF_7', E_640, '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_1'('#skF_7', '#skF_8', '#skF_9') | ~r1_orders_2('#skF_7', '#skF_9', E_640) | ~r1_orders_2('#skF_7', '#skF_8', E_640) | ~m1_subset_1(E_640, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_62, c_60, c_10120])).
% 35.12/23.24  tff(c_18058, plain, (k11_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_1'('#skF_7', '#skF_8', '#skF_9') | ~r1_orders_2('#skF_7', '#skF_9', '#skF_1'('#skF_7', '#skF_9', '#skF_8')) | ~r1_orders_2('#skF_7', '#skF_8', '#skF_1'('#skF_7', '#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_3929, c_18028])).
% 35.12/23.24  tff(c_18118, plain, ('#skF_1'('#skF_7', '#skF_9', '#skF_8')='#skF_1'('#skF_7', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3928, c_5668, c_17808, c_18058])).
% 35.12/23.24  tff(c_28, plain, (![A_62, C_98, B_86, D_104]: (r1_orders_2(A_62, C_98, '#skF_5'(A_62, B_86, C_98, D_104)) | k10_lattice3(A_62, B_86, C_98)=D_104 | ~r1_orders_2(A_62, C_98, D_104) | ~r1_orders_2(A_62, B_86, D_104) | ~m1_subset_1(D_104, u1_struct_0(A_62)) | ~m1_subset_1(C_98, u1_struct_0(A_62)) | ~m1_subset_1(B_86, u1_struct_0(A_62)) | ~l1_orders_2(A_62) | ~v1_lattice3(A_62) | ~v5_orders_2(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_103])).
% 35.12/23.24  tff(c_30, plain, (![A_62, B_86, C_98, D_104]: (r1_orders_2(A_62, B_86, '#skF_5'(A_62, B_86, C_98, D_104)) | k10_lattice3(A_62, B_86, C_98)=D_104 | ~r1_orders_2(A_62, C_98, D_104) | ~r1_orders_2(A_62, B_86, D_104) | ~m1_subset_1(D_104, u1_struct_0(A_62)) | ~m1_subset_1(C_98, u1_struct_0(A_62)) | ~m1_subset_1(B_86, u1_struct_0(A_62)) | ~l1_orders_2(A_62) | ~v1_lattice3(A_62) | ~v5_orders_2(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_103])).
% 35.12/23.24  tff(c_1232, plain, (![A_280, D_281, B_282, C_283]: (~r1_orders_2(A_280, D_281, '#skF_5'(A_280, B_282, C_283, D_281)) | k10_lattice3(A_280, B_282, C_283)=D_281 | ~r1_orders_2(A_280, C_283, D_281) | ~r1_orders_2(A_280, B_282, D_281) | ~m1_subset_1(D_281, u1_struct_0(A_280)) | ~m1_subset_1(C_283, u1_struct_0(A_280)) | ~m1_subset_1(B_282, u1_struct_0(A_280)) | ~l1_orders_2(A_280) | ~v1_lattice3(A_280) | ~v5_orders_2(A_280) | v2_struct_0(A_280))), inference(cnfTransformation, [status(thm)], [f_103])).
% 35.12/23.24  tff(c_5316, plain, (![C_432, C_431, B_428, A_429, B_430]: (k10_lattice3(A_429, B_428, C_431)='#skF_1'(A_429, B_430, C_432) | ~r1_orders_2(A_429, C_431, '#skF_1'(A_429, B_430, C_432)) | ~r1_orders_2(A_429, B_428, '#skF_1'(A_429, B_430, C_432)) | ~m1_subset_1('#skF_1'(A_429, B_430, C_432), u1_struct_0(A_429)) | ~m1_subset_1(C_431, u1_struct_0(A_429)) | ~m1_subset_1(B_428, u1_struct_0(A_429)) | ~v5_orders_2(A_429) | v2_struct_0(A_429) | ~r1_orders_2(A_429, C_432, '#skF_5'(A_429, B_428, C_431, '#skF_1'(A_429, B_430, C_432))) | ~r1_orders_2(A_429, B_430, '#skF_5'(A_429, B_428, C_431, '#skF_1'(A_429, B_430, C_432))) | ~m1_subset_1('#skF_5'(A_429, B_428, C_431, '#skF_1'(A_429, B_430, C_432)), u1_struct_0(A_429)) | ~m1_subset_1(C_432, u1_struct_0(A_429)) | ~m1_subset_1(B_430, u1_struct_0(A_429)) | ~v1_lattice3(A_429) | ~l1_orders_2(A_429))), inference(resolution, [status(thm)], [c_18, c_1232])).
% 35.12/23.24  tff(c_23655, plain, (![A_831, B_832, B_833, C_834]: (~r1_orders_2(A_831, B_832, '#skF_5'(A_831, B_833, C_834, '#skF_1'(A_831, B_832, B_833))) | ~m1_subset_1('#skF_5'(A_831, B_833, C_834, '#skF_1'(A_831, B_832, B_833)), u1_struct_0(A_831)) | ~m1_subset_1(B_832, u1_struct_0(A_831)) | k10_lattice3(A_831, B_833, C_834)='#skF_1'(A_831, B_832, B_833) | ~r1_orders_2(A_831, C_834, '#skF_1'(A_831, B_832, B_833)) | ~r1_orders_2(A_831, B_833, '#skF_1'(A_831, B_832, B_833)) | ~m1_subset_1('#skF_1'(A_831, B_832, B_833), u1_struct_0(A_831)) | ~m1_subset_1(C_834, u1_struct_0(A_831)) | ~m1_subset_1(B_833, u1_struct_0(A_831)) | ~l1_orders_2(A_831) | ~v1_lattice3(A_831) | ~v5_orders_2(A_831) | v2_struct_0(A_831))), inference(resolution, [status(thm)], [c_30, c_5316])).
% 35.12/23.24  tff(c_52401, plain, (![A_1237, B_1238, C_1239]: (~m1_subset_1('#skF_5'(A_1237, B_1238, C_1239, '#skF_1'(A_1237, C_1239, B_1238)), u1_struct_0(A_1237)) | k10_lattice3(A_1237, B_1238, C_1239)='#skF_1'(A_1237, C_1239, B_1238) | ~r1_orders_2(A_1237, C_1239, '#skF_1'(A_1237, C_1239, B_1238)) | ~r1_orders_2(A_1237, B_1238, '#skF_1'(A_1237, C_1239, B_1238)) | ~m1_subset_1('#skF_1'(A_1237, C_1239, B_1238), u1_struct_0(A_1237)) | ~m1_subset_1(C_1239, u1_struct_0(A_1237)) | ~m1_subset_1(B_1238, u1_struct_0(A_1237)) | ~l1_orders_2(A_1237) | ~v1_lattice3(A_1237) | ~v5_orders_2(A_1237) | v2_struct_0(A_1237))), inference(resolution, [status(thm)], [c_28, c_23655])).
% 35.12/23.24  tff(c_52404, plain, (~m1_subset_1('#skF_5'('#skF_7', '#skF_8', '#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0('#skF_7')) | k10_lattice3('#skF_7', '#skF_8', '#skF_9')='#skF_1'('#skF_7', '#skF_9', '#skF_8') | ~r1_orders_2('#skF_7', '#skF_9', '#skF_1'('#skF_7', '#skF_9', '#skF_8')) | ~r1_orders_2('#skF_7', '#skF_8', '#skF_1'('#skF_7', '#skF_9', '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_9', '#skF_8'), u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v1_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_18118, c_52401])).
% 35.12/23.24  tff(c_52416, plain, (~m1_subset_1('#skF_5'('#skF_7', '#skF_8', '#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0('#skF_7')) | k10_lattice3('#skF_7', '#skF_8', '#skF_9')='#skF_1'('#skF_7', '#skF_8', '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_60, c_4254, c_18118, c_4253, c_18118, c_5103, c_18118, c_18118, c_52404])).
% 35.12/23.24  tff(c_52417, plain, (~m1_subset_1('#skF_5'('#skF_7', '#skF_8', '#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0('#skF_7')) | k10_lattice3('#skF_7', '#skF_8', '#skF_9')='#skF_1'('#skF_7', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_102, c_52416])).
% 35.12/23.24  tff(c_52425, plain, (~m1_subset_1('#skF_5'('#skF_7', '#skF_8', '#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_52417])).
% 35.12/23.24  tff(c_52428, plain, (k10_lattice3('#skF_7', '#skF_8', '#skF_9')='#skF_1'('#skF_7', '#skF_8', '#skF_9') | ~r1_orders_2('#skF_7', '#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9')) | ~r1_orders_2('#skF_7', '#skF_8', '#skF_1'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v1_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_32, c_52425])).
% 35.12/23.24  tff(c_52431, plain, (k10_lattice3('#skF_7', '#skF_8', '#skF_9')='#skF_1'('#skF_7', '#skF_8', '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_60, c_4254, c_4253, c_5103, c_52428])).
% 35.12/23.24  tff(c_52432, plain, (k10_lattice3('#skF_7', '#skF_8', '#skF_9')='#skF_1'('#skF_7', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_102, c_52431])).
% 35.12/23.24  tff(c_112, plain, (![A_180, B_181, C_182]: (k13_lattice3(A_180, B_181, C_182)=k10_lattice3(A_180, B_181, C_182) | ~m1_subset_1(C_182, u1_struct_0(A_180)) | ~m1_subset_1(B_181, u1_struct_0(A_180)) | ~l1_orders_2(A_180) | ~v1_lattice3(A_180) | ~v5_orders_2(A_180))), inference(cnfTransformation, [status(thm)], [f_160])).
% 35.12/23.24  tff(c_120, plain, (![B_181]: (k13_lattice3('#skF_7', B_181, '#skF_9')=k10_lattice3('#skF_7', B_181, '#skF_9') | ~m1_subset_1(B_181, u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v1_lattice3('#skF_7') | ~v5_orders_2('#skF_7'))), inference(resolution, [status(thm)], [c_60, c_112])).
% 35.12/23.24  tff(c_132, plain, (![B_183]: (k13_lattice3('#skF_7', B_183, '#skF_9')=k10_lattice3('#skF_7', B_183, '#skF_9') | ~m1_subset_1(B_183, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_120])).
% 35.12/23.24  tff(c_161, plain, (k13_lattice3('#skF_7', '#skF_8', '#skF_9')=k10_lattice3('#skF_7', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_62, c_132])).
% 35.12/23.24  tff(c_58, plain, (k12_lattice3('#skF_7', '#skF_8', k13_lattice3('#skF_7', '#skF_8', '#skF_9'))!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_179])).
% 35.12/23.24  tff(c_186, plain, (k12_lattice3('#skF_7', '#skF_8', k10_lattice3('#skF_7', '#skF_8', '#skF_9'))!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_161, c_58])).
% 35.12/23.24  tff(c_52433, plain, (k12_lattice3('#skF_7', '#skF_8', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_52432, c_186])).
% 35.12/23.24  tff(c_52437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5269, c_52433])).
% 35.12/23.24  tff(c_52438, plain, (k10_lattice3('#skF_7', '#skF_8', '#skF_9')='#skF_1'('#skF_7', '#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_52417])).
% 35.12/23.24  tff(c_52456, plain, (k12_lattice3('#skF_7', '#skF_8', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_52438, c_186])).
% 35.12/23.24  tff(c_52460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5269, c_52456])).
% 35.12/23.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.12/23.24  
% 35.12/23.24  Inference rules
% 35.12/23.24  ----------------------
% 35.12/23.24  #Ref     : 0
% 35.12/23.24  #Sup     : 11136
% 35.12/23.24  #Fact    : 0
% 35.12/23.24  #Define  : 0
% 35.12/23.24  #Split   : 121
% 35.12/23.24  #Chain   : 0
% 35.12/23.24  #Close   : 0
% 35.12/23.24  
% 35.12/23.24  Ordering : KBO
% 35.12/23.24  
% 35.12/23.24  Simplification rules
% 35.12/23.24  ----------------------
% 35.12/23.24  #Subsume      : 697
% 35.12/23.24  #Demod        : 27841
% 35.12/23.24  #Tautology    : 5760
% 35.12/23.24  #SimpNegUnit  : 3032
% 35.12/23.24  #BackRed      : 261
% 35.12/23.24  
% 35.12/23.24  #Partial instantiations: 0
% 35.12/23.24  #Strategies tried      : 1
% 35.12/23.24  
% 35.12/23.24  Timing (in seconds)
% 35.12/23.24  ----------------------
% 35.12/23.24  Preprocessing        : 0.41
% 35.12/23.24  Parsing              : 0.19
% 35.12/23.24  CNF conversion       : 0.04
% 35.12/23.24  Main loop            : 22.04
% 35.12/23.24  Inferencing          : 3.81
% 35.12/23.24  Reduction            : 11.58
% 35.12/23.24  Demodulation         : 10.14
% 35.12/23.24  BG Simplification    : 0.25
% 35.12/23.24  Subsumption          : 5.58
% 35.12/23.24  Abstraction          : 0.50
% 35.12/23.24  MUC search           : 0.00
% 35.12/23.24  Cooper               : 0.00
% 35.12/23.24  Total                : 22.51
% 35.12/23.24  Index Insertion      : 0.00
% 35.12/23.24  Index Deletion       : 0.00
% 35.12/23.24  Index Matching       : 0.00
% 35.12/23.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
