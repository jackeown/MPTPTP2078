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

% Result     : Theorem 34.30s
% Output     : CNFRefutation 34.37s
% Verified   : 
% Statistics : Number of formulae       :  163 (36962 expanded)
%              Number of leaves         :   33 (13708 expanded)
%              Depth                    :   42
%              Number of atoms          :  570 (185132 expanded)
%              Number of equality atoms :   74 (16976 expanded)
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

tff(f_186,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattice3)).

tff(f_77,axiom,(
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

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_110,axiom,(
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

tff(f_167,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_143,axiom,(
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

tff(f_155,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(c_64,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_66,plain,(
    l1_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_68,plain,(
    v2_lattice3('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_62,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_22,plain,(
    ! [A_6,B_37,C_45] :
      ( r1_orders_2(A_6,'#skF_1'(A_6,B_37,C_45),C_45)
      | ~ m1_subset_1(C_45,u1_struct_0(A_6))
      | ~ m1_subset_1(B_37,u1_struct_0(A_6))
      | ~ v2_lattice3(A_6)
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    ! [A_6,B_37,C_45] :
      ( m1_subset_1('#skF_1'(A_6,B_37,C_45),u1_struct_0(A_6))
      | ~ m1_subset_1(C_45,u1_struct_0(A_6))
      | ~ m1_subset_1(B_37,u1_struct_0(A_6))
      | ~ v2_lattice3(A_6)
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_74,plain,(
    v3_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_79,plain,(
    ! [A_169,B_170] :
      ( r1_orders_2(A_169,B_170,B_170)
      | ~ m1_subset_1(B_170,u1_struct_0(A_169))
      | ~ l1_orders_2(A_169)
      | ~ v3_orders_2(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_85,plain,
    ( r1_orders_2('#skF_7','#skF_9','#skF_9')
    | ~ l1_orders_2('#skF_7')
    | ~ v3_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_79])).

tff(c_92,plain,
    ( r1_orders_2('#skF_7','#skF_9','#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_66,c_85])).

tff(c_96,plain,(
    v2_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_6,plain,(
    ! [A_5] :
      ( ~ v2_struct_0(A_5)
      | ~ v2_lattice3(A_5)
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_99,plain,
    ( ~ v2_lattice3('#skF_7')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_96,c_6])).

tff(c_106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_99])).

tff(c_108,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_72,plain,(
    v5_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_70,plain,(
    v1_lattice3('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_107,plain,(
    r1_orders_2('#skF_7','#skF_9','#skF_9') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_30,plain,(
    ! [A_63,C_99,B_87,D_105] :
      ( r1_orders_2(A_63,C_99,'#skF_5'(A_63,B_87,C_99,D_105))
      | k10_lattice3(A_63,B_87,C_99) = D_105
      | ~ r1_orders_2(A_63,C_99,D_105)
      | ~ r1_orders_2(A_63,B_87,D_105)
      | ~ m1_subset_1(D_105,u1_struct_0(A_63))
      | ~ m1_subset_1(C_99,u1_struct_0(A_63))
      | ~ m1_subset_1(B_87,u1_struct_0(A_63))
      | ~ l1_orders_2(A_63)
      | ~ v1_lattice3(A_63)
      | ~ v5_orders_2(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1991,plain,(
    ! [A_345,D_346,B_347,C_348] :
      ( ~ r1_orders_2(A_345,D_346,'#skF_5'(A_345,B_347,C_348,D_346))
      | k10_lattice3(A_345,B_347,C_348) = D_346
      | ~ r1_orders_2(A_345,C_348,D_346)
      | ~ r1_orders_2(A_345,B_347,D_346)
      | ~ m1_subset_1(D_346,u1_struct_0(A_345))
      | ~ m1_subset_1(C_348,u1_struct_0(A_345))
      | ~ m1_subset_1(B_347,u1_struct_0(A_345))
      | ~ l1_orders_2(A_345)
      | ~ v1_lattice3(A_345)
      | ~ v5_orders_2(A_345)
      | v2_struct_0(A_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2034,plain,(
    ! [A_352,B_353,D_354] :
      ( k10_lattice3(A_352,B_353,D_354) = D_354
      | ~ r1_orders_2(A_352,D_354,D_354)
      | ~ r1_orders_2(A_352,B_353,D_354)
      | ~ m1_subset_1(D_354,u1_struct_0(A_352))
      | ~ m1_subset_1(B_353,u1_struct_0(A_352))
      | ~ l1_orders_2(A_352)
      | ~ v1_lattice3(A_352)
      | ~ v5_orders_2(A_352)
      | v2_struct_0(A_352) ) ),
    inference(resolution,[status(thm)],[c_30,c_1991])).

tff(c_2049,plain,(
    ! [B_353] :
      ( k10_lattice3('#skF_7',B_353,'#skF_9') = '#skF_9'
      | ~ r1_orders_2('#skF_7',B_353,'#skF_9')
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_353,u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ v1_lattice3('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_107,c_2034])).

tff(c_2061,plain,(
    ! [B_353] :
      ( k10_lattice3('#skF_7',B_353,'#skF_9') = '#skF_9'
      | ~ r1_orders_2('#skF_7',B_353,'#skF_9')
      | ~ m1_subset_1(B_353,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_62,c_2049])).

tff(c_2139,plain,(
    ! [B_360] :
      ( k10_lattice3('#skF_7',B_360,'#skF_9') = '#skF_9'
      | ~ r1_orders_2('#skF_7',B_360,'#skF_9')
      | ~ m1_subset_1(B_360,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_2061])).

tff(c_2151,plain,(
    ! [B_37,C_45] :
      ( k10_lattice3('#skF_7','#skF_1'('#skF_7',B_37,C_45),'#skF_9') = '#skF_9'
      | ~ r1_orders_2('#skF_7','#skF_1'('#skF_7',B_37,C_45),'#skF_9')
      | ~ m1_subset_1(C_45,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_37,u1_struct_0('#skF_7'))
      | ~ v2_lattice3('#skF_7')
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_26,c_2139])).

tff(c_2206,plain,(
    ! [B_361,C_362] :
      ( k10_lattice3('#skF_7','#skF_1'('#skF_7',B_361,C_362),'#skF_9') = '#skF_9'
      | ~ r1_orders_2('#skF_7','#skF_1'('#skF_7',B_361,C_362),'#skF_9')
      | ~ m1_subset_1(C_362,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_361,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_2151])).

tff(c_2214,plain,(
    ! [B_37] :
      ( k10_lattice3('#skF_7','#skF_1'('#skF_7',B_37,'#skF_9'),'#skF_9') = '#skF_9'
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_37,u1_struct_0('#skF_7'))
      | ~ v2_lattice3('#skF_7')
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_22,c_2206])).

tff(c_2783,plain,(
    ! [B_372] :
      ( k10_lattice3('#skF_7','#skF_1'('#skF_7',B_372,'#skF_9'),'#skF_9') = '#skF_9'
      | ~ m1_subset_1(B_372,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_62,c_2214])).

tff(c_2840,plain,(
    k10_lattice3('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_64,c_2783])).

tff(c_118,plain,(
    ! [A_182,B_183,C_184] :
      ( k13_lattice3(A_182,B_183,C_184) = k10_lattice3(A_182,B_183,C_184)
      | ~ m1_subset_1(C_184,u1_struct_0(A_182))
      | ~ m1_subset_1(B_183,u1_struct_0(A_182))
      | ~ l1_orders_2(A_182)
      | ~ v1_lattice3(A_182)
      | ~ v5_orders_2(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_126,plain,(
    ! [B_183] :
      ( k13_lattice3('#skF_7',B_183,'#skF_9') = k10_lattice3('#skF_7',B_183,'#skF_9')
      | ~ m1_subset_1(B_183,u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ v1_lattice3('#skF_7')
      | ~ v5_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_62,c_118])).

tff(c_138,plain,(
    ! [B_185] :
      ( k13_lattice3('#skF_7',B_185,'#skF_9') = k10_lattice3('#skF_7',B_185,'#skF_9')
      | ~ m1_subset_1(B_185,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_126])).

tff(c_142,plain,(
    ! [B_37,C_45] :
      ( k13_lattice3('#skF_7','#skF_1'('#skF_7',B_37,C_45),'#skF_9') = k10_lattice3('#skF_7','#skF_1'('#skF_7',B_37,C_45),'#skF_9')
      | ~ m1_subset_1(C_45,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_37,u1_struct_0('#skF_7'))
      | ~ v2_lattice3('#skF_7')
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_26,c_138])).

tff(c_823,plain,(
    ! [B_225,C_226] :
      ( k13_lattice3('#skF_7','#skF_1'('#skF_7',B_225,C_226),'#skF_9') = k10_lattice3('#skF_7','#skF_1'('#skF_7',B_225,C_226),'#skF_9')
      | ~ m1_subset_1(C_226,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_225,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_142])).

tff(c_854,plain,(
    ! [B_227] :
      ( k13_lattice3('#skF_7','#skF_1'('#skF_7',B_227,'#skF_9'),'#skF_9') = k10_lattice3('#skF_7','#skF_1'('#skF_7',B_227,'#skF_9'),'#skF_9')
      | ~ m1_subset_1(B_227,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_62,c_823])).

tff(c_890,plain,(
    k13_lattice3('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_9') = k10_lattice3('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_64,c_854])).

tff(c_2841,plain,(
    k13_lattice3('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2840,c_890])).

tff(c_40,plain,(
    ! [A_63,B_87,C_99] :
      ( r1_orders_2(A_63,B_87,k10_lattice3(A_63,B_87,C_99))
      | ~ m1_subset_1(k10_lattice3(A_63,B_87,C_99),u1_struct_0(A_63))
      | ~ m1_subset_1(C_99,u1_struct_0(A_63))
      | ~ m1_subset_1(B_87,u1_struct_0(A_63))
      | ~ l1_orders_2(A_63)
      | ~ v1_lattice3(A_63)
      | ~ v5_orders_2(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2844,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),k10_lattice3('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_9'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7')
    | ~ v1_lattice3('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2840,c_40])).

tff(c_2850,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_62,c_62,c_2840,c_2844])).

tff(c_2851,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_2850])).

tff(c_3176,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_2851])).

tff(c_3179,plain,
    ( ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v2_lattice3('#skF_7')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_3176])).

tff(c_3183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_64,c_62,c_3179])).

tff(c_3185,plain,(
    m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_2851])).

tff(c_24,plain,(
    ! [A_6,B_37,C_45] :
      ( r1_orders_2(A_6,'#skF_1'(A_6,B_37,C_45),B_37)
      | ~ m1_subset_1(C_45,u1_struct_0(A_6))
      | ~ m1_subset_1(B_37,u1_struct_0(A_6))
      | ~ v2_lattice3(A_6)
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_87,plain,
    ( r1_orders_2('#skF_7','#skF_8','#skF_8')
    | ~ l1_orders_2('#skF_7')
    | ~ v3_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_79])).

tff(c_95,plain,
    ( r1_orders_2('#skF_7','#skF_8','#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_66,c_87])).

tff(c_110,plain,(
    r1_orders_2('#skF_7','#skF_8','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_95])).

tff(c_2047,plain,(
    ! [B_353] :
      ( k10_lattice3('#skF_7',B_353,'#skF_8') = '#skF_8'
      | ~ r1_orders_2('#skF_7',B_353,'#skF_8')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_353,u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ v1_lattice3('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_110,c_2034])).

tff(c_2057,plain,(
    ! [B_353] :
      ( k10_lattice3('#skF_7',B_353,'#skF_8') = '#skF_8'
      | ~ r1_orders_2('#skF_7',B_353,'#skF_8')
      | ~ m1_subset_1(B_353,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_2047])).

tff(c_2058,plain,(
    ! [B_353] :
      ( k10_lattice3('#skF_7',B_353,'#skF_8') = '#skF_8'
      | ~ r1_orders_2('#skF_7',B_353,'#skF_8')
      | ~ m1_subset_1(B_353,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_2057])).

tff(c_3305,plain,
    ( k10_lattice3('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_8') = '#skF_8'
    | ~ r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_3185,c_2058])).

tff(c_4182,plain,(
    ~ r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_3305])).

tff(c_4185,plain,
    ( ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v2_lattice3('#skF_7')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_4182])).

tff(c_4189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_64,c_62,c_4185])).

tff(c_4191,plain,(
    r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_3305])).

tff(c_3184,plain,(
    r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_2851])).

tff(c_48,plain,(
    ! [A_109,B_133,C_145,D_151] :
      ( m1_subset_1('#skF_6'(A_109,B_133,C_145,D_151),u1_struct_0(A_109))
      | k11_lattice3(A_109,B_133,C_145) = D_151
      | ~ r1_orders_2(A_109,D_151,C_145)
      | ~ r1_orders_2(A_109,D_151,B_133)
      | ~ m1_subset_1(D_151,u1_struct_0(A_109))
      | ~ m1_subset_1(C_145,u1_struct_0(A_109))
      | ~ m1_subset_1(B_133,u1_struct_0(A_109))
      | ~ l1_orders_2(A_109)
      | ~ v2_lattice3(A_109)
      | ~ v5_orders_2(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2210,plain,(
    ! [C_45] :
      ( k10_lattice3('#skF_7','#skF_1'('#skF_7','#skF_9',C_45),'#skF_9') = '#skF_9'
      | ~ m1_subset_1(C_45,u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
      | ~ v2_lattice3('#skF_7')
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_24,c_2206])).

tff(c_2221,plain,(
    ! [C_363] :
      ( k10_lattice3('#skF_7','#skF_1'('#skF_7','#skF_9',C_363),'#skF_9') = '#skF_9'
      | ~ m1_subset_1(C_363,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_62,c_2210])).

tff(c_2265,plain,(
    k10_lattice3('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_64,c_2221])).

tff(c_2546,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),k10_lattice3('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_9'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_9','#skF_8'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7')
    | ~ v1_lattice3('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2265,c_40])).

tff(c_2552,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_9','#skF_8'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_62,c_62,c_2265,c_2546])).

tff(c_2553,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_9','#skF_8'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_2552])).

tff(c_2890,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7','#skF_9','#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_2553])).

tff(c_2893,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ v2_lattice3('#skF_7')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_2890])).

tff(c_2897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_62,c_64,c_2893])).

tff(c_2899,plain,(
    m1_subset_1('#skF_1'('#skF_7','#skF_9','#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_2553])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( r1_orders_2(A_1,B_3,B_3)
      | ~ m1_subset_1(B_3,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3299,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_1'('#skF_7','#skF_8','#skF_9'))
    | ~ l1_orders_2('#skF_7')
    | ~ v3_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_3185,c_2])).

tff(c_3358,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_1'('#skF_7','#skF_8','#skF_9'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_66,c_3299])).

tff(c_3359,plain,(
    r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_1'('#skF_7','#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_3358])).

tff(c_3019,plain,
    ( k10_lattice3('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_8') = '#skF_8'
    | ~ r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_2899,c_2058])).

tff(c_4320,plain,(
    ~ r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_3019])).

tff(c_4323,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ v2_lattice3('#skF_7')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_22,c_4320])).

tff(c_4327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_62,c_64,c_4323])).

tff(c_4329,plain,(
    r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_3019])).

tff(c_2898,plain,(
    r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_2553])).

tff(c_20,plain,(
    ! [A_6,E_50,B_37,C_45] :
      ( r1_orders_2(A_6,E_50,'#skF_1'(A_6,B_37,C_45))
      | ~ r1_orders_2(A_6,E_50,C_45)
      | ~ r1_orders_2(A_6,E_50,B_37)
      | ~ m1_subset_1(E_50,u1_struct_0(A_6))
      | ~ m1_subset_1(C_45,u1_struct_0(A_6))
      | ~ m1_subset_1(B_37,u1_struct_0(A_6))
      | ~ v2_lattice3(A_6)
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2000,plain,(
    ! [A_63,B_87,D_105] :
      ( k10_lattice3(A_63,B_87,D_105) = D_105
      | ~ r1_orders_2(A_63,D_105,D_105)
      | ~ r1_orders_2(A_63,B_87,D_105)
      | ~ m1_subset_1(D_105,u1_struct_0(A_63))
      | ~ m1_subset_1(B_87,u1_struct_0(A_63))
      | ~ l1_orders_2(A_63)
      | ~ v1_lattice3(A_63)
      | ~ v5_orders_2(A_63)
      | v2_struct_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_30,c_1991])).

tff(c_3361,plain,(
    ! [B_87] :
      ( k10_lattice3('#skF_7',B_87,'#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_1'('#skF_7','#skF_8','#skF_9')
      | ~ r1_orders_2('#skF_7',B_87,'#skF_1'('#skF_7','#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ v1_lattice3('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3359,c_2000])).

tff(c_3366,plain,(
    ! [B_87] :
      ( k10_lattice3('#skF_7',B_87,'#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_1'('#skF_7','#skF_8','#skF_9')
      | ~ r1_orders_2('#skF_7',B_87,'#skF_1'('#skF_7','#skF_8','#skF_9'))
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_3185,c_3361])).

tff(c_8751,plain,(
    ! [B_483] :
      ( k10_lattice3('#skF_7',B_483,'#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_1'('#skF_7','#skF_8','#skF_9')
      | ~ r1_orders_2('#skF_7',B_483,'#skF_1'('#skF_7','#skF_8','#skF_9'))
      | ~ m1_subset_1(B_483,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_3366])).

tff(c_8772,plain,(
    ! [E_50] :
      ( k10_lattice3('#skF_7',E_50,'#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_1'('#skF_7','#skF_8','#skF_9')
      | ~ r1_orders_2('#skF_7',E_50,'#skF_9')
      | ~ r1_orders_2('#skF_7',E_50,'#skF_8')
      | ~ m1_subset_1(E_50,u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
      | ~ v2_lattice3('#skF_7')
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_20,c_8751])).

tff(c_17470,plain,(
    ! [E_635] :
      ( k10_lattice3('#skF_7',E_635,'#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_1'('#skF_7','#skF_8','#skF_9')
      | ~ r1_orders_2('#skF_7',E_635,'#skF_9')
      | ~ r1_orders_2('#skF_7',E_635,'#skF_8')
      | ~ m1_subset_1(E_635,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_64,c_62,c_8772])).

tff(c_17500,plain,
    ( k10_lattice3('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_1'('#skF_7','#skF_8','#skF_9')
    | ~ r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_9')
    | ~ r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_2899,c_17470])).

tff(c_17560,plain,(
    k10_lattice3('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_1'('#skF_7','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4329,c_2898,c_17500])).

tff(c_17608,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),k10_lattice3('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_1'('#skF_7','#skF_8','#skF_9')))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_9','#skF_8'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7')
    | ~ v1_lattice3('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_17560,c_40])).

tff(c_17617,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_1'('#skF_7','#skF_8','#skF_9'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_2899,c_3185,c_3185,c_17560,c_17608])).

tff(c_17618,plain,(
    r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_1'('#skF_7','#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_17617])).

tff(c_32,plain,(
    ! [A_63,B_87,C_99,D_105] :
      ( r1_orders_2(A_63,B_87,'#skF_5'(A_63,B_87,C_99,D_105))
      | k10_lattice3(A_63,B_87,C_99) = D_105
      | ~ r1_orders_2(A_63,C_99,D_105)
      | ~ r1_orders_2(A_63,B_87,D_105)
      | ~ m1_subset_1(D_105,u1_struct_0(A_63))
      | ~ m1_subset_1(C_99,u1_struct_0(A_63))
      | ~ m1_subset_1(B_87,u1_struct_0(A_63))
      | ~ l1_orders_2(A_63)
      | ~ v1_lattice3(A_63)
      | ~ v5_orders_2(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2001,plain,(
    ! [A_63,D_105,C_99] :
      ( k10_lattice3(A_63,D_105,C_99) = D_105
      | ~ r1_orders_2(A_63,C_99,D_105)
      | ~ r1_orders_2(A_63,D_105,D_105)
      | ~ m1_subset_1(C_99,u1_struct_0(A_63))
      | ~ m1_subset_1(D_105,u1_struct_0(A_63))
      | ~ l1_orders_2(A_63)
      | ~ v1_lattice3(A_63)
      | ~ v5_orders_2(A_63)
      | v2_struct_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_32,c_1991])).

tff(c_17634,plain,
    ( k10_lattice3('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_1'('#skF_7','#skF_9','#skF_8')) = '#skF_1'('#skF_7','#skF_8','#skF_9')
    | ~ r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_1'('#skF_7','#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_9','#skF_8'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7')
    | ~ v1_lattice3('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_17618,c_2001])).

tff(c_17653,plain,
    ( k10_lattice3('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_1'('#skF_7','#skF_9','#skF_8')) = '#skF_1'('#skF_7','#skF_8','#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_3185,c_2899,c_3359,c_17634])).

tff(c_17654,plain,(
    k10_lattice3('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_1'('#skF_7','#skF_9','#skF_8')) = '#skF_1'('#skF_7','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_17653])).

tff(c_3013,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_1'('#skF_7','#skF_9','#skF_8'))
    | ~ l1_orders_2('#skF_7')
    | ~ v3_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2899,c_2])).

tff(c_3072,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_1'('#skF_7','#skF_9','#skF_8'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_66,c_3013])).

tff(c_3073,plain,(
    r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_1'('#skF_7','#skF_9','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_3072])).

tff(c_3111,plain,(
    ! [B_87] :
      ( k10_lattice3('#skF_7',B_87,'#skF_1'('#skF_7','#skF_9','#skF_8')) = '#skF_1'('#skF_7','#skF_9','#skF_8')
      | ~ r1_orders_2('#skF_7',B_87,'#skF_1'('#skF_7','#skF_9','#skF_8'))
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_9','#skF_8'),u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ v1_lattice3('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3073,c_2000])).

tff(c_3116,plain,(
    ! [B_87] :
      ( k10_lattice3('#skF_7',B_87,'#skF_1'('#skF_7','#skF_9','#skF_8')) = '#skF_1'('#skF_7','#skF_9','#skF_8')
      | ~ r1_orders_2('#skF_7',B_87,'#skF_1'('#skF_7','#skF_9','#skF_8'))
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_2899,c_3111])).

tff(c_8071,plain,(
    ! [B_468] :
      ( k10_lattice3('#skF_7',B_468,'#skF_1'('#skF_7','#skF_9','#skF_8')) = '#skF_1'('#skF_7','#skF_9','#skF_8')
      | ~ r1_orders_2('#skF_7',B_468,'#skF_1'('#skF_7','#skF_9','#skF_8'))
      | ~ m1_subset_1(B_468,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_3116])).

tff(c_8092,plain,(
    ! [E_50] :
      ( k10_lattice3('#skF_7',E_50,'#skF_1'('#skF_7','#skF_9','#skF_8')) = '#skF_1'('#skF_7','#skF_9','#skF_8')
      | ~ r1_orders_2('#skF_7',E_50,'#skF_8')
      | ~ r1_orders_2('#skF_7',E_50,'#skF_9')
      | ~ m1_subset_1(E_50,u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
      | ~ v2_lattice3('#skF_7')
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_20,c_8071])).

tff(c_17801,plain,(
    ! [E_640] :
      ( k10_lattice3('#skF_7',E_640,'#skF_1'('#skF_7','#skF_9','#skF_8')) = '#skF_1'('#skF_7','#skF_9','#skF_8')
      | ~ r1_orders_2('#skF_7',E_640,'#skF_8')
      | ~ r1_orders_2('#skF_7',E_640,'#skF_9')
      | ~ m1_subset_1(E_640,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_62,c_64,c_8092])).

tff(c_17828,plain,
    ( k10_lattice3('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_1'('#skF_7','#skF_9','#skF_8')) = '#skF_1'('#skF_7','#skF_9','#skF_8')
    | ~ r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_3185,c_17801])).

tff(c_17888,plain,(
    '#skF_1'('#skF_7','#skF_9','#skF_8') = '#skF_1'('#skF_7','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3184,c_4191,c_17654,c_17828])).

tff(c_44,plain,(
    ! [A_109,B_133,C_145,D_151] :
      ( r1_orders_2(A_109,'#skF_6'(A_109,B_133,C_145,D_151),C_145)
      | k11_lattice3(A_109,B_133,C_145) = D_151
      | ~ r1_orders_2(A_109,D_151,C_145)
      | ~ r1_orders_2(A_109,D_151,B_133)
      | ~ m1_subset_1(D_151,u1_struct_0(A_109))
      | ~ m1_subset_1(C_145,u1_struct_0(A_109))
      | ~ m1_subset_1(B_133,u1_struct_0(A_109))
      | ~ l1_orders_2(A_109)
      | ~ v2_lattice3(A_109)
      | ~ v5_orders_2(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_46,plain,(
    ! [A_109,B_133,C_145,D_151] :
      ( r1_orders_2(A_109,'#skF_6'(A_109,B_133,C_145,D_151),B_133)
      | k11_lattice3(A_109,B_133,C_145) = D_151
      | ~ r1_orders_2(A_109,D_151,C_145)
      | ~ r1_orders_2(A_109,D_151,B_133)
      | ~ m1_subset_1(D_151,u1_struct_0(A_109))
      | ~ m1_subset_1(C_145,u1_struct_0(A_109))
      | ~ m1_subset_1(B_133,u1_struct_0(A_109))
      | ~ l1_orders_2(A_109)
      | ~ v2_lattice3(A_109)
      | ~ v5_orders_2(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1042,plain,(
    ! [A_268,B_269,C_270,D_271] :
      ( ~ r1_orders_2(A_268,'#skF_6'(A_268,B_269,C_270,D_271),D_271)
      | k11_lattice3(A_268,B_269,C_270) = D_271
      | ~ r1_orders_2(A_268,D_271,C_270)
      | ~ r1_orders_2(A_268,D_271,B_269)
      | ~ m1_subset_1(D_271,u1_struct_0(A_268))
      | ~ m1_subset_1(C_270,u1_struct_0(A_268))
      | ~ m1_subset_1(B_269,u1_struct_0(A_268))
      | ~ l1_orders_2(A_268)
      | ~ v2_lattice3(A_268)
      | ~ v5_orders_2(A_268)
      | v2_struct_0(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_5167,plain,(
    ! [A_427,B_425,C_424,C_428,B_426] :
      ( k11_lattice3(A_427,B_425,C_428) = '#skF_1'(A_427,B_426,C_424)
      | ~ r1_orders_2(A_427,'#skF_1'(A_427,B_426,C_424),C_428)
      | ~ r1_orders_2(A_427,'#skF_1'(A_427,B_426,C_424),B_425)
      | ~ m1_subset_1('#skF_1'(A_427,B_426,C_424),u1_struct_0(A_427))
      | ~ m1_subset_1(C_428,u1_struct_0(A_427))
      | ~ m1_subset_1(B_425,u1_struct_0(A_427))
      | ~ v5_orders_2(A_427)
      | v2_struct_0(A_427)
      | ~ r1_orders_2(A_427,'#skF_6'(A_427,B_425,C_428,'#skF_1'(A_427,B_426,C_424)),C_424)
      | ~ r1_orders_2(A_427,'#skF_6'(A_427,B_425,C_428,'#skF_1'(A_427,B_426,C_424)),B_426)
      | ~ m1_subset_1('#skF_6'(A_427,B_425,C_428,'#skF_1'(A_427,B_426,C_424)),u1_struct_0(A_427))
      | ~ m1_subset_1(C_424,u1_struct_0(A_427))
      | ~ m1_subset_1(B_426,u1_struct_0(A_427))
      | ~ v2_lattice3(A_427)
      | ~ l1_orders_2(A_427) ) ),
    inference(resolution,[status(thm)],[c_20,c_1042])).

tff(c_23380,plain,(
    ! [A_818,B_819,C_820,B_821] :
      ( ~ r1_orders_2(A_818,'#skF_6'(A_818,B_819,C_820,'#skF_1'(A_818,B_821,B_819)),B_821)
      | ~ m1_subset_1('#skF_6'(A_818,B_819,C_820,'#skF_1'(A_818,B_821,B_819)),u1_struct_0(A_818))
      | ~ m1_subset_1(B_821,u1_struct_0(A_818))
      | k11_lattice3(A_818,B_819,C_820) = '#skF_1'(A_818,B_821,B_819)
      | ~ r1_orders_2(A_818,'#skF_1'(A_818,B_821,B_819),C_820)
      | ~ r1_orders_2(A_818,'#skF_1'(A_818,B_821,B_819),B_819)
      | ~ m1_subset_1('#skF_1'(A_818,B_821,B_819),u1_struct_0(A_818))
      | ~ m1_subset_1(C_820,u1_struct_0(A_818))
      | ~ m1_subset_1(B_819,u1_struct_0(A_818))
      | ~ l1_orders_2(A_818)
      | ~ v2_lattice3(A_818)
      | ~ v5_orders_2(A_818)
      | v2_struct_0(A_818) ) ),
    inference(resolution,[status(thm)],[c_46,c_5167])).

tff(c_51230,plain,(
    ! [A_1211,B_1212,C_1213] :
      ( ~ m1_subset_1('#skF_6'(A_1211,B_1212,C_1213,'#skF_1'(A_1211,C_1213,B_1212)),u1_struct_0(A_1211))
      | k11_lattice3(A_1211,B_1212,C_1213) = '#skF_1'(A_1211,C_1213,B_1212)
      | ~ r1_orders_2(A_1211,'#skF_1'(A_1211,C_1213,B_1212),C_1213)
      | ~ r1_orders_2(A_1211,'#skF_1'(A_1211,C_1213,B_1212),B_1212)
      | ~ m1_subset_1('#skF_1'(A_1211,C_1213,B_1212),u1_struct_0(A_1211))
      | ~ m1_subset_1(C_1213,u1_struct_0(A_1211))
      | ~ m1_subset_1(B_1212,u1_struct_0(A_1211))
      | ~ l1_orders_2(A_1211)
      | ~ v2_lattice3(A_1211)
      | ~ v5_orders_2(A_1211)
      | v2_struct_0(A_1211) ) ),
    inference(resolution,[status(thm)],[c_44,c_23380])).

tff(c_51233,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')),u1_struct_0('#skF_7'))
    | k11_lattice3('#skF_7','#skF_8','#skF_9') = '#skF_1'('#skF_7','#skF_9','#skF_8')
    | ~ r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_9')
    | ~ r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_9','#skF_8'),'#skF_8')
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_9','#skF_8'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7')
    | ~ v2_lattice3('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_17888,c_51230])).

tff(c_51245,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')),u1_struct_0('#skF_7'))
    | k11_lattice3('#skF_7','#skF_8','#skF_9') = '#skF_1'('#skF_7','#skF_8','#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_64,c_62,c_3185,c_17888,c_4191,c_17888,c_3184,c_17888,c_17888,c_51233])).

tff(c_51246,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')),u1_struct_0('#skF_7'))
    | k11_lattice3('#skF_7','#skF_8','#skF_9') = '#skF_1'('#skF_7','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_51245])).

tff(c_51254,plain,(
    ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_51246])).

tff(c_51257,plain,
    ( k11_lattice3('#skF_7','#skF_8','#skF_9') = '#skF_1'('#skF_7','#skF_8','#skF_9')
    | ~ r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_9')
    | ~ r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7')
    | ~ v2_lattice3('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_51254])).

tff(c_51260,plain,
    ( k11_lattice3('#skF_7','#skF_8','#skF_9') = '#skF_1'('#skF_7','#skF_8','#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_64,c_62,c_3185,c_4191,c_3184,c_51257])).

tff(c_51261,plain,(
    k11_lattice3('#skF_7','#skF_8','#skF_9') = '#skF_1'('#skF_7','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_51260])).

tff(c_168,plain,(
    ! [A_186,B_187,C_188] :
      ( k12_lattice3(A_186,B_187,C_188) = k11_lattice3(A_186,B_187,C_188)
      | ~ m1_subset_1(C_188,u1_struct_0(A_186))
      | ~ m1_subset_1(B_187,u1_struct_0(A_186))
      | ~ l1_orders_2(A_186)
      | ~ v2_lattice3(A_186)
      | ~ v5_orders_2(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_176,plain,(
    ! [B_187] :
      ( k12_lattice3('#skF_7',B_187,'#skF_9') = k11_lattice3('#skF_7',B_187,'#skF_9')
      | ~ m1_subset_1(B_187,u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ v2_lattice3('#skF_7')
      | ~ v5_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_62,c_168])).

tff(c_272,plain,(
    ! [B_191] :
      ( k12_lattice3('#skF_7',B_191,'#skF_9') = k11_lattice3('#skF_7',B_191,'#skF_9')
      | ~ m1_subset_1(B_191,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_176])).

tff(c_301,plain,(
    k12_lattice3('#skF_7','#skF_8','#skF_9') = k11_lattice3('#skF_7','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_64,c_272])).

tff(c_60,plain,(
    k13_lattice3('#skF_7',k12_lattice3('#skF_7','#skF_8','#skF_9'),'#skF_9') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_307,plain,(
    k13_lattice3('#skF_7',k11_lattice3('#skF_7','#skF_8','#skF_9'),'#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_60])).

tff(c_51278,plain,(
    k13_lattice3('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51261,c_307])).

tff(c_51282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2841,c_51278])).

tff(c_51283,plain,(
    k11_lattice3('#skF_7','#skF_8','#skF_9') = '#skF_1'('#skF_7','#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_51246])).

tff(c_51285,plain,(
    k13_lattice3('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51283,c_307])).

tff(c_51289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2841,c_51285])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:56:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 34.30/22.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.30/22.92  
% 34.30/22.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.37/22.92  %$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_4
% 34.37/22.92  
% 34.37/22.92  %Foreground sorts:
% 34.37/22.92  
% 34.37/22.92  
% 34.37/22.92  %Background operators:
% 34.37/22.92  
% 34.37/22.92  
% 34.37/22.92  %Foreground operators:
% 34.37/22.92  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 34.37/22.92  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 34.37/22.92  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 34.37/22.92  tff('#skF_2', type, '#skF_2': $i > $i).
% 34.37/22.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 34.37/22.92  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 34.37/22.92  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 34.37/22.92  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 34.37/22.92  tff('#skF_7', type, '#skF_7': $i).
% 34.37/22.92  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 34.37/22.92  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 34.37/22.92  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 34.37/22.92  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 34.37/22.92  tff('#skF_9', type, '#skF_9': $i).
% 34.37/22.92  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 34.37/22.92  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 34.37/22.92  tff('#skF_8', type, '#skF_8': $i).
% 34.37/22.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 34.37/22.92  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 34.37/22.92  tff('#skF_3', type, '#skF_3': $i > $i).
% 34.37/22.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 34.37/22.92  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 34.37/22.92  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 34.37/22.92  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 34.37/22.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 34.37/22.92  
% 34.37/22.95  tff(f_186, negated_conjecture, ~(![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k13_lattice3(A, k12_lattice3(A, B, C), C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_lattice3)).
% 34.37/22.95  tff(f_77, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (?[D]: (((m1_subset_1(D, u1_struct_0(A)) & r1_orders_2(A, D, B)) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_lattice3)).
% 34.37/22.95  tff(f_37, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 34.37/22.95  tff(f_51, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 34.37/22.95  tff(f_110, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l26_lattice3)).
% 34.37/22.95  tff(f_167, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 34.37/22.95  tff(f_143, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l28_lattice3)).
% 34.37/22.95  tff(f_155, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 34.37/22.95  tff(c_64, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 34.37/22.95  tff(c_66, plain, (l1_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_186])).
% 34.37/22.95  tff(c_68, plain, (v2_lattice3('#skF_7')), inference(cnfTransformation, [status(thm)], [f_186])).
% 34.37/22.95  tff(c_62, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 34.37/22.95  tff(c_22, plain, (![A_6, B_37, C_45]: (r1_orders_2(A_6, '#skF_1'(A_6, B_37, C_45), C_45) | ~m1_subset_1(C_45, u1_struct_0(A_6)) | ~m1_subset_1(B_37, u1_struct_0(A_6)) | ~v2_lattice3(A_6) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_77])).
% 34.37/22.95  tff(c_26, plain, (![A_6, B_37, C_45]: (m1_subset_1('#skF_1'(A_6, B_37, C_45), u1_struct_0(A_6)) | ~m1_subset_1(C_45, u1_struct_0(A_6)) | ~m1_subset_1(B_37, u1_struct_0(A_6)) | ~v2_lattice3(A_6) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_77])).
% 34.37/22.95  tff(c_74, plain, (v3_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_186])).
% 34.37/22.95  tff(c_79, plain, (![A_169, B_170]: (r1_orders_2(A_169, B_170, B_170) | ~m1_subset_1(B_170, u1_struct_0(A_169)) | ~l1_orders_2(A_169) | ~v3_orders_2(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_37])).
% 34.37/22.95  tff(c_85, plain, (r1_orders_2('#skF_7', '#skF_9', '#skF_9') | ~l1_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_62, c_79])).
% 34.37/22.95  tff(c_92, plain, (r1_orders_2('#skF_7', '#skF_9', '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_66, c_85])).
% 34.37/22.95  tff(c_96, plain, (v2_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_92])).
% 34.37/22.95  tff(c_6, plain, (![A_5]: (~v2_struct_0(A_5) | ~v2_lattice3(A_5) | ~l1_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_51])).
% 34.37/22.95  tff(c_99, plain, (~v2_lattice3('#skF_7') | ~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_96, c_6])).
% 34.37/22.95  tff(c_106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_99])).
% 34.37/22.95  tff(c_108, plain, (~v2_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_92])).
% 34.37/22.95  tff(c_72, plain, (v5_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_186])).
% 34.37/22.95  tff(c_70, plain, (v1_lattice3('#skF_7')), inference(cnfTransformation, [status(thm)], [f_186])).
% 34.37/22.95  tff(c_107, plain, (r1_orders_2('#skF_7', '#skF_9', '#skF_9')), inference(splitRight, [status(thm)], [c_92])).
% 34.37/22.95  tff(c_30, plain, (![A_63, C_99, B_87, D_105]: (r1_orders_2(A_63, C_99, '#skF_5'(A_63, B_87, C_99, D_105)) | k10_lattice3(A_63, B_87, C_99)=D_105 | ~r1_orders_2(A_63, C_99, D_105) | ~r1_orders_2(A_63, B_87, D_105) | ~m1_subset_1(D_105, u1_struct_0(A_63)) | ~m1_subset_1(C_99, u1_struct_0(A_63)) | ~m1_subset_1(B_87, u1_struct_0(A_63)) | ~l1_orders_2(A_63) | ~v1_lattice3(A_63) | ~v5_orders_2(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_110])).
% 34.37/22.95  tff(c_1991, plain, (![A_345, D_346, B_347, C_348]: (~r1_orders_2(A_345, D_346, '#skF_5'(A_345, B_347, C_348, D_346)) | k10_lattice3(A_345, B_347, C_348)=D_346 | ~r1_orders_2(A_345, C_348, D_346) | ~r1_orders_2(A_345, B_347, D_346) | ~m1_subset_1(D_346, u1_struct_0(A_345)) | ~m1_subset_1(C_348, u1_struct_0(A_345)) | ~m1_subset_1(B_347, u1_struct_0(A_345)) | ~l1_orders_2(A_345) | ~v1_lattice3(A_345) | ~v5_orders_2(A_345) | v2_struct_0(A_345))), inference(cnfTransformation, [status(thm)], [f_110])).
% 34.37/22.95  tff(c_2034, plain, (![A_352, B_353, D_354]: (k10_lattice3(A_352, B_353, D_354)=D_354 | ~r1_orders_2(A_352, D_354, D_354) | ~r1_orders_2(A_352, B_353, D_354) | ~m1_subset_1(D_354, u1_struct_0(A_352)) | ~m1_subset_1(B_353, u1_struct_0(A_352)) | ~l1_orders_2(A_352) | ~v1_lattice3(A_352) | ~v5_orders_2(A_352) | v2_struct_0(A_352))), inference(resolution, [status(thm)], [c_30, c_1991])).
% 34.37/22.95  tff(c_2049, plain, (![B_353]: (k10_lattice3('#skF_7', B_353, '#skF_9')='#skF_9' | ~r1_orders_2('#skF_7', B_353, '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_subset_1(B_353, u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v1_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_107, c_2034])).
% 34.37/22.95  tff(c_2061, plain, (![B_353]: (k10_lattice3('#skF_7', B_353, '#skF_9')='#skF_9' | ~r1_orders_2('#skF_7', B_353, '#skF_9') | ~m1_subset_1(B_353, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_62, c_2049])).
% 34.37/22.95  tff(c_2139, plain, (![B_360]: (k10_lattice3('#skF_7', B_360, '#skF_9')='#skF_9' | ~r1_orders_2('#skF_7', B_360, '#skF_9') | ~m1_subset_1(B_360, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_108, c_2061])).
% 34.37/22.95  tff(c_2151, plain, (![B_37, C_45]: (k10_lattice3('#skF_7', '#skF_1'('#skF_7', B_37, C_45), '#skF_9')='#skF_9' | ~r1_orders_2('#skF_7', '#skF_1'('#skF_7', B_37, C_45), '#skF_9') | ~m1_subset_1(C_45, u1_struct_0('#skF_7')) | ~m1_subset_1(B_37, u1_struct_0('#skF_7')) | ~v2_lattice3('#skF_7') | ~l1_orders_2('#skF_7'))), inference(resolution, [status(thm)], [c_26, c_2139])).
% 34.37/22.95  tff(c_2206, plain, (![B_361, C_362]: (k10_lattice3('#skF_7', '#skF_1'('#skF_7', B_361, C_362), '#skF_9')='#skF_9' | ~r1_orders_2('#skF_7', '#skF_1'('#skF_7', B_361, C_362), '#skF_9') | ~m1_subset_1(C_362, u1_struct_0('#skF_7')) | ~m1_subset_1(B_361, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_2151])).
% 34.37/22.95  tff(c_2214, plain, (![B_37]: (k10_lattice3('#skF_7', '#skF_1'('#skF_7', B_37, '#skF_9'), '#skF_9')='#skF_9' | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_subset_1(B_37, u1_struct_0('#skF_7')) | ~v2_lattice3('#skF_7') | ~l1_orders_2('#skF_7'))), inference(resolution, [status(thm)], [c_22, c_2206])).
% 34.37/22.95  tff(c_2783, plain, (![B_372]: (k10_lattice3('#skF_7', '#skF_1'('#skF_7', B_372, '#skF_9'), '#skF_9')='#skF_9' | ~m1_subset_1(B_372, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_62, c_2214])).
% 34.37/22.95  tff(c_2840, plain, (k10_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_64, c_2783])).
% 34.37/22.95  tff(c_118, plain, (![A_182, B_183, C_184]: (k13_lattice3(A_182, B_183, C_184)=k10_lattice3(A_182, B_183, C_184) | ~m1_subset_1(C_184, u1_struct_0(A_182)) | ~m1_subset_1(B_183, u1_struct_0(A_182)) | ~l1_orders_2(A_182) | ~v1_lattice3(A_182) | ~v5_orders_2(A_182))), inference(cnfTransformation, [status(thm)], [f_167])).
% 34.37/22.95  tff(c_126, plain, (![B_183]: (k13_lattice3('#skF_7', B_183, '#skF_9')=k10_lattice3('#skF_7', B_183, '#skF_9') | ~m1_subset_1(B_183, u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v1_lattice3('#skF_7') | ~v5_orders_2('#skF_7'))), inference(resolution, [status(thm)], [c_62, c_118])).
% 34.37/22.95  tff(c_138, plain, (![B_185]: (k13_lattice3('#skF_7', B_185, '#skF_9')=k10_lattice3('#skF_7', B_185, '#skF_9') | ~m1_subset_1(B_185, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_126])).
% 34.37/22.95  tff(c_142, plain, (![B_37, C_45]: (k13_lattice3('#skF_7', '#skF_1'('#skF_7', B_37, C_45), '#skF_9')=k10_lattice3('#skF_7', '#skF_1'('#skF_7', B_37, C_45), '#skF_9') | ~m1_subset_1(C_45, u1_struct_0('#skF_7')) | ~m1_subset_1(B_37, u1_struct_0('#skF_7')) | ~v2_lattice3('#skF_7') | ~l1_orders_2('#skF_7'))), inference(resolution, [status(thm)], [c_26, c_138])).
% 34.37/22.95  tff(c_823, plain, (![B_225, C_226]: (k13_lattice3('#skF_7', '#skF_1'('#skF_7', B_225, C_226), '#skF_9')=k10_lattice3('#skF_7', '#skF_1'('#skF_7', B_225, C_226), '#skF_9') | ~m1_subset_1(C_226, u1_struct_0('#skF_7')) | ~m1_subset_1(B_225, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_142])).
% 34.37/22.95  tff(c_854, plain, (![B_227]: (k13_lattice3('#skF_7', '#skF_1'('#skF_7', B_227, '#skF_9'), '#skF_9')=k10_lattice3('#skF_7', '#skF_1'('#skF_7', B_227, '#skF_9'), '#skF_9') | ~m1_subset_1(B_227, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_62, c_823])).
% 34.37/22.95  tff(c_890, plain, (k13_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')=k10_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')), inference(resolution, [status(thm)], [c_64, c_854])).
% 34.37/22.95  tff(c_2841, plain, (k13_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2840, c_890])).
% 34.37/22.95  tff(c_40, plain, (![A_63, B_87, C_99]: (r1_orders_2(A_63, B_87, k10_lattice3(A_63, B_87, C_99)) | ~m1_subset_1(k10_lattice3(A_63, B_87, C_99), u1_struct_0(A_63)) | ~m1_subset_1(C_99, u1_struct_0(A_63)) | ~m1_subset_1(B_87, u1_struct_0(A_63)) | ~l1_orders_2(A_63) | ~v1_lattice3(A_63) | ~v5_orders_2(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_110])).
% 34.37/22.95  tff(c_2844, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), k10_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v1_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2840, c_40])).
% 34.37/22.95  tff(c_2850, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_62, c_62, c_2840, c_2844])).
% 34.37/22.95  tff(c_2851, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_108, c_2850])).
% 34.37/22.95  tff(c_3176, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_2851])).
% 34.37/22.95  tff(c_3179, plain, (~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v2_lattice3('#skF_7') | ~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_26, c_3176])).
% 34.37/22.95  tff(c_3183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_64, c_62, c_3179])).
% 34.37/22.95  tff(c_3185, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_2851])).
% 34.37/22.95  tff(c_24, plain, (![A_6, B_37, C_45]: (r1_orders_2(A_6, '#skF_1'(A_6, B_37, C_45), B_37) | ~m1_subset_1(C_45, u1_struct_0(A_6)) | ~m1_subset_1(B_37, u1_struct_0(A_6)) | ~v2_lattice3(A_6) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_77])).
% 34.37/22.95  tff(c_87, plain, (r1_orders_2('#skF_7', '#skF_8', '#skF_8') | ~l1_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_64, c_79])).
% 34.37/22.95  tff(c_95, plain, (r1_orders_2('#skF_7', '#skF_8', '#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_66, c_87])).
% 34.37/22.95  tff(c_110, plain, (r1_orders_2('#skF_7', '#skF_8', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_108, c_95])).
% 34.37/22.95  tff(c_2047, plain, (![B_353]: (k10_lattice3('#skF_7', B_353, '#skF_8')='#skF_8' | ~r1_orders_2('#skF_7', B_353, '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1(B_353, u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v1_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_110, c_2034])).
% 34.37/22.95  tff(c_2057, plain, (![B_353]: (k10_lattice3('#skF_7', B_353, '#skF_8')='#skF_8' | ~r1_orders_2('#skF_7', B_353, '#skF_8') | ~m1_subset_1(B_353, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_2047])).
% 34.37/22.95  tff(c_2058, plain, (![B_353]: (k10_lattice3('#skF_7', B_353, '#skF_8')='#skF_8' | ~r1_orders_2('#skF_7', B_353, '#skF_8') | ~m1_subset_1(B_353, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_108, c_2057])).
% 34.37/22.95  tff(c_3305, plain, (k10_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')='#skF_8' | ~r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_3185, c_2058])).
% 34.37/22.95  tff(c_4182, plain, (~r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_3305])).
% 34.37/22.95  tff(c_4185, plain, (~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v2_lattice3('#skF_7') | ~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_24, c_4182])).
% 34.37/22.95  tff(c_4189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_64, c_62, c_4185])).
% 34.37/22.95  tff(c_4191, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_3305])).
% 34.37/22.95  tff(c_3184, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')), inference(splitRight, [status(thm)], [c_2851])).
% 34.37/22.95  tff(c_48, plain, (![A_109, B_133, C_145, D_151]: (m1_subset_1('#skF_6'(A_109, B_133, C_145, D_151), u1_struct_0(A_109)) | k11_lattice3(A_109, B_133, C_145)=D_151 | ~r1_orders_2(A_109, D_151, C_145) | ~r1_orders_2(A_109, D_151, B_133) | ~m1_subset_1(D_151, u1_struct_0(A_109)) | ~m1_subset_1(C_145, u1_struct_0(A_109)) | ~m1_subset_1(B_133, u1_struct_0(A_109)) | ~l1_orders_2(A_109) | ~v2_lattice3(A_109) | ~v5_orders_2(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_143])).
% 34.37/22.95  tff(c_2210, plain, (![C_45]: (k10_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_9', C_45), '#skF_9')='#skF_9' | ~m1_subset_1(C_45, u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~v2_lattice3('#skF_7') | ~l1_orders_2('#skF_7'))), inference(resolution, [status(thm)], [c_24, c_2206])).
% 34.37/22.95  tff(c_2221, plain, (![C_363]: (k10_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_9', C_363), '#skF_9')='#skF_9' | ~m1_subset_1(C_363, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_62, c_2210])).
% 34.37/22.95  tff(c_2265, plain, (k10_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_64, c_2221])).
% 34.37/22.95  tff(c_2546, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), k10_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_9')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_9', '#skF_8'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v1_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2265, c_40])).
% 34.37/22.95  tff(c_2552, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_9') | ~m1_subset_1('#skF_1'('#skF_7', '#skF_9', '#skF_8'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_62, c_62, c_2265, c_2546])).
% 34.37/22.95  tff(c_2553, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_9') | ~m1_subset_1('#skF_1'('#skF_7', '#skF_9', '#skF_8'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_108, c_2552])).
% 34.37/22.95  tff(c_2890, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_9', '#skF_8'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_2553])).
% 34.37/22.95  tff(c_2893, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~v2_lattice3('#skF_7') | ~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_26, c_2890])).
% 34.37/22.95  tff(c_2897, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_62, c_64, c_2893])).
% 34.37/22.95  tff(c_2899, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_9', '#skF_8'), u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_2553])).
% 34.37/22.95  tff(c_2, plain, (![A_1, B_3]: (r1_orders_2(A_1, B_3, B_3) | ~m1_subset_1(B_3, u1_struct_0(A_1)) | ~l1_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 34.37/22.95  tff(c_3299, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'('#skF_7', '#skF_8', '#skF_9')) | ~l1_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_3185, c_2])).
% 34.37/22.95  tff(c_3358, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'('#skF_7', '#skF_8', '#skF_9')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_66, c_3299])).
% 34.37/22.95  tff(c_3359, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'('#skF_7', '#skF_8', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_108, c_3358])).
% 34.37/22.95  tff(c_3019, plain, (k10_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_8')='#skF_8' | ~r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_8')), inference(resolution, [status(thm)], [c_2899, c_2058])).
% 34.37/22.95  tff(c_4320, plain, (~r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_8')), inference(splitLeft, [status(thm)], [c_3019])).
% 34.37/22.95  tff(c_4323, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~v2_lattice3('#skF_7') | ~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_22, c_4320])).
% 34.37/22.95  tff(c_4327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_62, c_64, c_4323])).
% 34.37/22.95  tff(c_4329, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_8')), inference(splitRight, [status(thm)], [c_3019])).
% 34.37/22.95  tff(c_2898, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_9')), inference(splitRight, [status(thm)], [c_2553])).
% 34.37/22.95  tff(c_20, plain, (![A_6, E_50, B_37, C_45]: (r1_orders_2(A_6, E_50, '#skF_1'(A_6, B_37, C_45)) | ~r1_orders_2(A_6, E_50, C_45) | ~r1_orders_2(A_6, E_50, B_37) | ~m1_subset_1(E_50, u1_struct_0(A_6)) | ~m1_subset_1(C_45, u1_struct_0(A_6)) | ~m1_subset_1(B_37, u1_struct_0(A_6)) | ~v2_lattice3(A_6) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_77])).
% 34.37/22.95  tff(c_2000, plain, (![A_63, B_87, D_105]: (k10_lattice3(A_63, B_87, D_105)=D_105 | ~r1_orders_2(A_63, D_105, D_105) | ~r1_orders_2(A_63, B_87, D_105) | ~m1_subset_1(D_105, u1_struct_0(A_63)) | ~m1_subset_1(B_87, u1_struct_0(A_63)) | ~l1_orders_2(A_63) | ~v1_lattice3(A_63) | ~v5_orders_2(A_63) | v2_struct_0(A_63))), inference(resolution, [status(thm)], [c_30, c_1991])).
% 34.37/22.95  tff(c_3361, plain, (![B_87]: (k10_lattice3('#skF_7', B_87, '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_1'('#skF_7', '#skF_8', '#skF_9') | ~r1_orders_2('#skF_7', B_87, '#skF_1'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~m1_subset_1(B_87, u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v1_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_3359, c_2000])).
% 34.37/22.95  tff(c_3366, plain, (![B_87]: (k10_lattice3('#skF_7', B_87, '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_1'('#skF_7', '#skF_8', '#skF_9') | ~r1_orders_2('#skF_7', B_87, '#skF_1'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1(B_87, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_3185, c_3361])).
% 34.37/22.95  tff(c_8751, plain, (![B_483]: (k10_lattice3('#skF_7', B_483, '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_1'('#skF_7', '#skF_8', '#skF_9') | ~r1_orders_2('#skF_7', B_483, '#skF_1'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1(B_483, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_108, c_3366])).
% 34.37/22.95  tff(c_8772, plain, (![E_50]: (k10_lattice3('#skF_7', E_50, '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_1'('#skF_7', '#skF_8', '#skF_9') | ~r1_orders_2('#skF_7', E_50, '#skF_9') | ~r1_orders_2('#skF_7', E_50, '#skF_8') | ~m1_subset_1(E_50, u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v2_lattice3('#skF_7') | ~l1_orders_2('#skF_7'))), inference(resolution, [status(thm)], [c_20, c_8751])).
% 34.37/22.95  tff(c_17470, plain, (![E_635]: (k10_lattice3('#skF_7', E_635, '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_1'('#skF_7', '#skF_8', '#skF_9') | ~r1_orders_2('#skF_7', E_635, '#skF_9') | ~r1_orders_2('#skF_7', E_635, '#skF_8') | ~m1_subset_1(E_635, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_64, c_62, c_8772])).
% 34.37/22.95  tff(c_17500, plain, (k10_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_1'('#skF_7', '#skF_8', '#skF_9') | ~r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_9') | ~r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_8')), inference(resolution, [status(thm)], [c_2899, c_17470])).
% 34.37/22.95  tff(c_17560, plain, (k10_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_1'('#skF_7', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4329, c_2898, c_17500])).
% 34.37/22.95  tff(c_17608, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), k10_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_1'('#skF_7', '#skF_8', '#skF_9'))) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_9', '#skF_8'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v1_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_17560, c_40])).
% 34.37/22.95  tff(c_17617, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_1'('#skF_7', '#skF_8', '#skF_9')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_2899, c_3185, c_3185, c_17560, c_17608])).
% 34.37/22.95  tff(c_17618, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_1'('#skF_7', '#skF_8', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_108, c_17617])).
% 34.37/22.95  tff(c_32, plain, (![A_63, B_87, C_99, D_105]: (r1_orders_2(A_63, B_87, '#skF_5'(A_63, B_87, C_99, D_105)) | k10_lattice3(A_63, B_87, C_99)=D_105 | ~r1_orders_2(A_63, C_99, D_105) | ~r1_orders_2(A_63, B_87, D_105) | ~m1_subset_1(D_105, u1_struct_0(A_63)) | ~m1_subset_1(C_99, u1_struct_0(A_63)) | ~m1_subset_1(B_87, u1_struct_0(A_63)) | ~l1_orders_2(A_63) | ~v1_lattice3(A_63) | ~v5_orders_2(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_110])).
% 34.37/22.95  tff(c_2001, plain, (![A_63, D_105, C_99]: (k10_lattice3(A_63, D_105, C_99)=D_105 | ~r1_orders_2(A_63, C_99, D_105) | ~r1_orders_2(A_63, D_105, D_105) | ~m1_subset_1(C_99, u1_struct_0(A_63)) | ~m1_subset_1(D_105, u1_struct_0(A_63)) | ~l1_orders_2(A_63) | ~v1_lattice3(A_63) | ~v5_orders_2(A_63) | v2_struct_0(A_63))), inference(resolution, [status(thm)], [c_32, c_1991])).
% 34.37/22.95  tff(c_17634, plain, (k10_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'('#skF_7', '#skF_9', '#skF_8'))='#skF_1'('#skF_7', '#skF_8', '#skF_9') | ~r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_9', '#skF_8'), u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v1_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_17618, c_2001])).
% 34.37/22.95  tff(c_17653, plain, (k10_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'('#skF_7', '#skF_9', '#skF_8'))='#skF_1'('#skF_7', '#skF_8', '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_3185, c_2899, c_3359, c_17634])).
% 34.37/22.95  tff(c_17654, plain, (k10_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'('#skF_7', '#skF_9', '#skF_8'))='#skF_1'('#skF_7', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_108, c_17653])).
% 34.37/22.95  tff(c_3013, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_1'('#skF_7', '#skF_9', '#skF_8')) | ~l1_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_2899, c_2])).
% 34.37/22.95  tff(c_3072, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_1'('#skF_7', '#skF_9', '#skF_8')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_66, c_3013])).
% 34.37/22.95  tff(c_3073, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_1'('#skF_7', '#skF_9', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_108, c_3072])).
% 34.37/22.95  tff(c_3111, plain, (![B_87]: (k10_lattice3('#skF_7', B_87, '#skF_1'('#skF_7', '#skF_9', '#skF_8'))='#skF_1'('#skF_7', '#skF_9', '#skF_8') | ~r1_orders_2('#skF_7', B_87, '#skF_1'('#skF_7', '#skF_9', '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_9', '#skF_8'), u1_struct_0('#skF_7')) | ~m1_subset_1(B_87, u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v1_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_3073, c_2000])).
% 34.37/22.95  tff(c_3116, plain, (![B_87]: (k10_lattice3('#skF_7', B_87, '#skF_1'('#skF_7', '#skF_9', '#skF_8'))='#skF_1'('#skF_7', '#skF_9', '#skF_8') | ~r1_orders_2('#skF_7', B_87, '#skF_1'('#skF_7', '#skF_9', '#skF_8')) | ~m1_subset_1(B_87, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_2899, c_3111])).
% 34.37/22.95  tff(c_8071, plain, (![B_468]: (k10_lattice3('#skF_7', B_468, '#skF_1'('#skF_7', '#skF_9', '#skF_8'))='#skF_1'('#skF_7', '#skF_9', '#skF_8') | ~r1_orders_2('#skF_7', B_468, '#skF_1'('#skF_7', '#skF_9', '#skF_8')) | ~m1_subset_1(B_468, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_108, c_3116])).
% 34.37/22.95  tff(c_8092, plain, (![E_50]: (k10_lattice3('#skF_7', E_50, '#skF_1'('#skF_7', '#skF_9', '#skF_8'))='#skF_1'('#skF_7', '#skF_9', '#skF_8') | ~r1_orders_2('#skF_7', E_50, '#skF_8') | ~r1_orders_2('#skF_7', E_50, '#skF_9') | ~m1_subset_1(E_50, u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~v2_lattice3('#skF_7') | ~l1_orders_2('#skF_7'))), inference(resolution, [status(thm)], [c_20, c_8071])).
% 34.37/22.95  tff(c_17801, plain, (![E_640]: (k10_lattice3('#skF_7', E_640, '#skF_1'('#skF_7', '#skF_9', '#skF_8'))='#skF_1'('#skF_7', '#skF_9', '#skF_8') | ~r1_orders_2('#skF_7', E_640, '#skF_8') | ~r1_orders_2('#skF_7', E_640, '#skF_9') | ~m1_subset_1(E_640, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_62, c_64, c_8092])).
% 34.37/22.95  tff(c_17828, plain, (k10_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'('#skF_7', '#skF_9', '#skF_8'))='#skF_1'('#skF_7', '#skF_9', '#skF_8') | ~r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')), inference(resolution, [status(thm)], [c_3185, c_17801])).
% 34.37/22.95  tff(c_17888, plain, ('#skF_1'('#skF_7', '#skF_9', '#skF_8')='#skF_1'('#skF_7', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3184, c_4191, c_17654, c_17828])).
% 34.37/22.95  tff(c_44, plain, (![A_109, B_133, C_145, D_151]: (r1_orders_2(A_109, '#skF_6'(A_109, B_133, C_145, D_151), C_145) | k11_lattice3(A_109, B_133, C_145)=D_151 | ~r1_orders_2(A_109, D_151, C_145) | ~r1_orders_2(A_109, D_151, B_133) | ~m1_subset_1(D_151, u1_struct_0(A_109)) | ~m1_subset_1(C_145, u1_struct_0(A_109)) | ~m1_subset_1(B_133, u1_struct_0(A_109)) | ~l1_orders_2(A_109) | ~v2_lattice3(A_109) | ~v5_orders_2(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_143])).
% 34.37/22.95  tff(c_46, plain, (![A_109, B_133, C_145, D_151]: (r1_orders_2(A_109, '#skF_6'(A_109, B_133, C_145, D_151), B_133) | k11_lattice3(A_109, B_133, C_145)=D_151 | ~r1_orders_2(A_109, D_151, C_145) | ~r1_orders_2(A_109, D_151, B_133) | ~m1_subset_1(D_151, u1_struct_0(A_109)) | ~m1_subset_1(C_145, u1_struct_0(A_109)) | ~m1_subset_1(B_133, u1_struct_0(A_109)) | ~l1_orders_2(A_109) | ~v2_lattice3(A_109) | ~v5_orders_2(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_143])).
% 34.37/22.95  tff(c_1042, plain, (![A_268, B_269, C_270, D_271]: (~r1_orders_2(A_268, '#skF_6'(A_268, B_269, C_270, D_271), D_271) | k11_lattice3(A_268, B_269, C_270)=D_271 | ~r1_orders_2(A_268, D_271, C_270) | ~r1_orders_2(A_268, D_271, B_269) | ~m1_subset_1(D_271, u1_struct_0(A_268)) | ~m1_subset_1(C_270, u1_struct_0(A_268)) | ~m1_subset_1(B_269, u1_struct_0(A_268)) | ~l1_orders_2(A_268) | ~v2_lattice3(A_268) | ~v5_orders_2(A_268) | v2_struct_0(A_268))), inference(cnfTransformation, [status(thm)], [f_143])).
% 34.37/22.95  tff(c_5167, plain, (![A_427, B_425, C_424, C_428, B_426]: (k11_lattice3(A_427, B_425, C_428)='#skF_1'(A_427, B_426, C_424) | ~r1_orders_2(A_427, '#skF_1'(A_427, B_426, C_424), C_428) | ~r1_orders_2(A_427, '#skF_1'(A_427, B_426, C_424), B_425) | ~m1_subset_1('#skF_1'(A_427, B_426, C_424), u1_struct_0(A_427)) | ~m1_subset_1(C_428, u1_struct_0(A_427)) | ~m1_subset_1(B_425, u1_struct_0(A_427)) | ~v5_orders_2(A_427) | v2_struct_0(A_427) | ~r1_orders_2(A_427, '#skF_6'(A_427, B_425, C_428, '#skF_1'(A_427, B_426, C_424)), C_424) | ~r1_orders_2(A_427, '#skF_6'(A_427, B_425, C_428, '#skF_1'(A_427, B_426, C_424)), B_426) | ~m1_subset_1('#skF_6'(A_427, B_425, C_428, '#skF_1'(A_427, B_426, C_424)), u1_struct_0(A_427)) | ~m1_subset_1(C_424, u1_struct_0(A_427)) | ~m1_subset_1(B_426, u1_struct_0(A_427)) | ~v2_lattice3(A_427) | ~l1_orders_2(A_427))), inference(resolution, [status(thm)], [c_20, c_1042])).
% 34.37/22.95  tff(c_23380, plain, (![A_818, B_819, C_820, B_821]: (~r1_orders_2(A_818, '#skF_6'(A_818, B_819, C_820, '#skF_1'(A_818, B_821, B_819)), B_821) | ~m1_subset_1('#skF_6'(A_818, B_819, C_820, '#skF_1'(A_818, B_821, B_819)), u1_struct_0(A_818)) | ~m1_subset_1(B_821, u1_struct_0(A_818)) | k11_lattice3(A_818, B_819, C_820)='#skF_1'(A_818, B_821, B_819) | ~r1_orders_2(A_818, '#skF_1'(A_818, B_821, B_819), C_820) | ~r1_orders_2(A_818, '#skF_1'(A_818, B_821, B_819), B_819) | ~m1_subset_1('#skF_1'(A_818, B_821, B_819), u1_struct_0(A_818)) | ~m1_subset_1(C_820, u1_struct_0(A_818)) | ~m1_subset_1(B_819, u1_struct_0(A_818)) | ~l1_orders_2(A_818) | ~v2_lattice3(A_818) | ~v5_orders_2(A_818) | v2_struct_0(A_818))), inference(resolution, [status(thm)], [c_46, c_5167])).
% 34.37/22.95  tff(c_51230, plain, (![A_1211, B_1212, C_1213]: (~m1_subset_1('#skF_6'(A_1211, B_1212, C_1213, '#skF_1'(A_1211, C_1213, B_1212)), u1_struct_0(A_1211)) | k11_lattice3(A_1211, B_1212, C_1213)='#skF_1'(A_1211, C_1213, B_1212) | ~r1_orders_2(A_1211, '#skF_1'(A_1211, C_1213, B_1212), C_1213) | ~r1_orders_2(A_1211, '#skF_1'(A_1211, C_1213, B_1212), B_1212) | ~m1_subset_1('#skF_1'(A_1211, C_1213, B_1212), u1_struct_0(A_1211)) | ~m1_subset_1(C_1213, u1_struct_0(A_1211)) | ~m1_subset_1(B_1212, u1_struct_0(A_1211)) | ~l1_orders_2(A_1211) | ~v2_lattice3(A_1211) | ~v5_orders_2(A_1211) | v2_struct_0(A_1211))), inference(resolution, [status(thm)], [c_44, c_23380])).
% 34.37/22.95  tff(c_51233, plain, (~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0('#skF_7')) | k11_lattice3('#skF_7', '#skF_8', '#skF_9')='#skF_1'('#skF_7', '#skF_9', '#skF_8') | ~r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_9') | ~r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_9', '#skF_8'), '#skF_8') | ~m1_subset_1('#skF_1'('#skF_7', '#skF_9', '#skF_8'), u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v2_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_17888, c_51230])).
% 34.37/22.95  tff(c_51245, plain, (~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0('#skF_7')) | k11_lattice3('#skF_7', '#skF_8', '#skF_9')='#skF_1'('#skF_7', '#skF_8', '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_64, c_62, c_3185, c_17888, c_4191, c_17888, c_3184, c_17888, c_17888, c_51233])).
% 34.37/22.95  tff(c_51246, plain, (~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0('#skF_7')) | k11_lattice3('#skF_7', '#skF_8', '#skF_9')='#skF_1'('#skF_7', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_108, c_51245])).
% 34.37/22.95  tff(c_51254, plain, (~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_51246])).
% 34.37/22.95  tff(c_51257, plain, (k11_lattice3('#skF_7', '#skF_8', '#skF_9')='#skF_1'('#skF_7', '#skF_8', '#skF_9') | ~r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v2_lattice3('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_48, c_51254])).
% 34.37/22.95  tff(c_51260, plain, (k11_lattice3('#skF_7', '#skF_8', '#skF_9')='#skF_1'('#skF_7', '#skF_8', '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_64, c_62, c_3185, c_4191, c_3184, c_51257])).
% 34.37/22.95  tff(c_51261, plain, (k11_lattice3('#skF_7', '#skF_8', '#skF_9')='#skF_1'('#skF_7', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_108, c_51260])).
% 34.37/22.95  tff(c_168, plain, (![A_186, B_187, C_188]: (k12_lattice3(A_186, B_187, C_188)=k11_lattice3(A_186, B_187, C_188) | ~m1_subset_1(C_188, u1_struct_0(A_186)) | ~m1_subset_1(B_187, u1_struct_0(A_186)) | ~l1_orders_2(A_186) | ~v2_lattice3(A_186) | ~v5_orders_2(A_186))), inference(cnfTransformation, [status(thm)], [f_155])).
% 34.37/22.95  tff(c_176, plain, (![B_187]: (k12_lattice3('#skF_7', B_187, '#skF_9')=k11_lattice3('#skF_7', B_187, '#skF_9') | ~m1_subset_1(B_187, u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v2_lattice3('#skF_7') | ~v5_orders_2('#skF_7'))), inference(resolution, [status(thm)], [c_62, c_168])).
% 34.37/22.95  tff(c_272, plain, (![B_191]: (k12_lattice3('#skF_7', B_191, '#skF_9')=k11_lattice3('#skF_7', B_191, '#skF_9') | ~m1_subset_1(B_191, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_176])).
% 34.37/22.95  tff(c_301, plain, (k12_lattice3('#skF_7', '#skF_8', '#skF_9')=k11_lattice3('#skF_7', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_64, c_272])).
% 34.37/22.95  tff(c_60, plain, (k13_lattice3('#skF_7', k12_lattice3('#skF_7', '#skF_8', '#skF_9'), '#skF_9')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_186])).
% 34.37/22.95  tff(c_307, plain, (k13_lattice3('#skF_7', k11_lattice3('#skF_7', '#skF_8', '#skF_9'), '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_301, c_60])).
% 34.37/22.95  tff(c_51278, plain, (k13_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_51261, c_307])).
% 34.37/22.95  tff(c_51282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2841, c_51278])).
% 34.37/22.95  tff(c_51283, plain, (k11_lattice3('#skF_7', '#skF_8', '#skF_9')='#skF_1'('#skF_7', '#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_51246])).
% 34.37/22.95  tff(c_51285, plain, (k13_lattice3('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_51283, c_307])).
% 34.37/22.95  tff(c_51289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2841, c_51285])).
% 34.37/22.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.37/22.95  
% 34.37/22.95  Inference rules
% 34.37/22.95  ----------------------
% 34.37/22.95  #Ref     : 0
% 34.37/22.95  #Sup     : 10903
% 34.37/22.95  #Fact    : 0
% 34.37/22.95  #Define  : 0
% 34.37/22.95  #Split   : 116
% 34.37/22.95  #Chain   : 0
% 34.37/22.95  #Close   : 0
% 34.37/22.95  
% 34.37/22.95  Ordering : KBO
% 34.37/22.95  
% 34.37/22.95  Simplification rules
% 34.37/22.95  ----------------------
% 34.37/22.95  #Subsume      : 684
% 34.37/22.95  #Demod        : 26930
% 34.37/22.95  #Tautology    : 5611
% 34.37/22.95  #SimpNegUnit  : 2913
% 34.37/22.95  #BackRed      : 253
% 34.37/22.95  
% 34.37/22.95  #Partial instantiations: 0
% 34.37/22.95  #Strategies tried      : 1
% 34.37/22.95  
% 34.37/22.95  Timing (in seconds)
% 34.37/22.95  ----------------------
% 34.37/22.95  Preprocessing        : 0.40
% 34.37/22.95  Parsing              : 0.21
% 34.37/22.95  CNF conversion       : 0.04
% 34.37/22.95  Main loop            : 21.71
% 34.37/22.95  Inferencing          : 3.67
% 34.37/22.95  Reduction            : 11.27
% 34.37/22.95  Demodulation         : 9.95
% 34.37/22.95  BG Simplification    : 0.25
% 34.37/22.95  Subsumption          : 5.71
% 34.37/22.95  Abstraction          : 0.49
% 34.37/22.95  MUC search           : 0.00
% 34.37/22.95  Cooper               : 0.00
% 34.37/22.95  Total                : 22.17
% 34.37/22.95  Index Insertion      : 0.00
% 34.37/22.95  Index Deletion       : 0.00
% 34.37/22.95  Index Matching       : 0.00
% 34.37/22.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
