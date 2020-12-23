%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:02 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 240 expanded)
%              Number of leaves         :   24 ( 100 expanded)
%              Depth                    :    8
%              Number of atoms          :  223 ( 953 expanded)
%              Number of equality atoms :   22 ( 100 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > l1_orders_2 > k12_lattice3 > k11_lattice3 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v5_orders_2(A)
          & v2_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( B = k12_lattice3(A,B,C)
                <=> r3_orders_2(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_0)).

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_92,axiom,(
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

tff(c_30,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_32,plain,(
    v2_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_36,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_307,plain,(
    ! [A_103,B_104] :
      ( r1_orders_2(A_103,B_104,B_104)
      | ~ m1_subset_1(B_104,u1_struct_0(A_103))
      | ~ l1_orders_2(A_103)
      | ~ v3_orders_2(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_309,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_307])).

tff(c_314,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_309])).

tff(c_318,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_314])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ v2_struct_0(A_7)
      | ~ v2_lattice3(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_321,plain,
    ( ~ v2_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_318,c_8])).

tff(c_325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_321])).

tff(c_327,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_314])).

tff(c_49,plain,(
    ! [A_62,B_63] :
      ( r1_orders_2(A_62,B_63,B_63)
      | ~ m1_subset_1(B_63,u1_struct_0(A_62))
      | ~ l1_orders_2(A_62)
      | ~ v3_orders_2(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_51,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_49])).

tff(c_56,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_51])).

tff(c_60,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_63,plain,
    ( ~ v2_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_8])).

tff(c_67,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_63])).

tff(c_69,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_34,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_70,plain,(
    ! [A_64,B_65,C_66] :
      ( k12_lattice3(A_64,B_65,C_66) = k11_lattice3(A_64,B_65,C_66)
      | ~ m1_subset_1(C_66,u1_struct_0(A_64))
      | ~ m1_subset_1(B_65,u1_struct_0(A_64))
      | ~ l1_orders_2(A_64)
      | ~ v2_lattice3(A_64)
      | ~ v5_orders_2(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_74,plain,(
    ! [B_65] :
      ( k12_lattice3('#skF_2',B_65,'#skF_4') = k11_lattice3('#skF_2',B_65,'#skF_4')
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_70])).

tff(c_99,plain,(
    ! [B_68] :
      ( k12_lattice3('#skF_2',B_68,'#skF_4') = k11_lattice3('#skF_2',B_68,'#skF_4')
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_74])).

tff(c_106,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') = k11_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_99])).

tff(c_44,plain,
    ( k12_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3'
    | r3_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_46,plain,(
    r3_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,
    ( ~ r3_orders_2('#skF_2','#skF_3','#skF_4')
    | k12_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_48,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38])).

tff(c_108,plain,(
    k11_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_48])).

tff(c_68,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_130,plain,(
    ! [A_72,B_73,C_74] :
      ( r1_orders_2(A_72,B_73,C_74)
      | ~ r3_orders_2(A_72,B_73,C_74)
      | ~ m1_subset_1(C_74,u1_struct_0(A_72))
      | ~ m1_subset_1(B_73,u1_struct_0(A_72))
      | ~ l1_orders_2(A_72)
      | ~ v3_orders_2(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_132,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_130])).

tff(c_135,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_28,c_26,c_132])).

tff(c_136,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_135])).

tff(c_273,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( r1_orders_2(A_96,'#skF_1'(A_96,B_97,C_98,D_99),B_97)
      | k11_lattice3(A_96,B_97,C_98) = D_99
      | ~ r1_orders_2(A_96,D_99,C_98)
      | ~ r1_orders_2(A_96,D_99,B_97)
      | ~ m1_subset_1(D_99,u1_struct_0(A_96))
      | ~ m1_subset_1(C_98,u1_struct_0(A_96))
      | ~ m1_subset_1(B_97,u1_struct_0(A_96))
      | ~ l1_orders_2(A_96)
      | ~ v2_lattice3(A_96)
      | ~ v5_orders_2(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10,plain,(
    ! [A_8,B_32,C_44,D_50] :
      ( ~ r1_orders_2(A_8,'#skF_1'(A_8,B_32,C_44,D_50),D_50)
      | k11_lattice3(A_8,B_32,C_44) = D_50
      | ~ r1_orders_2(A_8,D_50,C_44)
      | ~ r1_orders_2(A_8,D_50,B_32)
      | ~ m1_subset_1(D_50,u1_struct_0(A_8))
      | ~ m1_subset_1(C_44,u1_struct_0(A_8))
      | ~ m1_subset_1(B_32,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8)
      | ~ v2_lattice3(A_8)
      | ~ v5_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_283,plain,(
    ! [A_100,B_101,C_102] :
      ( k11_lattice3(A_100,B_101,C_102) = B_101
      | ~ r1_orders_2(A_100,B_101,C_102)
      | ~ r1_orders_2(A_100,B_101,B_101)
      | ~ m1_subset_1(C_102,u1_struct_0(A_100))
      | ~ m1_subset_1(B_101,u1_struct_0(A_100))
      | ~ l1_orders_2(A_100)
      | ~ v2_lattice3(A_100)
      | ~ v5_orders_2(A_100)
      | v2_struct_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_273,c_10])).

tff(c_289,plain,
    ( k11_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3'
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v2_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_136,c_283])).

tff(c_298,plain,
    ( k11_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_26,c_68,c_289])).

tff(c_300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_108,c_298])).

tff(c_302,plain,(
    ~ r3_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_375,plain,(
    ! [A_110,B_111,C_112] :
      ( r3_orders_2(A_110,B_111,C_112)
      | ~ r1_orders_2(A_110,B_111,C_112)
      | ~ m1_subset_1(C_112,u1_struct_0(A_110))
      | ~ m1_subset_1(B_111,u1_struct_0(A_110))
      | ~ l1_orders_2(A_110)
      | ~ v3_orders_2(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_379,plain,(
    ! [B_111] :
      ( r3_orders_2('#skF_2',B_111,'#skF_4')
      | ~ r1_orders_2('#skF_2',B_111,'#skF_4')
      | ~ m1_subset_1(B_111,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_375])).

tff(c_386,plain,(
    ! [B_111] :
      ( r3_orders_2('#skF_2',B_111,'#skF_4')
      | ~ r1_orders_2('#skF_2',B_111,'#skF_4')
      | ~ m1_subset_1(B_111,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_379])).

tff(c_407,plain,(
    ! [B_117] :
      ( r3_orders_2('#skF_2',B_117,'#skF_4')
      | ~ r1_orders_2('#skF_2',B_117,'#skF_4')
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_327,c_386])).

tff(c_410,plain,
    ( r3_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_407])).

tff(c_416,plain,(
    ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_302,c_410])).

tff(c_301,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_328,plain,(
    ! [A_105,B_106,C_107] :
      ( k12_lattice3(A_105,B_106,C_107) = k11_lattice3(A_105,B_106,C_107)
      | ~ m1_subset_1(C_107,u1_struct_0(A_105))
      | ~ m1_subset_1(B_106,u1_struct_0(A_105))
      | ~ l1_orders_2(A_105)
      | ~ v2_lattice3(A_105)
      | ~ v5_orders_2(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_332,plain,(
    ! [B_106] :
      ( k12_lattice3('#skF_2',B_106,'#skF_4') = k11_lattice3('#skF_2',B_106,'#skF_4')
      | ~ m1_subset_1(B_106,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_328])).

tff(c_357,plain,(
    ! [B_109] :
      ( k12_lattice3('#skF_2',B_109,'#skF_4') = k11_lattice3('#skF_2',B_109,'#skF_4')
      | ~ m1_subset_1(B_109,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_332])).

tff(c_360,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') = k11_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_357])).

tff(c_365,plain,(
    k11_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_360])).

tff(c_432,plain,(
    ! [A_121,B_122,C_123] :
      ( r1_orders_2(A_121,k11_lattice3(A_121,B_122,C_123),C_123)
      | ~ m1_subset_1(k11_lattice3(A_121,B_122,C_123),u1_struct_0(A_121))
      | ~ m1_subset_1(C_123,u1_struct_0(A_121))
      | ~ m1_subset_1(B_122,u1_struct_0(A_121))
      | ~ l1_orders_2(A_121)
      | ~ v2_lattice3(A_121)
      | ~ v5_orders_2(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_434,plain,
    ( r1_orders_2('#skF_2',k11_lattice3('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v2_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_432])).

tff(c_436,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_26,c_28,c_365,c_434])).

tff(c_438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_327,c_416,c_436])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:44:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.34  
% 2.66/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.34  %$ r3_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > l1_orders_2 > k12_lattice3 > k11_lattice3 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.66/1.34  
% 2.66/1.34  %Foreground sorts:
% 2.66/1.34  
% 2.66/1.34  
% 2.66/1.34  %Background operators:
% 2.66/1.34  
% 2.66/1.34  
% 2.66/1.34  %Foreground operators:
% 2.66/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.66/1.34  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.66/1.34  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.66/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.34  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.66/1.34  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 2.66/1.34  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 2.66/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.34  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.66/1.34  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.66/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.34  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 2.66/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.66/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.66/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.34  
% 2.66/1.36  tff(f_123, negated_conjecture, ~(![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((B = k12_lattice3(A, B, C)) <=> r3_orders_2(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_yellow_0)).
% 2.66/1.36  tff(f_52, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 2.66/1.36  tff(f_59, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 2.66/1.36  tff(f_104, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 2.66/1.36  tff(f_40, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 2.66/1.36  tff(f_92, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l28_lattice3)).
% 2.66/1.36  tff(c_30, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.66/1.36  tff(c_32, plain, (v2_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.66/1.36  tff(c_36, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.66/1.36  tff(c_28, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.66/1.36  tff(c_307, plain, (![A_103, B_104]: (r1_orders_2(A_103, B_104, B_104) | ~m1_subset_1(B_104, u1_struct_0(A_103)) | ~l1_orders_2(A_103) | ~v3_orders_2(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.66/1.36  tff(c_309, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_307])).
% 2.66/1.36  tff(c_314, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_309])).
% 2.66/1.36  tff(c_318, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_314])).
% 2.66/1.36  tff(c_8, plain, (![A_7]: (~v2_struct_0(A_7) | ~v2_lattice3(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.66/1.36  tff(c_321, plain, (~v2_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_318, c_8])).
% 2.66/1.36  tff(c_325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_321])).
% 2.66/1.36  tff(c_327, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_314])).
% 2.66/1.36  tff(c_49, plain, (![A_62, B_63]: (r1_orders_2(A_62, B_63, B_63) | ~m1_subset_1(B_63, u1_struct_0(A_62)) | ~l1_orders_2(A_62) | ~v3_orders_2(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.66/1.36  tff(c_51, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_49])).
% 2.66/1.36  tff(c_56, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_51])).
% 2.66/1.36  tff(c_60, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_56])).
% 2.66/1.36  tff(c_63, plain, (~v2_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_60, c_8])).
% 2.66/1.36  tff(c_67, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_63])).
% 2.66/1.36  tff(c_69, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 2.66/1.36  tff(c_34, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.66/1.36  tff(c_26, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.66/1.36  tff(c_70, plain, (![A_64, B_65, C_66]: (k12_lattice3(A_64, B_65, C_66)=k11_lattice3(A_64, B_65, C_66) | ~m1_subset_1(C_66, u1_struct_0(A_64)) | ~m1_subset_1(B_65, u1_struct_0(A_64)) | ~l1_orders_2(A_64) | ~v2_lattice3(A_64) | ~v5_orders_2(A_64))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.66/1.36  tff(c_74, plain, (![B_65]: (k12_lattice3('#skF_2', B_65, '#skF_4')=k11_lattice3('#skF_2', B_65, '#skF_4') | ~m1_subset_1(B_65, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_70])).
% 2.66/1.36  tff(c_99, plain, (![B_68]: (k12_lattice3('#skF_2', B_68, '#skF_4')=k11_lattice3('#skF_2', B_68, '#skF_4') | ~m1_subset_1(B_68, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_74])).
% 2.66/1.36  tff(c_106, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')=k11_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_99])).
% 2.66/1.36  tff(c_44, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_3' | r3_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.66/1.36  tff(c_46, plain, (r3_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_44])).
% 2.66/1.36  tff(c_38, plain, (~r3_orders_2('#skF_2', '#skF_3', '#skF_4') | k12_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.66/1.36  tff(c_48, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38])).
% 2.66/1.36  tff(c_108, plain, (k11_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_48])).
% 2.66/1.36  tff(c_68, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 2.66/1.36  tff(c_130, plain, (![A_72, B_73, C_74]: (r1_orders_2(A_72, B_73, C_74) | ~r3_orders_2(A_72, B_73, C_74) | ~m1_subset_1(C_74, u1_struct_0(A_72)) | ~m1_subset_1(B_73, u1_struct_0(A_72)) | ~l1_orders_2(A_72) | ~v3_orders_2(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.66/1.36  tff(c_132, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_130])).
% 2.66/1.36  tff(c_135, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_28, c_26, c_132])).
% 2.66/1.36  tff(c_136, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_69, c_135])).
% 2.66/1.36  tff(c_273, plain, (![A_96, B_97, C_98, D_99]: (r1_orders_2(A_96, '#skF_1'(A_96, B_97, C_98, D_99), B_97) | k11_lattice3(A_96, B_97, C_98)=D_99 | ~r1_orders_2(A_96, D_99, C_98) | ~r1_orders_2(A_96, D_99, B_97) | ~m1_subset_1(D_99, u1_struct_0(A_96)) | ~m1_subset_1(C_98, u1_struct_0(A_96)) | ~m1_subset_1(B_97, u1_struct_0(A_96)) | ~l1_orders_2(A_96) | ~v2_lattice3(A_96) | ~v5_orders_2(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.66/1.36  tff(c_10, plain, (![A_8, B_32, C_44, D_50]: (~r1_orders_2(A_8, '#skF_1'(A_8, B_32, C_44, D_50), D_50) | k11_lattice3(A_8, B_32, C_44)=D_50 | ~r1_orders_2(A_8, D_50, C_44) | ~r1_orders_2(A_8, D_50, B_32) | ~m1_subset_1(D_50, u1_struct_0(A_8)) | ~m1_subset_1(C_44, u1_struct_0(A_8)) | ~m1_subset_1(B_32, u1_struct_0(A_8)) | ~l1_orders_2(A_8) | ~v2_lattice3(A_8) | ~v5_orders_2(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.66/1.36  tff(c_283, plain, (![A_100, B_101, C_102]: (k11_lattice3(A_100, B_101, C_102)=B_101 | ~r1_orders_2(A_100, B_101, C_102) | ~r1_orders_2(A_100, B_101, B_101) | ~m1_subset_1(C_102, u1_struct_0(A_100)) | ~m1_subset_1(B_101, u1_struct_0(A_100)) | ~l1_orders_2(A_100) | ~v2_lattice3(A_100) | ~v5_orders_2(A_100) | v2_struct_0(A_100))), inference(resolution, [status(thm)], [c_273, c_10])).
% 2.66/1.36  tff(c_289, plain, (k11_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_136, c_283])).
% 2.66/1.36  tff(c_298, plain, (k11_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_26, c_68, c_289])).
% 2.66/1.36  tff(c_300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_108, c_298])).
% 2.66/1.36  tff(c_302, plain, (~r3_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 2.66/1.36  tff(c_375, plain, (![A_110, B_111, C_112]: (r3_orders_2(A_110, B_111, C_112) | ~r1_orders_2(A_110, B_111, C_112) | ~m1_subset_1(C_112, u1_struct_0(A_110)) | ~m1_subset_1(B_111, u1_struct_0(A_110)) | ~l1_orders_2(A_110) | ~v3_orders_2(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.66/1.36  tff(c_379, plain, (![B_111]: (r3_orders_2('#skF_2', B_111, '#skF_4') | ~r1_orders_2('#skF_2', B_111, '#skF_4') | ~m1_subset_1(B_111, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_375])).
% 2.66/1.36  tff(c_386, plain, (![B_111]: (r3_orders_2('#skF_2', B_111, '#skF_4') | ~r1_orders_2('#skF_2', B_111, '#skF_4') | ~m1_subset_1(B_111, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_379])).
% 2.66/1.36  tff(c_407, plain, (![B_117]: (r3_orders_2('#skF_2', B_117, '#skF_4') | ~r1_orders_2('#skF_2', B_117, '#skF_4') | ~m1_subset_1(B_117, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_327, c_386])).
% 2.66/1.36  tff(c_410, plain, (r3_orders_2('#skF_2', '#skF_3', '#skF_4') | ~r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_407])).
% 2.66/1.36  tff(c_416, plain, (~r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_302, c_410])).
% 2.66/1.36  tff(c_301, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 2.66/1.36  tff(c_328, plain, (![A_105, B_106, C_107]: (k12_lattice3(A_105, B_106, C_107)=k11_lattice3(A_105, B_106, C_107) | ~m1_subset_1(C_107, u1_struct_0(A_105)) | ~m1_subset_1(B_106, u1_struct_0(A_105)) | ~l1_orders_2(A_105) | ~v2_lattice3(A_105) | ~v5_orders_2(A_105))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.66/1.36  tff(c_332, plain, (![B_106]: (k12_lattice3('#skF_2', B_106, '#skF_4')=k11_lattice3('#skF_2', B_106, '#skF_4') | ~m1_subset_1(B_106, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_328])).
% 2.66/1.36  tff(c_357, plain, (![B_109]: (k12_lattice3('#skF_2', B_109, '#skF_4')=k11_lattice3('#skF_2', B_109, '#skF_4') | ~m1_subset_1(B_109, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_332])).
% 2.66/1.36  tff(c_360, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')=k11_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_357])).
% 2.66/1.36  tff(c_365, plain, (k11_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_301, c_360])).
% 2.66/1.36  tff(c_432, plain, (![A_121, B_122, C_123]: (r1_orders_2(A_121, k11_lattice3(A_121, B_122, C_123), C_123) | ~m1_subset_1(k11_lattice3(A_121, B_122, C_123), u1_struct_0(A_121)) | ~m1_subset_1(C_123, u1_struct_0(A_121)) | ~m1_subset_1(B_122, u1_struct_0(A_121)) | ~l1_orders_2(A_121) | ~v2_lattice3(A_121) | ~v5_orders_2(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.66/1.36  tff(c_434, plain, (r1_orders_2('#skF_2', k11_lattice3('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_365, c_432])).
% 2.66/1.36  tff(c_436, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_26, c_28, c_365, c_434])).
% 2.66/1.36  tff(c_438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_327, c_416, c_436])).
% 2.66/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.36  
% 2.66/1.36  Inference rules
% 2.66/1.36  ----------------------
% 2.66/1.36  #Ref     : 0
% 2.66/1.36  #Sup     : 86
% 2.66/1.36  #Fact    : 0
% 2.66/1.36  #Define  : 0
% 2.66/1.36  #Split   : 5
% 2.66/1.36  #Chain   : 0
% 2.66/1.36  #Close   : 0
% 2.66/1.36  
% 2.66/1.36  Ordering : KBO
% 2.66/1.36  
% 2.66/1.36  Simplification rules
% 2.66/1.36  ----------------------
% 2.66/1.36  #Subsume      : 2
% 2.66/1.36  #Demod        : 144
% 2.66/1.36  #Tautology    : 44
% 2.66/1.36  #SimpNegUnit  : 23
% 2.66/1.36  #BackRed      : 4
% 2.66/1.36  
% 2.66/1.36  #Partial instantiations: 0
% 2.66/1.36  #Strategies tried      : 1
% 2.66/1.36  
% 2.66/1.36  Timing (in seconds)
% 2.66/1.36  ----------------------
% 2.66/1.36  Preprocessing        : 0.32
% 2.66/1.36  Parsing              : 0.16
% 2.66/1.36  CNF conversion       : 0.03
% 2.66/1.36  Main loop            : 0.26
% 2.66/1.36  Inferencing          : 0.10
% 2.66/1.36  Reduction            : 0.08
% 2.66/1.36  Demodulation         : 0.06
% 2.66/1.36  BG Simplification    : 0.02
% 2.66/1.36  Subsumption          : 0.05
% 2.66/1.36  Abstraction          : 0.02
% 2.66/1.36  MUC search           : 0.00
% 2.66/1.36  Cooper               : 0.00
% 2.66/1.37  Total                : 0.62
% 2.66/1.37  Index Insertion      : 0.00
% 2.66/1.37  Index Deletion       : 0.00
% 2.66/1.37  Index Matching       : 0.00
% 2.66/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
