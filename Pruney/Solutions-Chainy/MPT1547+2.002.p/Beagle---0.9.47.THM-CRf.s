%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:01 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 303 expanded)
%              Number of leaves         :   25 ( 123 expanded)
%              Depth                    :   10
%              Number of atoms          :  264 (1243 expanded)
%              Number of equality atoms :   30 ( 134 expanded)
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

tff(f_138,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_119,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k11_lattice3(A,B,C) = k11_lattice3(A,C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).

tff(f_105,axiom,(
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

tff(f_93,axiom,(
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

tff(c_32,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_34,plain,(
    v2_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_38,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_360,plain,(
    ! [A_119,B_120,C_121] :
      ( r3_orders_2(A_119,B_120,B_120)
      | ~ m1_subset_1(C_121,u1_struct_0(A_119))
      | ~ m1_subset_1(B_120,u1_struct_0(A_119))
      | ~ l1_orders_2(A_119)
      | ~ v3_orders_2(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_362,plain,(
    ! [B_120] :
      ( r3_orders_2('#skF_2',B_120,B_120)
      | ~ m1_subset_1(B_120,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_360])).

tff(c_367,plain,(
    ! [B_120] :
      ( r3_orders_2('#skF_2',B_120,B_120)
      | ~ m1_subset_1(B_120,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_362])).

tff(c_371,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_367])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ v2_struct_0(A_7)
      | ~ v2_lattice3(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_375,plain,
    ( ~ v2_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_371,c_8])).

tff(c_379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_375])).

tff(c_381,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_51,plain,(
    ! [A_69,B_70,C_71] :
      ( r3_orders_2(A_69,B_70,B_70)
      | ~ m1_subset_1(C_71,u1_struct_0(A_69))
      | ~ m1_subset_1(B_70,u1_struct_0(A_69))
      | ~ l1_orders_2(A_69)
      | ~ v3_orders_2(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_53,plain,(
    ! [B_70] :
      ( r3_orders_2('#skF_2',B_70,B_70)
      | ~ m1_subset_1(B_70,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_51])).

tff(c_58,plain,(
    ! [B_70] :
      ( r3_orders_2('#skF_2',B_70,B_70)
      | ~ m1_subset_1(B_70,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_53])).

tff(c_62,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_65,plain,
    ( ~ v2_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_8])).

tff(c_69,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_65])).

tff(c_71,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_36,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_134,plain,(
    ! [A_81,C_82,B_83] :
      ( k11_lattice3(A_81,C_82,B_83) = k11_lattice3(A_81,B_83,C_82)
      | ~ m1_subset_1(C_82,u1_struct_0(A_81))
      | ~ m1_subset_1(B_83,u1_struct_0(A_81))
      | ~ l1_orders_2(A_81)
      | ~ v2_lattice3(A_81)
      | ~ v5_orders_2(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_136,plain,(
    ! [B_83] :
      ( k11_lattice3('#skF_2',B_83,'#skF_3') = k11_lattice3('#skF_2','#skF_3',B_83)
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_134])).

tff(c_145,plain,(
    ! [B_84] :
      ( k11_lattice3('#skF_2',B_84,'#skF_3') = k11_lattice3('#skF_2','#skF_3',B_84)
      | ~ m1_subset_1(B_84,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_136])).

tff(c_154,plain,(
    k11_lattice3('#skF_2','#skF_3','#skF_4') = k11_lattice3('#skF_2','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_145])).

tff(c_170,plain,(
    ! [A_86,B_87,C_88] :
      ( k12_lattice3(A_86,B_87,C_88) = k11_lattice3(A_86,B_87,C_88)
      | ~ m1_subset_1(C_88,u1_struct_0(A_86))
      | ~ m1_subset_1(B_87,u1_struct_0(A_86))
      | ~ l1_orders_2(A_86)
      | ~ v2_lattice3(A_86)
      | ~ v5_orders_2(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_174,plain,(
    ! [B_87] :
      ( k12_lattice3('#skF_2',B_87,'#skF_4') = k11_lattice3('#skF_2',B_87,'#skF_4')
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_170])).

tff(c_204,plain,(
    ! [B_93] :
      ( k12_lattice3('#skF_2',B_93,'#skF_4') = k11_lattice3('#skF_2',B_93,'#skF_4')
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_174])).

tff(c_207,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') = k11_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_204])).

tff(c_212,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') = k11_lattice3('#skF_2','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_207])).

tff(c_46,plain,
    ( k12_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3'
    | r3_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_48,plain,(
    r3_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_40,plain,
    ( ~ r3_orders_2('#skF_2','#skF_3','#skF_4')
    | k12_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_50,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40])).

tff(c_214,plain,(
    k11_lattice3('#skF_2','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_50])).

tff(c_72,plain,(
    ! [B_72] :
      ( r3_orders_2('#skF_2',B_72,B_72)
      | ~ m1_subset_1(B_72,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_77,plain,(
    r3_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_72])).

tff(c_115,plain,(
    ! [A_78,B_79,C_80] :
      ( r1_orders_2(A_78,B_79,C_80)
      | ~ r3_orders_2(A_78,B_79,C_80)
      | ~ m1_subset_1(C_80,u1_struct_0(A_78))
      | ~ m1_subset_1(B_79,u1_struct_0(A_78))
      | ~ l1_orders_2(A_78)
      | ~ v3_orders_2(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_119,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_115])).

tff(c_128,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_30,c_119])).

tff(c_129,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_128])).

tff(c_121,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_115])).

tff(c_132,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_30,c_28,c_121])).

tff(c_133,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_132])).

tff(c_14,plain,(
    ! [A_8,B_32,C_44,D_50] :
      ( r1_orders_2(A_8,'#skF_1'(A_8,B_32,C_44,D_50),B_32)
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
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_307,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( ~ r1_orders_2(A_112,'#skF_1'(A_112,B_113,C_114,D_115),D_115)
      | k11_lattice3(A_112,B_113,C_114) = D_115
      | ~ r1_orders_2(A_112,D_115,C_114)
      | ~ r1_orders_2(A_112,D_115,B_113)
      | ~ m1_subset_1(D_115,u1_struct_0(A_112))
      | ~ m1_subset_1(C_114,u1_struct_0(A_112))
      | ~ m1_subset_1(B_113,u1_struct_0(A_112))
      | ~ l1_orders_2(A_112)
      | ~ v2_lattice3(A_112)
      | ~ v5_orders_2(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_318,plain,(
    ! [A_116,B_117,C_118] :
      ( k11_lattice3(A_116,B_117,C_118) = B_117
      | ~ r1_orders_2(A_116,B_117,C_118)
      | ~ r1_orders_2(A_116,B_117,B_117)
      | ~ m1_subset_1(C_118,u1_struct_0(A_116))
      | ~ m1_subset_1(B_117,u1_struct_0(A_116))
      | ~ l1_orders_2(A_116)
      | ~ v2_lattice3(A_116)
      | ~ v5_orders_2(A_116)
      | v2_struct_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_14,c_307])).

tff(c_328,plain,
    ( k11_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3'
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v2_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_133,c_318])).

tff(c_341,plain,
    ( k11_lattice3('#skF_2','#skF_4','#skF_3') = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_28,c_129,c_154,c_328])).

tff(c_343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_214,c_341])).

tff(c_345,plain,(
    ~ r3_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_389,plain,(
    ! [A_123,B_124,C_125] :
      ( r3_orders_2(A_123,B_124,C_125)
      | ~ r1_orders_2(A_123,B_124,C_125)
      | ~ m1_subset_1(C_125,u1_struct_0(A_123))
      | ~ m1_subset_1(B_124,u1_struct_0(A_123))
      | ~ l1_orders_2(A_123)
      | ~ v3_orders_2(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_393,plain,(
    ! [B_124] :
      ( r3_orders_2('#skF_2',B_124,'#skF_4')
      | ~ r1_orders_2('#skF_2',B_124,'#skF_4')
      | ~ m1_subset_1(B_124,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_389])).

tff(c_400,plain,(
    ! [B_124] :
      ( r3_orders_2('#skF_2',B_124,'#skF_4')
      | ~ r1_orders_2('#skF_2',B_124,'#skF_4')
      | ~ m1_subset_1(B_124,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_393])).

tff(c_414,plain,(
    ! [B_127] :
      ( r3_orders_2('#skF_2',B_127,'#skF_4')
      | ~ r1_orders_2('#skF_2',B_127,'#skF_4')
      | ~ m1_subset_1(B_127,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_400])).

tff(c_417,plain,
    ( r3_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_414])).

tff(c_423,plain,(
    ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_345,c_417])).

tff(c_344,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_346,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_346])).

tff(c_354,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_426,plain,(
    ! [A_128,B_129,C_130] :
      ( k12_lattice3(A_128,B_129,C_130) = k11_lattice3(A_128,B_129,C_130)
      | ~ m1_subset_1(C_130,u1_struct_0(A_128))
      | ~ m1_subset_1(B_129,u1_struct_0(A_128))
      | ~ l1_orders_2(A_128)
      | ~ v2_lattice3(A_128)
      | ~ v5_orders_2(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_430,plain,(
    ! [B_129] :
      ( k12_lattice3('#skF_2',B_129,'#skF_4') = k11_lattice3('#skF_2',B_129,'#skF_4')
      | ~ m1_subset_1(B_129,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_426])).

tff(c_465,plain,(
    ! [B_135] :
      ( k12_lattice3('#skF_2',B_135,'#skF_4') = k11_lattice3('#skF_2',B_135,'#skF_4')
      | ~ m1_subset_1(B_135,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_430])).

tff(c_468,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') = k11_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_465])).

tff(c_473,plain,(
    k11_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_468])).

tff(c_527,plain,(
    ! [A_141,B_142,C_143] :
      ( r1_orders_2(A_141,k11_lattice3(A_141,B_142,C_143),C_143)
      | ~ m1_subset_1(k11_lattice3(A_141,B_142,C_143),u1_struct_0(A_141))
      | ~ m1_subset_1(C_143,u1_struct_0(A_141))
      | ~ m1_subset_1(B_142,u1_struct_0(A_141))
      | ~ l1_orders_2(A_141)
      | ~ v2_lattice3(A_141)
      | ~ v5_orders_2(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_531,plain,
    ( r1_orders_2('#skF_2',k11_lattice3('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v2_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_527])).

tff(c_536,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_28,c_30,c_473,c_531])).

tff(c_538,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_423,c_536])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:26:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.39  
% 2.71/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.40  %$ r3_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > l1_orders_2 > k12_lattice3 > k11_lattice3 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.71/1.40  
% 2.71/1.40  %Foreground sorts:
% 2.71/1.40  
% 2.71/1.40  
% 2.71/1.40  %Background operators:
% 2.71/1.40  
% 2.71/1.40  
% 2.71/1.40  %Foreground operators:
% 2.71/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.71/1.40  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.71/1.40  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.71/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.40  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.71/1.40  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 2.71/1.40  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 2.71/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.40  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.71/1.40  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.71/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.40  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 2.71/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.71/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.71/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.40  
% 2.71/1.42  tff(f_138, negated_conjecture, ~(![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((B = k12_lattice3(A, B, C)) <=> r3_orders_2(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_yellow_0)).
% 2.71/1.42  tff(f_53, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_orders_2(A, B, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 2.71/1.42  tff(f_60, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 2.71/1.42  tff(f_119, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k11_lattice3(A, B, C) = k11_lattice3(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_lattice3)).
% 2.71/1.42  tff(f_105, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 2.71/1.42  tff(f_40, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 2.71/1.42  tff(f_93, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l28_lattice3)).
% 2.71/1.42  tff(c_32, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.71/1.42  tff(c_34, plain, (v2_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.71/1.42  tff(c_38, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.71/1.42  tff(c_30, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.71/1.42  tff(c_360, plain, (![A_119, B_120, C_121]: (r3_orders_2(A_119, B_120, B_120) | ~m1_subset_1(C_121, u1_struct_0(A_119)) | ~m1_subset_1(B_120, u1_struct_0(A_119)) | ~l1_orders_2(A_119) | ~v3_orders_2(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.71/1.42  tff(c_362, plain, (![B_120]: (r3_orders_2('#skF_2', B_120, B_120) | ~m1_subset_1(B_120, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_360])).
% 2.71/1.42  tff(c_367, plain, (![B_120]: (r3_orders_2('#skF_2', B_120, B_120) | ~m1_subset_1(B_120, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_362])).
% 2.71/1.42  tff(c_371, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_367])).
% 2.71/1.42  tff(c_8, plain, (![A_7]: (~v2_struct_0(A_7) | ~v2_lattice3(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.71/1.42  tff(c_375, plain, (~v2_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_371, c_8])).
% 2.71/1.42  tff(c_379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_375])).
% 2.71/1.42  tff(c_381, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_367])).
% 2.71/1.42  tff(c_51, plain, (![A_69, B_70, C_71]: (r3_orders_2(A_69, B_70, B_70) | ~m1_subset_1(C_71, u1_struct_0(A_69)) | ~m1_subset_1(B_70, u1_struct_0(A_69)) | ~l1_orders_2(A_69) | ~v3_orders_2(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.71/1.42  tff(c_53, plain, (![B_70]: (r3_orders_2('#skF_2', B_70, B_70) | ~m1_subset_1(B_70, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_51])).
% 2.71/1.42  tff(c_58, plain, (![B_70]: (r3_orders_2('#skF_2', B_70, B_70) | ~m1_subset_1(B_70, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_53])).
% 2.71/1.42  tff(c_62, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_58])).
% 2.71/1.42  tff(c_65, plain, (~v2_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_62, c_8])).
% 2.71/1.42  tff(c_69, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_65])).
% 2.71/1.42  tff(c_71, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 2.71/1.42  tff(c_28, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.71/1.42  tff(c_36, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.71/1.42  tff(c_134, plain, (![A_81, C_82, B_83]: (k11_lattice3(A_81, C_82, B_83)=k11_lattice3(A_81, B_83, C_82) | ~m1_subset_1(C_82, u1_struct_0(A_81)) | ~m1_subset_1(B_83, u1_struct_0(A_81)) | ~l1_orders_2(A_81) | ~v2_lattice3(A_81) | ~v5_orders_2(A_81))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.71/1.42  tff(c_136, plain, (![B_83]: (k11_lattice3('#skF_2', B_83, '#skF_3')=k11_lattice3('#skF_2', '#skF_3', B_83) | ~m1_subset_1(B_83, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_134])).
% 2.71/1.42  tff(c_145, plain, (![B_84]: (k11_lattice3('#skF_2', B_84, '#skF_3')=k11_lattice3('#skF_2', '#skF_3', B_84) | ~m1_subset_1(B_84, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_136])).
% 2.71/1.42  tff(c_154, plain, (k11_lattice3('#skF_2', '#skF_3', '#skF_4')=k11_lattice3('#skF_2', '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_145])).
% 2.71/1.42  tff(c_170, plain, (![A_86, B_87, C_88]: (k12_lattice3(A_86, B_87, C_88)=k11_lattice3(A_86, B_87, C_88) | ~m1_subset_1(C_88, u1_struct_0(A_86)) | ~m1_subset_1(B_87, u1_struct_0(A_86)) | ~l1_orders_2(A_86) | ~v2_lattice3(A_86) | ~v5_orders_2(A_86))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.71/1.42  tff(c_174, plain, (![B_87]: (k12_lattice3('#skF_2', B_87, '#skF_4')=k11_lattice3('#skF_2', B_87, '#skF_4') | ~m1_subset_1(B_87, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_170])).
% 2.71/1.42  tff(c_204, plain, (![B_93]: (k12_lattice3('#skF_2', B_93, '#skF_4')=k11_lattice3('#skF_2', B_93, '#skF_4') | ~m1_subset_1(B_93, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_174])).
% 2.71/1.42  tff(c_207, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')=k11_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_204])).
% 2.71/1.42  tff(c_212, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')=k11_lattice3('#skF_2', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_207])).
% 2.71/1.42  tff(c_46, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_3' | r3_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.71/1.42  tff(c_48, plain, (r3_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_46])).
% 2.71/1.42  tff(c_40, plain, (~r3_orders_2('#skF_2', '#skF_3', '#skF_4') | k12_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.71/1.42  tff(c_50, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40])).
% 2.71/1.42  tff(c_214, plain, (k11_lattice3('#skF_2', '#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_212, c_50])).
% 2.71/1.42  tff(c_72, plain, (![B_72]: (r3_orders_2('#skF_2', B_72, B_72) | ~m1_subset_1(B_72, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_58])).
% 2.71/1.42  tff(c_77, plain, (r3_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_72])).
% 2.71/1.42  tff(c_115, plain, (![A_78, B_79, C_80]: (r1_orders_2(A_78, B_79, C_80) | ~r3_orders_2(A_78, B_79, C_80) | ~m1_subset_1(C_80, u1_struct_0(A_78)) | ~m1_subset_1(B_79, u1_struct_0(A_78)) | ~l1_orders_2(A_78) | ~v3_orders_2(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.71/1.42  tff(c_119, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_77, c_115])).
% 2.71/1.42  tff(c_128, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_30, c_119])).
% 2.71/1.42  tff(c_129, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_71, c_128])).
% 2.71/1.42  tff(c_121, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_115])).
% 2.71/1.42  tff(c_132, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_30, c_28, c_121])).
% 2.71/1.42  tff(c_133, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_71, c_132])).
% 2.71/1.42  tff(c_14, plain, (![A_8, B_32, C_44, D_50]: (r1_orders_2(A_8, '#skF_1'(A_8, B_32, C_44, D_50), B_32) | k11_lattice3(A_8, B_32, C_44)=D_50 | ~r1_orders_2(A_8, D_50, C_44) | ~r1_orders_2(A_8, D_50, B_32) | ~m1_subset_1(D_50, u1_struct_0(A_8)) | ~m1_subset_1(C_44, u1_struct_0(A_8)) | ~m1_subset_1(B_32, u1_struct_0(A_8)) | ~l1_orders_2(A_8) | ~v2_lattice3(A_8) | ~v5_orders_2(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.71/1.42  tff(c_307, plain, (![A_112, B_113, C_114, D_115]: (~r1_orders_2(A_112, '#skF_1'(A_112, B_113, C_114, D_115), D_115) | k11_lattice3(A_112, B_113, C_114)=D_115 | ~r1_orders_2(A_112, D_115, C_114) | ~r1_orders_2(A_112, D_115, B_113) | ~m1_subset_1(D_115, u1_struct_0(A_112)) | ~m1_subset_1(C_114, u1_struct_0(A_112)) | ~m1_subset_1(B_113, u1_struct_0(A_112)) | ~l1_orders_2(A_112) | ~v2_lattice3(A_112) | ~v5_orders_2(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.71/1.42  tff(c_318, plain, (![A_116, B_117, C_118]: (k11_lattice3(A_116, B_117, C_118)=B_117 | ~r1_orders_2(A_116, B_117, C_118) | ~r1_orders_2(A_116, B_117, B_117) | ~m1_subset_1(C_118, u1_struct_0(A_116)) | ~m1_subset_1(B_117, u1_struct_0(A_116)) | ~l1_orders_2(A_116) | ~v2_lattice3(A_116) | ~v5_orders_2(A_116) | v2_struct_0(A_116))), inference(resolution, [status(thm)], [c_14, c_307])).
% 2.71/1.42  tff(c_328, plain, (k11_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_133, c_318])).
% 2.71/1.42  tff(c_341, plain, (k11_lattice3('#skF_2', '#skF_4', '#skF_3')='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_28, c_129, c_154, c_328])).
% 2.71/1.42  tff(c_343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_214, c_341])).
% 2.71/1.42  tff(c_345, plain, (~r3_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_46])).
% 2.71/1.42  tff(c_389, plain, (![A_123, B_124, C_125]: (r3_orders_2(A_123, B_124, C_125) | ~r1_orders_2(A_123, B_124, C_125) | ~m1_subset_1(C_125, u1_struct_0(A_123)) | ~m1_subset_1(B_124, u1_struct_0(A_123)) | ~l1_orders_2(A_123) | ~v3_orders_2(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.71/1.42  tff(c_393, plain, (![B_124]: (r3_orders_2('#skF_2', B_124, '#skF_4') | ~r1_orders_2('#skF_2', B_124, '#skF_4') | ~m1_subset_1(B_124, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_389])).
% 2.71/1.42  tff(c_400, plain, (![B_124]: (r3_orders_2('#skF_2', B_124, '#skF_4') | ~r1_orders_2('#skF_2', B_124, '#skF_4') | ~m1_subset_1(B_124, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_393])).
% 2.71/1.42  tff(c_414, plain, (![B_127]: (r3_orders_2('#skF_2', B_127, '#skF_4') | ~r1_orders_2('#skF_2', B_127, '#skF_4') | ~m1_subset_1(B_127, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_381, c_400])).
% 2.71/1.42  tff(c_417, plain, (r3_orders_2('#skF_2', '#skF_3', '#skF_4') | ~r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_414])).
% 2.71/1.42  tff(c_423, plain, (~r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_345, c_417])).
% 2.71/1.42  tff(c_344, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_46])).
% 2.71/1.42  tff(c_346, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_40])).
% 2.71/1.42  tff(c_352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_344, c_346])).
% 2.71/1.42  tff(c_354, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_40])).
% 2.71/1.42  tff(c_426, plain, (![A_128, B_129, C_130]: (k12_lattice3(A_128, B_129, C_130)=k11_lattice3(A_128, B_129, C_130) | ~m1_subset_1(C_130, u1_struct_0(A_128)) | ~m1_subset_1(B_129, u1_struct_0(A_128)) | ~l1_orders_2(A_128) | ~v2_lattice3(A_128) | ~v5_orders_2(A_128))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.71/1.42  tff(c_430, plain, (![B_129]: (k12_lattice3('#skF_2', B_129, '#skF_4')=k11_lattice3('#skF_2', B_129, '#skF_4') | ~m1_subset_1(B_129, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_426])).
% 2.71/1.42  tff(c_465, plain, (![B_135]: (k12_lattice3('#skF_2', B_135, '#skF_4')=k11_lattice3('#skF_2', B_135, '#skF_4') | ~m1_subset_1(B_135, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_430])).
% 2.71/1.42  tff(c_468, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')=k11_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_465])).
% 2.71/1.42  tff(c_473, plain, (k11_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_354, c_468])).
% 2.71/1.42  tff(c_527, plain, (![A_141, B_142, C_143]: (r1_orders_2(A_141, k11_lattice3(A_141, B_142, C_143), C_143) | ~m1_subset_1(k11_lattice3(A_141, B_142, C_143), u1_struct_0(A_141)) | ~m1_subset_1(C_143, u1_struct_0(A_141)) | ~m1_subset_1(B_142, u1_struct_0(A_141)) | ~l1_orders_2(A_141) | ~v2_lattice3(A_141) | ~v5_orders_2(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.71/1.42  tff(c_531, plain, (r1_orders_2('#skF_2', k11_lattice3('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_473, c_527])).
% 2.71/1.42  tff(c_536, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_28, c_30, c_473, c_531])).
% 2.71/1.42  tff(c_538, plain, $false, inference(negUnitSimplification, [status(thm)], [c_381, c_423, c_536])).
% 2.71/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.42  
% 2.71/1.42  Inference rules
% 2.71/1.42  ----------------------
% 2.71/1.42  #Ref     : 0
% 2.71/1.42  #Sup     : 100
% 2.71/1.42  #Fact    : 0
% 2.71/1.42  #Define  : 0
% 2.71/1.42  #Split   : 8
% 2.71/1.42  #Chain   : 0
% 2.71/1.42  #Close   : 0
% 2.71/1.42  
% 2.71/1.42  Ordering : KBO
% 2.71/1.42  
% 2.71/1.42  Simplification rules
% 2.71/1.42  ----------------------
% 2.71/1.42  #Subsume      : 4
% 2.71/1.42  #Demod        : 142
% 2.71/1.42  #Tautology    : 40
% 2.71/1.42  #SimpNegUnit  : 27
% 2.71/1.42  #BackRed      : 2
% 2.71/1.42  
% 2.71/1.42  #Partial instantiations: 0
% 2.71/1.42  #Strategies tried      : 1
% 2.71/1.42  
% 2.71/1.42  Timing (in seconds)
% 2.71/1.42  ----------------------
% 2.71/1.42  Preprocessing        : 0.33
% 2.71/1.42  Parsing              : 0.17
% 2.71/1.42  CNF conversion       : 0.03
% 2.71/1.42  Main loop            : 0.30
% 2.71/1.42  Inferencing          : 0.10
% 2.71/1.42  Reduction            : 0.09
% 2.71/1.42  Demodulation         : 0.06
% 2.71/1.42  BG Simplification    : 0.02
% 2.71/1.42  Subsumption          : 0.06
% 2.71/1.42  Abstraction          : 0.02
% 2.71/1.42  MUC search           : 0.00
% 2.71/1.42  Cooper               : 0.00
% 2.71/1.42  Total                : 0.67
% 2.71/1.42  Index Insertion      : 0.00
% 2.71/1.42  Index Deletion       : 0.00
% 2.71/1.42  Index Matching       : 0.00
% 2.71/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
