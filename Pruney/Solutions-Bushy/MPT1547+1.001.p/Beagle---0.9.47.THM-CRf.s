%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1547+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:02 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 212 expanded)
%              Number of leaves         :   23 (  88 expanded)
%              Depth                    :   13
%              Number of atoms          :  221 ( 855 expanded)
%              Number of equality atoms :   19 (  81 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > l1_orders_2 > k12_lattice3 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_120,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k12_lattice3(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k12_lattice3)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k12_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,D,B)
                      & r1_orders_2(A,D,C)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,E,B)
                              & r1_orders_2(A,E,C) )
                           => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_0)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_34,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_32,plain,(
    v2_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_30,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_77,plain,(
    ! [A_66,C_67,B_68] :
      ( k12_lattice3(A_66,C_67,B_68) = k12_lattice3(A_66,B_68,C_67)
      | ~ m1_subset_1(C_67,u1_struct_0(A_66))
      | ~ m1_subset_1(B_68,u1_struct_0(A_66))
      | ~ l1_orders_2(A_66)
      | ~ v2_lattice3(A_66)
      | ~ v5_orders_2(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_79,plain,(
    ! [B_68] :
      ( k12_lattice3('#skF_2',B_68,'#skF_3') = k12_lattice3('#skF_2','#skF_3',B_68)
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_77])).

tff(c_89,plain,(
    ! [B_69] :
      ( k12_lattice3('#skF_2',B_69,'#skF_3') = k12_lattice3('#skF_2','#skF_3',B_69)
      | ~ m1_subset_1(B_69,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_79])).

tff(c_98,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') = k12_lattice3('#skF_2','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_89])).

tff(c_44,plain,
    ( k12_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3'
    | r3_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_46,plain,(
    r3_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,
    ( ~ r3_orders_2('#skF_2','#skF_3','#skF_4')
    | k12_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38])).

tff(c_99,plain,(
    k12_lattice3('#skF_2','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_48])).

tff(c_36,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_49,plain,(
    ! [A_62,B_63,C_64] :
      ( r3_orders_2(A_62,B_63,B_63)
      | ~ m1_subset_1(C_64,u1_struct_0(A_62))
      | ~ m1_subset_1(B_63,u1_struct_0(A_62))
      | ~ l1_orders_2(A_62)
      | ~ v3_orders_2(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_51,plain,(
    ! [B_63] :
      ( r3_orders_2('#skF_2',B_63,B_63)
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_49])).

tff(c_56,plain,(
    ! [B_63] :
      ( r3_orders_2('#skF_2',B_63,B_63)
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_51])).

tff(c_60,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v2_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,
    ( ~ v2_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_2])).

tff(c_67,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_63])).

tff(c_69,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_138,plain,(
    ! [A_75,B_76,C_77] :
      ( r1_orders_2(A_75,B_76,C_77)
      | ~ r3_orders_2(A_75,B_76,C_77)
      | ~ m1_subset_1(C_77,u1_struct_0(A_75))
      | ~ m1_subset_1(B_76,u1_struct_0(A_75))
      | ~ l1_orders_2(A_75)
      | ~ v3_orders_2(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_144,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_138])).

tff(c_155,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_28,c_26,c_144])).

tff(c_156,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_155])).

tff(c_70,plain,(
    ! [B_65] :
      ( r3_orders_2('#skF_2',B_65,B_65)
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_75,plain,(
    r3_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_70])).

tff(c_142,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_75,c_138])).

tff(c_151,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_28,c_142])).

tff(c_152,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_151])).

tff(c_14,plain,(
    ! [A_11,B_35,C_47,D_53] :
      ( r1_orders_2(A_11,'#skF_1'(A_11,B_35,C_47,D_53),C_47)
      | k12_lattice3(A_11,B_35,C_47) = D_53
      | ~ r1_orders_2(A_11,D_53,C_47)
      | ~ r1_orders_2(A_11,D_53,B_35)
      | ~ m1_subset_1(D_53,u1_struct_0(A_11))
      | ~ m1_subset_1(C_47,u1_struct_0(A_11))
      | ~ m1_subset_1(B_35,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11)
      | ~ v2_lattice3(A_11)
      | ~ v5_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_184,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( ~ r1_orders_2(A_93,'#skF_1'(A_93,B_94,C_95,D_96),D_96)
      | k12_lattice3(A_93,B_94,C_95) = D_96
      | ~ r1_orders_2(A_93,D_96,C_95)
      | ~ r1_orders_2(A_93,D_96,B_94)
      | ~ m1_subset_1(D_96,u1_struct_0(A_93))
      | ~ m1_subset_1(C_95,u1_struct_0(A_93))
      | ~ m1_subset_1(B_94,u1_struct_0(A_93))
      | ~ l1_orders_2(A_93)
      | ~ v2_lattice3(A_93)
      | ~ v5_orders_2(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_239,plain,(
    ! [A_101,B_102,C_103] :
      ( k12_lattice3(A_101,B_102,C_103) = C_103
      | ~ r1_orders_2(A_101,C_103,C_103)
      | ~ r1_orders_2(A_101,C_103,B_102)
      | ~ m1_subset_1(C_103,u1_struct_0(A_101))
      | ~ m1_subset_1(B_102,u1_struct_0(A_101))
      | ~ l1_orders_2(A_101)
      | ~ v2_lattice3(A_101)
      | ~ v5_orders_2(A_101) ) ),
    inference(resolution,[status(thm)],[c_14,c_184])).

tff(c_243,plain,(
    ! [B_102] :
      ( k12_lattice3('#skF_2',B_102,'#skF_3') = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',B_102)
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_102,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_152,c_239])).

tff(c_281,plain,(
    ! [B_105] :
      ( k12_lattice3('#skF_2',B_105,'#skF_3') = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',B_105)
      | ~ m1_subset_1(B_105,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_243])).

tff(c_291,plain,
    ( k12_lattice3('#skF_2','#skF_4','#skF_3') = '#skF_3'
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_281])).

tff(c_300,plain,(
    k12_lattice3('#skF_2','#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_291])).

tff(c_302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_300])).

tff(c_304,plain,(
    ~ r3_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_303,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_415,plain,(
    ! [A_122,B_123,C_124] :
      ( r1_orders_2(A_122,k12_lattice3(A_122,B_123,C_124),C_124)
      | ~ m1_subset_1(k12_lattice3(A_122,B_123,C_124),u1_struct_0(A_122))
      | ~ m1_subset_1(C_124,u1_struct_0(A_122))
      | ~ m1_subset_1(B_123,u1_struct_0(A_122))
      | ~ l1_orders_2(A_122)
      | ~ v2_lattice3(A_122)
      | ~ v5_orders_2(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_419,plain,
    ( r1_orders_2('#skF_2',k12_lattice3('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v2_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_415])).

tff(c_423,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_26,c_28,c_303,c_419])).

tff(c_311,plain,(
    ! [A_106,B_107,C_108] :
      ( r3_orders_2(A_106,B_107,B_107)
      | ~ m1_subset_1(C_108,u1_struct_0(A_106))
      | ~ m1_subset_1(B_107,u1_struct_0(A_106))
      | ~ l1_orders_2(A_106)
      | ~ v3_orders_2(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_313,plain,(
    ! [B_107] :
      ( r3_orders_2('#skF_2',B_107,B_107)
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_311])).

tff(c_318,plain,(
    ! [B_107] :
      ( r3_orders_2('#skF_2',B_107,B_107)
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_313])).

tff(c_322,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_318])).

tff(c_326,plain,
    ( ~ v2_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_322,c_2])).

tff(c_330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_326])).

tff(c_332,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_318])).

tff(c_391,plain,(
    ! [A_118,B_119,C_120] :
      ( r3_orders_2(A_118,B_119,C_120)
      | ~ r1_orders_2(A_118,B_119,C_120)
      | ~ m1_subset_1(C_120,u1_struct_0(A_118))
      | ~ m1_subset_1(B_119,u1_struct_0(A_118))
      | ~ l1_orders_2(A_118)
      | ~ v3_orders_2(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_395,plain,(
    ! [B_119] :
      ( r3_orders_2('#skF_2',B_119,'#skF_4')
      | ~ r1_orders_2('#skF_2',B_119,'#skF_4')
      | ~ m1_subset_1(B_119,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_391])).

tff(c_402,plain,(
    ! [B_119] :
      ( r3_orders_2('#skF_2',B_119,'#skF_4')
      | ~ r1_orders_2('#skF_2',B_119,'#skF_4')
      | ~ m1_subset_1(B_119,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_395])).

tff(c_425,plain,(
    ! [B_125] :
      ( r3_orders_2('#skF_2',B_125,'#skF_4')
      | ~ r1_orders_2('#skF_2',B_125,'#skF_4')
      | ~ m1_subset_1(B_125,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_402])).

tff(c_428,plain,
    ( r3_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_425])).

tff(c_434,plain,(
    r3_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_428])).

tff(c_436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_304,c_434])).

%------------------------------------------------------------------------------
