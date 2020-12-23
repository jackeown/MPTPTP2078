%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1552+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:03 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  299 (1359 expanded)
%              Number of leaves         :   22 ( 453 expanded)
%              Depth                    :   13
%              Number of atoms          : 1002 (8323 expanded)
%              Number of equality atoms :   57 ( 855 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_yellow_0 > m1_subset_1 > v5_orders_2 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( ( ( B = k1_yellow_0(A,C)
                    & r1_yellow_0(A,C) )
                 => ( r2_lattice3(A,C,B)
                    & ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => ( r2_lattice3(A,C,D)
                         => r1_orders_2(A,B,D) ) ) ) )
                & ( ( r2_lattice3(A,C,B)
                    & ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => ( r2_lattice3(A,C,D)
                         => r1_orders_2(A,B,D) ) ) )
                 => ( B = k1_yellow_0(A,C)
                    & r1_yellow_0(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_yellow_0(A,B)
           => ( C = k1_yellow_0(A,B)
            <=> ( r2_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_lattice3(A,B,D)
                     => r1_orders_2(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r1_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r2_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_lattice3(A,B,D)
                   => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow_0)).

tff(c_46,plain,
    ( r2_lattice3('#skF_4','#skF_6','#skF_5')
    | m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ r2_lattice3('#skF_4','#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_67,plain,(
    ~ r2_lattice3('#skF_4','#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_26,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_52,plain,
    ( r2_lattice3('#skF_4','#skF_6','#skF_5')
    | r1_yellow_0('#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_59,plain,(
    r1_yellow_0('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,
    ( r2_lattice3('#skF_4','#skF_6','#skF_5')
    | k1_yellow_0('#skF_4','#skF_7') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_60,plain,(
    k1_yellow_0('#skF_4','#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_72,plain,(
    ! [A_61,B_62] :
      ( r2_lattice3(A_61,B_62,k1_yellow_0(A_61,B_62))
      | ~ r1_yellow_0(A_61,B_62)
      | ~ m1_subset_1(k1_yellow_0(A_61,B_62),u1_struct_0(A_61))
      | ~ l1_orders_2(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_74,plain,
    ( r2_lattice3('#skF_4','#skF_7',k1_yellow_0('#skF_4','#skF_7'))
    | ~ r1_yellow_0('#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_72])).

tff(c_76,plain,(
    r2_lattice3('#skF_4','#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_59,c_60,c_74])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_76])).

tff(c_80,plain,(
    r2_lattice3('#skF_4','#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_42,plain,
    ( ~ r1_yellow_0('#skF_4','#skF_6')
    | k1_yellow_0('#skF_4','#skF_6') != '#skF_5'
    | m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ r2_lattice3('#skF_4','#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_89,plain,
    ( ~ r1_yellow_0('#skF_4','#skF_6')
    | k1_yellow_0('#skF_4','#skF_6') != '#skF_5'
    | m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_42])).

tff(c_90,plain,(
    k1_yellow_0('#skF_4','#skF_6') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_79,plain,
    ( m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | r2_lattice3('#skF_4','#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_81,plain,(
    r2_lattice3('#skF_4','#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_28,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_14,plain,(
    ! [A_13,B_27] :
      ( r2_lattice3(A_13,B_27,'#skF_3'(A_13,B_27))
      | ~ r1_yellow_0(A_13,B_27)
      | ~ l1_orders_2(A_13)
      | ~ v5_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [A_13,B_27] :
      ( m1_subset_1('#skF_3'(A_13,B_27),u1_struct_0(A_13))
      | ~ r1_yellow_0(A_13,B_27)
      | ~ l1_orders_2(A_13)
      | ~ v5_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4','#skF_5',D_55)
      | ~ r2_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4','#skF_5','#skF_8')
      | ~ r2_lattice3('#skF_4','#skF_7','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_106,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4','#skF_5',D_55)
      | ~ r2_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4','#skF_5','#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_32])).

tff(c_107,plain,(
    ~ r1_orders_2('#skF_4','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_38,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4','#skF_5',D_55)
      | ~ r2_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4','#skF_7','#skF_8')
      | ~ r2_lattice3('#skF_4','#skF_7','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_109,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4','#skF_5',D_55)
      | ~ r2_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4','#skF_7','#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_38])).

tff(c_110,plain,(
    r2_lattice3('#skF_4','#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_44,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4','#skF_5',D_55)
      | ~ r2_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_4','#skF_7','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_103,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4','#skF_5',D_55)
      | ~ r2_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_44])).

tff(c_104,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_128,plain,(
    ! [A_90,B_91,D_92] :
      ( r1_orders_2(A_90,k1_yellow_0(A_90,B_91),D_92)
      | ~ r2_lattice3(A_90,B_91,D_92)
      | ~ m1_subset_1(D_92,u1_struct_0(A_90))
      | ~ r1_yellow_0(A_90,B_91)
      | ~ m1_subset_1(k1_yellow_0(A_90,B_91),u1_struct_0(A_90))
      | ~ l1_orders_2(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_130,plain,(
    ! [D_92] :
      ( r1_orders_2('#skF_4',k1_yellow_0('#skF_4','#skF_7'),D_92)
      | ~ r2_lattice3('#skF_4','#skF_7',D_92)
      | ~ m1_subset_1(D_92,u1_struct_0('#skF_4'))
      | ~ r1_yellow_0('#skF_4','#skF_7')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_128])).

tff(c_133,plain,(
    ! [D_93] :
      ( r1_orders_2('#skF_4','#skF_5',D_93)
      | ~ r2_lattice3('#skF_4','#skF_7',D_93)
      | ~ m1_subset_1(D_93,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_59,c_60,c_130])).

tff(c_144,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_8')
    | ~ r2_lattice3('#skF_4','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_104,c_133])).

tff(c_160,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_144])).

tff(c_162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_160])).

tff(c_165,plain,(
    ! [D_94] :
      ( r1_orders_2('#skF_4','#skF_5',D_94)
      | ~ r2_lattice3('#skF_4','#skF_6',D_94)
      | ~ m1_subset_1(D_94,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_172,plain,(
    ! [B_27] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_3'('#skF_4',B_27))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_3'('#skF_4',B_27))
      | ~ r1_yellow_0('#skF_4',B_27)
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_165])).

tff(c_185,plain,(
    ! [B_95] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_3'('#skF_4',B_95))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_3'('#skF_4',B_95))
      | ~ r1_yellow_0('#skF_4',B_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_172])).

tff(c_189,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_3'('#skF_4','#skF_6'))
    | ~ r1_yellow_0('#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_185])).

tff(c_192,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_3'('#skF_4','#skF_6'))
    | ~ r1_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_189])).

tff(c_194,plain,(
    ~ r1_yellow_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_20,plain,(
    ! [A_13,B_27,C_34] :
      ( r2_lattice3(A_13,B_27,'#skF_2'(A_13,B_27,C_34))
      | r1_yellow_0(A_13,B_27)
      | ~ r2_lattice3(A_13,B_27,C_34)
      | ~ m1_subset_1(C_34,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13)
      | ~ v5_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_201,plain,(
    ! [A_102,B_103,C_104] :
      ( m1_subset_1('#skF_2'(A_102,B_103,C_104),u1_struct_0(A_102))
      | r1_yellow_0(A_102,B_103)
      | ~ r2_lattice3(A_102,B_103,C_104)
      | ~ m1_subset_1(C_104,u1_struct_0(A_102))
      | ~ l1_orders_2(A_102)
      | ~ v5_orders_2(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_163,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4','#skF_5',D_55)
      | ~ r2_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_205,plain,(
    ! [B_103,C_104] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_103,C_104))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_103,C_104))
      | r1_yellow_0('#skF_4',B_103)
      | ~ r2_lattice3('#skF_4',B_103,C_104)
      | ~ m1_subset_1(C_104,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_201,c_163])).

tff(c_271,plain,(
    ! [B_122,C_123] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_122,C_123))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_122,C_123))
      | r1_yellow_0('#skF_4',B_122)
      | ~ r2_lattice3('#skF_4',B_122,C_123)
      | ~ m1_subset_1(C_123,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_205])).

tff(c_275,plain,(
    ! [C_34] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_34))
      | r1_yellow_0('#skF_4','#skF_6')
      | ~ r2_lattice3('#skF_4','#skF_6',C_34)
      | ~ m1_subset_1(C_34,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_271])).

tff(c_278,plain,(
    ! [C_34] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_34))
      | r1_yellow_0('#skF_4','#skF_6')
      | ~ r2_lattice3('#skF_4','#skF_6',C_34)
      | ~ m1_subset_1(C_34,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_275])).

tff(c_288,plain,(
    ! [C_126] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_126))
      | ~ r2_lattice3('#skF_4','#skF_6',C_126)
      | ~ m1_subset_1(C_126,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_278])).

tff(c_18,plain,(
    ! [A_13,C_34,B_27] :
      ( ~ r1_orders_2(A_13,C_34,'#skF_2'(A_13,B_27,C_34))
      | r1_yellow_0(A_13,B_27)
      | ~ r2_lattice3(A_13,B_27,C_34)
      | ~ m1_subset_1(C_34,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13)
      | ~ v5_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_292,plain,
    ( r1_yellow_0('#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ r2_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_288,c_18])).

tff(c_295,plain,(
    r1_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_81,c_28,c_26,c_292])).

tff(c_297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_295])).

tff(c_299,plain,(
    r1_yellow_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_4,plain,(
    ! [A_1,B_8,C_9] :
      ( r2_lattice3(A_1,B_8,'#skF_1'(A_1,B_8,C_9))
      | k1_yellow_0(A_1,B_8) = C_9
      | ~ r2_lattice3(A_1,B_8,C_9)
      | ~ r1_yellow_0(A_1,B_8)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_315,plain,(
    ! [A_136,B_137,C_138] :
      ( m1_subset_1('#skF_1'(A_136,B_137,C_138),u1_struct_0(A_136))
      | k1_yellow_0(A_136,B_137) = C_138
      | ~ r2_lattice3(A_136,B_137,C_138)
      | ~ r1_yellow_0(A_136,B_137)
      | ~ m1_subset_1(C_138,u1_struct_0(A_136))
      | ~ l1_orders_2(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_319,plain,(
    ! [B_137,C_138] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_1'('#skF_4',B_137,C_138))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_137,C_138))
      | k1_yellow_0('#skF_4',B_137) = C_138
      | ~ r2_lattice3('#skF_4',B_137,C_138)
      | ~ r1_yellow_0('#skF_4',B_137)
      | ~ m1_subset_1(C_138,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_315,c_163])).

tff(c_392,plain,(
    ! [B_154,C_155] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_1'('#skF_4',B_154,C_155))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_154,C_155))
      | k1_yellow_0('#skF_4',B_154) = C_155
      | ~ r2_lattice3('#skF_4',B_154,C_155)
      | ~ r1_yellow_0('#skF_4',B_154)
      | ~ m1_subset_1(C_155,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_319])).

tff(c_396,plain,(
    ! [C_9] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_6',C_9))
      | k1_yellow_0('#skF_4','#skF_6') = C_9
      | ~ r2_lattice3('#skF_4','#skF_6',C_9)
      | ~ r1_yellow_0('#skF_4','#skF_6')
      | ~ m1_subset_1(C_9,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4,c_392])).

tff(c_400,plain,(
    ! [C_156] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_6',C_156))
      | k1_yellow_0('#skF_4','#skF_6') = C_156
      | ~ r2_lattice3('#skF_4','#skF_6',C_156)
      | ~ m1_subset_1(C_156,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_299,c_396])).

tff(c_2,plain,(
    ! [A_1,C_9,B_8] :
      ( ~ r1_orders_2(A_1,C_9,'#skF_1'(A_1,B_8,C_9))
      | k1_yellow_0(A_1,B_8) = C_9
      | ~ r2_lattice3(A_1,B_8,C_9)
      | ~ r1_yellow_0(A_1,B_8)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_404,plain,
    ( ~ r1_yellow_0('#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_4')
    | k1_yellow_0('#skF_4','#skF_6') = '#skF_5'
    | ~ r2_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_400,c_2])).

tff(c_407,plain,(
    k1_yellow_0('#skF_4','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_81,c_26,c_299,c_404])).

tff(c_409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_407])).

tff(c_412,plain,(
    ! [D_157] :
      ( r1_orders_2('#skF_4','#skF_5',D_157)
      | ~ r2_lattice3('#skF_4','#skF_6',D_157)
      | ~ m1_subset_1(D_157,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_419,plain,(
    ! [B_27] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_3'('#skF_4',B_27))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_3'('#skF_4',B_27))
      | ~ r1_yellow_0('#skF_4',B_27)
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_412])).

tff(c_433,plain,(
    ! [B_158] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_3'('#skF_4',B_158))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_3'('#skF_4',B_158))
      | ~ r1_yellow_0('#skF_4',B_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_419])).

tff(c_437,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_3'('#skF_4','#skF_6'))
    | ~ r1_yellow_0('#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_433])).

tff(c_440,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_3'('#skF_4','#skF_6'))
    | ~ r1_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_437])).

tff(c_441,plain,(
    ~ r1_yellow_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_440])).

tff(c_443,plain,(
    ! [A_162,B_163,C_164] :
      ( m1_subset_1('#skF_2'(A_162,B_163,C_164),u1_struct_0(A_162))
      | r1_yellow_0(A_162,B_163)
      | ~ r2_lattice3(A_162,B_163,C_164)
      | ~ m1_subset_1(C_164,u1_struct_0(A_162))
      | ~ l1_orders_2(A_162)
      | ~ v5_orders_2(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_410,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4','#skF_5',D_55)
      | ~ r2_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_447,plain,(
    ! [B_163,C_164] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_163,C_164))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_163,C_164))
      | r1_yellow_0('#skF_4',B_163)
      | ~ r2_lattice3('#skF_4',B_163,C_164)
      | ~ m1_subset_1(C_164,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_443,c_410])).

tff(c_459,plain,(
    ! [B_174,C_175] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_174,C_175))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_174,C_175))
      | r1_yellow_0('#skF_4',B_174)
      | ~ r2_lattice3('#skF_4',B_174,C_175)
      | ~ m1_subset_1(C_175,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_447])).

tff(c_463,plain,(
    ! [C_34] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_34))
      | r1_yellow_0('#skF_4','#skF_6')
      | ~ r2_lattice3('#skF_4','#skF_6',C_34)
      | ~ m1_subset_1(C_34,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_459])).

tff(c_466,plain,(
    ! [C_34] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_34))
      | r1_yellow_0('#skF_4','#skF_6')
      | ~ r2_lattice3('#skF_4','#skF_6',C_34)
      | ~ m1_subset_1(C_34,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_463])).

tff(c_468,plain,(
    ! [C_176] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_176))
      | ~ r2_lattice3('#skF_4','#skF_6',C_176)
      | ~ m1_subset_1(C_176,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_441,c_466])).

tff(c_472,plain,
    ( r1_yellow_0('#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ r2_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_468,c_18])).

tff(c_475,plain,(
    r1_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_81,c_28,c_26,c_472])).

tff(c_477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_441,c_475])).

tff(c_479,plain,(
    r1_yellow_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_440])).

tff(c_502,plain,(
    ! [A_192,B_193,C_194] :
      ( m1_subset_1('#skF_1'(A_192,B_193,C_194),u1_struct_0(A_192))
      | k1_yellow_0(A_192,B_193) = C_194
      | ~ r2_lattice3(A_192,B_193,C_194)
      | ~ r1_yellow_0(A_192,B_193)
      | ~ m1_subset_1(C_194,u1_struct_0(A_192))
      | ~ l1_orders_2(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_506,plain,(
    ! [B_193,C_194] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_1'('#skF_4',B_193,C_194))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_193,C_194))
      | k1_yellow_0('#skF_4',B_193) = C_194
      | ~ r2_lattice3('#skF_4',B_193,C_194)
      | ~ r1_yellow_0('#skF_4',B_193)
      | ~ m1_subset_1(C_194,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_502,c_410])).

tff(c_565,plain,(
    ! [B_205,C_206] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_1'('#skF_4',B_205,C_206))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_205,C_206))
      | k1_yellow_0('#skF_4',B_205) = C_206
      | ~ r2_lattice3('#skF_4',B_205,C_206)
      | ~ r1_yellow_0('#skF_4',B_205)
      | ~ m1_subset_1(C_206,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_506])).

tff(c_569,plain,(
    ! [C_9] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_6',C_9))
      | k1_yellow_0('#skF_4','#skF_6') = C_9
      | ~ r2_lattice3('#skF_4','#skF_6',C_9)
      | ~ r1_yellow_0('#skF_4','#skF_6')
      | ~ m1_subset_1(C_9,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4,c_565])).

tff(c_573,plain,(
    ! [C_207] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_6',C_207))
      | k1_yellow_0('#skF_4','#skF_6') = C_207
      | ~ r2_lattice3('#skF_4','#skF_6',C_207)
      | ~ m1_subset_1(C_207,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_479,c_569])).

tff(c_577,plain,
    ( ~ r1_yellow_0('#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_4')
    | k1_yellow_0('#skF_4','#skF_6') = '#skF_5'
    | ~ r2_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_573,c_2])).

tff(c_580,plain,(
    k1_yellow_0('#skF_4','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_81,c_26,c_479,c_577])).

tff(c_582,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_580])).

tff(c_585,plain,(
    ! [D_208] :
      ( r1_orders_2('#skF_4','#skF_5',D_208)
      | ~ r2_lattice3('#skF_4','#skF_6',D_208)
      | ~ m1_subset_1(D_208,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_589,plain,(
    ! [B_27] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_3'('#skF_4',B_27))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_3'('#skF_4',B_27))
      | ~ r1_yellow_0('#skF_4',B_27)
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_585])).

tff(c_601,plain,(
    ! [B_209] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_3'('#skF_4',B_209))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_3'('#skF_4',B_209))
      | ~ r1_yellow_0('#skF_4',B_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_589])).

tff(c_605,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_3'('#skF_4','#skF_6'))
    | ~ r1_yellow_0('#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_601])).

tff(c_608,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_3'('#skF_4','#skF_6'))
    | ~ r1_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_605])).

tff(c_609,plain,(
    ~ r1_yellow_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_608])).

tff(c_619,plain,(
    ! [A_216,B_217,C_218] :
      ( m1_subset_1('#skF_2'(A_216,B_217,C_218),u1_struct_0(A_216))
      | r1_yellow_0(A_216,B_217)
      | ~ r2_lattice3(A_216,B_217,C_218)
      | ~ m1_subset_1(C_218,u1_struct_0(A_216))
      | ~ l1_orders_2(A_216)
      | ~ v5_orders_2(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_583,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4','#skF_5',D_55)
      | ~ r2_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_623,plain,(
    ! [B_217,C_218] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_217,C_218))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_217,C_218))
      | r1_yellow_0('#skF_4',B_217)
      | ~ r2_lattice3('#skF_4',B_217,C_218)
      | ~ m1_subset_1(C_218,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_619,c_583])).

tff(c_628,plain,(
    ! [B_222,C_223] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_222,C_223))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_222,C_223))
      | r1_yellow_0('#skF_4',B_222)
      | ~ r2_lattice3('#skF_4',B_222,C_223)
      | ~ m1_subset_1(C_223,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_623])).

tff(c_632,plain,(
    ! [C_34] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_34))
      | r1_yellow_0('#skF_4','#skF_6')
      | ~ r2_lattice3('#skF_4','#skF_6',C_34)
      | ~ m1_subset_1(C_34,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_628])).

tff(c_635,plain,(
    ! [C_34] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_34))
      | r1_yellow_0('#skF_4','#skF_6')
      | ~ r2_lattice3('#skF_4','#skF_6',C_34)
      | ~ m1_subset_1(C_34,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_632])).

tff(c_637,plain,(
    ! [C_224] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_224))
      | ~ r2_lattice3('#skF_4','#skF_6',C_224)
      | ~ m1_subset_1(C_224,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_609,c_635])).

tff(c_641,plain,
    ( r1_yellow_0('#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ r2_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_637,c_18])).

tff(c_644,plain,(
    r1_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_81,c_28,c_26,c_641])).

tff(c_646,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_609,c_644])).

tff(c_648,plain,(
    r1_yellow_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_608])).

tff(c_682,plain,(
    ! [A_245,B_246,C_247] :
      ( m1_subset_1('#skF_1'(A_245,B_246,C_247),u1_struct_0(A_245))
      | k1_yellow_0(A_245,B_246) = C_247
      | ~ r2_lattice3(A_245,B_246,C_247)
      | ~ r1_yellow_0(A_245,B_246)
      | ~ m1_subset_1(C_247,u1_struct_0(A_245))
      | ~ l1_orders_2(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_686,plain,(
    ! [B_246,C_247] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_1'('#skF_4',B_246,C_247))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_246,C_247))
      | k1_yellow_0('#skF_4',B_246) = C_247
      | ~ r2_lattice3('#skF_4',B_246,C_247)
      | ~ r1_yellow_0('#skF_4',B_246)
      | ~ m1_subset_1(C_247,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_682,c_583])).

tff(c_731,plain,(
    ! [B_253,C_254] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_1'('#skF_4',B_253,C_254))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_253,C_254))
      | k1_yellow_0('#skF_4',B_253) = C_254
      | ~ r2_lattice3('#skF_4',B_253,C_254)
      | ~ r1_yellow_0('#skF_4',B_253)
      | ~ m1_subset_1(C_254,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_686])).

tff(c_735,plain,(
    ! [C_9] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_6',C_9))
      | k1_yellow_0('#skF_4','#skF_6') = C_9
      | ~ r2_lattice3('#skF_4','#skF_6',C_9)
      | ~ r1_yellow_0('#skF_4','#skF_6')
      | ~ m1_subset_1(C_9,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4,c_731])).

tff(c_739,plain,(
    ! [C_255] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_6',C_255))
      | k1_yellow_0('#skF_4','#skF_6') = C_255
      | ~ r2_lattice3('#skF_4','#skF_6',C_255)
      | ~ m1_subset_1(C_255,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_648,c_735])).

tff(c_743,plain,
    ( ~ r1_yellow_0('#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_4')
    | k1_yellow_0('#skF_4','#skF_6') = '#skF_5'
    | ~ r2_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_739,c_2])).

tff(c_746,plain,(
    k1_yellow_0('#skF_4','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_81,c_26,c_648,c_743])).

tff(c_748,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_746])).

tff(c_750,plain,(
    k1_yellow_0('#skF_4','#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_749,plain,
    ( ~ r1_yellow_0('#skF_4','#skF_6')
    | m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_756,plain,(
    ~ r1_yellow_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_749])).

tff(c_990,plain,(
    ! [A_325,B_326,C_327] :
      ( m1_subset_1('#skF_2'(A_325,B_326,C_327),u1_struct_0(A_325))
      | r1_yellow_0(A_325,B_326)
      | ~ r2_lattice3(A_325,B_326,C_327)
      | ~ m1_subset_1(C_327,u1_struct_0(A_325))
      | ~ l1_orders_2(A_325)
      | ~ v5_orders_2(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_931,plain,(
    ! [A_310,B_311,C_312] :
      ( r2_lattice3(A_310,B_311,'#skF_2'(A_310,B_311,C_312))
      | r1_yellow_0(A_310,B_311)
      | ~ r2_lattice3(A_310,B_311,C_312)
      | ~ m1_subset_1(C_312,u1_struct_0(A_310))
      | ~ l1_orders_2(A_310)
      | ~ v5_orders_2(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_922,plain,(
    ! [A_305,B_306,C_307] :
      ( m1_subset_1('#skF_2'(A_305,B_306,C_307),u1_struct_0(A_305))
      | r1_yellow_0(A_305,B_306)
      | ~ r2_lattice3(A_305,B_306,C_307)
      | ~ m1_subset_1(C_307,u1_struct_0(A_305))
      | ~ l1_orders_2(A_305)
      | ~ v5_orders_2(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_876,plain,(
    ! [A_296,B_297,C_298] :
      ( r2_lattice3(A_296,B_297,'#skF_2'(A_296,B_297,C_298))
      | r1_yellow_0(A_296,B_297)
      | ~ r2_lattice3(A_296,B_297,C_298)
      | ~ m1_subset_1(C_298,u1_struct_0(A_296))
      | ~ l1_orders_2(A_296)
      | ~ v5_orders_2(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_867,plain,(
    ! [A_291,B_292,C_293] :
      ( m1_subset_1('#skF_2'(A_291,B_292,C_293),u1_struct_0(A_291))
      | r1_yellow_0(A_291,B_292)
      | ~ r2_lattice3(A_291,B_292,C_293)
      | ~ m1_subset_1(C_293,u1_struct_0(A_291))
      | ~ l1_orders_2(A_291)
      | ~ v5_orders_2(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_772,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4','#skF_5',D_55)
      | ~ r2_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4','#skF_5','#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_32])).

tff(c_773,plain,(
    ~ r1_orders_2('#skF_4','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_772])).

tff(c_775,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4','#skF_5',D_55)
      | ~ r2_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4','#skF_7','#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_38])).

tff(c_776,plain,(
    r2_lattice3('#skF_4','#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_775])).

tff(c_778,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4','#skF_5',D_55)
      | ~ r2_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_44])).

tff(c_779,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_778])).

tff(c_797,plain,(
    ! [A_279,B_280,D_281] :
      ( r1_orders_2(A_279,k1_yellow_0(A_279,B_280),D_281)
      | ~ r2_lattice3(A_279,B_280,D_281)
      | ~ m1_subset_1(D_281,u1_struct_0(A_279))
      | ~ r1_yellow_0(A_279,B_280)
      | ~ m1_subset_1(k1_yellow_0(A_279,B_280),u1_struct_0(A_279))
      | ~ l1_orders_2(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_801,plain,(
    ! [D_281] :
      ( r1_orders_2('#skF_4',k1_yellow_0('#skF_4','#skF_7'),D_281)
      | ~ r2_lattice3('#skF_4','#skF_7',D_281)
      | ~ m1_subset_1(D_281,u1_struct_0('#skF_4'))
      | ~ r1_yellow_0('#skF_4','#skF_7')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_797])).

tff(c_806,plain,(
    ! [D_282] :
      ( r1_orders_2('#skF_4','#skF_5',D_282)
      | ~ r2_lattice3('#skF_4','#skF_7',D_282)
      | ~ m1_subset_1(D_282,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_59,c_60,c_801])).

tff(c_817,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_8')
    | ~ r2_lattice3('#skF_4','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_779,c_806])).

tff(c_833,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_817])).

tff(c_835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_773,c_833])).

tff(c_836,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4','#skF_5',D_55)
      | ~ r2_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_778])).

tff(c_871,plain,(
    ! [B_292,C_293] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_292,C_293))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_292,C_293))
      | r1_yellow_0('#skF_4',B_292)
      | ~ r2_lattice3('#skF_4',B_292,C_293)
      | ~ m1_subset_1(C_293,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_867,c_836])).

tff(c_874,plain,(
    ! [B_292,C_293] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_292,C_293))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_292,C_293))
      | r1_yellow_0('#skF_4',B_292)
      | ~ r2_lattice3('#skF_4',B_292,C_293)
      | ~ m1_subset_1(C_293,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_871])).

tff(c_880,plain,(
    ! [C_298] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_298))
      | r1_yellow_0('#skF_4','#skF_6')
      | ~ r2_lattice3('#skF_4','#skF_6',C_298)
      | ~ m1_subset_1(C_298,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_876,c_874])).

tff(c_883,plain,(
    ! [C_298] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_298))
      | r1_yellow_0('#skF_4','#skF_6')
      | ~ r2_lattice3('#skF_4','#skF_6',C_298)
      | ~ m1_subset_1(C_298,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_880])).

tff(c_885,plain,(
    ! [C_299] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_299))
      | ~ r2_lattice3('#skF_4','#skF_6',C_299)
      | ~ m1_subset_1(C_299,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_756,c_883])).

tff(c_889,plain,
    ( r1_yellow_0('#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ r2_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_885,c_18])).

tff(c_892,plain,(
    r1_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_81,c_28,c_26,c_889])).

tff(c_894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_756,c_892])).

tff(c_895,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4','#skF_5',D_55)
      | ~ r2_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_775])).

tff(c_926,plain,(
    ! [B_306,C_307] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_306,C_307))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_306,C_307))
      | r1_yellow_0('#skF_4',B_306)
      | ~ r2_lattice3('#skF_4',B_306,C_307)
      | ~ m1_subset_1(C_307,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_922,c_895])).

tff(c_929,plain,(
    ! [B_306,C_307] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_306,C_307))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_306,C_307))
      | r1_yellow_0('#skF_4',B_306)
      | ~ r2_lattice3('#skF_4',B_306,C_307)
      | ~ m1_subset_1(C_307,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_926])).

tff(c_935,plain,(
    ! [C_312] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_312))
      | r1_yellow_0('#skF_4','#skF_6')
      | ~ r2_lattice3('#skF_4','#skF_6',C_312)
      | ~ m1_subset_1(C_312,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_931,c_929])).

tff(c_938,plain,(
    ! [C_312] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_312))
      | r1_yellow_0('#skF_4','#skF_6')
      | ~ r2_lattice3('#skF_4','#skF_6',C_312)
      | ~ m1_subset_1(C_312,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_935])).

tff(c_939,plain,(
    ! [C_312] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_312))
      | ~ r2_lattice3('#skF_4','#skF_6',C_312)
      | ~ m1_subset_1(C_312,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_756,c_938])).

tff(c_941,plain,(
    ! [A_314,C_315,B_316] :
      ( ~ r1_orders_2(A_314,C_315,'#skF_2'(A_314,B_316,C_315))
      | r1_yellow_0(A_314,B_316)
      | ~ r2_lattice3(A_314,B_316,C_315)
      | ~ m1_subset_1(C_315,u1_struct_0(A_314))
      | ~ l1_orders_2(A_314)
      | ~ v5_orders_2(A_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_945,plain,
    ( r1_yellow_0('#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ r2_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_939,c_941])).

tff(c_952,plain,(
    r1_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_81,c_28,c_26,c_945])).

tff(c_954,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_756,c_952])).

tff(c_955,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4','#skF_5',D_55)
      | ~ r2_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_772])).

tff(c_994,plain,(
    ! [B_326,C_327] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_326,C_327))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_326,C_327))
      | r1_yellow_0('#skF_4',B_326)
      | ~ r2_lattice3('#skF_4',B_326,C_327)
      | ~ m1_subset_1(C_327,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_990,c_955])).

tff(c_1059,plain,(
    ! [B_345,C_346] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_345,C_346))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_345,C_346))
      | r1_yellow_0('#skF_4',B_345)
      | ~ r2_lattice3('#skF_4',B_345,C_346)
      | ~ m1_subset_1(C_346,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_994])).

tff(c_1063,plain,(
    ! [C_34] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_34))
      | r1_yellow_0('#skF_4','#skF_6')
      | ~ r2_lattice3('#skF_4','#skF_6',C_34)
      | ~ m1_subset_1(C_34,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_1059])).

tff(c_1066,plain,(
    ! [C_34] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_34))
      | r1_yellow_0('#skF_4','#skF_6')
      | ~ r2_lattice3('#skF_4','#skF_6',C_34)
      | ~ m1_subset_1(C_34,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1063])).

tff(c_1068,plain,(
    ! [C_347] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_347))
      | ~ r2_lattice3('#skF_4','#skF_6',C_347)
      | ~ m1_subset_1(C_347,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_756,c_1066])).

tff(c_1072,plain,
    ( r1_yellow_0('#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ r2_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1068,c_18])).

tff(c_1075,plain,(
    r1_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_81,c_28,c_26,c_1072])).

tff(c_1077,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_756,c_1075])).

tff(c_1079,plain,(
    r1_yellow_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_749])).

tff(c_30,plain,
    ( ~ r1_yellow_0('#skF_4','#skF_6')
    | k1_yellow_0('#skF_4','#skF_6') != '#skF_5'
    | ~ r1_orders_2('#skF_4','#skF_5','#skF_8')
    | ~ r2_lattice3('#skF_4','#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1081,plain,(
    ~ r1_orders_2('#skF_4','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_750,c_1079,c_30])).

tff(c_36,plain,
    ( ~ r1_yellow_0('#skF_4','#skF_6')
    | k1_yellow_0('#skF_4','#skF_6') != '#skF_5'
    | r2_lattice3('#skF_4','#skF_7','#skF_8')
    | ~ r2_lattice3('#skF_4','#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1083,plain,(
    r2_lattice3('#skF_4','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_750,c_1079,c_36])).

tff(c_1078,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_749])).

tff(c_1117,plain,(
    ! [A_371,B_372,D_373] :
      ( r1_orders_2(A_371,k1_yellow_0(A_371,B_372),D_373)
      | ~ r2_lattice3(A_371,B_372,D_373)
      | ~ m1_subset_1(D_373,u1_struct_0(A_371))
      | ~ r1_yellow_0(A_371,B_372)
      | ~ m1_subset_1(k1_yellow_0(A_371,B_372),u1_struct_0(A_371))
      | ~ l1_orders_2(A_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1121,plain,(
    ! [D_373] :
      ( r1_orders_2('#skF_4',k1_yellow_0('#skF_4','#skF_7'),D_373)
      | ~ r2_lattice3('#skF_4','#skF_7',D_373)
      | ~ m1_subset_1(D_373,u1_struct_0('#skF_4'))
      | ~ r1_yellow_0('#skF_4','#skF_7')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1117])).

tff(c_1126,plain,(
    ! [D_374] :
      ( r1_orders_2('#skF_4','#skF_5',D_374)
      | ~ r2_lattice3('#skF_4','#skF_7',D_374)
      | ~ m1_subset_1(D_374,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_59,c_60,c_1121])).

tff(c_1137,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_8')
    | ~ r2_lattice3('#skF_4','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_1078,c_1126])).

tff(c_1153,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1083,c_1137])).

tff(c_1155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1081,c_1153])).

tff(c_1157,plain,(
    ~ r2_lattice3('#skF_4','#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_34,plain,
    ( r2_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ r1_orders_2('#skF_4','#skF_5','#skF_8')
    | ~ r2_lattice3('#skF_4','#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1162,plain,
    ( r2_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ r1_orders_2('#skF_4','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_34])).

tff(c_1163,plain,(
    ~ r1_orders_2('#skF_4','#skF_5','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1157,c_1162])).

tff(c_40,plain,
    ( r2_lattice3('#skF_4','#skF_6','#skF_5')
    | r2_lattice3('#skF_4','#skF_7','#skF_8')
    | ~ r2_lattice3('#skF_4','#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1159,plain,
    ( r2_lattice3('#skF_4','#skF_6','#skF_5')
    | r2_lattice3('#skF_4','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_40])).

tff(c_1160,plain,(
    r2_lattice3('#skF_4','#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1157,c_1159])).

tff(c_1156,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_1202,plain,(
    ! [A_402,B_403,D_404] :
      ( r1_orders_2(A_402,k1_yellow_0(A_402,B_403),D_404)
      | ~ r2_lattice3(A_402,B_403,D_404)
      | ~ m1_subset_1(D_404,u1_struct_0(A_402))
      | ~ r1_yellow_0(A_402,B_403)
      | ~ m1_subset_1(k1_yellow_0(A_402,B_403),u1_struct_0(A_402))
      | ~ l1_orders_2(A_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1204,plain,(
    ! [D_404] :
      ( r1_orders_2('#skF_4',k1_yellow_0('#skF_4','#skF_7'),D_404)
      | ~ r2_lattice3('#skF_4','#skF_7',D_404)
      | ~ m1_subset_1(D_404,u1_struct_0('#skF_4'))
      | ~ r1_yellow_0('#skF_4','#skF_7')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1202])).

tff(c_1207,plain,(
    ! [D_405] :
      ( r1_orders_2('#skF_4','#skF_5',D_405)
      | ~ r2_lattice3('#skF_4','#skF_7',D_405)
      | ~ m1_subset_1(D_405,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_59,c_60,c_1204])).

tff(c_1222,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_8')
    | ~ r2_lattice3('#skF_4','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_1156,c_1207])).

tff(c_1237,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1160,c_1222])).

tff(c_1239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1163,c_1237])).

tff(c_1241,plain,(
    k1_yellow_0('#skF_4','#skF_7') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_54,plain,
    ( ~ r1_yellow_0('#skF_4','#skF_6')
    | k1_yellow_0('#skF_4','#skF_6') != '#skF_5'
    | k1_yellow_0('#skF_4','#skF_7') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1243,plain,
    ( ~ r1_yellow_0('#skF_4','#skF_6')
    | k1_yellow_0('#skF_4','#skF_6') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1241,c_54])).

tff(c_1244,plain,(
    k1_yellow_0('#skF_4','#skF_6') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1243])).

tff(c_1240,plain,(
    r2_lattice3('#skF_4','#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4','#skF_5',D_55)
      | ~ r2_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | k1_yellow_0('#skF_4','#skF_7') = '#skF_5' ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1252,plain,(
    ! [D_410] :
      ( r1_orders_2('#skF_4','#skF_5',D_410)
      | ~ r2_lattice3('#skF_4','#skF_6',D_410)
      | ~ m1_subset_1(D_410,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1241,c_56])).

tff(c_1256,plain,(
    ! [B_27] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_3'('#skF_4',B_27))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_3'('#skF_4',B_27))
      | ~ r1_yellow_0('#skF_4',B_27)
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_1252])).

tff(c_1266,plain,(
    ! [B_411] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_3'('#skF_4',B_411))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_3'('#skF_4',B_411))
      | ~ r1_yellow_0('#skF_4',B_411) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1256])).

tff(c_1270,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_3'('#skF_4','#skF_6'))
    | ~ r1_yellow_0('#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_1266])).

tff(c_1273,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_3'('#skF_4','#skF_6'))
    | ~ r1_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1270])).

tff(c_1274,plain,(
    ~ r1_yellow_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1273])).

tff(c_1286,plain,(
    ! [A_422,B_423,C_424] :
      ( r2_lattice3(A_422,B_423,'#skF_2'(A_422,B_423,C_424))
      | r1_yellow_0(A_422,B_423)
      | ~ r2_lattice3(A_422,B_423,C_424)
      | ~ m1_subset_1(C_424,u1_struct_0(A_422))
      | ~ l1_orders_2(A_422)
      | ~ v5_orders_2(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1277,plain,(
    ! [A_417,B_418,C_419] :
      ( m1_subset_1('#skF_2'(A_417,B_418,C_419),u1_struct_0(A_417))
      | r1_yellow_0(A_417,B_418)
      | ~ r2_lattice3(A_417,B_418,C_419)
      | ~ m1_subset_1(C_419,u1_struct_0(A_417))
      | ~ l1_orders_2(A_417)
      | ~ v5_orders_2(A_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1251,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4','#skF_5',D_55)
      | ~ r2_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1241,c_56])).

tff(c_1281,plain,(
    ! [B_418,C_419] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_418,C_419))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_418,C_419))
      | r1_yellow_0('#skF_4',B_418)
      | ~ r2_lattice3('#skF_4',B_418,C_419)
      | ~ m1_subset_1(C_419,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1277,c_1251])).

tff(c_1284,plain,(
    ! [B_418,C_419] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_418,C_419))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_418,C_419))
      | r1_yellow_0('#skF_4',B_418)
      | ~ r2_lattice3('#skF_4',B_418,C_419)
      | ~ m1_subset_1(C_419,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1281])).

tff(c_1290,plain,(
    ! [C_424] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_424))
      | r1_yellow_0('#skF_4','#skF_6')
      | ~ r2_lattice3('#skF_4','#skF_6',C_424)
      | ~ m1_subset_1(C_424,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1286,c_1284])).

tff(c_1293,plain,(
    ! [C_424] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_424))
      | r1_yellow_0('#skF_4','#skF_6')
      | ~ r2_lattice3('#skF_4','#skF_6',C_424)
      | ~ m1_subset_1(C_424,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1290])).

tff(c_1294,plain,(
    ! [C_424] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_424))
      | ~ r2_lattice3('#skF_4','#skF_6',C_424)
      | ~ m1_subset_1(C_424,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1274,c_1293])).

tff(c_1296,plain,(
    ! [A_426,C_427,B_428] :
      ( ~ r1_orders_2(A_426,C_427,'#skF_2'(A_426,B_428,C_427))
      | r1_yellow_0(A_426,B_428)
      | ~ r2_lattice3(A_426,B_428,C_427)
      | ~ m1_subset_1(C_427,u1_struct_0(A_426))
      | ~ l1_orders_2(A_426)
      | ~ v5_orders_2(A_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1300,plain,
    ( r1_yellow_0('#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ r2_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1294,c_1296])).

tff(c_1307,plain,(
    r1_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1240,c_28,c_26,c_1300])).

tff(c_1309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1274,c_1307])).

tff(c_1311,plain,(
    r1_yellow_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1273])).

tff(c_1336,plain,(
    ! [A_449,B_450,C_451] :
      ( m1_subset_1('#skF_1'(A_449,B_450,C_451),u1_struct_0(A_449))
      | k1_yellow_0(A_449,B_450) = C_451
      | ~ r2_lattice3(A_449,B_450,C_451)
      | ~ r1_yellow_0(A_449,B_450)
      | ~ m1_subset_1(C_451,u1_struct_0(A_449))
      | ~ l1_orders_2(A_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1340,plain,(
    ! [B_450,C_451] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_1'('#skF_4',B_450,C_451))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_450,C_451))
      | k1_yellow_0('#skF_4',B_450) = C_451
      | ~ r2_lattice3('#skF_4',B_450,C_451)
      | ~ r1_yellow_0('#skF_4',B_450)
      | ~ m1_subset_1(C_451,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1336,c_1251])).

tff(c_1353,plain,(
    ! [B_457,C_458] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_1'('#skF_4',B_457,C_458))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_457,C_458))
      | k1_yellow_0('#skF_4',B_457) = C_458
      | ~ r2_lattice3('#skF_4',B_457,C_458)
      | ~ r1_yellow_0('#skF_4',B_457)
      | ~ m1_subset_1(C_458,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1340])).

tff(c_1357,plain,(
    ! [C_9] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_6',C_9))
      | k1_yellow_0('#skF_4','#skF_6') = C_9
      | ~ r2_lattice3('#skF_4','#skF_6',C_9)
      | ~ r1_yellow_0('#skF_4','#skF_6')
      | ~ m1_subset_1(C_9,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4,c_1353])).

tff(c_1361,plain,(
    ! [C_459] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_6',C_459))
      | k1_yellow_0('#skF_4','#skF_6') = C_459
      | ~ r2_lattice3('#skF_4','#skF_6',C_459)
      | ~ m1_subset_1(C_459,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1311,c_1357])).

tff(c_1365,plain,
    ( ~ r1_yellow_0('#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_4')
    | k1_yellow_0('#skF_4','#skF_6') = '#skF_5'
    | ~ r2_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1361,c_2])).

tff(c_1368,plain,(
    k1_yellow_0('#skF_4','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1240,c_26,c_1311,c_1365])).

tff(c_1370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1244,c_1368])).

tff(c_1371,plain,(
    ~ r1_yellow_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1243])).

tff(c_1427,plain,(
    ! [A_476,B_477,C_478] :
      ( r2_lattice3(A_476,B_477,'#skF_2'(A_476,B_477,C_478))
      | r1_yellow_0(A_476,B_477)
      | ~ r2_lattice3(A_476,B_477,C_478)
      | ~ m1_subset_1(C_478,u1_struct_0(A_476))
      | ~ l1_orders_2(A_476)
      | ~ v5_orders_2(A_476) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1418,plain,(
    ! [A_471,B_472,C_473] :
      ( m1_subset_1('#skF_2'(A_471,B_472,C_473),u1_struct_0(A_471))
      | r1_yellow_0(A_471,B_472)
      | ~ r2_lattice3(A_471,B_472,C_473)
      | ~ m1_subset_1(C_473,u1_struct_0(A_471))
      | ~ l1_orders_2(A_471)
      | ~ v5_orders_2(A_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1389,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4','#skF_5',D_55)
      | ~ r2_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1241,c_56])).

tff(c_1422,plain,(
    ! [B_472,C_473] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_472,C_473))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_472,C_473))
      | r1_yellow_0('#skF_4',B_472)
      | ~ r2_lattice3('#skF_4',B_472,C_473)
      | ~ m1_subset_1(C_473,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1418,c_1389])).

tff(c_1425,plain,(
    ! [B_472,C_473] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_472,C_473))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_472,C_473))
      | r1_yellow_0('#skF_4',B_472)
      | ~ r2_lattice3('#skF_4',B_472,C_473)
      | ~ m1_subset_1(C_473,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1422])).

tff(c_1431,plain,(
    ! [C_478] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_478))
      | r1_yellow_0('#skF_4','#skF_6')
      | ~ r2_lattice3('#skF_4','#skF_6',C_478)
      | ~ m1_subset_1(C_478,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1427,c_1425])).

tff(c_1434,plain,(
    ! [C_478] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_478))
      | r1_yellow_0('#skF_4','#skF_6')
      | ~ r2_lattice3('#skF_4','#skF_6',C_478)
      | ~ m1_subset_1(C_478,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1431])).

tff(c_1435,plain,(
    ! [C_478] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_478))
      | ~ r2_lattice3('#skF_4','#skF_6',C_478)
      | ~ m1_subset_1(C_478,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1371,c_1434])).

tff(c_1437,plain,(
    ! [A_480,C_481,B_482] :
      ( ~ r1_orders_2(A_480,C_481,'#skF_2'(A_480,B_482,C_481))
      | r1_yellow_0(A_480,B_482)
      | ~ r2_lattice3(A_480,B_482,C_481)
      | ~ m1_subset_1(C_481,u1_struct_0(A_480))
      | ~ l1_orders_2(A_480)
      | ~ v5_orders_2(A_480) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1441,plain,
    ( r1_yellow_0('#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ r2_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1435,c_1437])).

tff(c_1448,plain,(
    r1_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1240,c_28,c_26,c_1441])).

tff(c_1450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1371,c_1448])).

tff(c_1452,plain,(
    ~ r1_yellow_0('#skF_4','#skF_7') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_48,plain,
    ( ~ r1_yellow_0('#skF_4','#skF_6')
    | k1_yellow_0('#skF_4','#skF_6') != '#skF_5'
    | r1_yellow_0('#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1454,plain,
    ( ~ r1_yellow_0('#skF_4','#skF_6')
    | k1_yellow_0('#skF_4','#skF_6') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1452,c_48])).

tff(c_1455,plain,(
    k1_yellow_0('#skF_4','#skF_6') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1454])).

tff(c_1451,plain,(
    r2_lattice3('#skF_4','#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4','#skF_5',D_55)
      | ~ r2_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | r1_yellow_0('#skF_4','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1462,plain,(
    ! [D_487] :
      ( r1_orders_2('#skF_4','#skF_5',D_487)
      | ~ r2_lattice3('#skF_4','#skF_6',D_487)
      | ~ m1_subset_1(D_487,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1452,c_50])).

tff(c_1466,plain,(
    ! [B_27] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_3'('#skF_4',B_27))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_3'('#skF_4',B_27))
      | ~ r1_yellow_0('#skF_4',B_27)
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_1462])).

tff(c_1476,plain,(
    ! [B_488] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_3'('#skF_4',B_488))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_3'('#skF_4',B_488))
      | ~ r1_yellow_0('#skF_4',B_488) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1466])).

tff(c_1480,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_3'('#skF_4','#skF_6'))
    | ~ r1_yellow_0('#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_1476])).

tff(c_1483,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_3'('#skF_4','#skF_6'))
    | ~ r1_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1480])).

tff(c_1484,plain,(
    ~ r1_yellow_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1483])).

tff(c_1494,plain,(
    ! [A_500,B_501,C_502] :
      ( m1_subset_1('#skF_2'(A_500,B_501,C_502),u1_struct_0(A_500))
      | r1_yellow_0(A_500,B_501)
      | ~ r2_lattice3(A_500,B_501,C_502)
      | ~ m1_subset_1(C_502,u1_struct_0(A_500))
      | ~ l1_orders_2(A_500)
      | ~ v5_orders_2(A_500) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1461,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4','#skF_5',D_55)
      | ~ r2_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1452,c_50])).

tff(c_1498,plain,(
    ! [B_501,C_502] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_501,C_502))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_501,C_502))
      | r1_yellow_0('#skF_4',B_501)
      | ~ r2_lattice3('#skF_4',B_501,C_502)
      | ~ m1_subset_1(C_502,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1494,c_1461])).

tff(c_1518,plain,(
    ! [B_515,C_516] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_515,C_516))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_515,C_516))
      | r1_yellow_0('#skF_4',B_515)
      | ~ r2_lattice3('#skF_4',B_515,C_516)
      | ~ m1_subset_1(C_516,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1498])).

tff(c_1522,plain,(
    ! [C_34] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_34))
      | r1_yellow_0('#skF_4','#skF_6')
      | ~ r2_lattice3('#skF_4','#skF_6',C_34)
      | ~ m1_subset_1(C_34,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_1518])).

tff(c_1525,plain,(
    ! [C_34] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_34))
      | r1_yellow_0('#skF_4','#skF_6')
      | ~ r2_lattice3('#skF_4','#skF_6',C_34)
      | ~ m1_subset_1(C_34,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1522])).

tff(c_1527,plain,(
    ! [C_517] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_517))
      | ~ r2_lattice3('#skF_4','#skF_6',C_517)
      | ~ m1_subset_1(C_517,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1484,c_1525])).

tff(c_1531,plain,
    ( r1_yellow_0('#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ r2_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1527,c_18])).

tff(c_1534,plain,(
    r1_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1451,c_28,c_26,c_1531])).

tff(c_1536,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1484,c_1534])).

tff(c_1538,plain,(
    r1_yellow_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1483])).

tff(c_1556,plain,(
    ! [A_532,B_533,C_534] :
      ( m1_subset_1('#skF_1'(A_532,B_533,C_534),u1_struct_0(A_532))
      | k1_yellow_0(A_532,B_533) = C_534
      | ~ r2_lattice3(A_532,B_533,C_534)
      | ~ r1_yellow_0(A_532,B_533)
      | ~ m1_subset_1(C_534,u1_struct_0(A_532))
      | ~ l1_orders_2(A_532) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1560,plain,(
    ! [B_533,C_534] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_1'('#skF_4',B_533,C_534))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_533,C_534))
      | k1_yellow_0('#skF_4',B_533) = C_534
      | ~ r2_lattice3('#skF_4',B_533,C_534)
      | ~ r1_yellow_0('#skF_4',B_533)
      | ~ m1_subset_1(C_534,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1556,c_1461])).

tff(c_1580,plain,(
    ! [B_546,C_547] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_1'('#skF_4',B_546,C_547))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_546,C_547))
      | k1_yellow_0('#skF_4',B_546) = C_547
      | ~ r2_lattice3('#skF_4',B_546,C_547)
      | ~ r1_yellow_0('#skF_4',B_546)
      | ~ m1_subset_1(C_547,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1560])).

tff(c_1584,plain,(
    ! [C_9] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_6',C_9))
      | k1_yellow_0('#skF_4','#skF_6') = C_9
      | ~ r2_lattice3('#skF_4','#skF_6',C_9)
      | ~ r1_yellow_0('#skF_4','#skF_6')
      | ~ m1_subset_1(C_9,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4,c_1580])).

tff(c_1588,plain,(
    ! [C_548] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_6',C_548))
      | k1_yellow_0('#skF_4','#skF_6') = C_548
      | ~ r2_lattice3('#skF_4','#skF_6',C_548)
      | ~ m1_subset_1(C_548,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1538,c_1584])).

tff(c_1592,plain,
    ( ~ r1_yellow_0('#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_4')
    | k1_yellow_0('#skF_4','#skF_6') = '#skF_5'
    | ~ r2_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1588,c_2])).

tff(c_1595,plain,(
    k1_yellow_0('#skF_4','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1451,c_26,c_1538,c_1592])).

tff(c_1597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1455,c_1595])).

tff(c_1598,plain,(
    ~ r1_yellow_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1454])).

tff(c_1653,plain,(
    ! [A_566,B_567,C_568] :
      ( m1_subset_1('#skF_2'(A_566,B_567,C_568),u1_struct_0(A_566))
      | r1_yellow_0(A_566,B_567)
      | ~ r2_lattice3(A_566,B_567,C_568)
      | ~ m1_subset_1(C_568,u1_struct_0(A_566))
      | ~ l1_orders_2(A_566)
      | ~ v5_orders_2(A_566) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1613,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4','#skF_5',D_55)
      | ~ r2_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1452,c_50])).

tff(c_1657,plain,(
    ! [B_567,C_568] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_567,C_568))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_567,C_568))
      | r1_yellow_0('#skF_4',B_567)
      | ~ r2_lattice3('#skF_4',B_567,C_568)
      | ~ m1_subset_1(C_568,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1653,c_1613])).

tff(c_1675,plain,(
    ! [B_575,C_576] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_575,C_576))
      | ~ r2_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_575,C_576))
      | r1_yellow_0('#skF_4',B_575)
      | ~ r2_lattice3('#skF_4',B_575,C_576)
      | ~ m1_subset_1(C_576,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1657])).

tff(c_1679,plain,(
    ! [C_34] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_34))
      | r1_yellow_0('#skF_4','#skF_6')
      | ~ r2_lattice3('#skF_4','#skF_6',C_34)
      | ~ m1_subset_1(C_34,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_1675])).

tff(c_1682,plain,(
    ! [C_34] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_34))
      | r1_yellow_0('#skF_4','#skF_6')
      | ~ r2_lattice3('#skF_4','#skF_6',C_34)
      | ~ m1_subset_1(C_34,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1679])).

tff(c_1684,plain,(
    ! [C_577] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4','#skF_6',C_577))
      | ~ r2_lattice3('#skF_4','#skF_6',C_577)
      | ~ m1_subset_1(C_577,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1598,c_1682])).

tff(c_1688,plain,
    ( r1_yellow_0('#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ r2_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1684,c_18])).

tff(c_1691,plain,(
    r1_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1451,c_28,c_26,c_1688])).

tff(c_1693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1598,c_1691])).

%------------------------------------------------------------------------------
