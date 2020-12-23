%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1553+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:03 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :  243 ( 864 expanded)
%              Number of leaves         :   22 ( 298 expanded)
%              Depth                    :   12
%              Number of atoms          :  830 (5376 expanded)
%              Number of equality atoms :   57 ( 600 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r1_lattice3 > r2_yellow_0 > m1_subset_1 > v5_orders_2 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

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
                ( ( ( B = k2_yellow_0(A,C)
                    & r2_yellow_0(A,C) )
                 => ( r1_lattice3(A,C,B)
                    & ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => ( r1_lattice3(A,C,D)
                         => r1_orders_2(A,D,B) ) ) ) )
                & ( ( r1_lattice3(A,C,B)
                    & ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => ( r1_lattice3(A,C,D)
                         => r1_orders_2(A,D,B) ) ) )
                 => ( B = k2_yellow_0(A,C)
                    & r2_yellow_0(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_yellow_0)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_yellow_0(A,B)
           => ( C = k2_yellow_0(A,B)
            <=> ( r1_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r1_lattice3(A,B,D)
                     => r1_orders_2(A,D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r2_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r1_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r1_lattice3(A,B,D)
                   => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_0)).

tff(c_46,plain,
    ( r1_lattice3('#skF_4','#skF_6','#skF_5')
    | m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ r1_lattice3('#skF_4','#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_67,plain,(
    ~ r1_lattice3('#skF_4','#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_26,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_52,plain,
    ( r1_lattice3('#skF_4','#skF_6','#skF_5')
    | r2_yellow_0('#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_59,plain,(
    r2_yellow_0('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,
    ( r1_lattice3('#skF_4','#skF_6','#skF_5')
    | k2_yellow_0('#skF_4','#skF_7') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_60,plain,(
    k2_yellow_0('#skF_4','#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_72,plain,(
    ! [A_61,B_62] :
      ( r1_lattice3(A_61,B_62,k2_yellow_0(A_61,B_62))
      | ~ r2_yellow_0(A_61,B_62)
      | ~ m1_subset_1(k2_yellow_0(A_61,B_62),u1_struct_0(A_61))
      | ~ l1_orders_2(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_74,plain,
    ( r1_lattice3('#skF_4','#skF_7',k2_yellow_0('#skF_4','#skF_7'))
    | ~ r2_yellow_0('#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_72])).

tff(c_76,plain,(
    r1_lattice3('#skF_4','#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_59,c_60,c_74])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_76])).

tff(c_80,plain,(
    r1_lattice3('#skF_4','#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_42,plain,
    ( ~ r2_yellow_0('#skF_4','#skF_6')
    | k2_yellow_0('#skF_4','#skF_6') != '#skF_5'
    | m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ r1_lattice3('#skF_4','#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_89,plain,
    ( ~ r2_yellow_0('#skF_4','#skF_6')
    | k2_yellow_0('#skF_4','#skF_6') != '#skF_5'
    | m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_42])).

tff(c_90,plain,(
    k2_yellow_0('#skF_4','#skF_6') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_28,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_79,plain,
    ( m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | r1_lattice3('#skF_4','#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_81,plain,(
    r1_lattice3('#skF_4','#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_20,plain,(
    ! [A_13,B_27,C_34] :
      ( r1_lattice3(A_13,B_27,'#skF_2'(A_13,B_27,C_34))
      | r2_yellow_0(A_13,B_27)
      | ~ r1_lattice3(A_13,B_27,C_34)
      | ~ m1_subset_1(C_34,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13)
      | ~ v5_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_456,plain,(
    ! [A_170,B_171,C_172] :
      ( m1_subset_1('#skF_2'(A_170,B_171,C_172),u1_struct_0(A_170))
      | r2_yellow_0(A_170,B_171)
      | ~ r1_lattice3(A_170,B_171,C_172)
      | ~ m1_subset_1(C_172,u1_struct_0(A_170))
      | ~ l1_orders_2(A_170)
      | ~ v5_orders_2(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_331,plain,(
    ! [A_136,B_137,C_138] :
      ( m1_subset_1('#skF_2'(A_136,B_137,C_138),u1_struct_0(A_136))
      | r2_yellow_0(A_136,B_137)
      | ~ r1_lattice3(A_136,B_137,C_138)
      | ~ m1_subset_1(C_138,u1_struct_0(A_136))
      | ~ l1_orders_2(A_136)
      | ~ v5_orders_2(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_193,plain,(
    ! [A_102,B_103,C_104] :
      ( m1_subset_1('#skF_2'(A_102,B_103,C_104),u1_struct_0(A_102))
      | r2_yellow_0(A_102,B_103)
      | ~ r1_lattice3(A_102,B_103,C_104)
      | ~ m1_subset_1(C_104,u1_struct_0(A_102))
      | ~ l1_orders_2(A_102)
      | ~ v5_orders_2(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4',D_55,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4','#skF_8','#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_7','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_106,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4',D_55,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4','#skF_8','#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_32])).

tff(c_107,plain,(
    ~ r1_orders_2('#skF_4','#skF_8','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_38,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4',D_55,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4','#skF_7','#skF_8')
      | ~ r1_lattice3('#skF_4','#skF_7','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_109,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4',D_55,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4','#skF_7','#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_38])).

tff(c_110,plain,(
    r1_lattice3('#skF_4','#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_44,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4',D_55,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_4','#skF_7','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_103,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4',D_55,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_44])).

tff(c_104,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_128,plain,(
    ! [A_90,D_91,B_92] :
      ( r1_orders_2(A_90,D_91,k2_yellow_0(A_90,B_92))
      | ~ r1_lattice3(A_90,B_92,D_91)
      | ~ m1_subset_1(D_91,u1_struct_0(A_90))
      | ~ r2_yellow_0(A_90,B_92)
      | ~ m1_subset_1(k2_yellow_0(A_90,B_92),u1_struct_0(A_90))
      | ~ l1_orders_2(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_130,plain,(
    ! [D_91] :
      ( r1_orders_2('#skF_4',D_91,k2_yellow_0('#skF_4','#skF_7'))
      | ~ r1_lattice3('#skF_4','#skF_7',D_91)
      | ~ m1_subset_1(D_91,u1_struct_0('#skF_4'))
      | ~ r2_yellow_0('#skF_4','#skF_7')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_128])).

tff(c_133,plain,(
    ! [D_93] :
      ( r1_orders_2('#skF_4',D_93,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_7',D_93)
      | ~ m1_subset_1(D_93,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_59,c_60,c_130])).

tff(c_144,plain,
    ( r1_orders_2('#skF_4','#skF_8','#skF_5')
    | ~ r1_lattice3('#skF_4','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_104,c_133])).

tff(c_160,plain,(
    r1_orders_2('#skF_4','#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_144])).

tff(c_162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_160])).

tff(c_163,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4',D_55,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_197,plain,(
    ! [B_103,C_104] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_103,C_104),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_103,C_104))
      | r2_yellow_0('#skF_4',B_103)
      | ~ r1_lattice3('#skF_4',B_103,C_104)
      | ~ m1_subset_1(C_104,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_193,c_163])).

tff(c_202,plain,(
    ! [B_108,C_109] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_108,C_109),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_108,C_109))
      | r2_yellow_0('#skF_4',B_108)
      | ~ r1_lattice3('#skF_4',B_108,C_109)
      | ~ m1_subset_1(C_109,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_197])).

tff(c_18,plain,(
    ! [A_13,B_27,C_34] :
      ( ~ r1_orders_2(A_13,'#skF_2'(A_13,B_27,C_34),C_34)
      | r2_yellow_0(A_13,B_27)
      | ~ r1_lattice3(A_13,B_27,C_34)
      | ~ m1_subset_1(C_34,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13)
      | ~ v5_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_206,plain,(
    ! [B_108] :
      ( ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_108,'#skF_5'))
      | r2_yellow_0('#skF_4',B_108)
      | ~ r1_lattice3('#skF_4',B_108,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_202,c_18])).

tff(c_210,plain,(
    ! [B_110] :
      ( ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_110,'#skF_5'))
      | r2_yellow_0('#skF_4',B_110)
      | ~ r1_lattice3('#skF_4',B_110,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_26,c_206])).

tff(c_214,plain,
    ( r2_yellow_0('#skF_4','#skF_6')
    | ~ r1_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_210])).

tff(c_217,plain,(
    r2_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_81,c_214])).

tff(c_4,plain,(
    ! [A_1,B_8,C_9] :
      ( r1_lattice3(A_1,B_8,'#skF_1'(A_1,B_8,C_9))
      | k2_yellow_0(A_1,B_8) = C_9
      | ~ r1_lattice3(A_1,B_8,C_9)
      | ~ r2_yellow_0(A_1,B_8)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_225,plain,(
    ! [A_117,B_118,C_119] :
      ( m1_subset_1('#skF_1'(A_117,B_118,C_119),u1_struct_0(A_117))
      | k2_yellow_0(A_117,B_118) = C_119
      | ~ r1_lattice3(A_117,B_118,C_119)
      | ~ r2_yellow_0(A_117,B_118)
      | ~ m1_subset_1(C_119,u1_struct_0(A_117))
      | ~ l1_orders_2(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_229,plain,(
    ! [B_118,C_119] :
      ( r1_orders_2('#skF_4','#skF_1'('#skF_4',B_118,C_119),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_118,C_119))
      | k2_yellow_0('#skF_4',B_118) = C_119
      | ~ r1_lattice3('#skF_4',B_118,C_119)
      | ~ r2_yellow_0('#skF_4',B_118)
      | ~ m1_subset_1(C_119,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_225,c_163])).

tff(c_280,plain,(
    ! [B_127,C_128] :
      ( r1_orders_2('#skF_4','#skF_1'('#skF_4',B_127,C_128),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_127,C_128))
      | k2_yellow_0('#skF_4',B_127) = C_128
      | ~ r1_lattice3('#skF_4',B_127,C_128)
      | ~ r2_yellow_0('#skF_4',B_127)
      | ~ m1_subset_1(C_128,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_229])).

tff(c_2,plain,(
    ! [A_1,B_8,C_9] :
      ( ~ r1_orders_2(A_1,'#skF_1'(A_1,B_8,C_9),C_9)
      | k2_yellow_0(A_1,B_8) = C_9
      | ~ r1_lattice3(A_1,B_8,C_9)
      | ~ r2_yellow_0(A_1,B_8)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_284,plain,(
    ! [B_127] :
      ( ~ l1_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_127,'#skF_5'))
      | k2_yellow_0('#skF_4',B_127) = '#skF_5'
      | ~ r1_lattice3('#skF_4',B_127,'#skF_5')
      | ~ r2_yellow_0('#skF_4',B_127)
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_280,c_2])).

tff(c_296,plain,(
    ! [B_130] :
      ( ~ r1_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_130,'#skF_5'))
      | k2_yellow_0('#skF_4',B_130) = '#skF_5'
      | ~ r1_lattice3('#skF_4',B_130,'#skF_5')
      | ~ r2_yellow_0('#skF_4',B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_284])).

tff(c_300,plain,
    ( k2_yellow_0('#skF_4','#skF_6') = '#skF_5'
    | ~ r1_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ r2_yellow_0('#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_296])).

tff(c_303,plain,(
    k2_yellow_0('#skF_4','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_217,c_81,c_300])).

tff(c_305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_303])).

tff(c_306,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4',D_55,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_335,plain,(
    ! [B_137,C_138] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_137,C_138),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_137,C_138))
      | r2_yellow_0('#skF_4',B_137)
      | ~ r1_lattice3('#skF_4',B_137,C_138)
      | ~ m1_subset_1(C_138,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_331,c_306])).

tff(c_338,plain,(
    ! [B_137,C_138] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_137,C_138),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_137,C_138))
      | r2_yellow_0('#skF_4',B_137)
      | ~ r1_lattice3('#skF_4',B_137,C_138)
      | ~ m1_subset_1(C_138,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_335])).

tff(c_341,plain,(
    ! [A_144,B_145,C_146] :
      ( ~ r1_orders_2(A_144,'#skF_2'(A_144,B_145,C_146),C_146)
      | r2_yellow_0(A_144,B_145)
      | ~ r1_lattice3(A_144,B_145,C_146)
      | ~ m1_subset_1(C_146,u1_struct_0(A_144))
      | ~ l1_orders_2(A_144)
      | ~ v5_orders_2(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_345,plain,(
    ! [B_137] :
      ( ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_137,'#skF_5'))
      | r2_yellow_0('#skF_4',B_137)
      | ~ r1_lattice3('#skF_4',B_137,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_338,c_341])).

tff(c_354,plain,(
    ! [B_147] :
      ( ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_147,'#skF_5'))
      | r2_yellow_0('#skF_4',B_147)
      | ~ r1_lattice3('#skF_4',B_147,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_26,c_345])).

tff(c_358,plain,
    ( r2_yellow_0('#skF_4','#skF_6')
    | ~ r1_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_354])).

tff(c_361,plain,(
    r2_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_81,c_358])).

tff(c_369,plain,(
    ! [A_154,B_155,C_156] :
      ( m1_subset_1('#skF_1'(A_154,B_155,C_156),u1_struct_0(A_154))
      | k2_yellow_0(A_154,B_155) = C_156
      | ~ r1_lattice3(A_154,B_155,C_156)
      | ~ r2_yellow_0(A_154,B_155)
      | ~ m1_subset_1(C_156,u1_struct_0(A_154))
      | ~ l1_orders_2(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_373,plain,(
    ! [B_155,C_156] :
      ( r1_orders_2('#skF_4','#skF_1'('#skF_4',B_155,C_156),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_155,C_156))
      | k2_yellow_0('#skF_4',B_155) = C_156
      | ~ r1_lattice3('#skF_4',B_155,C_156)
      | ~ r2_yellow_0('#skF_4',B_155)
      | ~ m1_subset_1(C_156,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_369,c_306])).

tff(c_415,plain,(
    ! [B_161,C_162] :
      ( r1_orders_2('#skF_4','#skF_1'('#skF_4',B_161,C_162),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_161,C_162))
      | k2_yellow_0('#skF_4',B_161) = C_162
      | ~ r1_lattice3('#skF_4',B_161,C_162)
      | ~ r2_yellow_0('#skF_4',B_161)
      | ~ m1_subset_1(C_162,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_373])).

tff(c_419,plain,(
    ! [B_161] :
      ( ~ l1_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_161,'#skF_5'))
      | k2_yellow_0('#skF_4',B_161) = '#skF_5'
      | ~ r1_lattice3('#skF_4',B_161,'#skF_5')
      | ~ r2_yellow_0('#skF_4',B_161)
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_415,c_2])).

tff(c_424,plain,(
    ! [B_164] :
      ( ~ r1_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_164,'#skF_5'))
      | k2_yellow_0('#skF_4',B_164) = '#skF_5'
      | ~ r1_lattice3('#skF_4',B_164,'#skF_5')
      | ~ r2_yellow_0('#skF_4',B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_419])).

tff(c_428,plain,
    ( k2_yellow_0('#skF_4','#skF_6') = '#skF_5'
    | ~ r1_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ r2_yellow_0('#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_424])).

tff(c_431,plain,(
    k2_yellow_0('#skF_4','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_361,c_81,c_428])).

tff(c_433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_431])).

tff(c_434,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4',D_55,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_460,plain,(
    ! [B_171,C_172] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_171,C_172),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_171,C_172))
      | r2_yellow_0('#skF_4',B_171)
      | ~ r1_lattice3('#skF_4',B_171,C_172)
      | ~ m1_subset_1(C_172,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_456,c_434])).

tff(c_520,plain,(
    ! [B_193,C_194] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_193,C_194),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_193,C_194))
      | r2_yellow_0('#skF_4',B_193)
      | ~ r1_lattice3('#skF_4',B_193,C_194)
      | ~ m1_subset_1(C_194,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_460])).

tff(c_524,plain,(
    ! [B_193] :
      ( ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_193,'#skF_5'))
      | r2_yellow_0('#skF_4',B_193)
      | ~ r1_lattice3('#skF_4',B_193,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_520,c_18])).

tff(c_536,plain,(
    ! [B_197] :
      ( ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_197,'#skF_5'))
      | r2_yellow_0('#skF_4',B_197)
      | ~ r1_lattice3('#skF_4',B_197,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_26,c_524])).

tff(c_540,plain,
    ( r2_yellow_0('#skF_4','#skF_6')
    | ~ r1_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_536])).

tff(c_543,plain,(
    r2_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_81,c_540])).

tff(c_478,plain,(
    ! [A_185,B_186,C_187] :
      ( m1_subset_1('#skF_1'(A_185,B_186,C_187),u1_struct_0(A_185))
      | k2_yellow_0(A_185,B_186) = C_187
      | ~ r1_lattice3(A_185,B_186,C_187)
      | ~ r2_yellow_0(A_185,B_186)
      | ~ m1_subset_1(C_187,u1_struct_0(A_185))
      | ~ l1_orders_2(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_482,plain,(
    ! [B_186,C_187] :
      ( r1_orders_2('#skF_4','#skF_1'('#skF_4',B_186,C_187),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_186,C_187))
      | k2_yellow_0('#skF_4',B_186) = C_187
      | ~ r1_lattice3('#skF_4',B_186,C_187)
      | ~ r2_yellow_0('#skF_4',B_186)
      | ~ m1_subset_1(C_187,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_478,c_434])).

tff(c_528,plain,(
    ! [B_195,C_196] :
      ( r1_orders_2('#skF_4','#skF_1'('#skF_4',B_195,C_196),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_195,C_196))
      | k2_yellow_0('#skF_4',B_195) = C_196
      | ~ r1_lattice3('#skF_4',B_195,C_196)
      | ~ r2_yellow_0('#skF_4',B_195)
      | ~ m1_subset_1(C_196,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_482])).

tff(c_532,plain,(
    ! [B_195] :
      ( ~ l1_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_195,'#skF_5'))
      | k2_yellow_0('#skF_4',B_195) = '#skF_5'
      | ~ r1_lattice3('#skF_4',B_195,'#skF_5')
      | ~ r2_yellow_0('#skF_4',B_195)
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_528,c_2])).

tff(c_544,plain,(
    ! [B_198] :
      ( ~ r1_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_198,'#skF_5'))
      | k2_yellow_0('#skF_4',B_198) = '#skF_5'
      | ~ r1_lattice3('#skF_4',B_198,'#skF_5')
      | ~ r2_yellow_0('#skF_4',B_198) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_532])).

tff(c_548,plain,
    ( k2_yellow_0('#skF_4','#skF_6') = '#skF_5'
    | ~ r1_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ r2_yellow_0('#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_544])).

tff(c_551,plain,(
    k2_yellow_0('#skF_4','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_543,c_81,c_548])).

tff(c_553,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_551])).

tff(c_555,plain,(
    k2_yellow_0('#skF_4','#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_554,plain,
    ( ~ r2_yellow_0('#skF_4','#skF_6')
    | m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_560,plain,(
    ~ r2_yellow_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_554])).

tff(c_830,plain,(
    ! [A_278,B_279,C_280] :
      ( m1_subset_1('#skF_2'(A_278,B_279,C_280),u1_struct_0(A_278))
      | r2_yellow_0(A_278,B_279)
      | ~ r1_lattice3(A_278,B_279,C_280)
      | ~ m1_subset_1(C_280,u1_struct_0(A_278))
      | ~ l1_orders_2(A_278)
      | ~ v5_orders_2(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_775,plain,(
    ! [A_261,B_262,C_263] :
      ( m1_subset_1('#skF_2'(A_261,B_262,C_263),u1_struct_0(A_261))
      | r2_yellow_0(A_261,B_262)
      | ~ r1_lattice3(A_261,B_262,C_263)
      | ~ m1_subset_1(C_263,u1_struct_0(A_261))
      | ~ l1_orders_2(A_261)
      | ~ v5_orders_2(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_670,plain,(
    ! [A_234,B_235,C_236] :
      ( m1_subset_1('#skF_2'(A_234,B_235,C_236),u1_struct_0(A_234))
      | r2_yellow_0(A_234,B_235)
      | ~ r1_lattice3(A_234,B_235,C_236)
      | ~ m1_subset_1(C_236,u1_struct_0(A_234))
      | ~ l1_orders_2(A_234)
      | ~ v5_orders_2(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_583,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4',D_55,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4','#skF_8','#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_32])).

tff(c_584,plain,(
    ~ r1_orders_2('#skF_4','#skF_8','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_583])).

tff(c_577,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4',D_55,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4','#skF_7','#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_38])).

tff(c_578,plain,(
    r1_lattice3('#skF_4','#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_577])).

tff(c_580,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4',D_55,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_44])).

tff(c_581,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_580])).

tff(c_602,plain,(
    ! [A_222,D_223,B_224] :
      ( r1_orders_2(A_222,D_223,k2_yellow_0(A_222,B_224))
      | ~ r1_lattice3(A_222,B_224,D_223)
      | ~ m1_subset_1(D_223,u1_struct_0(A_222))
      | ~ r2_yellow_0(A_222,B_224)
      | ~ m1_subset_1(k2_yellow_0(A_222,B_224),u1_struct_0(A_222))
      | ~ l1_orders_2(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_606,plain,(
    ! [D_223] :
      ( r1_orders_2('#skF_4',D_223,k2_yellow_0('#skF_4','#skF_7'))
      | ~ r1_lattice3('#skF_4','#skF_7',D_223)
      | ~ m1_subset_1(D_223,u1_struct_0('#skF_4'))
      | ~ r2_yellow_0('#skF_4','#skF_7')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_602])).

tff(c_611,plain,(
    ! [D_225] :
      ( r1_orders_2('#skF_4',D_225,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_7',D_225)
      | ~ m1_subset_1(D_225,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_59,c_60,c_606])).

tff(c_622,plain,
    ( r1_orders_2('#skF_4','#skF_8','#skF_5')
    | ~ r1_lattice3('#skF_4','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_581,c_611])).

tff(c_638,plain,(
    r1_orders_2('#skF_4','#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_622])).

tff(c_640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_584,c_638])).

tff(c_641,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4',D_55,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_583])).

tff(c_674,plain,(
    ! [B_235,C_236] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_235,C_236),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_235,C_236))
      | r2_yellow_0('#skF_4',B_235)
      | ~ r1_lattice3('#skF_4',B_235,C_236)
      | ~ m1_subset_1(C_236,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_670,c_641])).

tff(c_737,plain,(
    ! [B_253,C_254] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_253,C_254),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_253,C_254))
      | r2_yellow_0('#skF_4',B_253)
      | ~ r1_lattice3('#skF_4',B_253,C_254)
      | ~ m1_subset_1(C_254,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_674])).

tff(c_741,plain,(
    ! [B_253] :
      ( ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_253,'#skF_5'))
      | r2_yellow_0('#skF_4',B_253)
      | ~ r1_lattice3('#skF_4',B_253,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_737,c_18])).

tff(c_745,plain,(
    ! [B_255] :
      ( ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_255,'#skF_5'))
      | r2_yellow_0('#skF_4',B_255)
      | ~ r1_lattice3('#skF_4',B_255,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_26,c_741])).

tff(c_749,plain,
    ( r2_yellow_0('#skF_4','#skF_6')
    | ~ r1_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_745])).

tff(c_752,plain,(
    r2_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_81,c_749])).

tff(c_754,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_560,c_752])).

tff(c_755,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4',D_55,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_580])).

tff(c_779,plain,(
    ! [B_262,C_263] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_262,C_263),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_262,C_263))
      | r2_yellow_0('#skF_4',B_262)
      | ~ r1_lattice3('#skF_4',B_262,C_263)
      | ~ m1_subset_1(C_263,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_775,c_755])).

tff(c_782,plain,(
    ! [B_262,C_263] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_262,C_263),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_262,C_263))
      | r2_yellow_0('#skF_4',B_262)
      | ~ r1_lattice3('#skF_4',B_262,C_263)
      | ~ m1_subset_1(C_263,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_779])).

tff(c_785,plain,(
    ! [A_269,B_270,C_271] :
      ( ~ r1_orders_2(A_269,'#skF_2'(A_269,B_270,C_271),C_271)
      | r2_yellow_0(A_269,B_270)
      | ~ r1_lattice3(A_269,B_270,C_271)
      | ~ m1_subset_1(C_271,u1_struct_0(A_269))
      | ~ l1_orders_2(A_269)
      | ~ v5_orders_2(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_789,plain,(
    ! [B_262] :
      ( ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_262,'#skF_5'))
      | r2_yellow_0('#skF_4',B_262)
      | ~ r1_lattice3('#skF_4',B_262,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_782,c_785])).

tff(c_798,plain,(
    ! [B_272] :
      ( ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_272,'#skF_5'))
      | r2_yellow_0('#skF_4',B_272)
      | ~ r1_lattice3('#skF_4',B_272,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_26,c_789])).

tff(c_802,plain,
    ( r2_yellow_0('#skF_4','#skF_6')
    | ~ r1_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_798])).

tff(c_805,plain,(
    r2_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_81,c_802])).

tff(c_807,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_560,c_805])).

tff(c_808,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4',D_55,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_577])).

tff(c_834,plain,(
    ! [B_279,C_280] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_279,C_280),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_279,C_280))
      | r2_yellow_0('#skF_4',B_279)
      | ~ r1_lattice3('#skF_4',B_279,C_280)
      | ~ m1_subset_1(C_280,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_830,c_808])).

tff(c_898,plain,(
    ! [B_301,C_302] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_301,C_302),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_301,C_302))
      | r2_yellow_0('#skF_4',B_301)
      | ~ r1_lattice3('#skF_4',B_301,C_302)
      | ~ m1_subset_1(C_302,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_834])).

tff(c_902,plain,(
    ! [B_301] :
      ( ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_301,'#skF_5'))
      | r2_yellow_0('#skF_4',B_301)
      | ~ r1_lattice3('#skF_4',B_301,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_898,c_18])).

tff(c_914,plain,(
    ! [B_305] :
      ( ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_305,'#skF_5'))
      | r2_yellow_0('#skF_4',B_305)
      | ~ r1_lattice3('#skF_4',B_305,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_26,c_902])).

tff(c_918,plain,
    ( r2_yellow_0('#skF_4','#skF_6')
    | ~ r1_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_914])).

tff(c_921,plain,(
    r2_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_81,c_918])).

tff(c_923,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_560,c_921])).

tff(c_925,plain,(
    r2_yellow_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_554])).

tff(c_30,plain,
    ( ~ r2_yellow_0('#skF_4','#skF_6')
    | k2_yellow_0('#skF_4','#skF_6') != '#skF_5'
    | ~ r1_orders_2('#skF_4','#skF_8','#skF_5')
    | ~ r1_lattice3('#skF_4','#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_930,plain,(
    ~ r1_orders_2('#skF_4','#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_555,c_925,c_30])).

tff(c_36,plain,
    ( ~ r2_yellow_0('#skF_4','#skF_6')
    | k2_yellow_0('#skF_4','#skF_6') != '#skF_5'
    | r1_lattice3('#skF_4','#skF_7','#skF_8')
    | ~ r1_lattice3('#skF_4','#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_928,plain,(
    r1_lattice3('#skF_4','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_555,c_925,c_36])).

tff(c_924,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_554])).

tff(c_964,plain,(
    ! [A_329,D_330,B_331] :
      ( r1_orders_2(A_329,D_330,k2_yellow_0(A_329,B_331))
      | ~ r1_lattice3(A_329,B_331,D_330)
      | ~ m1_subset_1(D_330,u1_struct_0(A_329))
      | ~ r2_yellow_0(A_329,B_331)
      | ~ m1_subset_1(k2_yellow_0(A_329,B_331),u1_struct_0(A_329))
      | ~ l1_orders_2(A_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_968,plain,(
    ! [D_330] :
      ( r1_orders_2('#skF_4',D_330,k2_yellow_0('#skF_4','#skF_7'))
      | ~ r1_lattice3('#skF_4','#skF_7',D_330)
      | ~ m1_subset_1(D_330,u1_struct_0('#skF_4'))
      | ~ r2_yellow_0('#skF_4','#skF_7')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_964])).

tff(c_973,plain,(
    ! [D_332] :
      ( r1_orders_2('#skF_4',D_332,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_7',D_332)
      | ~ m1_subset_1(D_332,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_59,c_60,c_968])).

tff(c_984,plain,
    ( r1_orders_2('#skF_4','#skF_8','#skF_5')
    | ~ r1_lattice3('#skF_4','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_924,c_973])).

tff(c_1000,plain,(
    r1_orders_2('#skF_4','#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_984])).

tff(c_1002,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_930,c_1000])).

tff(c_1004,plain,(
    ~ r1_lattice3('#skF_4','#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_34,plain,
    ( r1_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ r1_orders_2('#skF_4','#skF_8','#skF_5')
    | ~ r1_lattice3('#skF_4','#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1009,plain,
    ( r1_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ r1_orders_2('#skF_4','#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_34])).

tff(c_1010,plain,(
    ~ r1_orders_2('#skF_4','#skF_8','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1004,c_1009])).

tff(c_40,plain,
    ( r1_lattice3('#skF_4','#skF_6','#skF_5')
    | r1_lattice3('#skF_4','#skF_7','#skF_8')
    | ~ r1_lattice3('#skF_4','#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1006,plain,
    ( r1_lattice3('#skF_4','#skF_6','#skF_5')
    | r1_lattice3('#skF_4','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_40])).

tff(c_1007,plain,(
    r1_lattice3('#skF_4','#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1004,c_1006])).

tff(c_1003,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_1049,plain,(
    ! [A_360,D_361,B_362] :
      ( r1_orders_2(A_360,D_361,k2_yellow_0(A_360,B_362))
      | ~ r1_lattice3(A_360,B_362,D_361)
      | ~ m1_subset_1(D_361,u1_struct_0(A_360))
      | ~ r2_yellow_0(A_360,B_362)
      | ~ m1_subset_1(k2_yellow_0(A_360,B_362),u1_struct_0(A_360))
      | ~ l1_orders_2(A_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1051,plain,(
    ! [D_361] :
      ( r1_orders_2('#skF_4',D_361,k2_yellow_0('#skF_4','#skF_7'))
      | ~ r1_lattice3('#skF_4','#skF_7',D_361)
      | ~ m1_subset_1(D_361,u1_struct_0('#skF_4'))
      | ~ r2_yellow_0('#skF_4','#skF_7')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1049])).

tff(c_1054,plain,(
    ! [D_363] :
      ( r1_orders_2('#skF_4',D_363,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_7',D_363)
      | ~ m1_subset_1(D_363,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_59,c_60,c_1051])).

tff(c_1069,plain,
    ( r1_orders_2('#skF_4','#skF_8','#skF_5')
    | ~ r1_lattice3('#skF_4','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_1003,c_1054])).

tff(c_1084,plain,(
    r1_orders_2('#skF_4','#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1007,c_1069])).

tff(c_1086,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1010,c_1084])).

tff(c_1088,plain,(
    k2_yellow_0('#skF_4','#skF_7') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_54,plain,
    ( ~ r2_yellow_0('#skF_4','#skF_6')
    | k2_yellow_0('#skF_4','#skF_6') != '#skF_5'
    | k2_yellow_0('#skF_4','#skF_7') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1090,plain,
    ( ~ r2_yellow_0('#skF_4','#skF_6')
    | k2_yellow_0('#skF_4','#skF_6') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1088,c_54])).

tff(c_1091,plain,(
    k2_yellow_0('#skF_4','#skF_6') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1090])).

tff(c_1087,plain,(
    r1_lattice3('#skF_4','#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1116,plain,(
    ! [A_375,B_376,C_377] :
      ( m1_subset_1('#skF_2'(A_375,B_376,C_377),u1_struct_0(A_375))
      | r2_yellow_0(A_375,B_376)
      | ~ r1_lattice3(A_375,B_376,C_377)
      | ~ m1_subset_1(C_377,u1_struct_0(A_375))
      | ~ l1_orders_2(A_375)
      | ~ v5_orders_2(A_375) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_56,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4',D_55,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | k2_yellow_0('#skF_4','#skF_7') = '#skF_5' ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1098,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4',D_55,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1088,c_56])).

tff(c_1120,plain,(
    ! [B_376,C_377] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_376,C_377),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_376,C_377))
      | r2_yellow_0('#skF_4',B_376)
      | ~ r1_lattice3('#skF_4',B_376,C_377)
      | ~ m1_subset_1(C_377,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1116,c_1098])).

tff(c_1131,plain,(
    ! [B_384,C_385] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_384,C_385),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_384,C_385))
      | r2_yellow_0('#skF_4',B_384)
      | ~ r1_lattice3('#skF_4',B_384,C_385)
      | ~ m1_subset_1(C_385,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1120])).

tff(c_1135,plain,(
    ! [B_384] :
      ( ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_384,'#skF_5'))
      | r2_yellow_0('#skF_4',B_384)
      | ~ r1_lattice3('#skF_4',B_384,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1131,c_18])).

tff(c_1139,plain,(
    ! [B_386] :
      ( ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_386,'#skF_5'))
      | r2_yellow_0('#skF_4',B_386)
      | ~ r1_lattice3('#skF_4',B_386,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_26,c_1135])).

tff(c_1143,plain,
    ( r2_yellow_0('#skF_4','#skF_6')
    | ~ r1_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_1139])).

tff(c_1146,plain,(
    r2_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_1087,c_1143])).

tff(c_1147,plain,(
    ! [A_387,B_388,C_389] :
      ( m1_subset_1('#skF_1'(A_387,B_388,C_389),u1_struct_0(A_387))
      | k2_yellow_0(A_387,B_388) = C_389
      | ~ r1_lattice3(A_387,B_388,C_389)
      | ~ r2_yellow_0(A_387,B_388)
      | ~ m1_subset_1(C_389,u1_struct_0(A_387))
      | ~ l1_orders_2(A_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1151,plain,(
    ! [B_388,C_389] :
      ( r1_orders_2('#skF_4','#skF_1'('#skF_4',B_388,C_389),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_388,C_389))
      | k2_yellow_0('#skF_4',B_388) = C_389
      | ~ r1_lattice3('#skF_4',B_388,C_389)
      | ~ r2_yellow_0('#skF_4',B_388)
      | ~ m1_subset_1(C_389,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1147,c_1098])).

tff(c_1163,plain,(
    ! [B_399,C_400] :
      ( r1_orders_2('#skF_4','#skF_1'('#skF_4',B_399,C_400),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_399,C_400))
      | k2_yellow_0('#skF_4',B_399) = C_400
      | ~ r1_lattice3('#skF_4',B_399,C_400)
      | ~ r2_yellow_0('#skF_4',B_399)
      | ~ m1_subset_1(C_400,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1151])).

tff(c_1167,plain,(
    ! [B_399] :
      ( ~ l1_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_399,'#skF_5'))
      | k2_yellow_0('#skF_4',B_399) = '#skF_5'
      | ~ r1_lattice3('#skF_4',B_399,'#skF_5')
      | ~ r2_yellow_0('#skF_4',B_399)
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1163,c_2])).

tff(c_1171,plain,(
    ! [B_401] :
      ( ~ r1_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_401,'#skF_5'))
      | k2_yellow_0('#skF_4',B_401) = '#skF_5'
      | ~ r1_lattice3('#skF_4',B_401,'#skF_5')
      | ~ r2_yellow_0('#skF_4',B_401) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_1167])).

tff(c_1175,plain,
    ( k2_yellow_0('#skF_4','#skF_6') = '#skF_5'
    | ~ r1_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ r2_yellow_0('#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_1171])).

tff(c_1178,plain,(
    k2_yellow_0('#skF_4','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_1146,c_1087,c_1175])).

tff(c_1180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1091,c_1178])).

tff(c_1181,plain,(
    ~ r2_yellow_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1090])).

tff(c_1221,plain,(
    ! [A_413,B_414,C_415] :
      ( m1_subset_1('#skF_2'(A_413,B_414,C_415),u1_struct_0(A_413))
      | r2_yellow_0(A_413,B_414)
      | ~ r1_lattice3(A_413,B_414,C_415)
      | ~ m1_subset_1(C_415,u1_struct_0(A_413))
      | ~ l1_orders_2(A_413)
      | ~ v5_orders_2(A_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1199,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4',D_55,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1088,c_56])).

tff(c_1225,plain,(
    ! [B_414,C_415] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_414,C_415),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_414,C_415))
      | r2_yellow_0('#skF_4',B_414)
      | ~ r1_lattice3('#skF_4',B_414,C_415)
      | ~ m1_subset_1(C_415,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1221,c_1199])).

tff(c_1228,plain,(
    ! [B_414,C_415] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_414,C_415),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_414,C_415))
      | r2_yellow_0('#skF_4',B_414)
      | ~ r1_lattice3('#skF_4',B_414,C_415)
      | ~ m1_subset_1(C_415,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1225])).

tff(c_1231,plain,(
    ! [A_421,B_422,C_423] :
      ( ~ r1_orders_2(A_421,'#skF_2'(A_421,B_422,C_423),C_423)
      | r2_yellow_0(A_421,B_422)
      | ~ r1_lattice3(A_421,B_422,C_423)
      | ~ m1_subset_1(C_423,u1_struct_0(A_421))
      | ~ l1_orders_2(A_421)
      | ~ v5_orders_2(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1235,plain,(
    ! [B_414] :
      ( ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_414,'#skF_5'))
      | r2_yellow_0('#skF_4',B_414)
      | ~ r1_lattice3('#skF_4',B_414,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1228,c_1231])).

tff(c_1244,plain,(
    ! [B_424] :
      ( ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_424,'#skF_5'))
      | r2_yellow_0('#skF_4',B_424)
      | ~ r1_lattice3('#skF_4',B_424,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_26,c_1235])).

tff(c_1248,plain,
    ( r2_yellow_0('#skF_4','#skF_6')
    | ~ r1_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_1244])).

tff(c_1251,plain,(
    r2_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_1087,c_1248])).

tff(c_1253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1181,c_1251])).

tff(c_1255,plain,(
    ~ r2_yellow_0('#skF_4','#skF_7') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_48,plain,
    ( ~ r2_yellow_0('#skF_4','#skF_6')
    | k2_yellow_0('#skF_4','#skF_6') != '#skF_5'
    | r2_yellow_0('#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1257,plain,
    ( ~ r2_yellow_0('#skF_4','#skF_6')
    | k2_yellow_0('#skF_4','#skF_6') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1255,c_48])).

tff(c_1258,plain,(
    k2_yellow_0('#skF_4','#skF_6') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1257])).

tff(c_1254,plain,(
    r1_lattice3('#skF_4','#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1289,plain,(
    ! [A_442,B_443,C_444] :
      ( m1_subset_1('#skF_2'(A_442,B_443,C_444),u1_struct_0(A_442))
      | r2_yellow_0(A_442,B_443)
      | ~ r1_lattice3(A_442,B_443,C_444)
      | ~ m1_subset_1(C_444,u1_struct_0(A_442))
      | ~ l1_orders_2(A_442)
      | ~ v5_orders_2(A_442) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_50,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4',D_55,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4'))
      | r2_yellow_0('#skF_4','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1264,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4',D_55,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1255,c_50])).

tff(c_1293,plain,(
    ! [B_443,C_444] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_443,C_444),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_443,C_444))
      | r2_yellow_0('#skF_4',B_443)
      | ~ r1_lattice3('#skF_4',B_443,C_444)
      | ~ m1_subset_1(C_444,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1289,c_1264])).

tff(c_1298,plain,(
    ! [B_448,C_449] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_448,C_449),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_448,C_449))
      | r2_yellow_0('#skF_4',B_448)
      | ~ r1_lattice3('#skF_4',B_448,C_449)
      | ~ m1_subset_1(C_449,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1293])).

tff(c_1302,plain,(
    ! [B_448] :
      ( ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_448,'#skF_5'))
      | r2_yellow_0('#skF_4',B_448)
      | ~ r1_lattice3('#skF_4',B_448,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1298,c_18])).

tff(c_1306,plain,(
    ! [B_450] :
      ( ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_450,'#skF_5'))
      | r2_yellow_0('#skF_4',B_450)
      | ~ r1_lattice3('#skF_4',B_450,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_26,c_1302])).

tff(c_1310,plain,
    ( r2_yellow_0('#skF_4','#skF_6')
    | ~ r1_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_1306])).

tff(c_1313,plain,(
    r2_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_1254,c_1310])).

tff(c_1320,plain,(
    ! [A_454,B_455,C_456] :
      ( m1_subset_1('#skF_1'(A_454,B_455,C_456),u1_struct_0(A_454))
      | k2_yellow_0(A_454,B_455) = C_456
      | ~ r1_lattice3(A_454,B_455,C_456)
      | ~ r2_yellow_0(A_454,B_455)
      | ~ m1_subset_1(C_456,u1_struct_0(A_454))
      | ~ l1_orders_2(A_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1324,plain,(
    ! [B_455,C_456] :
      ( r1_orders_2('#skF_4','#skF_1'('#skF_4',B_455,C_456),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_455,C_456))
      | k2_yellow_0('#skF_4',B_455) = C_456
      | ~ r1_lattice3('#skF_4',B_455,C_456)
      | ~ r2_yellow_0('#skF_4',B_455)
      | ~ m1_subset_1(C_456,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1320,c_1264])).

tff(c_1329,plain,(
    ! [B_460,C_461] :
      ( r1_orders_2('#skF_4','#skF_1'('#skF_4',B_460,C_461),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_460,C_461))
      | k2_yellow_0('#skF_4',B_460) = C_461
      | ~ r1_lattice3('#skF_4',B_460,C_461)
      | ~ r2_yellow_0('#skF_4',B_460)
      | ~ m1_subset_1(C_461,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1324])).

tff(c_1333,plain,(
    ! [B_460] :
      ( ~ l1_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_460,'#skF_5'))
      | k2_yellow_0('#skF_4',B_460) = '#skF_5'
      | ~ r1_lattice3('#skF_4',B_460,'#skF_5')
      | ~ r2_yellow_0('#skF_4',B_460)
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1329,c_2])).

tff(c_1337,plain,(
    ! [B_462] :
      ( ~ r1_lattice3('#skF_4','#skF_6','#skF_1'('#skF_4',B_462,'#skF_5'))
      | k2_yellow_0('#skF_4',B_462) = '#skF_5'
      | ~ r1_lattice3('#skF_4',B_462,'#skF_5')
      | ~ r2_yellow_0('#skF_4',B_462) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_1333])).

tff(c_1341,plain,
    ( k2_yellow_0('#skF_4','#skF_6') = '#skF_5'
    | ~ r1_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ r2_yellow_0('#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_1337])).

tff(c_1344,plain,(
    k2_yellow_0('#skF_4','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_1313,c_1254,c_1341])).

tff(c_1346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1258,c_1344])).

tff(c_1347,plain,(
    ~ r2_yellow_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1257])).

tff(c_1395,plain,(
    ! [A_480,B_481,C_482] :
      ( m1_subset_1('#skF_2'(A_480,B_481,C_482),u1_struct_0(A_480))
      | r2_yellow_0(A_480,B_481)
      | ~ r1_lattice3(A_480,B_481,C_482)
      | ~ m1_subset_1(C_482,u1_struct_0(A_480))
      | ~ l1_orders_2(A_480)
      | ~ v5_orders_2(A_480) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1362,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_4',D_55,'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6',D_55)
      | ~ m1_subset_1(D_55,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1255,c_50])).

tff(c_1399,plain,(
    ! [B_481,C_482] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_481,C_482),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_481,C_482))
      | r2_yellow_0('#skF_4',B_481)
      | ~ r1_lattice3('#skF_4',B_481,C_482)
      | ~ m1_subset_1(C_482,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1395,c_1362])).

tff(c_1423,plain,(
    ! [B_495,C_496] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_495,C_496),'#skF_5')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_495,C_496))
      | r2_yellow_0('#skF_4',B_495)
      | ~ r1_lattice3('#skF_4',B_495,C_496)
      | ~ m1_subset_1(C_496,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1399])).

tff(c_1427,plain,(
    ! [B_495] :
      ( ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_495,'#skF_5'))
      | r2_yellow_0('#skF_4',B_495)
      | ~ r1_lattice3('#skF_4',B_495,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1423,c_18])).

tff(c_1439,plain,(
    ! [B_499] :
      ( ~ r1_lattice3('#skF_4','#skF_6','#skF_2'('#skF_4',B_499,'#skF_5'))
      | r2_yellow_0('#skF_4',B_499)
      | ~ r1_lattice3('#skF_4',B_499,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_26,c_1427])).

tff(c_1443,plain,
    ( r2_yellow_0('#skF_4','#skF_6')
    | ~ r1_lattice3('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_1439])).

tff(c_1446,plain,(
    r2_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_1254,c_1443])).

tff(c_1448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1347,c_1446])).

%------------------------------------------------------------------------------
