%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1570+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:05 EST 2020

% Result     : Theorem 4.75s
% Output     : CNFRefutation 4.78s
% Verified   : 
% Statistics : Number of formulae       :  170 (5666 expanded)
%              Number of leaves         :   19 (1923 expanded)
%              Depth                    :   29
%              Number of atoms          :  690 (32291 expanded)
%              Number of equality atoms :   60 (1832 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r1_lattice3 > r2_yellow_0 > m1_subset_1 > v2_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_orders_2(A) )
       => ! [B,C] :
            ( ( ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r1_lattice3(A,B,D)
                  <=> r1_lattice3(A,C,D) ) )
              & r2_yellow_0(A,B) )
           => r2_yellow_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_yellow_0)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( r2_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r1_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r1_lattice3(A,B,D)
                   => r1_orders_2(A,D,C) ) )
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r1_lattice3(A,B,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( r1_lattice3(A,B,E)
                           => r1_orders_2(A,E,D) ) ) )
                   => D = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_0)).

tff(c_38,plain,(
    ~ r2_yellow_0('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_42,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    r2_yellow_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [A_1,B_39] :
      ( m1_subset_1('#skF_3'(A_1,B_39),u1_struct_0(A_1))
      | ~ r2_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_1,B_39,C_58] :
      ( r1_lattice3(A_1,B_39,'#skF_1'(A_1,B_39,C_58))
      | '#skF_2'(A_1,B_39,C_58) != C_58
      | r2_yellow_0(A_1,B_39)
      | ~ r1_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_103,plain,(
    ! [A_98,B_99,C_100] :
      ( m1_subset_1('#skF_1'(A_98,B_99,C_100),u1_struct_0(A_98))
      | '#skF_2'(A_98,B_99,C_100) != C_100
      | r2_yellow_0(A_98,B_99)
      | ~ r1_lattice3(A_98,B_99,C_100)
      | ~ m1_subset_1(C_100,u1_struct_0(A_98))
      | ~ l1_orders_2(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    ! [D_77] :
      ( r1_lattice3('#skF_5','#skF_6',D_77)
      | ~ r1_lattice3('#skF_5','#skF_7',D_77)
      | ~ m1_subset_1(D_77,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_107,plain,(
    ! [B_99,C_100] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_99,C_100))
      | ~ r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5',B_99,C_100))
      | '#skF_2'('#skF_5',B_99,C_100) != C_100
      | r2_yellow_0('#skF_5',B_99)
      | ~ r1_lattice3('#skF_5',B_99,C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_103,c_46])).

tff(c_214,plain,(
    ! [B_135,C_136] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_135,C_136))
      | ~ r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5',B_135,C_136))
      | '#skF_2'('#skF_5',B_135,C_136) != C_136
      | r2_yellow_0('#skF_5',B_135)
      | ~ r1_lattice3('#skF_5',B_135,C_136)
      | ~ m1_subset_1(C_136,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_107])).

tff(c_229,plain,(
    ! [C_58] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_7',C_58))
      | '#skF_2'('#skF_5','#skF_7',C_58) != C_58
      | r2_yellow_0('#skF_5','#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_7',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_214])).

tff(c_237,plain,(
    ! [C_58] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_7',C_58))
      | '#skF_2'('#skF_5','#skF_7',C_58) != C_58
      | r2_yellow_0('#skF_5','#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_7',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_229])).

tff(c_238,plain,(
    ! [C_58] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_7',C_58))
      | '#skF_2'('#skF_5','#skF_7',C_58) != C_58
      | ~ r1_lattice3('#skF_5','#skF_7',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_237])).

tff(c_2,plain,(
    ! [A_1,D_69,B_39] :
      ( r1_orders_2(A_1,D_69,'#skF_3'(A_1,B_39))
      | ~ r1_lattice3(A_1,B_39,D_69)
      | ~ m1_subset_1(D_69,u1_struct_0(A_1))
      | ~ r2_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_157,plain,(
    ! [A_118,B_119,C_120] :
      ( ~ r1_orders_2(A_118,'#skF_1'(A_118,B_119,C_120),C_120)
      | m1_subset_1('#skF_2'(A_118,B_119,C_120),u1_struct_0(A_118))
      | r2_yellow_0(A_118,B_119)
      | ~ r1_lattice3(A_118,B_119,C_120)
      | ~ m1_subset_1(C_120,u1_struct_0(A_118))
      | ~ l1_orders_2(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_583,plain,(
    ! [A_182,B_183,B_184] :
      ( m1_subset_1('#skF_2'(A_182,B_183,'#skF_3'(A_182,B_184)),u1_struct_0(A_182))
      | r2_yellow_0(A_182,B_183)
      | ~ r1_lattice3(A_182,B_183,'#skF_3'(A_182,B_184))
      | ~ m1_subset_1('#skF_3'(A_182,B_184),u1_struct_0(A_182))
      | ~ r1_lattice3(A_182,B_184,'#skF_1'(A_182,B_183,'#skF_3'(A_182,B_184)))
      | ~ m1_subset_1('#skF_1'(A_182,B_183,'#skF_3'(A_182,B_184)),u1_struct_0(A_182))
      | ~ r2_yellow_0(A_182,B_184)
      | ~ l1_orders_2(A_182) ) ),
    inference(resolution,[status(thm)],[c_2,c_157])).

tff(c_601,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | r2_yellow_0('#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ r2_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_238,c_583])).

tff(c_635,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | r2_yellow_0('#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_601])).

tff(c_636,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_635])).

tff(c_644,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_636])).

tff(c_647,plain,
    ( ~ r2_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_644])).

tff(c_651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_647])).

tff(c_653,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_636])).

tff(c_4,plain,(
    ! [A_1,B_39] :
      ( r1_lattice3(A_1,B_39,'#skF_3'(A_1,B_39))
      | ~ r2_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_51,plain,(
    ! [D_82] :
      ( r1_lattice3('#skF_5','#skF_7',D_82)
      | ~ r1_lattice3('#skF_5','#skF_6',D_82)
      | ~ m1_subset_1(D_82,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_55,plain,(
    ! [B_39] :
      ( r1_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5',B_39))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_3'('#skF_5',B_39))
      | ~ r2_yellow_0('#skF_5',B_39)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_58,plain,(
    ! [B_39] :
      ( r1_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5',B_39))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_3'('#skF_5',B_39))
      | ~ r2_yellow_0('#skF_5',B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_55])).

tff(c_660,plain,
    ( r1_lattice3('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6'))
    | ~ r1_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_653,c_46])).

tff(c_723,plain,(
    ~ r1_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_660])).

tff(c_726,plain,
    ( ~ r1_lattice3('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6'))
    | ~ r2_yellow_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_723])).

tff(c_729,plain,(
    ~ r1_lattice3('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_726])).

tff(c_732,plain,
    ( ~ r2_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_729])).

tff(c_736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_732])).

tff(c_738,plain,(
    r1_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_660])).

tff(c_119,plain,(
    ! [A_104,B_105,C_106] :
      ( ~ r1_orders_2(A_104,'#skF_1'(A_104,B_105,C_106),C_106)
      | '#skF_2'(A_104,B_105,C_106) != C_106
      | r2_yellow_0(A_104,B_105)
      | ~ r1_lattice3(A_104,B_105,C_106)
      | ~ m1_subset_1(C_106,u1_struct_0(A_104))
      | ~ l1_orders_2(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_756,plain,(
    ! [A_188,B_189,B_190] :
      ( '#skF_2'(A_188,B_189,'#skF_3'(A_188,B_190)) != '#skF_3'(A_188,B_190)
      | r2_yellow_0(A_188,B_189)
      | ~ r1_lattice3(A_188,B_189,'#skF_3'(A_188,B_190))
      | ~ m1_subset_1('#skF_3'(A_188,B_190),u1_struct_0(A_188))
      | ~ r1_lattice3(A_188,B_190,'#skF_1'(A_188,B_189,'#skF_3'(A_188,B_190)))
      | ~ m1_subset_1('#skF_1'(A_188,B_189,'#skF_3'(A_188,B_190)),u1_struct_0(A_188))
      | ~ r2_yellow_0(A_188,B_190)
      | ~ l1_orders_2(A_188) ) ),
    inference(resolution,[status(thm)],[c_2,c_119])).

tff(c_774,plain,
    ( r2_yellow_0('#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ r2_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_238,c_756])).

tff(c_808,plain,
    ( r2_yellow_0('#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_738,c_42,c_40,c_774])).

tff(c_809,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_808])).

tff(c_819,plain,(
    '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_809])).

tff(c_36,plain,(
    ! [A_1,B_39,C_58] :
      ( m1_subset_1('#skF_1'(A_1,B_39,C_58),u1_struct_0(A_1))
      | m1_subset_1('#skF_2'(A_1,B_39,C_58),u1_struct_0(A_1))
      | r2_yellow_0(A_1,B_39)
      | ~ r1_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [A_1,B_39,C_58] :
      ( r1_lattice3(A_1,B_39,'#skF_1'(A_1,B_39,C_58))
      | r1_lattice3(A_1,B_39,'#skF_2'(A_1,B_39,C_58))
      | r2_yellow_0(A_1,B_39)
      | ~ r1_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_126,plain,(
    ! [A_110,B_111,C_112] :
      ( m1_subset_1('#skF_1'(A_110,B_111,C_112),u1_struct_0(A_110))
      | r1_lattice3(A_110,B_111,'#skF_2'(A_110,B_111,C_112))
      | r2_yellow_0(A_110,B_111)
      | ~ r1_lattice3(A_110,B_111,C_112)
      | ~ m1_subset_1(C_112,u1_struct_0(A_110))
      | ~ l1_orders_2(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_130,plain,(
    ! [B_111,C_112] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_111,C_112))
      | ~ r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5',B_111,C_112))
      | r1_lattice3('#skF_5',B_111,'#skF_2'('#skF_5',B_111,C_112))
      | r2_yellow_0('#skF_5',B_111)
      | ~ r1_lattice3('#skF_5',B_111,C_112)
      | ~ m1_subset_1(C_112,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_126,c_46])).

tff(c_261,plain,(
    ! [B_144,C_145] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_144,C_145))
      | ~ r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5',B_144,C_145))
      | r1_lattice3('#skF_5',B_144,'#skF_2'('#skF_5',B_144,C_145))
      | r2_yellow_0('#skF_5',B_144)
      | ~ r1_lattice3('#skF_5',B_144,C_145)
      | ~ m1_subset_1(C_145,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_130])).

tff(c_271,plain,(
    ! [C_58] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_7',C_58))
      | r1_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7',C_58))
      | r2_yellow_0('#skF_5','#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_7',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_261])).

tff(c_281,plain,(
    ! [C_58] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_7',C_58))
      | r1_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7',C_58))
      | r2_yellow_0('#skF_5','#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_7',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_271])).

tff(c_282,plain,(
    ! [C_58] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_7',C_58))
      | r1_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7',C_58))
      | ~ r1_lattice3('#skF_5','#skF_7',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_281])).

tff(c_287,plain,(
    ! [C_146] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_7',C_146))
      | r1_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7',C_146))
      | ~ r1_lattice3('#skF_5','#skF_7',C_146)
      | ~ m1_subset_1(C_146,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_281])).

tff(c_142,plain,(
    ! [A_115,B_116,C_117] :
      ( r1_lattice3(A_115,B_116,'#skF_1'(A_115,B_116,C_117))
      | m1_subset_1('#skF_2'(A_115,B_116,C_117),u1_struct_0(A_115))
      | r2_yellow_0(A_115,B_116)
      | ~ r1_lattice3(A_115,B_116,C_117)
      | ~ m1_subset_1(C_117,u1_struct_0(A_115))
      | ~ l1_orders_2(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_146,plain,(
    ! [B_116,C_117] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_116,C_117))
      | ~ r1_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5',B_116,C_117))
      | r1_lattice3('#skF_5',B_116,'#skF_1'('#skF_5',B_116,C_117))
      | r2_yellow_0('#skF_5',B_116)
      | ~ r1_lattice3('#skF_5',B_116,C_117)
      | ~ m1_subset_1(C_117,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_142,c_46])).

tff(c_153,plain,(
    ! [B_116,C_117] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_116,C_117))
      | ~ r1_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5',B_116,C_117))
      | r1_lattice3('#skF_5',B_116,'#skF_1'('#skF_5',B_116,C_117))
      | r2_yellow_0('#skF_5',B_116)
      | ~ r1_lattice3('#skF_5',B_116,C_117)
      | ~ m1_subset_1(C_117,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_146])).

tff(c_289,plain,(
    ! [C_146] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7',C_146))
      | r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7',C_146))
      | r2_yellow_0('#skF_5','#skF_7')
      | r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_7',C_146))
      | ~ r1_lattice3('#skF_5','#skF_7',C_146)
      | ~ m1_subset_1(C_146,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_287,c_153])).

tff(c_292,plain,(
    ! [C_146] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7',C_146))
      | r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7',C_146))
      | r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_7',C_146))
      | ~ r1_lattice3('#skF_5','#skF_7',C_146)
      | ~ m1_subset_1(C_146,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_289])).

tff(c_162,plain,(
    ! [A_121,B_122,C_123] :
      ( m1_subset_1('#skF_1'(A_121,B_122,C_123),u1_struct_0(A_121))
      | m1_subset_1('#skF_2'(A_121,B_122,C_123),u1_struct_0(A_121))
      | r2_yellow_0(A_121,B_122)
      | ~ r1_lattice3(A_121,B_122,C_123)
      | ~ m1_subset_1(C_123,u1_struct_0(A_121))
      | ~ l1_orders_2(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_166,plain,(
    ! [B_122,C_123] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_122,C_123))
      | ~ r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5',B_122,C_123))
      | m1_subset_1('#skF_2'('#skF_5',B_122,C_123),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_122)
      | ~ r1_lattice3('#skF_5',B_122,C_123)
      | ~ m1_subset_1(C_123,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_162,c_46])).

tff(c_240,plain,(
    ! [B_138,C_139] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_138,C_139))
      | ~ r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5',B_138,C_139))
      | m1_subset_1('#skF_2'('#skF_5',B_138,C_139),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_138)
      | ~ r1_lattice3('#skF_5',B_138,C_139)
      | ~ m1_subset_1(C_139,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_166])).

tff(c_407,plain,(
    ! [B_162,C_163] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_162,C_163))
      | ~ r1_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5',B_162,C_163))
      | r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_162,C_163))
      | ~ r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5',B_162,C_163))
      | r2_yellow_0('#skF_5',B_162)
      | ~ r1_lattice3('#skF_5',B_162,C_163)
      | ~ m1_subset_1(C_163,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_240,c_46])).

tff(c_413,plain,(
    ! [C_146] :
      ( ~ r1_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7',C_146))
      | r2_yellow_0('#skF_5','#skF_7')
      | r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7',C_146))
      | r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_7',C_146))
      | ~ r1_lattice3('#skF_5','#skF_7',C_146)
      | ~ m1_subset_1(C_146,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_292,c_407])).

tff(c_448,plain,(
    ! [C_164] :
      ( ~ r1_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7',C_164))
      | r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7',C_164))
      | r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_7',C_164))
      | ~ r1_lattice3('#skF_5','#skF_7',C_164)
      | ~ m1_subset_1(C_164,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_413])).

tff(c_458,plain,(
    ! [C_58] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7',C_58))
      | r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_7',C_58))
      | ~ r1_lattice3('#skF_5','#skF_7',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_282,c_448])).

tff(c_765,plain,
    ( '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | r2_yellow_0('#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ r2_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | ~ r1_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_458,c_756])).

tff(c_798,plain,
    ( '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | r2_yellow_0('#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_738,c_42,c_40,c_765])).

tff(c_799,plain,
    ( '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_798])).

tff(c_820,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_799])).

tff(c_826,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | r2_yellow_0('#skF_5','#skF_7')
    | ~ r1_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_820])).

tff(c_839,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | r2_yellow_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_653,c_738,c_826])).

tff(c_840,plain,(
    m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_839])).

tff(c_30,plain,(
    ! [A_1,B_39,C_58] :
      ( m1_subset_1('#skF_1'(A_1,B_39,C_58),u1_struct_0(A_1))
      | r1_lattice3(A_1,B_39,'#skF_2'(A_1,B_39,C_58))
      | r2_yellow_0(A_1,B_39)
      | ~ r1_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_829,plain,
    ( r1_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r2_yellow_0('#skF_5','#skF_7')
    | ~ r1_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_820])).

tff(c_843,plain,
    ( r1_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r2_yellow_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_653,c_738,c_829])).

tff(c_844,plain,(
    r1_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_843])).

tff(c_855,plain,
    ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | ~ r1_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_840,c_46])).

tff(c_958,plain,(
    r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_844,c_855])).

tff(c_10,plain,(
    ! [A_1,B_39,D_70] :
      ( r1_lattice3(A_1,B_39,'#skF_4'(A_1,B_39,D_70))
      | D_70 = '#skF_3'(A_1,B_39)
      | ~ r1_lattice3(A_1,B_39,D_70)
      | ~ m1_subset_1(D_70,u1_struct_0(A_1))
      | ~ r2_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_81,plain,(
    ! [A_89,B_90,D_91] :
      ( m1_subset_1('#skF_4'(A_89,B_90,D_91),u1_struct_0(A_89))
      | D_91 = '#skF_3'(A_89,B_90)
      | ~ r1_lattice3(A_89,B_90,D_91)
      | ~ m1_subset_1(D_91,u1_struct_0(A_89))
      | ~ r2_yellow_0(A_89,B_90)
      | ~ l1_orders_2(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,(
    ! [D_77] :
      ( r1_lattice3('#skF_5','#skF_7',D_77)
      | ~ r1_lattice3('#skF_5','#skF_6',D_77)
      | ~ m1_subset_1(D_77,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_89,plain,(
    ! [B_90,D_91] :
      ( r1_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_90,D_91))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_4'('#skF_5',B_90,D_91))
      | D_91 = '#skF_3'('#skF_5',B_90)
      | ~ r1_lattice3('#skF_5',B_90,D_91)
      | ~ m1_subset_1(D_91,u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_90)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_81,c_48])).

tff(c_95,plain,(
    ! [B_90,D_91] :
      ( r1_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_90,D_91))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_4'('#skF_5',B_90,D_91))
      | D_91 = '#skF_3'('#skF_5',B_90)
      | ~ r1_lattice3('#skF_5',B_90,D_91)
      | ~ m1_subset_1(D_91,u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_89])).

tff(c_12,plain,(
    ! [A_1,B_39,D_70] :
      ( m1_subset_1('#skF_4'(A_1,B_39,D_70),u1_struct_0(A_1))
      | D_70 = '#skF_3'(A_1,B_39)
      | ~ r1_lattice3(A_1,B_39,D_70)
      | ~ m1_subset_1(D_70,u1_struct_0(A_1))
      | ~ r2_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    ! [A_1,B_39,C_58,E_64] :
      ( m1_subset_1('#skF_1'(A_1,B_39,C_58),u1_struct_0(A_1))
      | r1_orders_2(A_1,E_64,'#skF_2'(A_1,B_39,C_58))
      | ~ r1_lattice3(A_1,B_39,E_64)
      | ~ m1_subset_1(E_64,u1_struct_0(A_1))
      | r2_yellow_0(A_1,B_39)
      | ~ r1_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_823,plain,(
    ! [E_64] :
      ( r1_orders_2('#skF_5',E_64,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ r1_lattice3('#skF_5','#skF_7',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5','#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_820])).

tff(c_835,plain,(
    ! [E_64] :
      ( r1_orders_2('#skF_5',E_64,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ r1_lattice3('#skF_5','#skF_7',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5','#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_653,c_738,c_823])).

tff(c_863,plain,(
    ! [E_191] :
      ( r1_orders_2('#skF_5',E_191,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ r1_lattice3('#skF_5','#skF_7',E_191)
      | ~ m1_subset_1(E_191,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_835])).

tff(c_8,plain,(
    ! [A_1,B_39,D_70] :
      ( ~ r1_orders_2(A_1,'#skF_4'(A_1,B_39,D_70),D_70)
      | D_70 = '#skF_3'(A_1,B_39)
      | ~ r1_lattice3(A_1,B_39,D_70)
      | ~ m1_subset_1(D_70,u1_struct_0(A_1))
      | ~ r2_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_880,plain,(
    ! [B_39] :
      ( '#skF_3'('#skF_5',B_39) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r1_lattice3('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_39)
      | ~ l1_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_863,c_8])).

tff(c_970,plain,(
    ! [B_196] :
      ( '#skF_3'('#skF_5',B_196) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r1_lattice3('#skF_5',B_196,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ r2_yellow_0('#skF_5',B_196)
      | ~ r1_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_196,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_196,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_840,c_880])).

tff(c_974,plain,(
    ! [B_39] :
      ( ~ r1_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | '#skF_3'('#skF_5',B_39) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r1_lattice3('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_39)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_970])).

tff(c_978,plain,(
    ! [B_197] :
      ( ~ r1_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_197,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | '#skF_3'('#skF_5',B_197) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r1_lattice3('#skF_5',B_197,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ r2_yellow_0('#skF_5',B_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_840,c_974])).

tff(c_982,plain,(
    ! [B_90] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_4'('#skF_5',B_90,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | '#skF_3'('#skF_5',B_90) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r1_lattice3('#skF_5',B_90,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_90) ) ),
    inference(resolution,[status(thm)],[c_95,c_978])).

tff(c_1005,plain,(
    ! [B_202] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_4'('#skF_5',B_202,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | '#skF_3'('#skF_5',B_202) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r1_lattice3('#skF_5',B_202,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ r2_yellow_0('#skF_5',B_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_840,c_982])).

tff(c_1009,plain,
    ( '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ r2_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_1005])).

tff(c_1012,plain,(
    '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_840,c_958,c_1009])).

tff(c_1014,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_819,c_1012])).

tff(c_1016,plain,(
    m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_799])).

tff(c_1023,plain,
    ( r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | ~ r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1016,c_46])).

tff(c_1025,plain,(
    ~ r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1023])).

tff(c_1045,plain,
    ( r1_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r2_yellow_0('#skF_5','#skF_7')
    | ~ r1_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_1025])).

tff(c_1071,plain,
    ( r1_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r2_yellow_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_653,c_738,c_1045])).

tff(c_1072,plain,(
    r1_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1071])).

tff(c_1078,plain,
    ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r2_yellow_0('#skF_5','#skF_7')
    | ~ r1_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1072,c_153])).

tff(c_1081,plain,
    ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r2_yellow_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_738,c_1078])).

tff(c_1082,plain,(
    r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1025,c_1081])).

tff(c_34,plain,(
    ! [A_1,B_39,C_58] :
      ( r1_lattice3(A_1,B_39,'#skF_1'(A_1,B_39,C_58))
      | m1_subset_1('#skF_2'(A_1,B_39,C_58),u1_struct_0(A_1))
      | r2_yellow_0(A_1,B_39)
      | ~ r1_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_194,plain,(
    ! [A_129,B_130,C_131,E_132] :
      ( r1_lattice3(A_129,B_130,'#skF_1'(A_129,B_130,C_131))
      | r1_orders_2(A_129,E_132,'#skF_2'(A_129,B_130,C_131))
      | ~ r1_lattice3(A_129,B_130,E_132)
      | ~ m1_subset_1(E_132,u1_struct_0(A_129))
      | r2_yellow_0(A_129,B_130)
      | ~ r1_lattice3(A_129,B_130,C_131)
      | ~ m1_subset_1(C_131,u1_struct_0(A_129))
      | ~ l1_orders_2(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1173,plain,(
    ! [A_207,B_208,B_209,C_210] :
      ( '#skF_3'(A_207,B_208) = '#skF_2'(A_207,B_209,C_210)
      | ~ r1_lattice3(A_207,B_208,'#skF_2'(A_207,B_209,C_210))
      | ~ m1_subset_1('#skF_2'(A_207,B_209,C_210),u1_struct_0(A_207))
      | ~ r2_yellow_0(A_207,B_208)
      | r1_lattice3(A_207,B_209,'#skF_1'(A_207,B_209,C_210))
      | ~ r1_lattice3(A_207,B_209,'#skF_4'(A_207,B_208,'#skF_2'(A_207,B_209,C_210)))
      | ~ m1_subset_1('#skF_4'(A_207,B_208,'#skF_2'(A_207,B_209,C_210)),u1_struct_0(A_207))
      | r2_yellow_0(A_207,B_209)
      | ~ r1_lattice3(A_207,B_209,C_210)
      | ~ m1_subset_1(C_210,u1_struct_0(A_207))
      | ~ l1_orders_2(A_207) ) ),
    inference(resolution,[status(thm)],[c_194,c_8])).

tff(c_1176,plain,(
    ! [C_210,B_90] :
      ( r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7',C_210))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_90,'#skF_2'('#skF_5','#skF_7',C_210)),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5','#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_7',C_210)
      | ~ m1_subset_1(C_210,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_4'('#skF_5',B_90,'#skF_2'('#skF_5','#skF_7',C_210)))
      | '#skF_3'('#skF_5',B_90) = '#skF_2'('#skF_5','#skF_7',C_210)
      | ~ r1_lattice3('#skF_5',B_90,'#skF_2'('#skF_5','#skF_7',C_210))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7',C_210),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_90) ) ),
    inference(resolution,[status(thm)],[c_95,c_1173])).

tff(c_1182,plain,(
    ! [C_210,B_90] :
      ( r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7',C_210))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_90,'#skF_2'('#skF_5','#skF_7',C_210)),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5','#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_7',C_210)
      | ~ m1_subset_1(C_210,u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_4'('#skF_5',B_90,'#skF_2'('#skF_5','#skF_7',C_210)))
      | '#skF_3'('#skF_5',B_90) = '#skF_2'('#skF_5','#skF_7',C_210)
      | ~ r1_lattice3('#skF_5',B_90,'#skF_2'('#skF_5','#skF_7',C_210))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7',C_210),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1176])).

tff(c_1197,plain,(
    ! [C_215,B_216] :
      ( r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7',C_215))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_216,'#skF_2'('#skF_5','#skF_7',C_215)),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_7',C_215)
      | ~ m1_subset_1(C_215,u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_4'('#skF_5',B_216,'#skF_2'('#skF_5','#skF_7',C_215)))
      | '#skF_3'('#skF_5',B_216) = '#skF_2'('#skF_5','#skF_7',C_215)
      | ~ r1_lattice3('#skF_5',B_216,'#skF_2'('#skF_5','#skF_7',C_215))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7',C_215),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_216) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1182])).

tff(c_1201,plain,(
    ! [C_215,B_39] :
      ( r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7',C_215))
      | ~ r1_lattice3('#skF_5','#skF_7',C_215)
      | ~ m1_subset_1(C_215,u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_4'('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7',C_215)))
      | '#skF_3'('#skF_5',B_39) = '#skF_2'('#skF_5','#skF_7',C_215)
      | ~ r1_lattice3('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7',C_215))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7',C_215),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_39)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_1197])).

tff(c_1205,plain,(
    ! [C_217,B_218] :
      ( r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7',C_217))
      | ~ r1_lattice3('#skF_5','#skF_7',C_217)
      | ~ m1_subset_1(C_217,u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_4'('#skF_5',B_218,'#skF_2'('#skF_5','#skF_7',C_217)))
      | '#skF_3'('#skF_5',B_218) = '#skF_2'('#skF_5','#skF_7',C_217)
      | ~ r1_lattice3('#skF_5',B_218,'#skF_2'('#skF_5','#skF_7',C_217))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7',C_217),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1201])).

tff(c_1209,plain,(
    ! [C_217] :
      ( r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7',C_217))
      | ~ r1_lattice3('#skF_5','#skF_7',C_217)
      | ~ m1_subset_1(C_217,u1_struct_0('#skF_5'))
      | '#skF_3'('#skF_5','#skF_6') = '#skF_2'('#skF_5','#skF_7',C_217)
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7',C_217))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7',C_217),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5','#skF_6')
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10,c_1205])).

tff(c_1213,plain,(
    ! [C_219] :
      ( r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7',C_219))
      | ~ r1_lattice3('#skF_5','#skF_7',C_219)
      | ~ m1_subset_1(C_219,u1_struct_0('#skF_5'))
      | '#skF_3'('#skF_5','#skF_6') = '#skF_2'('#skF_5','#skF_7',C_219)
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7',C_219))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7',C_219),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1209])).

tff(c_1225,plain,(
    ! [C_58] :
      ( '#skF_3'('#skF_5','#skF_6') = '#skF_2'('#skF_5','#skF_7',C_58)
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7',C_58))
      | r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7',C_58))
      | r2_yellow_0('#skF_5','#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_7',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_1213])).

tff(c_1234,plain,(
    ! [C_58] :
      ( '#skF_3'('#skF_5','#skF_6') = '#skF_2'('#skF_5','#skF_7',C_58)
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7',C_58))
      | r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7',C_58))
      | r2_yellow_0('#skF_5','#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_7',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1225])).

tff(c_1236,plain,(
    ! [C_220] :
      ( '#skF_3'('#skF_5','#skF_6') = '#skF_2'('#skF_5','#skF_7',C_220)
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7',C_220))
      | r1_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7',C_220))
      | ~ r1_lattice3('#skF_5','#skF_7',C_220)
      | ~ m1_subset_1(C_220,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1234])).

tff(c_1242,plain,
    ( '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | ~ r1_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1236,c_1025])).

tff(c_1269,plain,(
    '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_738,c_1082,c_1242])).

tff(c_1271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_819,c_1269])).

tff(c_1272,plain,(
    r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_1023])).

tff(c_161,plain,(
    ! [A_1,B_119,B_39] :
      ( m1_subset_1('#skF_2'(A_1,B_119,'#skF_3'(A_1,B_39)),u1_struct_0(A_1))
      | r2_yellow_0(A_1,B_119)
      | ~ r1_lattice3(A_1,B_119,'#skF_3'(A_1,B_39))
      | ~ m1_subset_1('#skF_3'(A_1,B_39),u1_struct_0(A_1))
      | ~ r1_lattice3(A_1,B_39,'#skF_1'(A_1,B_119,'#skF_3'(A_1,B_39)))
      | ~ m1_subset_1('#skF_1'(A_1,B_119,'#skF_3'(A_1,B_39)),u1_struct_0(A_1))
      | ~ r2_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_157])).

tff(c_1279,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | r2_yellow_0('#skF_5','#skF_7')
    | ~ r1_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ r2_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_1272,c_161])).

tff(c_1290,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | r2_yellow_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1016,c_653,c_738,c_1279])).

tff(c_1291,plain,(
    m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1290])).

tff(c_177,plain,(
    ! [A_124,B_125,C_126] :
      ( ~ r1_orders_2(A_124,'#skF_1'(A_124,B_125,C_126),C_126)
      | r1_lattice3(A_124,B_125,'#skF_2'(A_124,B_125,C_126))
      | r2_yellow_0(A_124,B_125)
      | ~ r1_lattice3(A_124,B_125,C_126)
      | ~ m1_subset_1(C_126,u1_struct_0(A_124))
      | ~ l1_orders_2(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_181,plain,(
    ! [A_1,B_125,B_39] :
      ( r1_lattice3(A_1,B_125,'#skF_2'(A_1,B_125,'#skF_3'(A_1,B_39)))
      | r2_yellow_0(A_1,B_125)
      | ~ r1_lattice3(A_1,B_125,'#skF_3'(A_1,B_39))
      | ~ m1_subset_1('#skF_3'(A_1,B_39),u1_struct_0(A_1))
      | ~ r1_lattice3(A_1,B_39,'#skF_1'(A_1,B_125,'#skF_3'(A_1,B_39)))
      | ~ m1_subset_1('#skF_1'(A_1,B_125,'#skF_3'(A_1,B_39)),u1_struct_0(A_1))
      | ~ r2_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_177])).

tff(c_1277,plain,
    ( r1_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r2_yellow_0('#skF_5','#skF_7')
    | ~ r1_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ r2_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_1272,c_181])).

tff(c_1286,plain,
    ( r1_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r2_yellow_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1016,c_653,c_738,c_1277])).

tff(c_1287,plain,(
    r1_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1286])).

tff(c_1327,plain,
    ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | ~ r1_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1291,c_46])).

tff(c_1333,plain,(
    r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1287,c_1327])).

tff(c_293,plain,(
    ! [A_147,B_148,C_149,E_150] :
      ( ~ r1_orders_2(A_147,'#skF_1'(A_147,B_148,C_149),C_149)
      | r1_orders_2(A_147,E_150,'#skF_2'(A_147,B_148,C_149))
      | ~ r1_lattice3(A_147,B_148,E_150)
      | ~ m1_subset_1(E_150,u1_struct_0(A_147))
      | r2_yellow_0(A_147,B_148)
      | ~ r1_lattice3(A_147,B_148,C_149)
      | ~ m1_subset_1(C_149,u1_struct_0(A_147))
      | ~ l1_orders_2(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1336,plain,(
    ! [A_221,E_222,B_223,B_224] :
      ( r1_orders_2(A_221,E_222,'#skF_2'(A_221,B_223,'#skF_3'(A_221,B_224)))
      | ~ r1_lattice3(A_221,B_223,E_222)
      | ~ m1_subset_1(E_222,u1_struct_0(A_221))
      | r2_yellow_0(A_221,B_223)
      | ~ r1_lattice3(A_221,B_223,'#skF_3'(A_221,B_224))
      | ~ m1_subset_1('#skF_3'(A_221,B_224),u1_struct_0(A_221))
      | ~ r1_lattice3(A_221,B_224,'#skF_1'(A_221,B_223,'#skF_3'(A_221,B_224)))
      | ~ m1_subset_1('#skF_1'(A_221,B_223,'#skF_3'(A_221,B_224)),u1_struct_0(A_221))
      | ~ r2_yellow_0(A_221,B_224)
      | ~ l1_orders_2(A_221) ) ),
    inference(resolution,[status(thm)],[c_2,c_293])).

tff(c_1338,plain,(
    ! [E_222] :
      ( r1_orders_2('#skF_5',E_222,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ r1_lattice3('#skF_5','#skF_7',E_222)
      | ~ m1_subset_1(E_222,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5','#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5','#skF_6')
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1272,c_1336])).

tff(c_1374,plain,(
    ! [E_222] :
      ( r1_orders_2('#skF_5',E_222,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ r1_lattice3('#skF_5','#skF_7',E_222)
      | ~ m1_subset_1(E_222,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5','#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1016,c_653,c_738,c_1338])).

tff(c_1403,plain,(
    ! [E_225] :
      ( r1_orders_2('#skF_5',E_225,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ r1_lattice3('#skF_5','#skF_7',E_225)
      | ~ m1_subset_1(E_225,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1374])).

tff(c_1420,plain,(
    ! [B_39] :
      ( '#skF_3'('#skF_5',B_39) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r1_lattice3('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_39)
      | ~ l1_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1403,c_8])).

tff(c_1447,plain,(
    ! [B_226] :
      ( '#skF_3'('#skF_5',B_226) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r1_lattice3('#skF_5',B_226,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ r2_yellow_0('#skF_5',B_226)
      | ~ r1_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_226,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_226,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1291,c_1420])).

tff(c_1451,plain,(
    ! [B_39] :
      ( ~ r1_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | '#skF_3'('#skF_5',B_39) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r1_lattice3('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_39)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_1447])).

tff(c_1455,plain,(
    ! [B_227] :
      ( ~ r1_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_227,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | '#skF_3'('#skF_5',B_227) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r1_lattice3('#skF_5',B_227,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ r2_yellow_0('#skF_5',B_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1291,c_1451])).

tff(c_1459,plain,(
    ! [B_90] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_4'('#skF_5',B_90,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | '#skF_3'('#skF_5',B_90) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r1_lattice3('#skF_5',B_90,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_90) ) ),
    inference(resolution,[status(thm)],[c_95,c_1455])).

tff(c_1482,plain,(
    ! [B_232] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_4'('#skF_5',B_232,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | '#skF_3'('#skF_5',B_232) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r1_lattice3('#skF_5',B_232,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ r2_yellow_0('#skF_5',B_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1291,c_1459])).

tff(c_1486,plain,
    ( '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ r2_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_1482])).

tff(c_1489,plain,(
    '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1291,c_1333,c_1486])).

tff(c_1491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_819,c_1489])).

tff(c_1493,plain,(
    '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_809])).

tff(c_18,plain,(
    ! [A_1,B_39,C_58] :
      ( m1_subset_1('#skF_1'(A_1,B_39,C_58),u1_struct_0(A_1))
      | '#skF_2'(A_1,B_39,C_58) != C_58
      | r2_yellow_0(A_1,B_39)
      | ~ r1_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1492,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_809])).

tff(c_1505,plain,
    ( '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | r2_yellow_0('#skF_5','#skF_7')
    | ~ r1_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_1492])).

tff(c_1520,plain,
    ( '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | r2_yellow_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_653,c_738,c_1505])).

tff(c_1521,plain,(
    '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1520])).

tff(c_1588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1493,c_1521])).

%------------------------------------------------------------------------------
