%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1568+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:05 EST 2020

% Result     : Theorem 5.31s
% Output     : CNFRefutation 5.66s
% Verified   : 
% Statistics : Number of formulae       :  163 (7106 expanded)
%              Number of leaves         :   19 (2369 expanded)
%              Depth                    :   30
%              Number of atoms          :  573 (39937 expanded)
%              Number of equality atoms :   55 (2830 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_yellow_0 > m1_subset_1 > v2_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2

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
                 => ( r2_lattice3(A,B,D)
                  <=> r2_lattice3(A,C,D) ) )
              & r1_yellow_0(A,B) )
           => r1_yellow_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_yellow_0)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( r1_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r2_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_lattice3(A,B,D)
                   => r1_orders_2(A,C,D) ) )
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r2_lattice3(A,B,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( r2_lattice3(A,B,E)
                           => r1_orders_2(A,D,E) ) ) )
                   => D = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_yellow_0)).

tff(c_38,plain,(
    ~ r1_yellow_0('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_42,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    r1_yellow_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [A_1,B_39] :
      ( m1_subset_1('#skF_3'(A_1,B_39),u1_struct_0(A_1))
      | ~ r1_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_1,B_39,C_58] :
      ( r2_lattice3(A_1,B_39,'#skF_1'(A_1,B_39,C_58))
      | '#skF_2'(A_1,B_39,C_58) != C_58
      | r1_yellow_0(A_1,B_39)
      | ~ r2_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_103,plain,(
    ! [A_98,B_99,C_100] :
      ( m1_subset_1('#skF_1'(A_98,B_99,C_100),u1_struct_0(A_98))
      | '#skF_2'(A_98,B_99,C_100) != C_100
      | r1_yellow_0(A_98,B_99)
      | ~ r2_lattice3(A_98,B_99,C_100)
      | ~ m1_subset_1(C_100,u1_struct_0(A_98))
      | ~ l1_orders_2(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    ! [D_77] :
      ( r2_lattice3('#skF_5','#skF_6',D_77)
      | ~ r2_lattice3('#skF_5','#skF_7',D_77)
      | ~ m1_subset_1(D_77,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_107,plain,(
    ! [B_99,C_100] :
      ( r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_99,C_100))
      | ~ r2_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5',B_99,C_100))
      | '#skF_2'('#skF_5',B_99,C_100) != C_100
      | r1_yellow_0('#skF_5',B_99)
      | ~ r2_lattice3('#skF_5',B_99,C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_103,c_46])).

tff(c_214,plain,(
    ! [B_135,C_136] :
      ( r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_135,C_136))
      | ~ r2_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5',B_135,C_136))
      | '#skF_2'('#skF_5',B_135,C_136) != C_136
      | r1_yellow_0('#skF_5',B_135)
      | ~ r2_lattice3('#skF_5',B_135,C_136)
      | ~ m1_subset_1(C_136,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_107])).

tff(c_231,plain,(
    ! [C_58] :
      ( r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_7',C_58))
      | '#skF_2'('#skF_5','#skF_7',C_58) != C_58
      | r1_yellow_0('#skF_5','#skF_7')
      | ~ r2_lattice3('#skF_5','#skF_7',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_214])).

tff(c_243,plain,(
    ! [C_58] :
      ( r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_7',C_58))
      | '#skF_2'('#skF_5','#skF_7',C_58) != C_58
      | r1_yellow_0('#skF_5','#skF_7')
      | ~ r2_lattice3('#skF_5','#skF_7',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_231])).

tff(c_244,plain,(
    ! [C_58] :
      ( r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_7',C_58))
      | '#skF_2'('#skF_5','#skF_7',C_58) != C_58
      | ~ r2_lattice3('#skF_5','#skF_7',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_243])).

tff(c_2,plain,(
    ! [A_1,B_39,D_69] :
      ( r1_orders_2(A_1,'#skF_3'(A_1,B_39),D_69)
      | ~ r2_lattice3(A_1,B_39,D_69)
      | ~ m1_subset_1(D_69,u1_struct_0(A_1))
      | ~ r1_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_157,plain,(
    ! [A_118,C_119,B_120] :
      ( ~ r1_orders_2(A_118,C_119,'#skF_1'(A_118,B_120,C_119))
      | m1_subset_1('#skF_2'(A_118,B_120,C_119),u1_struct_0(A_118))
      | r1_yellow_0(A_118,B_120)
      | ~ r2_lattice3(A_118,B_120,C_119)
      | ~ m1_subset_1(C_119,u1_struct_0(A_118))
      | ~ l1_orders_2(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_769,plain,(
    ! [A_186,B_187,B_188] :
      ( m1_subset_1('#skF_2'(A_186,B_187,'#skF_3'(A_186,B_188)),u1_struct_0(A_186))
      | r1_yellow_0(A_186,B_187)
      | ~ r2_lattice3(A_186,B_187,'#skF_3'(A_186,B_188))
      | ~ m1_subset_1('#skF_3'(A_186,B_188),u1_struct_0(A_186))
      | ~ r2_lattice3(A_186,B_188,'#skF_1'(A_186,B_187,'#skF_3'(A_186,B_188)))
      | ~ m1_subset_1('#skF_1'(A_186,B_187,'#skF_3'(A_186,B_188)),u1_struct_0(A_186))
      | ~ r1_yellow_0(A_186,B_188)
      | ~ l1_orders_2(A_186) ) ),
    inference(resolution,[status(thm)],[c_2,c_157])).

tff(c_793,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_244,c_769])).

tff(c_834,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_793])).

tff(c_835,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_834])).

tff(c_843,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_835])).

tff(c_846,plain,
    ( ~ r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_843])).

tff(c_850,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_846])).

tff(c_852,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_835])).

tff(c_4,plain,(
    ! [A_1,B_39] :
      ( r2_lattice3(A_1,B_39,'#skF_3'(A_1,B_39))
      | ~ r1_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_51,plain,(
    ! [D_82] :
      ( r2_lattice3('#skF_5','#skF_7',D_82)
      | ~ r2_lattice3('#skF_5','#skF_6',D_82)
      | ~ m1_subset_1(D_82,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_55,plain,(
    ! [B_39] :
      ( r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5',B_39))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_3'('#skF_5',B_39))
      | ~ r1_yellow_0('#skF_5',B_39)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_58,plain,(
    ! [B_39] :
      ( r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5',B_39))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_3'('#skF_5',B_39))
      | ~ r1_yellow_0('#skF_5',B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_55])).

tff(c_872,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6'))
    | ~ r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_852,c_46])).

tff(c_875,plain,(
    ~ r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_872])).

tff(c_952,plain,
    ( ~ r2_lattice3('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6'))
    | ~ r1_yellow_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_875])).

tff(c_955,plain,(
    ~ r2_lattice3('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_952])).

tff(c_958,plain,
    ( ~ r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_955])).

tff(c_962,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_958])).

tff(c_963,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_872])).

tff(c_48,plain,(
    ! [D_77] :
      ( r2_lattice3('#skF_5','#skF_7',D_77)
      | ~ r2_lattice3('#skF_5','#skF_6',D_77)
      | ~ m1_subset_1(D_77,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_873,plain,
    ( r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_852,c_48])).

tff(c_966,plain,(
    r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_963,c_873])).

tff(c_18,plain,(
    ! [A_1,B_39,C_58] :
      ( m1_subset_1('#skF_1'(A_1,B_39,C_58),u1_struct_0(A_1))
      | '#skF_2'(A_1,B_39,C_58) != C_58
      | r1_yellow_0(A_1,B_39)
      | ~ r2_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_851,plain,
    ( ~ r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_835])).

tff(c_975,plain,
    ( '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_966,c_851])).

tff(c_976,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_975])).

tff(c_988,plain,
    ( '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | r1_yellow_0('#skF_5','#skF_7')
    | ~ r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_976])).

tff(c_1003,plain,
    ( '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | r1_yellow_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_852,c_966,c_988])).

tff(c_1004,plain,(
    '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1003])).

tff(c_36,plain,(
    ! [A_1,B_39,C_58] :
      ( m1_subset_1('#skF_1'(A_1,B_39,C_58),u1_struct_0(A_1))
      | m1_subset_1('#skF_2'(A_1,B_39,C_58),u1_struct_0(A_1))
      | r1_yellow_0(A_1,B_39)
      | ~ r2_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_982,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_7')
    | ~ r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_976])).

tff(c_995,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_852,c_966,c_982])).

tff(c_996,plain,(
    m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_995])).

tff(c_30,plain,(
    ! [A_1,B_39,C_58] :
      ( m1_subset_1('#skF_1'(A_1,B_39,C_58),u1_struct_0(A_1))
      | r2_lattice3(A_1,B_39,'#skF_2'(A_1,B_39,C_58))
      | r1_yellow_0(A_1,B_39)
      | ~ r2_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_985,plain,
    ( r2_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r1_yellow_0('#skF_5','#skF_7')
    | ~ r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_976])).

tff(c_999,plain,
    ( r2_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r1_yellow_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_852,c_966,c_985])).

tff(c_1000,plain,(
    r2_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_999])).

tff(c_1011,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | ~ r2_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_996,c_46])).

tff(c_1128,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_1011])).

tff(c_10,plain,(
    ! [A_1,B_39,D_70] :
      ( r2_lattice3(A_1,B_39,'#skF_4'(A_1,B_39,D_70))
      | D_70 = '#skF_3'(A_1,B_39)
      | ~ r2_lattice3(A_1,B_39,D_70)
      | ~ m1_subset_1(D_70,u1_struct_0(A_1))
      | ~ r1_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_81,plain,(
    ! [A_89,B_90,D_91] :
      ( m1_subset_1('#skF_4'(A_89,B_90,D_91),u1_struct_0(A_89))
      | D_91 = '#skF_3'(A_89,B_90)
      | ~ r2_lattice3(A_89,B_90,D_91)
      | ~ m1_subset_1(D_91,u1_struct_0(A_89))
      | ~ r1_yellow_0(A_89,B_90)
      | ~ l1_orders_2(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_89,plain,(
    ! [B_90,D_91] :
      ( r2_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_90,D_91))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_4'('#skF_5',B_90,D_91))
      | D_91 = '#skF_3'('#skF_5',B_90)
      | ~ r2_lattice3('#skF_5',B_90,D_91)
      | ~ m1_subset_1(D_91,u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_90)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_81,c_48])).

tff(c_95,plain,(
    ! [B_90,D_91] :
      ( r2_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_90,D_91))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_4'('#skF_5',B_90,D_91))
      | D_91 = '#skF_3'('#skF_5',B_90)
      | ~ r2_lattice3('#skF_5',B_90,D_91)
      | ~ m1_subset_1(D_91,u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_89])).

tff(c_12,plain,(
    ! [A_1,B_39,D_70] :
      ( m1_subset_1('#skF_4'(A_1,B_39,D_70),u1_struct_0(A_1))
      | D_70 = '#skF_3'(A_1,B_39)
      | ~ r2_lattice3(A_1,B_39,D_70)
      | ~ m1_subset_1(D_70,u1_struct_0(A_1))
      | ~ r1_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    ! [A_1,B_39,C_58,E_64] :
      ( m1_subset_1('#skF_1'(A_1,B_39,C_58),u1_struct_0(A_1))
      | r1_orders_2(A_1,'#skF_2'(A_1,B_39,C_58),E_64)
      | ~ r2_lattice3(A_1,B_39,E_64)
      | ~ m1_subset_1(E_64,u1_struct_0(A_1))
      | r1_yellow_0(A_1,B_39)
      | ~ r2_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_979,plain,(
    ! [E_64] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),E_64)
      | ~ r2_lattice3('#skF_5','#skF_7',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_7')
      | ~ r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_976])).

tff(c_991,plain,(
    ! [E_64] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),E_64)
      | ~ r2_lattice3('#skF_5','#skF_7',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_852,c_966,c_979])).

tff(c_1093,plain,(
    ! [E_195] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),E_195)
      | ~ r2_lattice3('#skF_5','#skF_7',E_195)
      | ~ m1_subset_1(E_195,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_991])).

tff(c_8,plain,(
    ! [A_1,D_70,B_39] :
      ( ~ r1_orders_2(A_1,D_70,'#skF_4'(A_1,B_39,D_70))
      | D_70 = '#skF_3'(A_1,B_39)
      | ~ r2_lattice3(A_1,B_39,D_70)
      | ~ m1_subset_1(D_70,u1_struct_0(A_1))
      | ~ r1_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1110,plain,(
    ! [B_39] :
      ( '#skF_3'('#skF_5',B_39) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r2_lattice3('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_39)
      | ~ l1_orders_2('#skF_5')
      | ~ r2_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1093,c_8])).

tff(c_1166,plain,(
    ! [B_196] :
      ( '#skF_3'('#skF_5',B_196) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r2_lattice3('#skF_5',B_196,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ r1_yellow_0('#skF_5',B_196)
      | ~ r2_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_196,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_196,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_996,c_1110])).

tff(c_1170,plain,(
    ! [B_39] :
      ( ~ r2_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | '#skF_3'('#skF_5',B_39) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r2_lattice3('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_39)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_1166])).

tff(c_1174,plain,(
    ! [B_197] :
      ( ~ r2_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_197,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | '#skF_3'('#skF_5',B_197) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r2_lattice3('#skF_5',B_197,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ r1_yellow_0('#skF_5',B_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_996,c_1170])).

tff(c_1178,plain,(
    ! [B_90] :
      ( ~ r2_lattice3('#skF_5','#skF_6','#skF_4'('#skF_5',B_90,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | '#skF_3'('#skF_5',B_90) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r2_lattice3('#skF_5',B_90,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_90) ) ),
    inference(resolution,[status(thm)],[c_95,c_1174])).

tff(c_1263,plain,(
    ! [B_201] :
      ( ~ r2_lattice3('#skF_5','#skF_6','#skF_4'('#skF_5',B_201,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | '#skF_3'('#skF_5',B_201) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r2_lattice3('#skF_5',B_201,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ r1_yellow_0('#skF_5',B_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_996,c_1178])).

tff(c_1267,plain,
    ( '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_1263])).

tff(c_1270,plain,(
    '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_996,c_1128,c_1267])).

tff(c_1272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1004,c_1270])).

tff(c_1274,plain,(
    m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_975])).

tff(c_1273,plain,
    ( '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_975])).

tff(c_1283,plain,(
    '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1273])).

tff(c_1281,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | ~ r2_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1274,c_46])).

tff(c_1284,plain,(
    ~ r2_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1281])).

tff(c_34,plain,(
    ! [A_1,B_39,C_58] :
      ( r2_lattice3(A_1,B_39,'#skF_1'(A_1,B_39,C_58))
      | m1_subset_1('#skF_2'(A_1,B_39,C_58),u1_struct_0(A_1))
      | r1_yellow_0(A_1,B_39)
      | ~ r2_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22,plain,(
    ! [A_1,B_39,C_58,E_64] :
      ( r2_lattice3(A_1,B_39,'#skF_1'(A_1,B_39,C_58))
      | r1_orders_2(A_1,'#skF_2'(A_1,B_39,C_58),E_64)
      | ~ r2_lattice3(A_1,B_39,E_64)
      | ~ m1_subset_1(E_64,u1_struct_0(A_1))
      | r1_yellow_0(A_1,B_39)
      | ~ r2_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1305,plain,(
    ! [E_64] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),E_64)
      | ~ r2_lattice3('#skF_5','#skF_7',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_7')
      | ~ r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_1284])).

tff(c_1339,plain,(
    ! [E_64] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),E_64)
      | ~ r2_lattice3('#skF_5','#skF_7',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_852,c_966,c_1305])).

tff(c_1355,plain,(
    ! [E_202] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),E_202)
      | ~ r2_lattice3('#skF_5','#skF_7',E_202)
      | ~ m1_subset_1(E_202,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1339])).

tff(c_1372,plain,(
    ! [B_39] :
      ( '#skF_3'('#skF_5',B_39) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r2_lattice3('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_39)
      | ~ l1_orders_2('#skF_5')
      | ~ r2_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1355,c_8])).

tff(c_1387,plain,(
    ! [B_39] :
      ( '#skF_3'('#skF_5',B_39) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r2_lattice3('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_39)
      | ~ r2_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1372])).

tff(c_1640,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1387])).

tff(c_1649,plain,
    ( r2_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r1_yellow_0('#skF_5','#skF_7')
    | ~ r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_1640])).

tff(c_1660,plain,
    ( r2_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r1_yellow_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_852,c_966,c_1649])).

tff(c_1662,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1284,c_1660])).

tff(c_1664,plain,(
    m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1387])).

tff(c_28,plain,(
    ! [A_1,B_39,C_58] :
      ( r2_lattice3(A_1,B_39,'#skF_1'(A_1,B_39,C_58))
      | r2_lattice3(A_1,B_39,'#skF_2'(A_1,B_39,C_58))
      | r1_yellow_0(A_1,B_39)
      | ~ r2_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1309,plain,
    ( r2_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r1_yellow_0('#skF_5','#skF_7')
    | ~ r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_1284])).

tff(c_1343,plain,
    ( r2_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r1_yellow_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_852,c_966,c_1309])).

tff(c_1344,plain,(
    r2_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1343])).

tff(c_142,plain,(
    ! [A_115,B_116,C_117] :
      ( r2_lattice3(A_115,B_116,'#skF_1'(A_115,B_116,C_117))
      | m1_subset_1('#skF_2'(A_115,B_116,C_117),u1_struct_0(A_115))
      | r1_yellow_0(A_115,B_116)
      | ~ r2_lattice3(A_115,B_116,C_117)
      | ~ m1_subset_1(C_117,u1_struct_0(A_115))
      | ~ l1_orders_2(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_146,plain,(
    ! [B_116,C_117] :
      ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_116,C_117))
      | ~ r2_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5',B_116,C_117))
      | r2_lattice3('#skF_5',B_116,'#skF_1'('#skF_5',B_116,C_117))
      | r1_yellow_0('#skF_5',B_116)
      | ~ r2_lattice3('#skF_5',B_116,C_117)
      | ~ m1_subset_1(C_117,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_142,c_46])).

tff(c_153,plain,(
    ! [B_116,C_117] :
      ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_116,C_117))
      | ~ r2_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5',B_116,C_117))
      | r2_lattice3('#skF_5',B_116,'#skF_1'('#skF_5',B_116,C_117))
      | r1_yellow_0('#skF_5',B_116)
      | ~ r2_lattice3('#skF_5',B_116,C_117)
      | ~ m1_subset_1(C_117,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_146])).

tff(c_1350,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r2_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r1_yellow_0('#skF_5','#skF_7')
    | ~ r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1344,c_153])).

tff(c_1353,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r2_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r1_yellow_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_852,c_966,c_1350])).

tff(c_1354,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1284,c_1353])).

tff(c_1717,plain,(
    ! [B_215] :
      ( '#skF_3'('#skF_5',B_215) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r2_lattice3('#skF_5',B_215,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ r1_yellow_0('#skF_5',B_215)
      | ~ r2_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_215,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_215,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))),u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_1387])).

tff(c_1721,plain,(
    ! [B_39] :
      ( ~ r2_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | '#skF_3'('#skF_5',B_39) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r2_lattice3('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_39)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_1717])).

tff(c_1725,plain,(
    ! [B_216] :
      ( ~ r2_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_216,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | '#skF_3'('#skF_5',B_216) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r2_lattice3('#skF_5',B_216,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ r1_yellow_0('#skF_5',B_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1664,c_1721])).

tff(c_1729,plain,(
    ! [B_90] :
      ( ~ r2_lattice3('#skF_5','#skF_6','#skF_4'('#skF_5',B_90,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | '#skF_3'('#skF_5',B_90) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r2_lattice3('#skF_5',B_90,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_90) ) ),
    inference(resolution,[status(thm)],[c_95,c_1725])).

tff(c_1740,plain,(
    ! [B_217] :
      ( ~ r2_lattice3('#skF_5','#skF_6','#skF_4'('#skF_5',B_217,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | '#skF_3'('#skF_5',B_217) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r2_lattice3('#skF_5',B_217,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ r1_yellow_0('#skF_5',B_217) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1664,c_1729])).

tff(c_1744,plain,
    ( '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_1740])).

tff(c_1747,plain,(
    '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1664,c_1354,c_1744])).

tff(c_1749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1283,c_1747])).

tff(c_1750,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_1281])).

tff(c_161,plain,(
    ! [A_1,B_120,B_39] :
      ( m1_subset_1('#skF_2'(A_1,B_120,'#skF_3'(A_1,B_39)),u1_struct_0(A_1))
      | r1_yellow_0(A_1,B_120)
      | ~ r2_lattice3(A_1,B_120,'#skF_3'(A_1,B_39))
      | ~ m1_subset_1('#skF_3'(A_1,B_39),u1_struct_0(A_1))
      | ~ r2_lattice3(A_1,B_39,'#skF_1'(A_1,B_120,'#skF_3'(A_1,B_39)))
      | ~ m1_subset_1('#skF_1'(A_1,B_120,'#skF_3'(A_1,B_39)),u1_struct_0(A_1))
      | ~ r1_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_157])).

tff(c_1829,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_7')
    | ~ r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_1750,c_161])).

tff(c_1836,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1274,c_852,c_966,c_1829])).

tff(c_1837,plain,(
    m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1836])).

tff(c_177,plain,(
    ! [A_124,C_125,B_126] :
      ( ~ r1_orders_2(A_124,C_125,'#skF_1'(A_124,B_126,C_125))
      | r2_lattice3(A_124,B_126,'#skF_2'(A_124,B_126,C_125))
      | r1_yellow_0(A_124,B_126)
      | ~ r2_lattice3(A_124,B_126,C_125)
      | ~ m1_subset_1(C_125,u1_struct_0(A_124))
      | ~ l1_orders_2(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_181,plain,(
    ! [A_1,B_126,B_39] :
      ( r2_lattice3(A_1,B_126,'#skF_2'(A_1,B_126,'#skF_3'(A_1,B_39)))
      | r1_yellow_0(A_1,B_126)
      | ~ r2_lattice3(A_1,B_126,'#skF_3'(A_1,B_39))
      | ~ m1_subset_1('#skF_3'(A_1,B_39),u1_struct_0(A_1))
      | ~ r2_lattice3(A_1,B_39,'#skF_1'(A_1,B_126,'#skF_3'(A_1,B_39)))
      | ~ m1_subset_1('#skF_1'(A_1,B_126,'#skF_3'(A_1,B_39)),u1_struct_0(A_1))
      | ~ r1_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_177])).

tff(c_1827,plain,
    ( r2_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r1_yellow_0('#skF_5','#skF_7')
    | ~ r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_1750,c_181])).

tff(c_1832,plain,
    ( r2_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | r1_yellow_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1274,c_852,c_966,c_1827])).

tff(c_1833,plain,(
    r2_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1832])).

tff(c_1879,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | ~ r2_lattice3('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1837,c_46])).

tff(c_1885,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1833,c_1879])).

tff(c_308,plain,(
    ! [A_148,C_149,B_150,E_151] :
      ( ~ r1_orders_2(A_148,C_149,'#skF_1'(A_148,B_150,C_149))
      | r1_orders_2(A_148,'#skF_2'(A_148,B_150,C_149),E_151)
      | ~ r2_lattice3(A_148,B_150,E_151)
      | ~ m1_subset_1(E_151,u1_struct_0(A_148))
      | r1_yellow_0(A_148,B_150)
      | ~ r2_lattice3(A_148,B_150,C_149)
      | ~ m1_subset_1(C_149,u1_struct_0(A_148))
      | ~ l1_orders_2(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1976,plain,(
    ! [A_224,B_225,B_226,E_227] :
      ( r1_orders_2(A_224,'#skF_2'(A_224,B_225,'#skF_3'(A_224,B_226)),E_227)
      | ~ r2_lattice3(A_224,B_225,E_227)
      | ~ m1_subset_1(E_227,u1_struct_0(A_224))
      | r1_yellow_0(A_224,B_225)
      | ~ r2_lattice3(A_224,B_225,'#skF_3'(A_224,B_226))
      | ~ m1_subset_1('#skF_3'(A_224,B_226),u1_struct_0(A_224))
      | ~ r2_lattice3(A_224,B_226,'#skF_1'(A_224,B_225,'#skF_3'(A_224,B_226)))
      | ~ m1_subset_1('#skF_1'(A_224,B_225,'#skF_3'(A_224,B_226)),u1_struct_0(A_224))
      | ~ r1_yellow_0(A_224,B_226)
      | ~ l1_orders_2(A_224) ) ),
    inference(resolution,[status(thm)],[c_2,c_308])).

tff(c_1978,plain,(
    ! [E_227] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),E_227)
      | ~ r2_lattice3('#skF_5','#skF_7',E_227)
      | ~ m1_subset_1(E_227,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_7')
      | ~ r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5','#skF_6')
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1750,c_1976])).

tff(c_2020,plain,(
    ! [E_227] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),E_227)
      | ~ r2_lattice3('#skF_5','#skF_7',E_227)
      | ~ m1_subset_1(E_227,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1274,c_852,c_966,c_1978])).

tff(c_2056,plain,(
    ! [E_228] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),E_228)
      | ~ r2_lattice3('#skF_5','#skF_7',E_228)
      | ~ m1_subset_1(E_228,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_2020])).

tff(c_2073,plain,(
    ! [B_39] :
      ( '#skF_3'('#skF_5',B_39) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r2_lattice3('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_39)
      | ~ l1_orders_2('#skF_5')
      | ~ r2_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2056,c_8])).

tff(c_2089,plain,(
    ! [B_229] :
      ( '#skF_3'('#skF_5',B_229) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r2_lattice3('#skF_5',B_229,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ r1_yellow_0('#skF_5',B_229)
      | ~ r2_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_229,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_229,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1837,c_2073])).

tff(c_2093,plain,(
    ! [B_39] :
      ( ~ r2_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | '#skF_3'('#skF_5',B_39) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r2_lattice3('#skF_5',B_39,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_39)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_2089])).

tff(c_2097,plain,(
    ! [B_230] :
      ( ~ r2_lattice3('#skF_5','#skF_7','#skF_4'('#skF_5',B_230,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | '#skF_3'('#skF_5',B_230) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r2_lattice3('#skF_5',B_230,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ r1_yellow_0('#skF_5',B_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1837,c_2093])).

tff(c_2101,plain,(
    ! [B_90] :
      ( ~ r2_lattice3('#skF_5','#skF_6','#skF_4'('#skF_5',B_90,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | '#skF_3'('#skF_5',B_90) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r2_lattice3('#skF_5',B_90,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_90) ) ),
    inference(resolution,[status(thm)],[c_95,c_2097])).

tff(c_2112,plain,(
    ! [B_231] :
      ( ~ r2_lattice3('#skF_5','#skF_6','#skF_4'('#skF_5',B_231,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))))
      | '#skF_3'('#skF_5',B_231) = '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
      | ~ r2_lattice3('#skF_5',B_231,'#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
      | ~ r1_yellow_0('#skF_5',B_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1837,c_2101])).

tff(c_2116,plain,
    ( '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_2112])).

tff(c_2119,plain,(
    '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1837,c_1885,c_2116])).

tff(c_2121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1283,c_2119])).

tff(c_2123,plain,(
    '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1273])).

tff(c_2266,plain,(
    ~ r2_lattice3('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1281])).

tff(c_2294,plain,
    ( '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | r1_yellow_0('#skF_5','#skF_7')
    | ~ r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_2266])).

tff(c_2329,plain,(
    r1_yellow_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_852,c_966,c_2123,c_2294])).

tff(c_2331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_2329])).

tff(c_2332,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_1281])).

tff(c_119,plain,(
    ! [A_104,C_105,B_106] :
      ( ~ r1_orders_2(A_104,C_105,'#skF_1'(A_104,B_106,C_105))
      | '#skF_2'(A_104,B_106,C_105) != C_105
      | r1_yellow_0(A_104,B_106)
      | ~ r2_lattice3(A_104,B_106,C_105)
      | ~ m1_subset_1(C_105,u1_struct_0(A_104))
      | ~ l1_orders_2(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2387,plain,(
    ! [A_235,B_236,B_237] :
      ( '#skF_2'(A_235,B_236,'#skF_3'(A_235,B_237)) != '#skF_3'(A_235,B_237)
      | r1_yellow_0(A_235,B_236)
      | ~ r2_lattice3(A_235,B_236,'#skF_3'(A_235,B_237))
      | ~ m1_subset_1('#skF_3'(A_235,B_237),u1_struct_0(A_235))
      | ~ r2_lattice3(A_235,B_237,'#skF_1'(A_235,B_236,'#skF_3'(A_235,B_237)))
      | ~ m1_subset_1('#skF_1'(A_235,B_236,'#skF_3'(A_235,B_237)),u1_struct_0(A_235))
      | ~ r1_yellow_0(A_235,B_237)
      | ~ l1_orders_2(A_235) ) ),
    inference(resolution,[status(thm)],[c_2,c_119])).

tff(c_2389,plain,
    ( '#skF_2'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | r1_yellow_0('#skF_5','#skF_7')
    | ~ r2_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_7','#skF_3'('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_2332,c_2387])).

tff(c_2431,plain,(
    r1_yellow_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1274,c_852,c_966,c_2123,c_2389])).

tff(c_2433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_2431])).

%------------------------------------------------------------------------------
