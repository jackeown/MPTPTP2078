%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1631+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:09 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 264 expanded)
%              Number of leaves         :   24 ( 107 expanded)
%              Depth                    :   19
%              Number of atoms          :  248 (1282 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_waybel_0 > r1_orders_2 > v10_waybel_0 > m1_subset_1 > l1_waybel_0 > v2_struct_0 > l1_orders_2 > k2_waybel_0 > a_3_0_waybel_0 > #nlpp > u1_struct_0 > #skF_7 > #skF_8 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v10_waybel_0,type,(
    v10_waybel_0: ( $i * $i ) > $o )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff(a_3_0_waybel_0,type,(
    a_3_0_waybel_0: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => ( v10_waybel_0(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(B))
                 => ? [D] :
                      ( m1_subset_1(D,u1_struct_0(B))
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(B))
                         => ( r1_orders_2(B,D,E)
                           => r1_orders_2(A,k2_waybel_0(A,B,C),k2_waybel_0(A,B,E)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_waybel_0)).

tff(f_42,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ( v10_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => r1_waybel_0(A,B,a_3_0_waybel_0(A,B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_waybel_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( r1_waybel_0(A,B,a_3_0_waybel_0(A,B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r1_orders_2(B,D,E)
                 => r1_orders_2(A,k2_waybel_0(A,B,C),k2_waybel_0(A,B,E)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_waybel_0__e1_34_1__waybel_0)).

tff(c_24,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_20,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_22,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_18,plain,(
    l1_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,
    ( m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ v10_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_55,plain,(
    ~ v10_waybel_0('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_6,plain,(
    ! [A_1,B_7] :
      ( m1_subset_1('#skF_1'(A_1,B_7),u1_struct_0(B_7))
      | v10_waybel_0(B_7,A_1)
      | ~ l1_waybel_0(B_7,A_1)
      | v2_struct_0(B_7)
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48,plain,(
    ! [C_72] :
      ( v10_waybel_0('#skF_5','#skF_4')
      | m1_subset_1('#skF_8'(C_72),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_72,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_56,plain,(
    ! [C_72] :
      ( m1_subset_1('#skF_8'(C_72),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_72,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_48])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13,D_22] :
      ( m1_subset_1('#skF_3'(A_11,B_12,C_13,D_22),u1_struct_0(B_12))
      | r1_waybel_0(A_11,B_12,a_3_0_waybel_0(A_11,B_12,C_13))
      | ~ m1_subset_1(D_22,u1_struct_0(B_12))
      | ~ m1_subset_1(C_13,u1_struct_0(B_12))
      | ~ l1_waybel_0(B_12,A_11)
      | v2_struct_0(B_12)
      | ~ l1_orders_2(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [B_12,D_22,A_11,C_13] :
      ( r1_orders_2(B_12,D_22,'#skF_3'(A_11,B_12,C_13,D_22))
      | r1_waybel_0(A_11,B_12,a_3_0_waybel_0(A_11,B_12,C_13))
      | ~ m1_subset_1(D_22,u1_struct_0(B_12))
      | ~ m1_subset_1(C_13,u1_struct_0(B_12))
      | ~ l1_waybel_0(B_12,A_11)
      | v2_struct_0(B_12)
      | ~ l1_orders_2(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_38,plain,(
    ! [C_72,E_77] :
      ( v10_waybel_0('#skF_5','#skF_4')
      | r1_orders_2('#skF_4',k2_waybel_0('#skF_4','#skF_5',C_72),k2_waybel_0('#skF_4','#skF_5',E_77))
      | ~ r1_orders_2('#skF_5','#skF_8'(C_72),E_77)
      | ~ m1_subset_1(E_77,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_72,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_66,plain,(
    ! [C_72,E_77] :
      ( r1_orders_2('#skF_4',k2_waybel_0('#skF_4','#skF_5',C_72),k2_waybel_0('#skF_4','#skF_5',E_77))
      | ~ r1_orders_2('#skF_5','#skF_8'(C_72),E_77)
      | ~ m1_subset_1(E_77,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_72,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_38])).

tff(c_94,plain,(
    ! [A_113,B_114,C_115,D_116] :
      ( ~ r1_orders_2(A_113,k2_waybel_0(A_113,B_114,C_115),k2_waybel_0(A_113,B_114,'#skF_3'(A_113,B_114,C_115,D_116)))
      | r1_waybel_0(A_113,B_114,a_3_0_waybel_0(A_113,B_114,C_115))
      | ~ m1_subset_1(D_116,u1_struct_0(B_114))
      | ~ m1_subset_1(C_115,u1_struct_0(B_114))
      | ~ l1_waybel_0(B_114,A_113)
      | v2_struct_0(B_114)
      | ~ l1_orders_2(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_98,plain,(
    ! [C_72,D_116] :
      ( r1_waybel_0('#skF_4','#skF_5',a_3_0_waybel_0('#skF_4','#skF_5',C_72))
      | ~ m1_subset_1(D_116,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0('#skF_5','#skF_4')
      | v2_struct_0('#skF_5')
      | ~ l1_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_orders_2('#skF_5','#skF_8'(C_72),'#skF_3'('#skF_4','#skF_5',C_72,D_116))
      | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5',C_72,D_116),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_72,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_66,c_94])).

tff(c_101,plain,(
    ! [C_72,D_116] :
      ( r1_waybel_0('#skF_4','#skF_5',a_3_0_waybel_0('#skF_4','#skF_5',C_72))
      | ~ m1_subset_1(D_116,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ r1_orders_2('#skF_5','#skF_8'(C_72),'#skF_3'('#skF_4','#skF_5',C_72,D_116))
      | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5',C_72,D_116),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_72,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_98])).

tff(c_104,plain,(
    ! [C_120,D_121] :
      ( r1_waybel_0('#skF_4','#skF_5',a_3_0_waybel_0('#skF_4','#skF_5',C_120))
      | ~ m1_subset_1(D_121,u1_struct_0('#skF_5'))
      | ~ r1_orders_2('#skF_5','#skF_8'(C_120),'#skF_3'('#skF_4','#skF_5',C_120,D_121))
      | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5',C_120,D_121),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_120,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_20,c_101])).

tff(c_116,plain,(
    ! [C_13] :
      ( ~ m1_subset_1('#skF_3'('#skF_4','#skF_5',C_13,'#skF_8'(C_13)),u1_struct_0('#skF_5'))
      | r1_waybel_0('#skF_4','#skF_5',a_3_0_waybel_0('#skF_4','#skF_5',C_13))
      | ~ m1_subset_1('#skF_8'(C_13),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_13,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0('#skF_5','#skF_4')
      | v2_struct_0('#skF_5')
      | ~ l1_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10,c_104])).

tff(c_127,plain,(
    ! [C_13] :
      ( ~ m1_subset_1('#skF_3'('#skF_4','#skF_5',C_13,'#skF_8'(C_13)),u1_struct_0('#skF_5'))
      | r1_waybel_0('#skF_4','#skF_5',a_3_0_waybel_0('#skF_4','#skF_5',C_13))
      | ~ m1_subset_1('#skF_8'(C_13),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_13,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_116])).

tff(c_129,plain,(
    ! [C_122] :
      ( ~ m1_subset_1('#skF_3'('#skF_4','#skF_5',C_122,'#skF_8'(C_122)),u1_struct_0('#skF_5'))
      | r1_waybel_0('#skF_4','#skF_5',a_3_0_waybel_0('#skF_4','#skF_5',C_122))
      | ~ m1_subset_1('#skF_8'(C_122),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_122,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_20,c_127])).

tff(c_141,plain,(
    ! [C_13] :
      ( r1_waybel_0('#skF_4','#skF_5',a_3_0_waybel_0('#skF_4','#skF_5',C_13))
      | ~ m1_subset_1('#skF_8'(C_13),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_13,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0('#skF_5','#skF_4')
      | v2_struct_0('#skF_5')
      | ~ l1_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_129])).

tff(c_152,plain,(
    ! [C_13] :
      ( r1_waybel_0('#skF_4','#skF_5',a_3_0_waybel_0('#skF_4','#skF_5',C_13))
      | ~ m1_subset_1('#skF_8'(C_13),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_13,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_141])).

tff(c_154,plain,(
    ! [C_123] :
      ( r1_waybel_0('#skF_4','#skF_5',a_3_0_waybel_0('#skF_4','#skF_5',C_123))
      | ~ m1_subset_1('#skF_8'(C_123),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_123,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_20,c_152])).

tff(c_159,plain,(
    ! [C_124] :
      ( r1_waybel_0('#skF_4','#skF_5',a_3_0_waybel_0('#skF_4','#skF_5',C_124))
      | ~ m1_subset_1(C_124,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_56,c_154])).

tff(c_4,plain,(
    ! [A_1,B_7] :
      ( ~ r1_waybel_0(A_1,B_7,a_3_0_waybel_0(A_1,B_7,'#skF_1'(A_1,B_7)))
      | v10_waybel_0(B_7,A_1)
      | ~ l1_waybel_0(B_7,A_1)
      | v2_struct_0(B_7)
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_165,plain,
    ( v10_waybel_0('#skF_5','#skF_4')
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_159,c_4])).

tff(c_172,plain,
    ( v10_waybel_0('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_165])).

tff(c_173,plain,(
    ~ m1_subset_1('#skF_1'('#skF_4','#skF_5'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_20,c_55,c_172])).

tff(c_182,plain,
    ( v10_waybel_0('#skF_5','#skF_4')
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_173])).

tff(c_185,plain,
    ( v10_waybel_0('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_182])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_20,c_55,c_185])).

tff(c_188,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_189,plain,(
    v10_waybel_0('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_2,plain,(
    ! [A_1,B_7,C_10] :
      ( r1_waybel_0(A_1,B_7,a_3_0_waybel_0(A_1,B_7,C_10))
      | ~ m1_subset_1(C_10,u1_struct_0(B_7))
      | ~ v10_waybel_0(B_7,A_1)
      | ~ l1_waybel_0(B_7,A_1)
      | v2_struct_0(B_7)
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_239,plain,(
    ! [A_171,B_172,C_173,E_174] :
      ( r1_orders_2(A_171,k2_waybel_0(A_171,B_172,C_173),k2_waybel_0(A_171,B_172,E_174))
      | ~ r1_orders_2(B_172,'#skF_2'(A_171,B_172,C_173),E_174)
      | ~ m1_subset_1(E_174,u1_struct_0(B_172))
      | ~ r1_waybel_0(A_171,B_172,a_3_0_waybel_0(A_171,B_172,C_173))
      | ~ m1_subset_1(C_173,u1_struct_0(B_172))
      | ~ l1_waybel_0(B_172,A_171)
      | v2_struct_0(B_172)
      | ~ l1_orders_2(A_171)
      | v2_struct_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    ! [D_70] :
      ( ~ r1_orders_2('#skF_4',k2_waybel_0('#skF_4','#skF_5','#skF_6'),k2_waybel_0('#skF_4','#skF_5','#skF_7'(D_70)))
      | ~ m1_subset_1(D_70,u1_struct_0('#skF_5'))
      | ~ v10_waybel_0('#skF_5','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_200,plain,(
    ! [D_70] :
      ( ~ r1_orders_2('#skF_4',k2_waybel_0('#skF_4','#skF_5','#skF_6'),k2_waybel_0('#skF_4','#skF_5','#skF_7'(D_70)))
      | ~ m1_subset_1(D_70,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_30])).

tff(c_246,plain,(
    ! [D_70] :
      ( ~ m1_subset_1(D_70,u1_struct_0('#skF_5'))
      | ~ r1_orders_2('#skF_5','#skF_2'('#skF_4','#skF_5','#skF_6'),'#skF_7'(D_70))
      | ~ m1_subset_1('#skF_7'(D_70),u1_struct_0('#skF_5'))
      | ~ r1_waybel_0('#skF_4','#skF_5',a_3_0_waybel_0('#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ l1_waybel_0('#skF_5','#skF_4')
      | v2_struct_0('#skF_5')
      | ~ l1_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_239,c_200])).

tff(c_250,plain,(
    ! [D_70] :
      ( ~ m1_subset_1(D_70,u1_struct_0('#skF_5'))
      | ~ r1_orders_2('#skF_5','#skF_2'('#skF_4','#skF_5','#skF_6'),'#skF_7'(D_70))
      | ~ m1_subset_1('#skF_7'(D_70),u1_struct_0('#skF_5'))
      | ~ r1_waybel_0('#skF_4','#skF_5',a_3_0_waybel_0('#skF_4','#skF_5','#skF_6'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_188,c_246])).

tff(c_251,plain,(
    ! [D_70] :
      ( ~ m1_subset_1(D_70,u1_struct_0('#skF_5'))
      | ~ r1_orders_2('#skF_5','#skF_2'('#skF_4','#skF_5','#skF_6'),'#skF_7'(D_70))
      | ~ m1_subset_1('#skF_7'(D_70),u1_struct_0('#skF_5'))
      | ~ r1_waybel_0('#skF_4','#skF_5',a_3_0_waybel_0('#skF_4','#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_20,c_250])).

tff(c_252,plain,(
    ~ r1_waybel_0('#skF_4','#skF_5',a_3_0_waybel_0('#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_251])).

tff(c_259,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ v10_waybel_0('#skF_5','#skF_4')
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_252])).

tff(c_266,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_189,c_188,c_259])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_20,c_266])).

tff(c_270,plain,(
    r1_waybel_0('#skF_4','#skF_5',a_3_0_waybel_0('#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( m1_subset_1('#skF_2'(A_11,B_12,C_13),u1_struct_0(B_12))
      | ~ r1_waybel_0(A_11,B_12,a_3_0_waybel_0(A_11,B_12,C_13))
      | ~ m1_subset_1(C_13,u1_struct_0(B_12))
      | ~ l1_waybel_0(B_12,A_11)
      | v2_struct_0(B_12)
      | ~ l1_orders_2(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_272,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_270,c_16])).

tff(c_275,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_188,c_272])).

tff(c_276,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_20,c_275])).

tff(c_34,plain,(
    ! [D_70] :
      ( m1_subset_1('#skF_7'(D_70),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(D_70,u1_struct_0('#skF_5'))
      | ~ v10_waybel_0('#skF_5','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_191,plain,(
    ! [D_70] :
      ( m1_subset_1('#skF_7'(D_70),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(D_70,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_34])).

tff(c_32,plain,(
    ! [D_70] :
      ( r1_orders_2('#skF_5',D_70,'#skF_7'(D_70))
      | ~ m1_subset_1(D_70,u1_struct_0('#skF_5'))
      | ~ v10_waybel_0('#skF_5','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_194,plain,(
    ! [D_70] :
      ( r1_orders_2('#skF_5',D_70,'#skF_7'(D_70))
      | ~ m1_subset_1(D_70,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_32])).

tff(c_277,plain,(
    ! [D_175] :
      ( ~ m1_subset_1(D_175,u1_struct_0('#skF_5'))
      | ~ r1_orders_2('#skF_5','#skF_2'('#skF_4','#skF_5','#skF_6'),'#skF_7'(D_175))
      | ~ m1_subset_1('#skF_7'(D_175),u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_281,plain,
    ( ~ m1_subset_1('#skF_7'('#skF_2'('#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_194,c_277])).

tff(c_284,plain,(
    ~ m1_subset_1('#skF_7'('#skF_2'('#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_281])).

tff(c_287,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_191,c_284])).

tff(c_291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_287])).

%------------------------------------------------------------------------------
