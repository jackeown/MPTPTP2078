%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1554+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:03 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 416 expanded)
%              Number of leaves         :   23 ( 155 expanded)
%              Depth                    :   12
%              Number of atoms          :  384 (2056 expanded)
%              Number of equality atoms :   45 ( 243 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r2_yellow_0 > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v3_lattice3 > v2_struct_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_lattice3,type,(
    v3_lattice3: $i > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v5_orders_2(A)
          & v3_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( B = k1_yellow_0(A,C)
              <=> ( r2_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,C,D)
                       => r1_orders_2(A,B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_yellow_0)).

tff(f_38,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v3_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r1_yellow_0(A,B)
          & r2_yellow_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_0)).

tff(f_72,axiom,(
    ! [A] :
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

tff(c_30,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_28,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26,plain,(
    v3_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( r1_yellow_0(A_1,B_3)
      | ~ l1_orders_2(A_1)
      | ~ v3_lattice3(A_1)
      | ~ v5_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_48,plain,
    ( r2_lattice3('#skF_2','#skF_4','#skF_3')
    | m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | ~ r2_lattice3('#skF_2','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_641,plain,(
    ~ r2_lattice3('#skF_2','#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_50,plain,
    ( k1_yellow_0('#skF_2','#skF_4') != '#skF_3'
    | k1_yellow_0('#skF_2','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_55,plain,(
    k1_yellow_0('#skF_2','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_36,plain,
    ( r2_lattice3('#skF_2','#skF_4','#skF_3')
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_6')
    | ~ r2_lattice3('#skF_2','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_61,plain,(
    ~ r2_lattice3('#skF_2','#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_54,plain,
    ( r2_lattice3('#skF_2','#skF_4','#skF_3')
    | k1_yellow_0('#skF_2','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_56,plain,(
    k1_yellow_0('#skF_2','#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_65,plain,(
    ! [A_49,C_50] :
      ( r2_lattice3(A_49,C_50,k1_yellow_0(A_49,C_50))
      | ~ r1_yellow_0(A_49,C_50)
      | ~ m1_subset_1(k1_yellow_0(A_49,C_50),u1_struct_0(A_49))
      | ~ l1_orders_2(A_49)
      | ~ v5_orders_2(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_67,plain,
    ( r2_lattice3('#skF_2','#skF_5',k1_yellow_0('#skF_2','#skF_5'))
    | ~ r1_yellow_0('#skF_2','#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_65])).

tff(c_69,plain,
    ( r2_lattice3('#skF_2','#skF_5','#skF_3')
    | ~ r1_yellow_0('#skF_2','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_22,c_56,c_67])).

tff(c_70,plain,(
    ~ r1_yellow_0('#skF_2','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_69])).

tff(c_73,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v3_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_70])).

tff(c_76,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_73])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_76])).

tff(c_79,plain,
    ( ~ r1_orders_2('#skF_2','#skF_3','#skF_6')
    | r2_lattice3('#skF_2','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_81,plain,(
    ~ r1_orders_2('#skF_2','#skF_3','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_80,plain,(
    r2_lattice3('#skF_2','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_42,plain,
    ( r2_lattice3('#skF_2','#skF_4','#skF_3')
    | r2_lattice3('#skF_2','#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_2','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_94,plain,
    ( r2_lattice3('#skF_2','#skF_4','#skF_3')
    | r2_lattice3('#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_42])).

tff(c_95,plain,(
    r2_lattice3('#skF_2','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_91,plain,
    ( r2_lattice3('#skF_2','#skF_4','#skF_3')
    | m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_48])).

tff(c_92,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_114,plain,(
    ! [A_75,C_76,D_77] :
      ( r1_orders_2(A_75,k1_yellow_0(A_75,C_76),D_77)
      | ~ r2_lattice3(A_75,C_76,D_77)
      | ~ m1_subset_1(D_77,u1_struct_0(A_75))
      | ~ r1_yellow_0(A_75,C_76)
      | ~ m1_subset_1(k1_yellow_0(A_75,C_76),u1_struct_0(A_75))
      | ~ l1_orders_2(A_75)
      | ~ v5_orders_2(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_116,plain,(
    ! [D_77] :
      ( r1_orders_2('#skF_2',k1_yellow_0('#skF_2','#skF_5'),D_77)
      | ~ r2_lattice3('#skF_2','#skF_5',D_77)
      | ~ m1_subset_1(D_77,u1_struct_0('#skF_2'))
      | ~ r1_yellow_0('#skF_2','#skF_5')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_114])).

tff(c_118,plain,(
    ! [D_77] :
      ( r1_orders_2('#skF_2','#skF_3',D_77)
      | ~ r2_lattice3('#skF_2','#skF_5',D_77)
      | ~ m1_subset_1(D_77,u1_struct_0('#skF_2'))
      | ~ r1_yellow_0('#skF_2','#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_22,c_56,c_116])).

tff(c_119,plain,(
    ~ r1_yellow_0('#skF_2','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_122,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v3_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_119])).

tff(c_125,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_122])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_125])).

tff(c_130,plain,(
    ! [D_78] :
      ( r1_orders_2('#skF_2','#skF_3',D_78)
      | ~ r2_lattice3('#skF_2','#skF_5',D_78)
      | ~ m1_subset_1(D_78,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_141,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_6')
    | ~ r2_lattice3('#skF_2','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_92,c_130])).

tff(c_153,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_141])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_153])).

tff(c_156,plain,(
    r2_lattice3('#skF_2','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_18,plain,(
    ! [A_4,C_22,B_16] :
      ( r2_lattice3(A_4,C_22,'#skF_1'(A_4,B_16,C_22))
      | k1_yellow_0(A_4,C_22) = B_16
      | ~ r2_lattice3(A_4,C_22,B_16)
      | ~ m1_subset_1(B_16,u1_struct_0(A_4))
      | ~ l1_orders_2(A_4)
      | ~ v5_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_196,plain,(
    ! [A_97,B_98,C_99] :
      ( m1_subset_1('#skF_1'(A_97,B_98,C_99),u1_struct_0(A_97))
      | k1_yellow_0(A_97,C_99) = B_98
      | ~ r2_lattice3(A_97,C_99,B_98)
      | ~ m1_subset_1(B_98,u1_struct_0(A_97))
      | ~ l1_orders_2(A_97)
      | ~ v5_orders_2(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_157,plain,(
    ~ r2_lattice3('#skF_2','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_40,plain,(
    ! [D_43] :
      ( r1_orders_2('#skF_2','#skF_3',D_43)
      | ~ r2_lattice3('#skF_2','#skF_4',D_43)
      | ~ m1_subset_1(D_43,u1_struct_0('#skF_2'))
      | r2_lattice3('#skF_2','#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_2','#skF_5','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_167,plain,(
    ! [D_43] :
      ( r1_orders_2('#skF_2','#skF_3',D_43)
      | ~ r2_lattice3('#skF_2','#skF_4',D_43)
      | ~ m1_subset_1(D_43,u1_struct_0('#skF_2'))
      | r2_lattice3('#skF_2','#skF_5','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_40])).

tff(c_168,plain,(
    ! [D_43] :
      ( r1_orders_2('#skF_2','#skF_3',D_43)
      | ~ r2_lattice3('#skF_2','#skF_4',D_43)
      | ~ m1_subset_1(D_43,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_167])).

tff(c_200,plain,(
    ! [B_98,C_99] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_98,C_99))
      | ~ r2_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2',B_98,C_99))
      | k1_yellow_0('#skF_2',C_99) = B_98
      | ~ r2_lattice3('#skF_2',C_99,B_98)
      | ~ m1_subset_1(B_98,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_196,c_168])).

tff(c_278,plain,(
    ! [B_108,C_109] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_108,C_109))
      | ~ r2_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2',B_108,C_109))
      | k1_yellow_0('#skF_2',C_109) = B_108
      | ~ r2_lattice3('#skF_2',C_109,B_108)
      | ~ m1_subset_1(B_108,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_200])).

tff(c_282,plain,(
    ! [B_16] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_16,'#skF_4'))
      | k1_yellow_0('#skF_2','#skF_4') = B_16
      | ~ r2_lattice3('#skF_2','#skF_4',B_16)
      | ~ m1_subset_1(B_16,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_278])).

tff(c_293,plain,(
    ! [B_110] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_110,'#skF_4'))
      | k1_yellow_0('#skF_2','#skF_4') = B_110
      | ~ r2_lattice3('#skF_2','#skF_4',B_110)
      | ~ m1_subset_1(B_110,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_282])).

tff(c_16,plain,(
    ! [A_4,B_16,C_22] :
      ( ~ r1_orders_2(A_4,B_16,'#skF_1'(A_4,B_16,C_22))
      | k1_yellow_0(A_4,C_22) = B_16
      | ~ r2_lattice3(A_4,C_22,B_16)
      | ~ m1_subset_1(B_16,u1_struct_0(A_4))
      | ~ l1_orders_2(A_4)
      | ~ v5_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_297,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | k1_yellow_0('#skF_2','#skF_4') = '#skF_3'
    | ~ r2_lattice3('#skF_2','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_293,c_16])).

tff(c_304,plain,(
    k1_yellow_0('#skF_2','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_156,c_28,c_24,c_297])).

tff(c_306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_304])).

tff(c_307,plain,(
    r2_lattice3('#skF_2','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_359,plain,(
    ! [A_131,B_132,C_133] :
      ( m1_subset_1('#skF_1'(A_131,B_132,C_133),u1_struct_0(A_131))
      | k1_yellow_0(A_131,C_133) = B_132
      | ~ r2_lattice3(A_131,C_133,B_132)
      | ~ m1_subset_1(B_132,u1_struct_0(A_131))
      | ~ l1_orders_2(A_131)
      | ~ v5_orders_2(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_308,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_46,plain,(
    ! [D_43] :
      ( r1_orders_2('#skF_2','#skF_3',D_43)
      | ~ r2_lattice3('#skF_2','#skF_4',D_43)
      | ~ m1_subset_1(D_43,u1_struct_0('#skF_2'))
      | m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
      | ~ r2_lattice3('#skF_2','#skF_5','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_320,plain,(
    ! [D_43] :
      ( r1_orders_2('#skF_2','#skF_3',D_43)
      | ~ r2_lattice3('#skF_2','#skF_4',D_43)
      | ~ m1_subset_1(D_43,u1_struct_0('#skF_2'))
      | m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_46])).

tff(c_321,plain,(
    ! [D_43] :
      ( r1_orders_2('#skF_2','#skF_3',D_43)
      | ~ r2_lattice3('#skF_2','#skF_4',D_43)
      | ~ m1_subset_1(D_43,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_308,c_320])).

tff(c_363,plain,(
    ! [B_132,C_133] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_132,C_133))
      | ~ r2_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2',B_132,C_133))
      | k1_yellow_0('#skF_2',C_133) = B_132
      | ~ r2_lattice3('#skF_2',C_133,B_132)
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_359,c_321])).

tff(c_419,plain,(
    ! [B_140,C_141] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_140,C_141))
      | ~ r2_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2',B_140,C_141))
      | k1_yellow_0('#skF_2',C_141) = B_140
      | ~ r2_lattice3('#skF_2',C_141,B_140)
      | ~ m1_subset_1(B_140,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_363])).

tff(c_423,plain,(
    ! [B_16] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_16,'#skF_4'))
      | k1_yellow_0('#skF_2','#skF_4') = B_16
      | ~ r2_lattice3('#skF_2','#skF_4',B_16)
      | ~ m1_subset_1(B_16,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_419])).

tff(c_434,plain,(
    ! [B_142] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_142,'#skF_4'))
      | k1_yellow_0('#skF_2','#skF_4') = B_142
      | ~ r2_lattice3('#skF_2','#skF_4',B_142)
      | ~ m1_subset_1(B_142,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_423])).

tff(c_438,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | k1_yellow_0('#skF_2','#skF_4') = '#skF_3'
    | ~ r2_lattice3('#skF_2','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_434,c_16])).

tff(c_445,plain,(
    k1_yellow_0('#skF_2','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_307,c_28,c_24,c_438])).

tff(c_447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_445])).

tff(c_448,plain,(
    r2_lattice3('#skF_2','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_500,plain,(
    ! [A_161,B_162,C_163] :
      ( m1_subset_1('#skF_1'(A_161,B_162,C_163),u1_struct_0(A_161))
      | k1_yellow_0(A_161,C_163) = B_162
      | ~ r2_lattice3(A_161,C_163,B_162)
      | ~ m1_subset_1(B_162,u1_struct_0(A_161))
      | ~ l1_orders_2(A_161)
      | ~ v5_orders_2(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_449,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_34,plain,(
    ! [D_43] :
      ( r1_orders_2('#skF_2','#skF_3',D_43)
      | ~ r2_lattice3('#skF_2','#skF_4',D_43)
      | ~ m1_subset_1(D_43,u1_struct_0('#skF_2'))
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_6')
      | ~ r2_lattice3('#skF_2','#skF_5','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_469,plain,(
    ! [D_43] :
      ( r1_orders_2('#skF_2','#skF_3',D_43)
      | ~ r2_lattice3('#skF_2','#skF_4',D_43)
      | ~ m1_subset_1(D_43,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_449,c_34])).

tff(c_504,plain,(
    ! [B_162,C_163] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_162,C_163))
      | ~ r2_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2',B_162,C_163))
      | k1_yellow_0('#skF_2',C_163) = B_162
      | ~ r2_lattice3('#skF_2',C_163,B_162)
      | ~ m1_subset_1(B_162,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_500,c_469])).

tff(c_517,plain,(
    ! [B_170,C_171] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_170,C_171))
      | ~ r2_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2',B_170,C_171))
      | k1_yellow_0('#skF_2',C_171) = B_170
      | ~ r2_lattice3('#skF_2',C_171,B_170)
      | ~ m1_subset_1(B_170,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_504])).

tff(c_521,plain,(
    ! [B_16] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_16,'#skF_4'))
      | k1_yellow_0('#skF_2','#skF_4') = B_16
      | ~ r2_lattice3('#skF_2','#skF_4',B_16)
      | ~ m1_subset_1(B_16,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_517])).

tff(c_532,plain,(
    ! [B_172] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_172,'#skF_4'))
      | k1_yellow_0('#skF_2','#skF_4') = B_172
      | ~ r2_lattice3('#skF_2','#skF_4',B_172)
      | ~ m1_subset_1(B_172,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_521])).

tff(c_536,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | k1_yellow_0('#skF_2','#skF_4') = '#skF_3'
    | ~ r2_lattice3('#skF_2','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_532,c_16])).

tff(c_543,plain,(
    k1_yellow_0('#skF_2','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_448,c_28,c_24,c_536])).

tff(c_545,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_543])).

tff(c_546,plain,(
    r2_lattice3('#skF_2','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_581,plain,(
    ! [A_191,B_192,C_193] :
      ( m1_subset_1('#skF_1'(A_191,B_192,C_193),u1_struct_0(A_191))
      | k1_yellow_0(A_191,C_193) = B_192
      | ~ r2_lattice3(A_191,C_193,B_192)
      | ~ m1_subset_1(B_192,u1_struct_0(A_191))
      | ~ l1_orders_2(A_191)
      | ~ v5_orders_2(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_547,plain,(
    k1_yellow_0('#skF_2','#skF_5') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [D_43] :
      ( r1_orders_2('#skF_2','#skF_3',D_43)
      | ~ r2_lattice3('#skF_2','#skF_4',D_43)
      | ~ m1_subset_1(D_43,u1_struct_0('#skF_2'))
      | k1_yellow_0('#skF_2','#skF_5') = '#skF_3' ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_553,plain,(
    ! [D_43] :
      ( r1_orders_2('#skF_2','#skF_3',D_43)
      | ~ r2_lattice3('#skF_2','#skF_4',D_43)
      | ~ m1_subset_1(D_43,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_547,c_52])).

tff(c_585,plain,(
    ! [B_192,C_193] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_192,C_193))
      | ~ r2_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2',B_192,C_193))
      | k1_yellow_0('#skF_2',C_193) = B_192
      | ~ r2_lattice3('#skF_2',C_193,B_192)
      | ~ m1_subset_1(B_192,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_581,c_553])).

tff(c_599,plain,(
    ! [B_203,C_204] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_203,C_204))
      | ~ r2_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2',B_203,C_204))
      | k1_yellow_0('#skF_2',C_204) = B_203
      | ~ r2_lattice3('#skF_2',C_204,B_203)
      | ~ m1_subset_1(B_203,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_585])).

tff(c_603,plain,(
    ! [B_16] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_16,'#skF_4'))
      | k1_yellow_0('#skF_2','#skF_4') = B_16
      | ~ r2_lattice3('#skF_2','#skF_4',B_16)
      | ~ m1_subset_1(B_16,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_599])).

tff(c_614,plain,(
    ! [B_205] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_205,'#skF_4'))
      | k1_yellow_0('#skF_2','#skF_4') = B_205
      | ~ r2_lattice3('#skF_2','#skF_4',B_205)
      | ~ m1_subset_1(B_205,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_603])).

tff(c_618,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | k1_yellow_0('#skF_2','#skF_4') = '#skF_3'
    | ~ r2_lattice3('#skF_2','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_614,c_16])).

tff(c_625,plain,(
    k1_yellow_0('#skF_2','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_546,c_28,c_24,c_618])).

tff(c_627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_625])).

tff(c_628,plain,(
    k1_yellow_0('#skF_2','#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_649,plain,(
    ! [A_210,C_211] :
      ( r2_lattice3(A_210,C_211,k1_yellow_0(A_210,C_211))
      | ~ r1_yellow_0(A_210,C_211)
      | ~ m1_subset_1(k1_yellow_0(A_210,C_211),u1_struct_0(A_210))
      | ~ l1_orders_2(A_210)
      | ~ v5_orders_2(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_653,plain,
    ( r2_lattice3('#skF_2','#skF_5',k1_yellow_0('#skF_2','#skF_5'))
    | ~ r1_yellow_0('#skF_2','#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_649])).

tff(c_657,plain,
    ( r2_lattice3('#skF_2','#skF_5','#skF_3')
    | ~ r1_yellow_0('#skF_2','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_22,c_628,c_653])).

tff(c_658,plain,(
    ~ r1_yellow_0('#skF_2','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_641,c_657])).

tff(c_661,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v3_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_658])).

tff(c_664,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_661])).

tff(c_666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_664])).

tff(c_668,plain,(
    r2_lattice3('#skF_2','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_629,plain,(
    k1_yellow_0('#skF_2','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_32,plain,
    ( k1_yellow_0('#skF_2','#skF_4') != '#skF_3'
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_6')
    | ~ r2_lattice3('#skF_2','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_679,plain,(
    ~ r1_orders_2('#skF_2','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_629,c_32])).

tff(c_38,plain,
    ( k1_yellow_0('#skF_2','#skF_4') != '#skF_3'
    | r2_lattice3('#skF_2','#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_2','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_675,plain,(
    r2_lattice3('#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_629,c_38])).

tff(c_44,plain,
    ( k1_yellow_0('#skF_2','#skF_4') != '#skF_3'
    | m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | ~ r2_lattice3('#skF_2','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_671,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_629,c_44])).

tff(c_702,plain,(
    ! [A_232,C_233,D_234] :
      ( r1_orders_2(A_232,k1_yellow_0(A_232,C_233),D_234)
      | ~ r2_lattice3(A_232,C_233,D_234)
      | ~ m1_subset_1(D_234,u1_struct_0(A_232))
      | ~ r1_yellow_0(A_232,C_233)
      | ~ m1_subset_1(k1_yellow_0(A_232,C_233),u1_struct_0(A_232))
      | ~ l1_orders_2(A_232)
      | ~ v5_orders_2(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_706,plain,(
    ! [D_234] :
      ( r1_orders_2('#skF_2',k1_yellow_0('#skF_2','#skF_5'),D_234)
      | ~ r2_lattice3('#skF_2','#skF_5',D_234)
      | ~ m1_subset_1(D_234,u1_struct_0('#skF_2'))
      | ~ r1_yellow_0('#skF_2','#skF_5')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_702])).

tff(c_710,plain,(
    ! [D_234] :
      ( r1_orders_2('#skF_2','#skF_3',D_234)
      | ~ r2_lattice3('#skF_2','#skF_5',D_234)
      | ~ m1_subset_1(D_234,u1_struct_0('#skF_2'))
      | ~ r1_yellow_0('#skF_2','#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_22,c_628,c_706])).

tff(c_749,plain,(
    ~ r1_yellow_0('#skF_2','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_710])).

tff(c_752,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v3_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_749])).

tff(c_755,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_752])).

tff(c_757,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_755])).

tff(c_760,plain,(
    ! [D_236] :
      ( r1_orders_2('#skF_2','#skF_3',D_236)
      | ~ r2_lattice3('#skF_2','#skF_5',D_236)
      | ~ m1_subset_1(D_236,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_710])).

tff(c_771,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_6')
    | ~ r2_lattice3('#skF_2','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_671,c_760])).

tff(c_783,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_771])).

tff(c_785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_679,c_783])).

%------------------------------------------------------------------------------
