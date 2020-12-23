%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1555+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 2.78s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 432 expanded)
%              Number of leaves         :   23 ( 161 expanded)
%              Depth                    :   12
%              Number of atoms          :  384 (2128 expanded)
%              Number of equality atoms :   45 ( 249 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r1_lattice3 > r2_yellow_0 > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v3_lattice3 > v2_struct_0 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(v3_lattice3,type,(
    v3_lattice3: $i > $o )).

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

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

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
                ( B = k2_yellow_0(A,C)
              <=> ( r1_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_lattice3(A,C,D)
                       => r1_orders_2(A,D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_yellow_0)).

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

tff(c_4,plain,(
    ! [A_1,B_3] :
      ( r2_yellow_0(A_1,B_3)
      | ~ l1_orders_2(A_1)
      | ~ v3_lattice3(A_1)
      | ~ v5_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36,plain,
    ( r1_lattice3('#skF_2','#skF_4','#skF_3')
    | ~ r1_orders_2('#skF_2','#skF_6','#skF_3')
    | ~ r1_lattice3('#skF_2','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_709,plain,(
    ~ r1_lattice3('#skF_2','#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_50,plain,
    ( k2_yellow_0('#skF_2','#skF_4') != '#skF_3'
    | k2_yellow_0('#skF_2','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_55,plain,(
    k2_yellow_0('#skF_2','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_61,plain,(
    ~ r1_lattice3('#skF_2','#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_54,plain,
    ( r1_lattice3('#skF_2','#skF_4','#skF_3')
    | k2_yellow_0('#skF_2','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_56,plain,(
    k2_yellow_0('#skF_2','#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_65,plain,(
    ! [A_49,C_50] :
      ( r1_lattice3(A_49,C_50,k2_yellow_0(A_49,C_50))
      | ~ r2_yellow_0(A_49,C_50)
      | ~ m1_subset_1(k2_yellow_0(A_49,C_50),u1_struct_0(A_49))
      | ~ l1_orders_2(A_49)
      | ~ v5_orders_2(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_67,plain,
    ( r1_lattice3('#skF_2','#skF_5',k2_yellow_0('#skF_2','#skF_5'))
    | ~ r2_yellow_0('#skF_2','#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_65])).

tff(c_69,plain,
    ( r1_lattice3('#skF_2','#skF_5','#skF_3')
    | ~ r2_yellow_0('#skF_2','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_22,c_56,c_67])).

tff(c_70,plain,(
    ~ r2_yellow_0('#skF_2','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_69])).

tff(c_73,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v3_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_70])).

tff(c_76,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_73])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_76])).

tff(c_79,plain,
    ( ~ r1_orders_2('#skF_2','#skF_6','#skF_3')
    | r1_lattice3('#skF_2','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_81,plain,(
    ~ r1_orders_2('#skF_2','#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_80,plain,(
    r1_lattice3('#skF_2','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_42,plain,
    ( r1_lattice3('#skF_2','#skF_4','#skF_3')
    | r1_lattice3('#skF_2','#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_2','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_94,plain,
    ( r1_lattice3('#skF_2','#skF_4','#skF_3')
    | r1_lattice3('#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_42])).

tff(c_95,plain,(
    r1_lattice3('#skF_2','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_48,plain,
    ( r1_lattice3('#skF_2','#skF_4','#skF_3')
    | m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | ~ r1_lattice3('#skF_2','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_91,plain,
    ( r1_lattice3('#skF_2','#skF_4','#skF_3')
    | m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_48])).

tff(c_92,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_114,plain,(
    ! [A_75,D_76,C_77] :
      ( r1_orders_2(A_75,D_76,k2_yellow_0(A_75,C_77))
      | ~ r1_lattice3(A_75,C_77,D_76)
      | ~ m1_subset_1(D_76,u1_struct_0(A_75))
      | ~ r2_yellow_0(A_75,C_77)
      | ~ m1_subset_1(k2_yellow_0(A_75,C_77),u1_struct_0(A_75))
      | ~ l1_orders_2(A_75)
      | ~ v5_orders_2(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_116,plain,(
    ! [D_76] :
      ( r1_orders_2('#skF_2',D_76,k2_yellow_0('#skF_2','#skF_5'))
      | ~ r1_lattice3('#skF_2','#skF_5',D_76)
      | ~ m1_subset_1(D_76,u1_struct_0('#skF_2'))
      | ~ r2_yellow_0('#skF_2','#skF_5')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_114])).

tff(c_118,plain,(
    ! [D_76] :
      ( r1_orders_2('#skF_2',D_76,'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_5',D_76)
      | ~ m1_subset_1(D_76,u1_struct_0('#skF_2'))
      | ~ r2_yellow_0('#skF_2','#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_22,c_56,c_116])).

tff(c_119,plain,(
    ~ r2_yellow_0('#skF_2','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_122,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v3_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_119])).

tff(c_125,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_122])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_125])).

tff(c_130,plain,(
    ! [D_78] :
      ( r1_orders_2('#skF_2',D_78,'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_5',D_78)
      | ~ m1_subset_1(D_78,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_141,plain,
    ( r1_orders_2('#skF_2','#skF_6','#skF_3')
    | ~ r1_lattice3('#skF_2','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_92,c_130])).

tff(c_153,plain,(
    r1_orders_2('#skF_2','#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_141])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_153])).

tff(c_156,plain,(
    r1_lattice3('#skF_2','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_18,plain,(
    ! [A_4,C_22,B_16] :
      ( r1_lattice3(A_4,C_22,'#skF_1'(A_4,B_16,C_22))
      | k2_yellow_0(A_4,C_22) = B_16
      | ~ r1_lattice3(A_4,C_22,B_16)
      | ~ m1_subset_1(B_16,u1_struct_0(A_4))
      | ~ l1_orders_2(A_4)
      | ~ v5_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_196,plain,(
    ! [A_97,B_98,C_99] :
      ( m1_subset_1('#skF_1'(A_97,B_98,C_99),u1_struct_0(A_97))
      | k2_yellow_0(A_97,C_99) = B_98
      | ~ r1_lattice3(A_97,C_99,B_98)
      | ~ m1_subset_1(B_98,u1_struct_0(A_97))
      | ~ l1_orders_2(A_97)
      | ~ v5_orders_2(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_157,plain,(
    ~ r1_lattice3('#skF_2','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_40,plain,(
    ! [D_43] :
      ( r1_orders_2('#skF_2',D_43,'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_4',D_43)
      | ~ m1_subset_1(D_43,u1_struct_0('#skF_2'))
      | r1_lattice3('#skF_2','#skF_5','#skF_6')
      | ~ r1_lattice3('#skF_2','#skF_5','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_167,plain,(
    ! [D_43] :
      ( r1_orders_2('#skF_2',D_43,'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_4',D_43)
      | ~ m1_subset_1(D_43,u1_struct_0('#skF_2'))
      | r1_lattice3('#skF_2','#skF_5','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_40])).

tff(c_168,plain,(
    ! [D_43] :
      ( r1_orders_2('#skF_2',D_43,'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_4',D_43)
      | ~ m1_subset_1(D_43,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_167])).

tff(c_200,plain,(
    ! [B_98,C_99] :
      ( r1_orders_2('#skF_2','#skF_1'('#skF_2',B_98,C_99),'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2',B_98,C_99))
      | k2_yellow_0('#skF_2',C_99) = B_98
      | ~ r1_lattice3('#skF_2',C_99,B_98)
      | ~ m1_subset_1(B_98,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_196,c_168])).

tff(c_278,plain,(
    ! [B_107,C_108] :
      ( r1_orders_2('#skF_2','#skF_1'('#skF_2',B_107,C_108),'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2',B_107,C_108))
      | k2_yellow_0('#skF_2',C_108) = B_107
      | ~ r1_lattice3('#skF_2',C_108,B_107)
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_200])).

tff(c_16,plain,(
    ! [A_4,B_16,C_22] :
      ( ~ r1_orders_2(A_4,'#skF_1'(A_4,B_16,C_22),B_16)
      | k2_yellow_0(A_4,C_22) = B_16
      | ~ r1_lattice3(A_4,C_22,B_16)
      | ~ m1_subset_1(B_16,u1_struct_0(A_4))
      | ~ l1_orders_2(A_4)
      | ~ v5_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_282,plain,(
    ! [C_108] :
      ( ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ r1_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_3',C_108))
      | k2_yellow_0('#skF_2',C_108) = '#skF_3'
      | ~ r1_lattice3('#skF_2',C_108,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_278,c_16])).

tff(c_293,plain,(
    ! [C_109] :
      ( ~ r1_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_3',C_109))
      | k2_yellow_0('#skF_2',C_109) = '#skF_3'
      | ~ r1_lattice3('#skF_2',C_109,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_28,c_24,c_282])).

tff(c_297,plain,
    ( k2_yellow_0('#skF_2','#skF_4') = '#skF_3'
    | ~ r1_lattice3('#skF_2','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_293])).

tff(c_304,plain,(
    k2_yellow_0('#skF_2','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_22,c_156,c_297])).

tff(c_306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_304])).

tff(c_307,plain,(
    r1_lattice3('#skF_2','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_374,plain,(
    ! [A_131,B_132,C_133] :
      ( m1_subset_1('#skF_1'(A_131,B_132,C_133),u1_struct_0(A_131))
      | k2_yellow_0(A_131,C_133) = B_132
      | ~ r1_lattice3(A_131,C_133,B_132)
      | ~ m1_subset_1(B_132,u1_struct_0(A_131))
      | ~ l1_orders_2(A_131)
      | ~ v5_orders_2(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_308,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_46,plain,(
    ! [D_43] :
      ( r1_orders_2('#skF_2',D_43,'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_4',D_43)
      | ~ m1_subset_1(D_43,u1_struct_0('#skF_2'))
      | m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
      | ~ r1_lattice3('#skF_2','#skF_5','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_320,plain,(
    ! [D_43] :
      ( r1_orders_2('#skF_2',D_43,'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_4',D_43)
      | ~ m1_subset_1(D_43,u1_struct_0('#skF_2'))
      | m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_46])).

tff(c_321,plain,(
    ! [D_43] :
      ( r1_orders_2('#skF_2',D_43,'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_4',D_43)
      | ~ m1_subset_1(D_43,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_308,c_320])).

tff(c_378,plain,(
    ! [B_132,C_133] :
      ( r1_orders_2('#skF_2','#skF_1'('#skF_2',B_132,C_133),'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2',B_132,C_133))
      | k2_yellow_0('#skF_2',C_133) = B_132
      | ~ r1_lattice3('#skF_2',C_133,B_132)
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_374,c_321])).

tff(c_449,plain,(
    ! [B_141,C_142] :
      ( r1_orders_2('#skF_2','#skF_1'('#skF_2',B_141,C_142),'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2',B_141,C_142))
      | k2_yellow_0('#skF_2',C_142) = B_141
      | ~ r1_lattice3('#skF_2',C_142,B_141)
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_378])).

tff(c_453,plain,(
    ! [C_142] :
      ( ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ r1_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_3',C_142))
      | k2_yellow_0('#skF_2',C_142) = '#skF_3'
      | ~ r1_lattice3('#skF_2',C_142,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_449,c_16])).

tff(c_464,plain,(
    ! [C_143] :
      ( ~ r1_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_3',C_143))
      | k2_yellow_0('#skF_2',C_143) = '#skF_3'
      | ~ r1_lattice3('#skF_2',C_143,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_28,c_24,c_453])).

tff(c_468,plain,
    ( k2_yellow_0('#skF_2','#skF_4') = '#skF_3'
    | ~ r1_lattice3('#skF_2','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_464])).

tff(c_475,plain,(
    k2_yellow_0('#skF_2','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_22,c_307,c_468])).

tff(c_477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_475])).

tff(c_478,plain,(
    r1_lattice3('#skF_2','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_529,plain,(
    ! [A_163,B_164,C_165] :
      ( m1_subset_1('#skF_1'(A_163,B_164,C_165),u1_struct_0(A_163))
      | k2_yellow_0(A_163,C_165) = B_164
      | ~ r1_lattice3(A_163,C_165,B_164)
      | ~ m1_subset_1(B_164,u1_struct_0(A_163))
      | ~ l1_orders_2(A_163)
      | ~ v5_orders_2(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_479,plain,(
    r1_orders_2('#skF_2','#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_34,plain,(
    ! [D_43] :
      ( r1_orders_2('#skF_2',D_43,'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_4',D_43)
      | ~ m1_subset_1(D_43,u1_struct_0('#skF_2'))
      | ~ r1_orders_2('#skF_2','#skF_6','#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_5','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_505,plain,(
    ! [D_43] :
      ( r1_orders_2('#skF_2',D_43,'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_4',D_43)
      | ~ m1_subset_1(D_43,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_479,c_34])).

tff(c_533,plain,(
    ! [B_164,C_165] :
      ( r1_orders_2('#skF_2','#skF_1'('#skF_2',B_164,C_165),'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2',B_164,C_165))
      | k2_yellow_0('#skF_2',C_165) = B_164
      | ~ r1_lattice3('#skF_2',C_165,B_164)
      | ~ m1_subset_1(B_164,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_529,c_505])).

tff(c_553,plain,(
    ! [B_171,C_172] :
      ( r1_orders_2('#skF_2','#skF_1'('#skF_2',B_171,C_172),'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2',B_171,C_172))
      | k2_yellow_0('#skF_2',C_172) = B_171
      | ~ r1_lattice3('#skF_2',C_172,B_171)
      | ~ m1_subset_1(B_171,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_533])).

tff(c_557,plain,(
    ! [C_172] :
      ( ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ r1_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_3',C_172))
      | k2_yellow_0('#skF_2',C_172) = '#skF_3'
      | ~ r1_lattice3('#skF_2',C_172,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_553,c_16])).

tff(c_585,plain,(
    ! [C_174] :
      ( ~ r1_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_3',C_174))
      | k2_yellow_0('#skF_2',C_174) = '#skF_3'
      | ~ r1_lattice3('#skF_2',C_174,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_28,c_24,c_557])).

tff(c_589,plain,
    ( k2_yellow_0('#skF_2','#skF_4') = '#skF_3'
    | ~ r1_lattice3('#skF_2','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_585])).

tff(c_596,plain,(
    k2_yellow_0('#skF_2','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_22,c_478,c_589])).

tff(c_598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_596])).

tff(c_599,plain,(
    r1_lattice3('#skF_2','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_625,plain,(
    ! [A_191,B_192,C_193] :
      ( m1_subset_1('#skF_1'(A_191,B_192,C_193),u1_struct_0(A_191))
      | k2_yellow_0(A_191,C_193) = B_192
      | ~ r1_lattice3(A_191,C_193,B_192)
      | ~ m1_subset_1(B_192,u1_struct_0(A_191))
      | ~ l1_orders_2(A_191)
      | ~ v5_orders_2(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_600,plain,(
    k2_yellow_0('#skF_2','#skF_5') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [D_43] :
      ( r1_orders_2('#skF_2',D_43,'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_4',D_43)
      | ~ m1_subset_1(D_43,u1_struct_0('#skF_2'))
      | k2_yellow_0('#skF_2','#skF_5') = '#skF_3' ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_606,plain,(
    ! [D_43] :
      ( r1_orders_2('#skF_2',D_43,'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_4',D_43)
      | ~ m1_subset_1(D_43,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_600,c_52])).

tff(c_629,plain,(
    ! [B_192,C_193] :
      ( r1_orders_2('#skF_2','#skF_1'('#skF_2',B_192,C_193),'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2',B_192,C_193))
      | k2_yellow_0('#skF_2',C_193) = B_192
      | ~ r1_lattice3('#skF_2',C_193,B_192)
      | ~ m1_subset_1(B_192,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_625,c_606])).

tff(c_666,plain,(
    ! [B_203,C_204] :
      ( r1_orders_2('#skF_2','#skF_1'('#skF_2',B_203,C_204),'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2',B_203,C_204))
      | k2_yellow_0('#skF_2',C_204) = B_203
      | ~ r1_lattice3('#skF_2',C_204,B_203)
      | ~ m1_subset_1(B_203,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_629])).

tff(c_670,plain,(
    ! [C_204] :
      ( ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ r1_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_3',C_204))
      | k2_yellow_0('#skF_2',C_204) = '#skF_3'
      | ~ r1_lattice3('#skF_2',C_204,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_666,c_16])).

tff(c_682,plain,(
    ! [C_205] :
      ( ~ r1_lattice3('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_3',C_205))
      | k2_yellow_0('#skF_2',C_205) = '#skF_3'
      | ~ r1_lattice3('#skF_2',C_205,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_28,c_24,c_670])).

tff(c_686,plain,
    ( k2_yellow_0('#skF_2','#skF_4') = '#skF_3'
    | ~ r1_lattice3('#skF_2','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_682])).

tff(c_693,plain,(
    k2_yellow_0('#skF_2','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_22,c_599,c_686])).

tff(c_695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_693])).

tff(c_696,plain,(
    k2_yellow_0('#skF_2','#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_717,plain,(
    ! [A_210,C_211] :
      ( r1_lattice3(A_210,C_211,k2_yellow_0(A_210,C_211))
      | ~ r2_yellow_0(A_210,C_211)
      | ~ m1_subset_1(k2_yellow_0(A_210,C_211),u1_struct_0(A_210))
      | ~ l1_orders_2(A_210)
      | ~ v5_orders_2(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_721,plain,
    ( r1_lattice3('#skF_2','#skF_5',k2_yellow_0('#skF_2','#skF_5'))
    | ~ r2_yellow_0('#skF_2','#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_696,c_717])).

tff(c_725,plain,
    ( r1_lattice3('#skF_2','#skF_5','#skF_3')
    | ~ r2_yellow_0('#skF_2','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_22,c_696,c_721])).

tff(c_726,plain,(
    ~ r2_yellow_0('#skF_2','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_709,c_725])).

tff(c_729,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v3_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_726])).

tff(c_732,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_729])).

tff(c_734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_732])).

tff(c_736,plain,(
    r1_lattice3('#skF_2','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_735,plain,
    ( ~ r1_orders_2('#skF_2','#skF_6','#skF_3')
    | r1_lattice3('#skF_2','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_737,plain,(
    ~ r1_orders_2('#skF_2','#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_735])).

tff(c_697,plain,(
    k2_yellow_0('#skF_2','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_38,plain,
    ( k2_yellow_0('#skF_2','#skF_4') != '#skF_3'
    | r1_lattice3('#skF_2','#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_2','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_739,plain,(
    r1_lattice3('#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_697,c_38])).

tff(c_44,plain,
    ( k2_yellow_0('#skF_2','#skF_4') != '#skF_3'
    | m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | ~ r1_lattice3('#skF_2','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_741,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_697,c_44])).

tff(c_781,plain,(
    ! [A_232,D_233,C_234] :
      ( r1_orders_2(A_232,D_233,k2_yellow_0(A_232,C_234))
      | ~ r1_lattice3(A_232,C_234,D_233)
      | ~ m1_subset_1(D_233,u1_struct_0(A_232))
      | ~ r2_yellow_0(A_232,C_234)
      | ~ m1_subset_1(k2_yellow_0(A_232,C_234),u1_struct_0(A_232))
      | ~ l1_orders_2(A_232)
      | ~ v5_orders_2(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_785,plain,(
    ! [D_233] :
      ( r1_orders_2('#skF_2',D_233,k2_yellow_0('#skF_2','#skF_5'))
      | ~ r1_lattice3('#skF_2','#skF_5',D_233)
      | ~ m1_subset_1(D_233,u1_struct_0('#skF_2'))
      | ~ r2_yellow_0('#skF_2','#skF_5')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_696,c_781])).

tff(c_789,plain,(
    ! [D_233] :
      ( r1_orders_2('#skF_2',D_233,'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_5',D_233)
      | ~ m1_subset_1(D_233,u1_struct_0('#skF_2'))
      | ~ r2_yellow_0('#skF_2','#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_22,c_696,c_785])).

tff(c_817,plain,(
    ~ r2_yellow_0('#skF_2','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_789])).

tff(c_820,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v3_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_817])).

tff(c_823,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_820])).

tff(c_825,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_823])).

tff(c_828,plain,(
    ! [D_236] :
      ( r1_orders_2('#skF_2',D_236,'#skF_3')
      | ~ r1_lattice3('#skF_2','#skF_5',D_236)
      | ~ m1_subset_1(D_236,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_789])).

tff(c_839,plain,
    ( r1_orders_2('#skF_2','#skF_6','#skF_3')
    | ~ r1_lattice3('#skF_2','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_741,c_828])).

tff(c_851,plain,(
    r1_orders_2('#skF_2','#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_739,c_839])).

tff(c_853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_737,c_851])).

tff(c_855,plain,(
    r1_orders_2('#skF_2','#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_735])).

tff(c_32,plain,
    ( k2_yellow_0('#skF_2','#skF_4') != '#skF_3'
    | ~ r1_orders_2('#skF_2','#skF_6','#skF_3')
    | ~ r1_lattice3('#skF_2','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_865,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_855,c_697,c_32])).

%------------------------------------------------------------------------------
