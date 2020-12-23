%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:20 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 185 expanded)
%              Number of leaves         :   26 (  85 expanded)
%              Depth                    :   15
%              Number of atoms          :  234 ( 986 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r2_waybel_0 > m2_yellow_6 > m1_connsp_2 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m2_yellow_6,type,(
    m2_yellow_6: ( $i * $i * $i ) > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & l1_waybel_0(B,A) )
           => ! [C] :
                ( m2_yellow_6(C,A,B)
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r3_waybel_9(A,C,D)
                     => r3_waybel_9(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_9)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => ! [C] :
          ( m2_yellow_6(C,A,B)
         => ( ~ v2_struct_0(C)
            & v4_orders_2(C)
            & v7_waybel_0(C)
            & l1_waybel_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r3_waybel_9(A,B,C)
              <=> ! [D] :
                    ( m1_connsp_2(D,A,C)
                   => r2_waybel_0(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_waybel_9)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m2_yellow_6(C,A,B)
             => ! [D] :
                  ( r2_waybel_0(A,C,D)
                 => r2_waybel_0(A,B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_6)).

tff(c_20,plain,(
    ~ r3_waybel_9('#skF_2','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_22,plain,(
    r3_waybel_9('#skF_2','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_28,plain,(
    l1_waybel_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_38,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_30,plain,(
    v7_waybel_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_26,plain,(
    m2_yellow_6('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_42,plain,(
    ! [C_55,A_56,B_57] :
      ( v4_orders_2(C_55)
      | ~ m2_yellow_6(C_55,A_56,B_57)
      | ~ l1_waybel_0(B_57,A_56)
      | ~ v7_waybel_0(B_57)
      | ~ v4_orders_2(B_57)
      | v2_struct_0(B_57)
      | ~ l1_struct_0(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_45,plain,
    ( v4_orders_2('#skF_4')
    | ~ l1_waybel_0('#skF_3','#skF_2')
    | ~ v7_waybel_0('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_42])).

tff(c_48,plain,
    ( v4_orders_2('#skF_4')
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_45])).

tff(c_49,plain,
    ( v4_orders_2('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_34,c_48])).

tff(c_50,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_53,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_50])).

tff(c_57,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_53])).

tff(c_59,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_60,plain,(
    ! [C_58,A_59,B_60] :
      ( ~ v2_struct_0(C_58)
      | ~ m2_yellow_6(C_58,A_59,B_60)
      | ~ l1_waybel_0(B_60,A_59)
      | ~ v7_waybel_0(B_60)
      | ~ v4_orders_2(B_60)
      | v2_struct_0(B_60)
      | ~ l1_struct_0(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_63,plain,
    ( ~ v2_struct_0('#skF_4')
    | ~ l1_waybel_0('#skF_3','#skF_2')
    | ~ v7_waybel_0('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_60])).

tff(c_66,plain,
    ( ~ v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_63])).

tff(c_67,plain,
    ( ~ v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_34,c_66])).

tff(c_69,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_67])).

tff(c_78,plain,(
    ! [C_64,A_65,B_66] :
      ( l1_waybel_0(C_64,A_65)
      | ~ m2_yellow_6(C_64,A_65,B_66)
      | ~ l1_waybel_0(B_66,A_65)
      | ~ v7_waybel_0(B_66)
      | ~ v4_orders_2(B_66)
      | v2_struct_0(B_66)
      | ~ l1_struct_0(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_81,plain,
    ( l1_waybel_0('#skF_4','#skF_2')
    | ~ l1_waybel_0('#skF_3','#skF_2')
    | ~ v7_waybel_0('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_78])).

tff(c_84,plain,
    ( l1_waybel_0('#skF_4','#skF_2')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_32,c_30,c_28,c_81])).

tff(c_85,plain,(
    l1_waybel_0('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_34,c_84])).

tff(c_18,plain,(
    ! [A_21,B_33,C_39] :
      ( m1_connsp_2('#skF_1'(A_21,B_33,C_39),A_21,C_39)
      | r3_waybel_9(A_21,B_33,C_39)
      | ~ m1_subset_1(C_39,u1_struct_0(A_21))
      | ~ l1_waybel_0(B_33,A_21)
      | v2_struct_0(B_33)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_89,plain,(
    ! [A_77,B_78,D_79,C_80] :
      ( r2_waybel_0(A_77,B_78,D_79)
      | ~ m1_connsp_2(D_79,A_77,C_80)
      | ~ r3_waybel_9(A_77,B_78,C_80)
      | ~ m1_subset_1(C_80,u1_struct_0(A_77))
      | ~ l1_waybel_0(B_78,A_77)
      | v2_struct_0(B_78)
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_93,plain,(
    ! [A_81,B_82,B_83,C_84] :
      ( r2_waybel_0(A_81,B_82,'#skF_1'(A_81,B_83,C_84))
      | ~ r3_waybel_9(A_81,B_82,C_84)
      | ~ l1_waybel_0(B_82,A_81)
      | v2_struct_0(B_82)
      | r3_waybel_9(A_81,B_83,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_81))
      | ~ l1_waybel_0(B_83,A_81)
      | v2_struct_0(B_83)
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_18,c_89])).

tff(c_12,plain,(
    ! [A_6,B_14,D_20,C_18] :
      ( r2_waybel_0(A_6,B_14,D_20)
      | ~ r2_waybel_0(A_6,C_18,D_20)
      | ~ m2_yellow_6(C_18,A_6,B_14)
      | ~ l1_waybel_0(B_14,A_6)
      | ~ v7_waybel_0(B_14)
      | ~ v4_orders_2(B_14)
      | v2_struct_0(B_14)
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_102,plain,(
    ! [B_88,B_89,B_85,C_87,A_86] :
      ( r2_waybel_0(A_86,B_85,'#skF_1'(A_86,B_88,C_87))
      | ~ m2_yellow_6(B_89,A_86,B_85)
      | ~ l1_waybel_0(B_85,A_86)
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85)
      | ~ l1_struct_0(A_86)
      | ~ r3_waybel_9(A_86,B_89,C_87)
      | ~ l1_waybel_0(B_89,A_86)
      | v2_struct_0(B_89)
      | r3_waybel_9(A_86,B_88,C_87)
      | ~ m1_subset_1(C_87,u1_struct_0(A_86))
      | ~ l1_waybel_0(B_88,A_86)
      | v2_struct_0(B_88)
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(resolution,[status(thm)],[c_93,c_12])).

tff(c_104,plain,(
    ! [B_88,C_87] :
      ( r2_waybel_0('#skF_2','#skF_3','#skF_1'('#skF_2',B_88,C_87))
      | ~ l1_waybel_0('#skF_3','#skF_2')
      | ~ v7_waybel_0('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ r3_waybel_9('#skF_2','#skF_4',C_87)
      | ~ l1_waybel_0('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | r3_waybel_9('#skF_2',B_88,C_87)
      | ~ m1_subset_1(C_87,u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_88,'#skF_2')
      | v2_struct_0(B_88)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_102])).

tff(c_107,plain,(
    ! [B_88,C_87] :
      ( r2_waybel_0('#skF_2','#skF_3','#skF_1'('#skF_2',B_88,C_87))
      | v2_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_2','#skF_4',C_87)
      | v2_struct_0('#skF_4')
      | r3_waybel_9('#skF_2',B_88,C_87)
      | ~ m1_subset_1(C_87,u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_88,'#skF_2')
      | v2_struct_0(B_88)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_85,c_59,c_32,c_30,c_28,c_104])).

tff(c_109,plain,(
    ! [B_90,C_91] :
      ( r2_waybel_0('#skF_2','#skF_3','#skF_1'('#skF_2',B_90,C_91))
      | ~ r3_waybel_9('#skF_2','#skF_4',C_91)
      | r3_waybel_9('#skF_2',B_90,C_91)
      | ~ m1_subset_1(C_91,u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(B_90,'#skF_2')
      | v2_struct_0(B_90) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_69,c_34,c_107])).

tff(c_16,plain,(
    ! [A_21,B_33,C_39] :
      ( ~ r2_waybel_0(A_21,B_33,'#skF_1'(A_21,B_33,C_39))
      | r3_waybel_9(A_21,B_33,C_39)
      | ~ m1_subset_1(C_39,u1_struct_0(A_21))
      | ~ l1_waybel_0(B_33,A_21)
      | v2_struct_0(B_33)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_113,plain,(
    ! [C_91] :
      ( ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r3_waybel_9('#skF_2','#skF_4',C_91)
      | r3_waybel_9('#skF_2','#skF_3',C_91)
      | ~ m1_subset_1(C_91,u1_struct_0('#skF_2'))
      | ~ l1_waybel_0('#skF_3','#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_109,c_16])).

tff(c_118,plain,(
    ! [C_91] :
      ( v2_struct_0('#skF_2')
      | ~ r3_waybel_9('#skF_2','#skF_4',C_91)
      | r3_waybel_9('#skF_2','#skF_3',C_91)
      | ~ m1_subset_1(C_91,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38,c_36,c_113])).

tff(c_124,plain,(
    ! [C_92] :
      ( ~ r3_waybel_9('#skF_2','#skF_4',C_92)
      | r3_waybel_9('#skF_2','#skF_3',C_92)
      | ~ m1_subset_1(C_92,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_40,c_118])).

tff(c_127,plain,
    ( ~ r3_waybel_9('#skF_2','#skF_4','#skF_5')
    | r3_waybel_9('#skF_2','#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_124])).

tff(c_130,plain,(
    r3_waybel_9('#skF_2','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_127])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.21  
% 1.98/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.21  %$ r3_waybel_9 > r2_waybel_0 > m2_yellow_6 > m1_connsp_2 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 1.98/1.21  
% 1.98/1.21  %Foreground sorts:
% 1.98/1.21  
% 1.98/1.21  
% 1.98/1.21  %Background operators:
% 1.98/1.21  
% 1.98/1.21  
% 1.98/1.21  %Foreground operators:
% 1.98/1.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.98/1.21  tff(m2_yellow_6, type, m2_yellow_6: ($i * $i * $i) > $o).
% 1.98/1.21  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 1.98/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.98/1.21  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.98/1.21  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 1.98/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.98/1.21  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 1.98/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.21  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 1.98/1.21  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.21  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 1.98/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.21  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.98/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.98/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.21  
% 2.30/1.23  tff(f_129, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_waybel_9(A, C, D) => r3_waybel_9(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_waybel_9)).
% 2.30/1.23  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.30/1.23  tff(f_55, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 2.30/1.23  tff(f_101, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> (![D]: (m1_connsp_2(D, A, C) => r2_waybel_0(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_waybel_9)).
% 2.30/1.23  tff(f_78, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (![D]: (r2_waybel_0(A, C, D) => r2_waybel_0(A, B, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_6)).
% 2.30/1.23  tff(c_20, plain, (~r3_waybel_9('#skF_2', '#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.30/1.23  tff(c_22, plain, (r3_waybel_9('#skF_2', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.30/1.23  tff(c_24, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.30/1.23  tff(c_34, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.30/1.23  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.30/1.23  tff(c_28, plain, (l1_waybel_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.30/1.23  tff(c_38, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.30/1.23  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.30/1.23  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.23  tff(c_32, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.30/1.23  tff(c_30, plain, (v7_waybel_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.30/1.23  tff(c_26, plain, (m2_yellow_6('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.30/1.23  tff(c_42, plain, (![C_55, A_56, B_57]: (v4_orders_2(C_55) | ~m2_yellow_6(C_55, A_56, B_57) | ~l1_waybel_0(B_57, A_56) | ~v7_waybel_0(B_57) | ~v4_orders_2(B_57) | v2_struct_0(B_57) | ~l1_struct_0(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.30/1.23  tff(c_45, plain, (v4_orders_2('#skF_4') | ~l1_waybel_0('#skF_3', '#skF_2') | ~v7_waybel_0('#skF_3') | ~v4_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_42])).
% 2.30/1.23  tff(c_48, plain, (v4_orders_2('#skF_4') | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_45])).
% 2.30/1.23  tff(c_49, plain, (v4_orders_2('#skF_4') | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_34, c_48])).
% 2.30/1.23  tff(c_50, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_49])).
% 2.30/1.23  tff(c_53, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_50])).
% 2.30/1.23  tff(c_57, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_53])).
% 2.30/1.23  tff(c_59, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_49])).
% 2.30/1.23  tff(c_60, plain, (![C_58, A_59, B_60]: (~v2_struct_0(C_58) | ~m2_yellow_6(C_58, A_59, B_60) | ~l1_waybel_0(B_60, A_59) | ~v7_waybel_0(B_60) | ~v4_orders_2(B_60) | v2_struct_0(B_60) | ~l1_struct_0(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.30/1.23  tff(c_63, plain, (~v2_struct_0('#skF_4') | ~l1_waybel_0('#skF_3', '#skF_2') | ~v7_waybel_0('#skF_3') | ~v4_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_60])).
% 2.30/1.23  tff(c_66, plain, (~v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_63])).
% 2.30/1.23  tff(c_67, plain, (~v2_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_34, c_66])).
% 2.30/1.23  tff(c_69, plain, (~v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_67])).
% 2.30/1.23  tff(c_78, plain, (![C_64, A_65, B_66]: (l1_waybel_0(C_64, A_65) | ~m2_yellow_6(C_64, A_65, B_66) | ~l1_waybel_0(B_66, A_65) | ~v7_waybel_0(B_66) | ~v4_orders_2(B_66) | v2_struct_0(B_66) | ~l1_struct_0(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.30/1.23  tff(c_81, plain, (l1_waybel_0('#skF_4', '#skF_2') | ~l1_waybel_0('#skF_3', '#skF_2') | ~v7_waybel_0('#skF_3') | ~v4_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_78])).
% 2.30/1.23  tff(c_84, plain, (l1_waybel_0('#skF_4', '#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_32, c_30, c_28, c_81])).
% 2.30/1.23  tff(c_85, plain, (l1_waybel_0('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_34, c_84])).
% 2.30/1.23  tff(c_18, plain, (![A_21, B_33, C_39]: (m1_connsp_2('#skF_1'(A_21, B_33, C_39), A_21, C_39) | r3_waybel_9(A_21, B_33, C_39) | ~m1_subset_1(C_39, u1_struct_0(A_21)) | ~l1_waybel_0(B_33, A_21) | v2_struct_0(B_33) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.30/1.23  tff(c_89, plain, (![A_77, B_78, D_79, C_80]: (r2_waybel_0(A_77, B_78, D_79) | ~m1_connsp_2(D_79, A_77, C_80) | ~r3_waybel_9(A_77, B_78, C_80) | ~m1_subset_1(C_80, u1_struct_0(A_77)) | ~l1_waybel_0(B_78, A_77) | v2_struct_0(B_78) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.30/1.23  tff(c_93, plain, (![A_81, B_82, B_83, C_84]: (r2_waybel_0(A_81, B_82, '#skF_1'(A_81, B_83, C_84)) | ~r3_waybel_9(A_81, B_82, C_84) | ~l1_waybel_0(B_82, A_81) | v2_struct_0(B_82) | r3_waybel_9(A_81, B_83, C_84) | ~m1_subset_1(C_84, u1_struct_0(A_81)) | ~l1_waybel_0(B_83, A_81) | v2_struct_0(B_83) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(resolution, [status(thm)], [c_18, c_89])).
% 2.30/1.23  tff(c_12, plain, (![A_6, B_14, D_20, C_18]: (r2_waybel_0(A_6, B_14, D_20) | ~r2_waybel_0(A_6, C_18, D_20) | ~m2_yellow_6(C_18, A_6, B_14) | ~l1_waybel_0(B_14, A_6) | ~v7_waybel_0(B_14) | ~v4_orders_2(B_14) | v2_struct_0(B_14) | ~l1_struct_0(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.30/1.23  tff(c_102, plain, (![B_88, B_89, B_85, C_87, A_86]: (r2_waybel_0(A_86, B_85, '#skF_1'(A_86, B_88, C_87)) | ~m2_yellow_6(B_89, A_86, B_85) | ~l1_waybel_0(B_85, A_86) | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85) | ~l1_struct_0(A_86) | ~r3_waybel_9(A_86, B_89, C_87) | ~l1_waybel_0(B_89, A_86) | v2_struct_0(B_89) | r3_waybel_9(A_86, B_88, C_87) | ~m1_subset_1(C_87, u1_struct_0(A_86)) | ~l1_waybel_0(B_88, A_86) | v2_struct_0(B_88) | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86) | v2_struct_0(A_86))), inference(resolution, [status(thm)], [c_93, c_12])).
% 2.30/1.23  tff(c_104, plain, (![B_88, C_87]: (r2_waybel_0('#skF_2', '#skF_3', '#skF_1'('#skF_2', B_88, C_87)) | ~l1_waybel_0('#skF_3', '#skF_2') | ~v7_waybel_0('#skF_3') | ~v4_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_2') | ~r3_waybel_9('#skF_2', '#skF_4', C_87) | ~l1_waybel_0('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | r3_waybel_9('#skF_2', B_88, C_87) | ~m1_subset_1(C_87, u1_struct_0('#skF_2')) | ~l1_waybel_0(B_88, '#skF_2') | v2_struct_0(B_88) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_102])).
% 2.30/1.23  tff(c_107, plain, (![B_88, C_87]: (r2_waybel_0('#skF_2', '#skF_3', '#skF_1'('#skF_2', B_88, C_87)) | v2_struct_0('#skF_3') | ~r3_waybel_9('#skF_2', '#skF_4', C_87) | v2_struct_0('#skF_4') | r3_waybel_9('#skF_2', B_88, C_87) | ~m1_subset_1(C_87, u1_struct_0('#skF_2')) | ~l1_waybel_0(B_88, '#skF_2') | v2_struct_0(B_88) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_85, c_59, c_32, c_30, c_28, c_104])).
% 2.30/1.23  tff(c_109, plain, (![B_90, C_91]: (r2_waybel_0('#skF_2', '#skF_3', '#skF_1'('#skF_2', B_90, C_91)) | ~r3_waybel_9('#skF_2', '#skF_4', C_91) | r3_waybel_9('#skF_2', B_90, C_91) | ~m1_subset_1(C_91, u1_struct_0('#skF_2')) | ~l1_waybel_0(B_90, '#skF_2') | v2_struct_0(B_90))), inference(negUnitSimplification, [status(thm)], [c_40, c_69, c_34, c_107])).
% 2.30/1.23  tff(c_16, plain, (![A_21, B_33, C_39]: (~r2_waybel_0(A_21, B_33, '#skF_1'(A_21, B_33, C_39)) | r3_waybel_9(A_21, B_33, C_39) | ~m1_subset_1(C_39, u1_struct_0(A_21)) | ~l1_waybel_0(B_33, A_21) | v2_struct_0(B_33) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.30/1.23  tff(c_113, plain, (![C_91]: (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r3_waybel_9('#skF_2', '#skF_4', C_91) | r3_waybel_9('#skF_2', '#skF_3', C_91) | ~m1_subset_1(C_91, u1_struct_0('#skF_2')) | ~l1_waybel_0('#skF_3', '#skF_2') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_109, c_16])).
% 2.30/1.23  tff(c_118, plain, (![C_91]: (v2_struct_0('#skF_2') | ~r3_waybel_9('#skF_2', '#skF_4', C_91) | r3_waybel_9('#skF_2', '#skF_3', C_91) | ~m1_subset_1(C_91, u1_struct_0('#skF_2')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38, c_36, c_113])).
% 2.30/1.23  tff(c_124, plain, (![C_92]: (~r3_waybel_9('#skF_2', '#skF_4', C_92) | r3_waybel_9('#skF_2', '#skF_3', C_92) | ~m1_subset_1(C_92, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_34, c_40, c_118])).
% 2.30/1.23  tff(c_127, plain, (~r3_waybel_9('#skF_2', '#skF_4', '#skF_5') | r3_waybel_9('#skF_2', '#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_124])).
% 2.30/1.23  tff(c_130, plain, (r3_waybel_9('#skF_2', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_127])).
% 2.30/1.23  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_130])).
% 2.30/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.23  
% 2.30/1.23  Inference rules
% 2.30/1.23  ----------------------
% 2.30/1.23  #Ref     : 0
% 2.30/1.23  #Sup     : 12
% 2.30/1.23  #Fact    : 0
% 2.30/1.23  #Define  : 0
% 2.30/1.23  #Split   : 1
% 2.30/1.23  #Chain   : 0
% 2.30/1.23  #Close   : 0
% 2.30/1.23  
% 2.30/1.23  Ordering : KBO
% 2.30/1.23  
% 2.30/1.23  Simplification rules
% 2.30/1.23  ----------------------
% 2.30/1.23  #Subsume      : 0
% 2.30/1.23  #Demod        : 28
% 2.30/1.23  #Tautology    : 1
% 2.30/1.23  #SimpNegUnit  : 8
% 2.30/1.23  #BackRed      : 0
% 2.30/1.23  
% 2.30/1.23  #Partial instantiations: 0
% 2.30/1.23  #Strategies tried      : 1
% 2.30/1.23  
% 2.30/1.23  Timing (in seconds)
% 2.30/1.23  ----------------------
% 2.30/1.23  Preprocessing        : 0.29
% 2.30/1.23  Parsing              : 0.16
% 2.30/1.23  CNF conversion       : 0.02
% 2.30/1.23  Main loop            : 0.18
% 2.30/1.23  Inferencing          : 0.08
% 2.30/1.23  Reduction            : 0.05
% 2.30/1.23  Demodulation         : 0.03
% 2.30/1.23  BG Simplification    : 0.02
% 2.30/1.23  Subsumption          : 0.03
% 2.30/1.23  Abstraction          : 0.01
% 2.30/1.23  MUC search           : 0.00
% 2.30/1.23  Cooper               : 0.00
% 2.30/1.23  Total                : 0.50
% 2.30/1.23  Index Insertion      : 0.00
% 2.30/1.23  Index Deletion       : 0.00
% 2.30/1.23  Index Matching       : 0.00
% 2.30/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
