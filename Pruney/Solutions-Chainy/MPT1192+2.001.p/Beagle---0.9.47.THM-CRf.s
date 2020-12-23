%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:11 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 172 expanded)
%              Number of leaves         :   28 (  74 expanded)
%              Depth                    :   14
%              Number of atoms          :  197 ( 554 expanded)
%              Number of equality atoms :   47 (  85 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v9_lattices > v8_lattices > v6_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_lattices,type,(
    k4_lattices: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v6_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k1_lattices(A,B,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattices)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v9_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k2_lattices(A,B,k1_lattices(A,B,C)) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).

tff(f_85,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k1_lattices(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattices)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k4_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v8_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k1_lattices(A,k2_lattices(A,B,C),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

tff(c_28,plain,(
    k1_lattices('#skF_5','#skF_6','#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_30,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_32,plain,(
    l3_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_34,plain,(
    v9_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_58,plain,(
    ! [A_45,B_46,C_47] :
      ( k2_lattices(A_45,B_46,k1_lattices(A_45,B_46,C_47)) = B_46
      | ~ m1_subset_1(C_47,u1_struct_0(A_45))
      | ~ m1_subset_1(B_46,u1_struct_0(A_45))
      | ~ v9_lattices(A_45)
      | ~ l3_lattices(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_70,plain,(
    ! [B_46] :
      ( k2_lattices('#skF_5',B_46,k1_lattices('#skF_5',B_46,'#skF_6')) = B_46
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_58])).

tff(c_78,plain,(
    ! [B_46] :
      ( k2_lattices('#skF_5',B_46,k1_lattices('#skF_5',B_46,'#skF_6')) = B_46
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_70])).

tff(c_80,plain,(
    ! [B_48] :
      ( k2_lattices('#skF_5',B_48,k1_lattices('#skF_5',B_48,'#skF_6')) = B_48
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_78])).

tff(c_118,plain,(
    k2_lattices('#skF_5','#skF_6',k1_lattices('#skF_5','#skF_6','#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_30,c_80])).

tff(c_46,plain,(
    ! [A_35] :
      ( l2_lattices(A_35)
      | ~ l3_lattices(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_50,plain,(
    l2_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_46])).

tff(c_38,plain,(
    v6_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_41,plain,(
    ! [A_34] :
      ( l1_lattices(A_34)
      | ~ l3_lattices(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_45,plain,(
    l1_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_41])).

tff(c_20,plain,(
    ! [A_26,B_27,C_28] :
      ( m1_subset_1(k1_lattices(A_26,B_27,C_28),u1_struct_0(A_26))
      | ~ m1_subset_1(C_28,u1_struct_0(A_26))
      | ~ m1_subset_1(B_27,u1_struct_0(A_26))
      | ~ l2_lattices(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_208,plain,(
    ! [A_57,B_58,C_59] :
      ( k4_lattices(A_57,B_58,C_59) = k2_lattices(A_57,B_58,C_59)
      | ~ m1_subset_1(C_59,u1_struct_0(A_57))
      | ~ m1_subset_1(B_58,u1_struct_0(A_57))
      | ~ l1_lattices(A_57)
      | ~ v6_lattices(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1160,plain,(
    ! [A_125,B_126,B_127,C_128] :
      ( k4_lattices(A_125,B_126,k1_lattices(A_125,B_127,C_128)) = k2_lattices(A_125,B_126,k1_lattices(A_125,B_127,C_128))
      | ~ m1_subset_1(B_126,u1_struct_0(A_125))
      | ~ l1_lattices(A_125)
      | ~ v6_lattices(A_125)
      | ~ m1_subset_1(C_128,u1_struct_0(A_125))
      | ~ m1_subset_1(B_127,u1_struct_0(A_125))
      | ~ l2_lattices(A_125)
      | v2_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_20,c_208])).

tff(c_1172,plain,(
    ! [B_127,C_128] :
      ( k4_lattices('#skF_5','#skF_6',k1_lattices('#skF_5',B_127,C_128)) = k2_lattices('#skF_5','#skF_6',k1_lattices('#skF_5',B_127,C_128))
      | ~ l1_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | ~ m1_subset_1(C_128,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_127,u1_struct_0('#skF_5'))
      | ~ l2_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_1160])).

tff(c_1180,plain,(
    ! [B_127,C_128] :
      ( k4_lattices('#skF_5','#skF_6',k1_lattices('#skF_5',B_127,C_128)) = k2_lattices('#skF_5','#skF_6',k1_lattices('#skF_5',B_127,C_128))
      | ~ m1_subset_1(C_128,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_127,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_38,c_45,c_1172])).

tff(c_1182,plain,(
    ! [B_129,C_130] :
      ( k4_lattices('#skF_5','#skF_6',k1_lattices('#skF_5',B_129,C_130)) = k2_lattices('#skF_5','#skF_6',k1_lattices('#skF_5',B_129,C_130))
      | ~ m1_subset_1(C_130,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_129,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1180])).

tff(c_1221,plain,(
    ! [B_131] :
      ( k4_lattices('#skF_5','#skF_6',k1_lattices('#skF_5',B_131,'#skF_6')) = k2_lattices('#skF_5','#skF_6',k1_lattices('#skF_5',B_131,'#skF_6'))
      | ~ m1_subset_1(B_131,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_30,c_1182])).

tff(c_1244,plain,(
    k4_lattices('#skF_5','#skF_6',k1_lattices('#skF_5','#skF_6','#skF_6')) = k2_lattices('#skF_5','#skF_6',k1_lattices('#skF_5','#skF_6','#skF_6')) ),
    inference(resolution,[status(thm)],[c_30,c_1221])).

tff(c_1266,plain,(
    k4_lattices('#skF_5','#skF_6',k1_lattices('#skF_5','#skF_6','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_1244])).

tff(c_220,plain,(
    ! [B_58] :
      ( k4_lattices('#skF_5',B_58,'#skF_6') = k2_lattices('#skF_5',B_58,'#skF_6')
      | ~ m1_subset_1(B_58,u1_struct_0('#skF_5'))
      | ~ l1_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_208])).

tff(c_228,plain,(
    ! [B_58] :
      ( k4_lattices('#skF_5',B_58,'#skF_6') = k2_lattices('#skF_5',B_58,'#skF_6')
      | ~ m1_subset_1(B_58,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_45,c_220])).

tff(c_240,plain,(
    ! [B_60] :
      ( k4_lattices('#skF_5',B_60,'#skF_6') = k2_lattices('#skF_5',B_60,'#skF_6')
      | ~ m1_subset_1(B_60,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_228])).

tff(c_244,plain,(
    ! [B_27,C_28] :
      ( k4_lattices('#skF_5',k1_lattices('#skF_5',B_27,C_28),'#skF_6') = k2_lattices('#skF_5',k1_lattices('#skF_5',B_27,C_28),'#skF_6')
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_5'))
      | ~ l2_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_20,c_240])).

tff(c_266,plain,(
    ! [B_27,C_28] :
      ( k4_lattices('#skF_5',k1_lattices('#skF_5',B_27,C_28),'#skF_6') = k2_lattices('#skF_5',k1_lattices('#skF_5',B_27,C_28),'#skF_6')
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_244])).

tff(c_387,plain,(
    ! [B_67,C_68] :
      ( k4_lattices('#skF_5',k1_lattices('#skF_5',B_67,C_68),'#skF_6') = k2_lattices('#skF_5',k1_lattices('#skF_5',B_67,C_68),'#skF_6')
      | ~ m1_subset_1(C_68,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_67,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_266])).

tff(c_426,plain,(
    ! [B_69] :
      ( k4_lattices('#skF_5',k1_lattices('#skF_5',B_69,'#skF_6'),'#skF_6') = k2_lattices('#skF_5',k1_lattices('#skF_5',B_69,'#skF_6'),'#skF_6')
      | ~ m1_subset_1(B_69,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_30,c_387])).

tff(c_470,plain,(
    k4_lattices('#skF_5',k1_lattices('#skF_5','#skF_6','#skF_6'),'#skF_6') = k2_lattices('#skF_5',k1_lattices('#skF_5','#skF_6','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_426])).

tff(c_319,plain,(
    ! [A_63,C_64,B_65] :
      ( k4_lattices(A_63,C_64,B_65) = k4_lattices(A_63,B_65,C_64)
      | ~ m1_subset_1(C_64,u1_struct_0(A_63))
      | ~ m1_subset_1(B_65,u1_struct_0(A_63))
      | ~ l1_lattices(A_63)
      | ~ v6_lattices(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_331,plain,(
    ! [B_65] :
      ( k4_lattices('#skF_5',B_65,'#skF_6') = k4_lattices('#skF_5','#skF_6',B_65)
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_5'))
      | ~ l1_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_319])).

tff(c_339,plain,(
    ! [B_65] :
      ( k4_lattices('#skF_5',B_65,'#skF_6') = k4_lattices('#skF_5','#skF_6',B_65)
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_45,c_331])).

tff(c_341,plain,(
    ! [B_66] :
      ( k4_lattices('#skF_5',B_66,'#skF_6') = k4_lattices('#skF_5','#skF_6',B_66)
      | ~ m1_subset_1(B_66,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_339])).

tff(c_345,plain,(
    ! [B_27,C_28] :
      ( k4_lattices('#skF_5',k1_lattices('#skF_5',B_27,C_28),'#skF_6') = k4_lattices('#skF_5','#skF_6',k1_lattices('#skF_5',B_27,C_28))
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_5'))
      | ~ l2_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_20,c_341])).

tff(c_367,plain,(
    ! [B_27,C_28] :
      ( k4_lattices('#skF_5',k1_lattices('#skF_5',B_27,C_28),'#skF_6') = k4_lattices('#skF_5','#skF_6',k1_lattices('#skF_5',B_27,C_28))
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_345])).

tff(c_494,plain,(
    ! [B_72,C_73] :
      ( k4_lattices('#skF_5',k1_lattices('#skF_5',B_72,C_73),'#skF_6') = k4_lattices('#skF_5','#skF_6',k1_lattices('#skF_5',B_72,C_73))
      | ~ m1_subset_1(C_73,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_72,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_367])).

tff(c_533,plain,(
    ! [B_74] :
      ( k4_lattices('#skF_5',k1_lattices('#skF_5',B_74,'#skF_6'),'#skF_6') = k4_lattices('#skF_5','#skF_6',k1_lattices('#skF_5',B_74,'#skF_6'))
      | ~ m1_subset_1(B_74,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_30,c_494])).

tff(c_556,plain,(
    k4_lattices('#skF_5',k1_lattices('#skF_5','#skF_6','#skF_6'),'#skF_6') = k4_lattices('#skF_5','#skF_6',k1_lattices('#skF_5','#skF_6','#skF_6')) ),
    inference(resolution,[status(thm)],[c_30,c_533])).

tff(c_578,plain,(
    k4_lattices('#skF_5','#skF_6',k1_lattices('#skF_5','#skF_6','#skF_6')) = k2_lattices('#skF_5',k1_lattices('#skF_5','#skF_6','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_556])).

tff(c_1267,plain,(
    k2_lattices('#skF_5',k1_lattices('#skF_5','#skF_6','#skF_6'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1266,c_578])).

tff(c_36,plain,(
    v8_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_141,plain,(
    ! [A_53,B_54,C_55] :
      ( k1_lattices(A_53,k2_lattices(A_53,B_54,C_55),C_55) = C_55
      | ~ m1_subset_1(C_55,u1_struct_0(A_53))
      | ~ m1_subset_1(B_54,u1_struct_0(A_53))
      | ~ v8_lattices(A_53)
      | ~ l3_lattices(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_153,plain,(
    ! [B_54] :
      ( k1_lattices('#skF_5',k2_lattices('#skF_5',B_54,'#skF_6'),'#skF_6') = '#skF_6'
      | ~ m1_subset_1(B_54,u1_struct_0('#skF_5'))
      | ~ v8_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_141])).

tff(c_161,plain,(
    ! [B_54] :
      ( k1_lattices('#skF_5',k2_lattices('#skF_5',B_54,'#skF_6'),'#skF_6') = '#skF_6'
      | ~ m1_subset_1(B_54,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36,c_153])).

tff(c_163,plain,(
    ! [B_56] :
      ( k1_lattices('#skF_5',k2_lattices('#skF_5',B_56,'#skF_6'),'#skF_6') = '#skF_6'
      | ~ m1_subset_1(B_56,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_161])).

tff(c_167,plain,(
    ! [B_27,C_28] :
      ( k1_lattices('#skF_5',k2_lattices('#skF_5',k1_lattices('#skF_5',B_27,C_28),'#skF_6'),'#skF_6') = '#skF_6'
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_5'))
      | ~ l2_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_20,c_163])).

tff(c_189,plain,(
    ! [B_27,C_28] :
      ( k1_lattices('#skF_5',k2_lattices('#skF_5',k1_lattices('#skF_5',B_27,C_28),'#skF_6'),'#skF_6') = '#skF_6'
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_167])).

tff(c_190,plain,(
    ! [B_27,C_28] :
      ( k1_lattices('#skF_5',k2_lattices('#skF_5',k1_lattices('#skF_5',B_27,C_28),'#skF_6'),'#skF_6') = '#skF_6'
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_189])).

tff(c_1309,plain,
    ( k1_lattices('#skF_5','#skF_6','#skF_6') = '#skF_6'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1267,c_190])).

tff(c_1313,plain,(
    k1_lattices('#skF_5','#skF_6','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_1309])).

tff(c_1315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1313])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:53:09 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.66/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.58  
% 3.66/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.58  %$ m1_subset_1 > v9_lattices > v8_lattices > v6_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_3
% 3.66/1.58  
% 3.66/1.58  %Foreground sorts:
% 3.66/1.58  
% 3.66/1.58  
% 3.66/1.58  %Background operators:
% 3.66/1.58  
% 3.66/1.58  
% 3.66/1.58  %Foreground operators:
% 3.66/1.58  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.66/1.58  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.66/1.58  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 3.66/1.58  tff(l2_lattices, type, l2_lattices: $i > $o).
% 3.66/1.58  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.66/1.58  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.66/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.58  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 3.66/1.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.66/1.58  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 3.66/1.58  tff(l1_lattices, type, l1_lattices: $i > $o).
% 3.66/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.66/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.66/1.58  tff(v6_lattices, type, v6_lattices: $i > $o).
% 3.66/1.58  tff(v9_lattices, type, v9_lattices: $i > $o).
% 3.66/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.58  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.66/1.58  tff(v8_lattices, type, v8_lattices: $i > $o).
% 3.66/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.66/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.66/1.58  
% 3.66/1.60  tff(f_115, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k1_lattices(A, B, B) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_lattices)).
% 3.66/1.60  tff(f_68, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v9_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, B, C)) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattices)).
% 3.66/1.60  tff(f_85, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 3.66/1.60  tff(f_79, axiom, (![A, B, C]: ((((~v2_struct_0(A) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k1_lattices(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_lattices)).
% 3.66/1.60  tff(f_98, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 3.66/1.60  tff(f_38, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k4_lattices(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 3.66/1.60  tff(f_53, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v8_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k1_lattices(A, k2_lattices(A, B, C), C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattices)).
% 3.66/1.60  tff(c_28, plain, (k1_lattices('#skF_5', '#skF_6', '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.66/1.60  tff(c_30, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.66/1.60  tff(c_40, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.66/1.60  tff(c_32, plain, (l3_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.66/1.60  tff(c_34, plain, (v9_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.66/1.60  tff(c_58, plain, (![A_45, B_46, C_47]: (k2_lattices(A_45, B_46, k1_lattices(A_45, B_46, C_47))=B_46 | ~m1_subset_1(C_47, u1_struct_0(A_45)) | ~m1_subset_1(B_46, u1_struct_0(A_45)) | ~v9_lattices(A_45) | ~l3_lattices(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.66/1.60  tff(c_70, plain, (![B_46]: (k2_lattices('#skF_5', B_46, k1_lattices('#skF_5', B_46, '#skF_6'))=B_46 | ~m1_subset_1(B_46, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_58])).
% 3.66/1.60  tff(c_78, plain, (![B_46]: (k2_lattices('#skF_5', B_46, k1_lattices('#skF_5', B_46, '#skF_6'))=B_46 | ~m1_subset_1(B_46, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_70])).
% 3.66/1.60  tff(c_80, plain, (![B_48]: (k2_lattices('#skF_5', B_48, k1_lattices('#skF_5', B_48, '#skF_6'))=B_48 | ~m1_subset_1(B_48, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_40, c_78])).
% 3.66/1.60  tff(c_118, plain, (k2_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', '#skF_6', '#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_30, c_80])).
% 3.66/1.60  tff(c_46, plain, (![A_35]: (l2_lattices(A_35) | ~l3_lattices(A_35))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.66/1.60  tff(c_50, plain, (l2_lattices('#skF_5')), inference(resolution, [status(thm)], [c_32, c_46])).
% 3.66/1.60  tff(c_38, plain, (v6_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.66/1.60  tff(c_41, plain, (![A_34]: (l1_lattices(A_34) | ~l3_lattices(A_34))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.66/1.60  tff(c_45, plain, (l1_lattices('#skF_5')), inference(resolution, [status(thm)], [c_32, c_41])).
% 3.66/1.60  tff(c_20, plain, (![A_26, B_27, C_28]: (m1_subset_1(k1_lattices(A_26, B_27, C_28), u1_struct_0(A_26)) | ~m1_subset_1(C_28, u1_struct_0(A_26)) | ~m1_subset_1(B_27, u1_struct_0(A_26)) | ~l2_lattices(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.66/1.60  tff(c_208, plain, (![A_57, B_58, C_59]: (k4_lattices(A_57, B_58, C_59)=k2_lattices(A_57, B_58, C_59) | ~m1_subset_1(C_59, u1_struct_0(A_57)) | ~m1_subset_1(B_58, u1_struct_0(A_57)) | ~l1_lattices(A_57) | ~v6_lattices(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.66/1.60  tff(c_1160, plain, (![A_125, B_126, B_127, C_128]: (k4_lattices(A_125, B_126, k1_lattices(A_125, B_127, C_128))=k2_lattices(A_125, B_126, k1_lattices(A_125, B_127, C_128)) | ~m1_subset_1(B_126, u1_struct_0(A_125)) | ~l1_lattices(A_125) | ~v6_lattices(A_125) | ~m1_subset_1(C_128, u1_struct_0(A_125)) | ~m1_subset_1(B_127, u1_struct_0(A_125)) | ~l2_lattices(A_125) | v2_struct_0(A_125))), inference(resolution, [status(thm)], [c_20, c_208])).
% 3.66/1.60  tff(c_1172, plain, (![B_127, C_128]: (k4_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', B_127, C_128))=k2_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', B_127, C_128)) | ~l1_lattices('#skF_5') | ~v6_lattices('#skF_5') | ~m1_subset_1(C_128, u1_struct_0('#skF_5')) | ~m1_subset_1(B_127, u1_struct_0('#skF_5')) | ~l2_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_1160])).
% 3.66/1.60  tff(c_1180, plain, (![B_127, C_128]: (k4_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', B_127, C_128))=k2_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', B_127, C_128)) | ~m1_subset_1(C_128, u1_struct_0('#skF_5')) | ~m1_subset_1(B_127, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_38, c_45, c_1172])).
% 3.66/1.60  tff(c_1182, plain, (![B_129, C_130]: (k4_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', B_129, C_130))=k2_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', B_129, C_130)) | ~m1_subset_1(C_130, u1_struct_0('#skF_5')) | ~m1_subset_1(B_129, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_40, c_1180])).
% 3.66/1.60  tff(c_1221, plain, (![B_131]: (k4_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', B_131, '#skF_6'))=k2_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', B_131, '#skF_6')) | ~m1_subset_1(B_131, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_30, c_1182])).
% 3.66/1.60  tff(c_1244, plain, (k4_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', '#skF_6', '#skF_6'))=k2_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', '#skF_6', '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_1221])).
% 3.66/1.60  tff(c_1266, plain, (k4_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', '#skF_6', '#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_1244])).
% 3.66/1.60  tff(c_220, plain, (![B_58]: (k4_lattices('#skF_5', B_58, '#skF_6')=k2_lattices('#skF_5', B_58, '#skF_6') | ~m1_subset_1(B_58, u1_struct_0('#skF_5')) | ~l1_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_208])).
% 3.66/1.60  tff(c_228, plain, (![B_58]: (k4_lattices('#skF_5', B_58, '#skF_6')=k2_lattices('#skF_5', B_58, '#skF_6') | ~m1_subset_1(B_58, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_45, c_220])).
% 3.66/1.60  tff(c_240, plain, (![B_60]: (k4_lattices('#skF_5', B_60, '#skF_6')=k2_lattices('#skF_5', B_60, '#skF_6') | ~m1_subset_1(B_60, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_40, c_228])).
% 3.66/1.60  tff(c_244, plain, (![B_27, C_28]: (k4_lattices('#skF_5', k1_lattices('#skF_5', B_27, C_28), '#skF_6')=k2_lattices('#skF_5', k1_lattices('#skF_5', B_27, C_28), '#skF_6') | ~m1_subset_1(C_28, u1_struct_0('#skF_5')) | ~m1_subset_1(B_27, u1_struct_0('#skF_5')) | ~l2_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_20, c_240])).
% 3.66/1.60  tff(c_266, plain, (![B_27, C_28]: (k4_lattices('#skF_5', k1_lattices('#skF_5', B_27, C_28), '#skF_6')=k2_lattices('#skF_5', k1_lattices('#skF_5', B_27, C_28), '#skF_6') | ~m1_subset_1(C_28, u1_struct_0('#skF_5')) | ~m1_subset_1(B_27, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_244])).
% 3.66/1.60  tff(c_387, plain, (![B_67, C_68]: (k4_lattices('#skF_5', k1_lattices('#skF_5', B_67, C_68), '#skF_6')=k2_lattices('#skF_5', k1_lattices('#skF_5', B_67, C_68), '#skF_6') | ~m1_subset_1(C_68, u1_struct_0('#skF_5')) | ~m1_subset_1(B_67, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_40, c_266])).
% 3.66/1.60  tff(c_426, plain, (![B_69]: (k4_lattices('#skF_5', k1_lattices('#skF_5', B_69, '#skF_6'), '#skF_6')=k2_lattices('#skF_5', k1_lattices('#skF_5', B_69, '#skF_6'), '#skF_6') | ~m1_subset_1(B_69, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_30, c_387])).
% 3.66/1.60  tff(c_470, plain, (k4_lattices('#skF_5', k1_lattices('#skF_5', '#skF_6', '#skF_6'), '#skF_6')=k2_lattices('#skF_5', k1_lattices('#skF_5', '#skF_6', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_30, c_426])).
% 3.66/1.60  tff(c_319, plain, (![A_63, C_64, B_65]: (k4_lattices(A_63, C_64, B_65)=k4_lattices(A_63, B_65, C_64) | ~m1_subset_1(C_64, u1_struct_0(A_63)) | ~m1_subset_1(B_65, u1_struct_0(A_63)) | ~l1_lattices(A_63) | ~v6_lattices(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.66/1.60  tff(c_331, plain, (![B_65]: (k4_lattices('#skF_5', B_65, '#skF_6')=k4_lattices('#skF_5', '#skF_6', B_65) | ~m1_subset_1(B_65, u1_struct_0('#skF_5')) | ~l1_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_319])).
% 3.66/1.60  tff(c_339, plain, (![B_65]: (k4_lattices('#skF_5', B_65, '#skF_6')=k4_lattices('#skF_5', '#skF_6', B_65) | ~m1_subset_1(B_65, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_45, c_331])).
% 3.66/1.60  tff(c_341, plain, (![B_66]: (k4_lattices('#skF_5', B_66, '#skF_6')=k4_lattices('#skF_5', '#skF_6', B_66) | ~m1_subset_1(B_66, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_40, c_339])).
% 3.66/1.60  tff(c_345, plain, (![B_27, C_28]: (k4_lattices('#skF_5', k1_lattices('#skF_5', B_27, C_28), '#skF_6')=k4_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', B_27, C_28)) | ~m1_subset_1(C_28, u1_struct_0('#skF_5')) | ~m1_subset_1(B_27, u1_struct_0('#skF_5')) | ~l2_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_20, c_341])).
% 3.66/1.60  tff(c_367, plain, (![B_27, C_28]: (k4_lattices('#skF_5', k1_lattices('#skF_5', B_27, C_28), '#skF_6')=k4_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', B_27, C_28)) | ~m1_subset_1(C_28, u1_struct_0('#skF_5')) | ~m1_subset_1(B_27, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_345])).
% 3.66/1.60  tff(c_494, plain, (![B_72, C_73]: (k4_lattices('#skF_5', k1_lattices('#skF_5', B_72, C_73), '#skF_6')=k4_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', B_72, C_73)) | ~m1_subset_1(C_73, u1_struct_0('#skF_5')) | ~m1_subset_1(B_72, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_40, c_367])).
% 3.66/1.60  tff(c_533, plain, (![B_74]: (k4_lattices('#skF_5', k1_lattices('#skF_5', B_74, '#skF_6'), '#skF_6')=k4_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', B_74, '#skF_6')) | ~m1_subset_1(B_74, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_30, c_494])).
% 3.66/1.60  tff(c_556, plain, (k4_lattices('#skF_5', k1_lattices('#skF_5', '#skF_6', '#skF_6'), '#skF_6')=k4_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', '#skF_6', '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_533])).
% 3.66/1.60  tff(c_578, plain, (k4_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', '#skF_6', '#skF_6'))=k2_lattices('#skF_5', k1_lattices('#skF_5', '#skF_6', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_470, c_556])).
% 3.66/1.60  tff(c_1267, plain, (k2_lattices('#skF_5', k1_lattices('#skF_5', '#skF_6', '#skF_6'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1266, c_578])).
% 3.66/1.60  tff(c_36, plain, (v8_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.66/1.60  tff(c_141, plain, (![A_53, B_54, C_55]: (k1_lattices(A_53, k2_lattices(A_53, B_54, C_55), C_55)=C_55 | ~m1_subset_1(C_55, u1_struct_0(A_53)) | ~m1_subset_1(B_54, u1_struct_0(A_53)) | ~v8_lattices(A_53) | ~l3_lattices(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.66/1.60  tff(c_153, plain, (![B_54]: (k1_lattices('#skF_5', k2_lattices('#skF_5', B_54, '#skF_6'), '#skF_6')='#skF_6' | ~m1_subset_1(B_54, u1_struct_0('#skF_5')) | ~v8_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_141])).
% 3.66/1.60  tff(c_161, plain, (![B_54]: (k1_lattices('#skF_5', k2_lattices('#skF_5', B_54, '#skF_6'), '#skF_6')='#skF_6' | ~m1_subset_1(B_54, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36, c_153])).
% 3.66/1.60  tff(c_163, plain, (![B_56]: (k1_lattices('#skF_5', k2_lattices('#skF_5', B_56, '#skF_6'), '#skF_6')='#skF_6' | ~m1_subset_1(B_56, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_40, c_161])).
% 3.66/1.60  tff(c_167, plain, (![B_27, C_28]: (k1_lattices('#skF_5', k2_lattices('#skF_5', k1_lattices('#skF_5', B_27, C_28), '#skF_6'), '#skF_6')='#skF_6' | ~m1_subset_1(C_28, u1_struct_0('#skF_5')) | ~m1_subset_1(B_27, u1_struct_0('#skF_5')) | ~l2_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_20, c_163])).
% 3.66/1.60  tff(c_189, plain, (![B_27, C_28]: (k1_lattices('#skF_5', k2_lattices('#skF_5', k1_lattices('#skF_5', B_27, C_28), '#skF_6'), '#skF_6')='#skF_6' | ~m1_subset_1(C_28, u1_struct_0('#skF_5')) | ~m1_subset_1(B_27, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_167])).
% 3.66/1.60  tff(c_190, plain, (![B_27, C_28]: (k1_lattices('#skF_5', k2_lattices('#skF_5', k1_lattices('#skF_5', B_27, C_28), '#skF_6'), '#skF_6')='#skF_6' | ~m1_subset_1(C_28, u1_struct_0('#skF_5')) | ~m1_subset_1(B_27, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_40, c_189])).
% 3.66/1.60  tff(c_1309, plain, (k1_lattices('#skF_5', '#skF_6', '#skF_6')='#skF_6' | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1267, c_190])).
% 3.66/1.60  tff(c_1313, plain, (k1_lattices('#skF_5', '#skF_6', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_1309])).
% 3.66/1.60  tff(c_1315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_1313])).
% 3.66/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.60  
% 3.66/1.60  Inference rules
% 3.66/1.60  ----------------------
% 3.66/1.60  #Ref     : 0
% 3.66/1.60  #Sup     : 260
% 3.66/1.60  #Fact    : 0
% 3.66/1.60  #Define  : 0
% 3.66/1.60  #Split   : 0
% 3.66/1.60  #Chain   : 0
% 3.66/1.60  #Close   : 0
% 3.66/1.60  
% 3.66/1.60  Ordering : KBO
% 3.66/1.60  
% 3.66/1.60  Simplification rules
% 3.66/1.60  ----------------------
% 3.66/1.60  #Subsume      : 14
% 3.66/1.60  #Demod        : 233
% 3.66/1.60  #Tautology    : 152
% 3.66/1.60  #SimpNegUnit  : 82
% 3.66/1.60  #BackRed      : 2
% 3.66/1.60  
% 3.66/1.60  #Partial instantiations: 0
% 3.66/1.60  #Strategies tried      : 1
% 3.66/1.60  
% 3.66/1.60  Timing (in seconds)
% 3.66/1.60  ----------------------
% 3.66/1.60  Preprocessing        : 0.33
% 3.66/1.60  Parsing              : 0.17
% 3.66/1.60  CNF conversion       : 0.02
% 3.66/1.60  Main loop            : 0.52
% 3.66/1.60  Inferencing          : 0.20
% 3.66/1.60  Reduction            : 0.15
% 3.66/1.60  Demodulation         : 0.11
% 3.66/1.60  BG Simplification    : 0.03
% 3.66/1.60  Subsumption          : 0.10
% 3.66/1.60  Abstraction          : 0.04
% 3.66/1.60  MUC search           : 0.00
% 3.66/1.60  Cooper               : 0.00
% 3.66/1.60  Total                : 0.88
% 3.66/1.60  Index Insertion      : 0.00
% 3.66/1.60  Index Deletion       : 0.00
% 3.66/1.60  Index Matching       : 0.00
% 3.66/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
