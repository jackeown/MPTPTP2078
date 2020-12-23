%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:44 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 100 expanded)
%              Number of leaves         :   26 (  48 expanded)
%              Depth                    :   20
%              Number of atoms          :  161 ( 307 expanded)
%              Number of equality atoms :   32 (  53 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v6_waybel_0 > m1_subset_1 > l1_waybel_0 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k8_funcop_1 > k3_yellow_6 > u1_waybel_0 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_waybel_0,type,(
    v6_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_6,type,(
    k3_yellow_6: ( $i * $i * $i ) > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k8_funcop_1,type,(
    k8_funcop_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => u1_struct_0(k3_yellow_6(A,B,C)) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_6)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & ~ v2_struct_0(B)
        & l1_struct_0(B)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( v6_waybel_0(k3_yellow_6(A,B,C),B)
        & l1_waybel_0(k3_yellow_6(A,B,C),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_6)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_struct_0(B) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => ! [D] :
                  ( ( v6_waybel_0(D,B)
                    & l1_waybel_0(D,B) )
                 => ( D = k3_yellow_6(A,B,C)
                  <=> ( g1_orders_2(u1_struct_0(D),u1_orders_2(D)) = g1_orders_2(u1_struct_0(A),u1_orders_2(A))
                      & r2_funct_2(u1_struct_0(D),u1_struct_0(B),u1_waybel_0(B,D),k8_funcop_1(u1_struct_0(B),u1_struct_0(D),C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_yellow_6)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(c_26,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_38,plain,(
    ! [A_39,B_40,C_41] :
      ( l1_waybel_0(k3_yellow_6(A_39,B_40,C_41),B_40)
      | ~ m1_subset_1(C_41,u1_struct_0(B_40))
      | ~ l1_struct_0(B_40)
      | v2_struct_0(B_40)
      | ~ l1_orders_2(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    ! [A_39] :
      ( l1_waybel_0(k3_yellow_6(A_39,'#skF_2','#skF_3'),'#skF_2')
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_39) ) ),
    inference(resolution,[status(thm)],[c_20,c_38])).

tff(c_43,plain,(
    ! [A_39] :
      ( l1_waybel_0(k3_yellow_6(A_39,'#skF_2','#skF_3'),'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_40])).

tff(c_44,plain,(
    ! [A_39] :
      ( l1_waybel_0(k3_yellow_6(A_39,'#skF_2','#skF_3'),'#skF_2')
      | ~ l1_orders_2(A_39) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_43])).

tff(c_16,plain,(
    ! [A_23,B_24,C_25] :
      ( v6_waybel_0(k3_yellow_6(A_23,B_24,C_25),B_24)
      | ~ m1_subset_1(C_25,u1_struct_0(B_24))
      | ~ l1_struct_0(B_24)
      | v2_struct_0(B_24)
      | ~ l1_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [A_1] :
      ( m1_subset_1(u1_orders_2(A_1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1),u1_struct_0(A_1))))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    ! [A_46,B_47,C_48] :
      ( g1_orders_2(u1_struct_0(k3_yellow_6(A_46,B_47,C_48)),u1_orders_2(k3_yellow_6(A_46,B_47,C_48))) = g1_orders_2(u1_struct_0(A_46),u1_orders_2(A_46))
      | ~ l1_waybel_0(k3_yellow_6(A_46,B_47,C_48),B_47)
      | ~ v6_waybel_0(k3_yellow_6(A_46,B_47,C_48),B_47)
      | ~ m1_subset_1(C_48,u1_struct_0(B_47))
      | ~ l1_struct_0(B_47)
      | v2_struct_0(B_47)
      | ~ l1_orders_2(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [D_7,B_3,C_6,A_2] :
      ( D_7 = B_3
      | g1_orders_2(C_6,D_7) != g1_orders_2(A_2,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k2_zfmisc_1(A_2,A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_52,plain,(
    ! [A_46,B_47,C_48,B_3,A_2] :
      ( u1_orders_2(k3_yellow_6(A_46,B_47,C_48)) = B_3
      | g1_orders_2(u1_struct_0(A_46),u1_orders_2(A_46)) != g1_orders_2(A_2,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k2_zfmisc_1(A_2,A_2)))
      | ~ l1_waybel_0(k3_yellow_6(A_46,B_47,C_48),B_47)
      | ~ v6_waybel_0(k3_yellow_6(A_46,B_47,C_48),B_47)
      | ~ m1_subset_1(C_48,u1_struct_0(B_47))
      | ~ l1_struct_0(B_47)
      | v2_struct_0(B_47)
      | ~ l1_orders_2(A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_4])).

tff(c_72,plain,(
    ! [A_54,B_55,C_56] :
      ( u1_orders_2(k3_yellow_6(A_54,B_55,C_56)) = u1_orders_2(A_54)
      | ~ m1_subset_1(u1_orders_2(A_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_54),u1_struct_0(A_54))))
      | ~ l1_waybel_0(k3_yellow_6(A_54,B_55,C_56),B_55)
      | ~ v6_waybel_0(k3_yellow_6(A_54,B_55,C_56),B_55)
      | ~ m1_subset_1(C_56,u1_struct_0(B_55))
      | ~ l1_struct_0(B_55)
      | v2_struct_0(B_55)
      | ~ l1_orders_2(A_54) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_52])).

tff(c_76,plain,(
    ! [A_57,B_58,C_59] :
      ( u1_orders_2(k3_yellow_6(A_57,B_58,C_59)) = u1_orders_2(A_57)
      | ~ l1_waybel_0(k3_yellow_6(A_57,B_58,C_59),B_58)
      | ~ v6_waybel_0(k3_yellow_6(A_57,B_58,C_59),B_58)
      | ~ m1_subset_1(C_59,u1_struct_0(B_58))
      | ~ l1_struct_0(B_58)
      | v2_struct_0(B_58)
      | ~ l1_orders_2(A_57) ) ),
    inference(resolution,[status(thm)],[c_2,c_72])).

tff(c_82,plain,(
    ! [A_63,B_64,C_65] :
      ( u1_orders_2(k3_yellow_6(A_63,B_64,C_65)) = u1_orders_2(A_63)
      | ~ l1_waybel_0(k3_yellow_6(A_63,B_64,C_65),B_64)
      | ~ m1_subset_1(C_65,u1_struct_0(B_64))
      | ~ l1_struct_0(B_64)
      | v2_struct_0(B_64)
      | ~ l1_orders_2(A_63) ) ),
    inference(resolution,[status(thm)],[c_16,c_76])).

tff(c_84,plain,(
    ! [A_39] :
      ( u1_orders_2(k3_yellow_6(A_39,'#skF_2','#skF_3')) = u1_orders_2(A_39)
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_39) ) ),
    inference(resolution,[status(thm)],[c_44,c_82])).

tff(c_87,plain,(
    ! [A_39] :
      ( u1_orders_2(k3_yellow_6(A_39,'#skF_2','#skF_3')) = u1_orders_2(A_39)
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_84])).

tff(c_89,plain,(
    ! [A_66] :
      ( u1_orders_2(k3_yellow_6(A_66,'#skF_2','#skF_3')) = u1_orders_2(A_66)
      | ~ l1_orders_2(A_66) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_87])).

tff(c_12,plain,(
    ! [A_8,B_16,C_20] :
      ( g1_orders_2(u1_struct_0(k3_yellow_6(A_8,B_16,C_20)),u1_orders_2(k3_yellow_6(A_8,B_16,C_20))) = g1_orders_2(u1_struct_0(A_8),u1_orders_2(A_8))
      | ~ l1_waybel_0(k3_yellow_6(A_8,B_16,C_20),B_16)
      | ~ v6_waybel_0(k3_yellow_6(A_8,B_16,C_20),B_16)
      | ~ m1_subset_1(C_20,u1_struct_0(B_16))
      | ~ l1_struct_0(B_16)
      | v2_struct_0(B_16)
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_97,plain,(
    ! [A_66] :
      ( g1_orders_2(u1_struct_0(k3_yellow_6(A_66,'#skF_2','#skF_3')),u1_orders_2(A_66)) = g1_orders_2(u1_struct_0(A_66),u1_orders_2(A_66))
      | ~ l1_waybel_0(k3_yellow_6(A_66,'#skF_2','#skF_3'),'#skF_2')
      | ~ v6_waybel_0(k3_yellow_6(A_66,'#skF_2','#skF_3'),'#skF_2')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_66)
      | ~ l1_orders_2(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_12])).

tff(c_106,plain,(
    ! [A_66] :
      ( g1_orders_2(u1_struct_0(k3_yellow_6(A_66,'#skF_2','#skF_3')),u1_orders_2(A_66)) = g1_orders_2(u1_struct_0(A_66),u1_orders_2(A_66))
      | ~ l1_waybel_0(k3_yellow_6(A_66,'#skF_2','#skF_3'),'#skF_2')
      | ~ v6_waybel_0(k3_yellow_6(A_66,'#skF_2','#skF_3'),'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_97])).

tff(c_113,plain,(
    ! [A_68] :
      ( g1_orders_2(u1_struct_0(k3_yellow_6(A_68,'#skF_2','#skF_3')),u1_orders_2(A_68)) = g1_orders_2(u1_struct_0(A_68),u1_orders_2(A_68))
      | ~ l1_waybel_0(k3_yellow_6(A_68,'#skF_2','#skF_3'),'#skF_2')
      | ~ v6_waybel_0(k3_yellow_6(A_68,'#skF_2','#skF_3'),'#skF_2')
      | ~ l1_orders_2(A_68) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_106])).

tff(c_6,plain,(
    ! [C_6,A_2,D_7,B_3] :
      ( C_6 = A_2
      | g1_orders_2(C_6,D_7) != g1_orders_2(A_2,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k2_zfmisc_1(A_2,A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_124,plain,(
    ! [A_68,A_2,B_3] :
      ( u1_struct_0(k3_yellow_6(A_68,'#skF_2','#skF_3')) = A_2
      | g1_orders_2(u1_struct_0(A_68),u1_orders_2(A_68)) != g1_orders_2(A_2,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k2_zfmisc_1(A_2,A_2)))
      | ~ l1_waybel_0(k3_yellow_6(A_68,'#skF_2','#skF_3'),'#skF_2')
      | ~ v6_waybel_0(k3_yellow_6(A_68,'#skF_2','#skF_3'),'#skF_2')
      | ~ l1_orders_2(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_6])).

tff(c_147,plain,(
    ! [A_72] :
      ( u1_struct_0(k3_yellow_6(A_72,'#skF_2','#skF_3')) = u1_struct_0(A_72)
      | ~ m1_subset_1(u1_orders_2(A_72),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_72),u1_struct_0(A_72))))
      | ~ l1_waybel_0(k3_yellow_6(A_72,'#skF_2','#skF_3'),'#skF_2')
      | ~ v6_waybel_0(k3_yellow_6(A_72,'#skF_2','#skF_3'),'#skF_2')
      | ~ l1_orders_2(A_72) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_124])).

tff(c_155,plain,(
    ! [A_73] :
      ( u1_struct_0(k3_yellow_6(A_73,'#skF_2','#skF_3')) = u1_struct_0(A_73)
      | ~ l1_waybel_0(k3_yellow_6(A_73,'#skF_2','#skF_3'),'#skF_2')
      | ~ v6_waybel_0(k3_yellow_6(A_73,'#skF_2','#skF_3'),'#skF_2')
      | ~ l1_orders_2(A_73) ) ),
    inference(resolution,[status(thm)],[c_2,c_147])).

tff(c_159,plain,(
    ! [A_23] :
      ( u1_struct_0(k3_yellow_6(A_23,'#skF_2','#skF_3')) = u1_struct_0(A_23)
      | ~ l1_waybel_0(k3_yellow_6(A_23,'#skF_2','#skF_3'),'#skF_2')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_23) ) ),
    inference(resolution,[status(thm)],[c_16,c_155])).

tff(c_162,plain,(
    ! [A_23] :
      ( u1_struct_0(k3_yellow_6(A_23,'#skF_2','#skF_3')) = u1_struct_0(A_23)
      | ~ l1_waybel_0(k3_yellow_6(A_23,'#skF_2','#skF_3'),'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_159])).

tff(c_164,plain,(
    ! [A_74] :
      ( u1_struct_0(k3_yellow_6(A_74,'#skF_2','#skF_3')) = u1_struct_0(A_74)
      | ~ l1_waybel_0(k3_yellow_6(A_74,'#skF_2','#skF_3'),'#skF_2')
      | ~ l1_orders_2(A_74) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_162])).

tff(c_169,plain,(
    ! [A_75] :
      ( u1_struct_0(k3_yellow_6(A_75,'#skF_2','#skF_3')) = u1_struct_0(A_75)
      | ~ l1_orders_2(A_75) ) ),
    inference(resolution,[status(thm)],[c_44,c_164])).

tff(c_18,plain,(
    u1_struct_0(k3_yellow_6('#skF_1','#skF_2','#skF_3')) != u1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_211,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_18])).

tff(c_229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_211])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:02:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.32  
% 2.58/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.32  %$ r2_funct_2 > v6_waybel_0 > m1_subset_1 > l1_waybel_0 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k8_funcop_1 > k3_yellow_6 > u1_waybel_0 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.58/1.32  
% 2.58/1.32  %Foreground sorts:
% 2.58/1.32  
% 2.58/1.32  
% 2.58/1.32  %Background operators:
% 2.58/1.32  
% 2.58/1.32  
% 2.58/1.32  %Foreground operators:
% 2.58/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.58/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.32  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 2.58/1.32  tff(k3_yellow_6, type, k3_yellow_6: ($i * $i * $i) > $i).
% 2.58/1.32  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.58/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.32  tff(k8_funcop_1, type, k8_funcop_1: ($i * $i * $i) > $i).
% 2.58/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.58/1.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.58/1.32  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.58/1.32  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 2.58/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.32  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.58/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.58/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.32  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.58/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.58/1.32  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.58/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.58/1.32  
% 2.58/1.34  tff(f_87, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (u1_struct_0(k3_yellow_6(A, B, C)) = u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_6)).
% 2.58/1.34  tff(f_73, axiom, (![A, B, C]: ((((l1_orders_2(A) & ~v2_struct_0(B)) & l1_struct_0(B)) & m1_subset_1(C, u1_struct_0(B))) => (v6_waybel_0(k3_yellow_6(A, B, C), B) & l1_waybel_0(k3_yellow_6(A, B, C), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_6)).
% 2.58/1.34  tff(f_29, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 2.58/1.34  tff(f_60, axiom, (![A]: (l1_orders_2(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (![D]: ((v6_waybel_0(D, B) & l1_waybel_0(D, B)) => ((D = k3_yellow_6(A, B, C)) <=> ((g1_orders_2(u1_struct_0(D), u1_orders_2(D)) = g1_orders_2(u1_struct_0(A), u1_orders_2(A))) & r2_funct_2(u1_struct_0(D), u1_struct_0(B), u1_waybel_0(B, D), k8_funcop_1(u1_struct_0(B), u1_struct_0(D), C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_yellow_6)).
% 2.58/1.34  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C, D]: ((g1_orders_2(A, B) = g1_orders_2(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_orders_2)).
% 2.58/1.34  tff(c_26, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.58/1.34  tff(c_24, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.58/1.34  tff(c_22, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.58/1.34  tff(c_20, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.58/1.34  tff(c_38, plain, (![A_39, B_40, C_41]: (l1_waybel_0(k3_yellow_6(A_39, B_40, C_41), B_40) | ~m1_subset_1(C_41, u1_struct_0(B_40)) | ~l1_struct_0(B_40) | v2_struct_0(B_40) | ~l1_orders_2(A_39))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.58/1.34  tff(c_40, plain, (![A_39]: (l1_waybel_0(k3_yellow_6(A_39, '#skF_2', '#skF_3'), '#skF_2') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_orders_2(A_39))), inference(resolution, [status(thm)], [c_20, c_38])).
% 2.58/1.34  tff(c_43, plain, (![A_39]: (l1_waybel_0(k3_yellow_6(A_39, '#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2') | ~l1_orders_2(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_40])).
% 2.58/1.34  tff(c_44, plain, (![A_39]: (l1_waybel_0(k3_yellow_6(A_39, '#skF_2', '#skF_3'), '#skF_2') | ~l1_orders_2(A_39))), inference(negUnitSimplification, [status(thm)], [c_24, c_43])).
% 2.58/1.34  tff(c_16, plain, (![A_23, B_24, C_25]: (v6_waybel_0(k3_yellow_6(A_23, B_24, C_25), B_24) | ~m1_subset_1(C_25, u1_struct_0(B_24)) | ~l1_struct_0(B_24) | v2_struct_0(B_24) | ~l1_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.58/1.34  tff(c_2, plain, (![A_1]: (m1_subset_1(u1_orders_2(A_1), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1), u1_struct_0(A_1)))) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.58/1.34  tff(c_47, plain, (![A_46, B_47, C_48]: (g1_orders_2(u1_struct_0(k3_yellow_6(A_46, B_47, C_48)), u1_orders_2(k3_yellow_6(A_46, B_47, C_48)))=g1_orders_2(u1_struct_0(A_46), u1_orders_2(A_46)) | ~l1_waybel_0(k3_yellow_6(A_46, B_47, C_48), B_47) | ~v6_waybel_0(k3_yellow_6(A_46, B_47, C_48), B_47) | ~m1_subset_1(C_48, u1_struct_0(B_47)) | ~l1_struct_0(B_47) | v2_struct_0(B_47) | ~l1_orders_2(A_46))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.58/1.34  tff(c_4, plain, (![D_7, B_3, C_6, A_2]: (D_7=B_3 | g1_orders_2(C_6, D_7)!=g1_orders_2(A_2, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(k2_zfmisc_1(A_2, A_2))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.58/1.34  tff(c_52, plain, (![A_46, B_47, C_48, B_3, A_2]: (u1_orders_2(k3_yellow_6(A_46, B_47, C_48))=B_3 | g1_orders_2(u1_struct_0(A_46), u1_orders_2(A_46))!=g1_orders_2(A_2, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(k2_zfmisc_1(A_2, A_2))) | ~l1_waybel_0(k3_yellow_6(A_46, B_47, C_48), B_47) | ~v6_waybel_0(k3_yellow_6(A_46, B_47, C_48), B_47) | ~m1_subset_1(C_48, u1_struct_0(B_47)) | ~l1_struct_0(B_47) | v2_struct_0(B_47) | ~l1_orders_2(A_46))), inference(superposition, [status(thm), theory('equality')], [c_47, c_4])).
% 2.58/1.34  tff(c_72, plain, (![A_54, B_55, C_56]: (u1_orders_2(k3_yellow_6(A_54, B_55, C_56))=u1_orders_2(A_54) | ~m1_subset_1(u1_orders_2(A_54), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_54), u1_struct_0(A_54)))) | ~l1_waybel_0(k3_yellow_6(A_54, B_55, C_56), B_55) | ~v6_waybel_0(k3_yellow_6(A_54, B_55, C_56), B_55) | ~m1_subset_1(C_56, u1_struct_0(B_55)) | ~l1_struct_0(B_55) | v2_struct_0(B_55) | ~l1_orders_2(A_54))), inference(reflexivity, [status(thm), theory('equality')], [c_52])).
% 2.58/1.34  tff(c_76, plain, (![A_57, B_58, C_59]: (u1_orders_2(k3_yellow_6(A_57, B_58, C_59))=u1_orders_2(A_57) | ~l1_waybel_0(k3_yellow_6(A_57, B_58, C_59), B_58) | ~v6_waybel_0(k3_yellow_6(A_57, B_58, C_59), B_58) | ~m1_subset_1(C_59, u1_struct_0(B_58)) | ~l1_struct_0(B_58) | v2_struct_0(B_58) | ~l1_orders_2(A_57))), inference(resolution, [status(thm)], [c_2, c_72])).
% 2.58/1.34  tff(c_82, plain, (![A_63, B_64, C_65]: (u1_orders_2(k3_yellow_6(A_63, B_64, C_65))=u1_orders_2(A_63) | ~l1_waybel_0(k3_yellow_6(A_63, B_64, C_65), B_64) | ~m1_subset_1(C_65, u1_struct_0(B_64)) | ~l1_struct_0(B_64) | v2_struct_0(B_64) | ~l1_orders_2(A_63))), inference(resolution, [status(thm)], [c_16, c_76])).
% 2.58/1.34  tff(c_84, plain, (![A_39]: (u1_orders_2(k3_yellow_6(A_39, '#skF_2', '#skF_3'))=u1_orders_2(A_39) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_orders_2(A_39))), inference(resolution, [status(thm)], [c_44, c_82])).
% 2.58/1.34  tff(c_87, plain, (![A_39]: (u1_orders_2(k3_yellow_6(A_39, '#skF_2', '#skF_3'))=u1_orders_2(A_39) | v2_struct_0('#skF_2') | ~l1_orders_2(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_84])).
% 2.58/1.34  tff(c_89, plain, (![A_66]: (u1_orders_2(k3_yellow_6(A_66, '#skF_2', '#skF_3'))=u1_orders_2(A_66) | ~l1_orders_2(A_66))), inference(negUnitSimplification, [status(thm)], [c_24, c_87])).
% 2.58/1.34  tff(c_12, plain, (![A_8, B_16, C_20]: (g1_orders_2(u1_struct_0(k3_yellow_6(A_8, B_16, C_20)), u1_orders_2(k3_yellow_6(A_8, B_16, C_20)))=g1_orders_2(u1_struct_0(A_8), u1_orders_2(A_8)) | ~l1_waybel_0(k3_yellow_6(A_8, B_16, C_20), B_16) | ~v6_waybel_0(k3_yellow_6(A_8, B_16, C_20), B_16) | ~m1_subset_1(C_20, u1_struct_0(B_16)) | ~l1_struct_0(B_16) | v2_struct_0(B_16) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.58/1.34  tff(c_97, plain, (![A_66]: (g1_orders_2(u1_struct_0(k3_yellow_6(A_66, '#skF_2', '#skF_3')), u1_orders_2(A_66))=g1_orders_2(u1_struct_0(A_66), u1_orders_2(A_66)) | ~l1_waybel_0(k3_yellow_6(A_66, '#skF_2', '#skF_3'), '#skF_2') | ~v6_waybel_0(k3_yellow_6(A_66, '#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_orders_2(A_66) | ~l1_orders_2(A_66))), inference(superposition, [status(thm), theory('equality')], [c_89, c_12])).
% 2.58/1.34  tff(c_106, plain, (![A_66]: (g1_orders_2(u1_struct_0(k3_yellow_6(A_66, '#skF_2', '#skF_3')), u1_orders_2(A_66))=g1_orders_2(u1_struct_0(A_66), u1_orders_2(A_66)) | ~l1_waybel_0(k3_yellow_6(A_66, '#skF_2', '#skF_3'), '#skF_2') | ~v6_waybel_0(k3_yellow_6(A_66, '#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2') | ~l1_orders_2(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_97])).
% 2.58/1.34  tff(c_113, plain, (![A_68]: (g1_orders_2(u1_struct_0(k3_yellow_6(A_68, '#skF_2', '#skF_3')), u1_orders_2(A_68))=g1_orders_2(u1_struct_0(A_68), u1_orders_2(A_68)) | ~l1_waybel_0(k3_yellow_6(A_68, '#skF_2', '#skF_3'), '#skF_2') | ~v6_waybel_0(k3_yellow_6(A_68, '#skF_2', '#skF_3'), '#skF_2') | ~l1_orders_2(A_68))), inference(negUnitSimplification, [status(thm)], [c_24, c_106])).
% 2.58/1.34  tff(c_6, plain, (![C_6, A_2, D_7, B_3]: (C_6=A_2 | g1_orders_2(C_6, D_7)!=g1_orders_2(A_2, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(k2_zfmisc_1(A_2, A_2))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.58/1.34  tff(c_124, plain, (![A_68, A_2, B_3]: (u1_struct_0(k3_yellow_6(A_68, '#skF_2', '#skF_3'))=A_2 | g1_orders_2(u1_struct_0(A_68), u1_orders_2(A_68))!=g1_orders_2(A_2, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(k2_zfmisc_1(A_2, A_2))) | ~l1_waybel_0(k3_yellow_6(A_68, '#skF_2', '#skF_3'), '#skF_2') | ~v6_waybel_0(k3_yellow_6(A_68, '#skF_2', '#skF_3'), '#skF_2') | ~l1_orders_2(A_68))), inference(superposition, [status(thm), theory('equality')], [c_113, c_6])).
% 2.58/1.34  tff(c_147, plain, (![A_72]: (u1_struct_0(k3_yellow_6(A_72, '#skF_2', '#skF_3'))=u1_struct_0(A_72) | ~m1_subset_1(u1_orders_2(A_72), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_72), u1_struct_0(A_72)))) | ~l1_waybel_0(k3_yellow_6(A_72, '#skF_2', '#skF_3'), '#skF_2') | ~v6_waybel_0(k3_yellow_6(A_72, '#skF_2', '#skF_3'), '#skF_2') | ~l1_orders_2(A_72))), inference(reflexivity, [status(thm), theory('equality')], [c_124])).
% 2.58/1.34  tff(c_155, plain, (![A_73]: (u1_struct_0(k3_yellow_6(A_73, '#skF_2', '#skF_3'))=u1_struct_0(A_73) | ~l1_waybel_0(k3_yellow_6(A_73, '#skF_2', '#skF_3'), '#skF_2') | ~v6_waybel_0(k3_yellow_6(A_73, '#skF_2', '#skF_3'), '#skF_2') | ~l1_orders_2(A_73))), inference(resolution, [status(thm)], [c_2, c_147])).
% 2.58/1.34  tff(c_159, plain, (![A_23]: (u1_struct_0(k3_yellow_6(A_23, '#skF_2', '#skF_3'))=u1_struct_0(A_23) | ~l1_waybel_0(k3_yellow_6(A_23, '#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_orders_2(A_23))), inference(resolution, [status(thm)], [c_16, c_155])).
% 2.58/1.34  tff(c_162, plain, (![A_23]: (u1_struct_0(k3_yellow_6(A_23, '#skF_2', '#skF_3'))=u1_struct_0(A_23) | ~l1_waybel_0(k3_yellow_6(A_23, '#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2') | ~l1_orders_2(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_159])).
% 2.58/1.34  tff(c_164, plain, (![A_74]: (u1_struct_0(k3_yellow_6(A_74, '#skF_2', '#skF_3'))=u1_struct_0(A_74) | ~l1_waybel_0(k3_yellow_6(A_74, '#skF_2', '#skF_3'), '#skF_2') | ~l1_orders_2(A_74))), inference(negUnitSimplification, [status(thm)], [c_24, c_162])).
% 2.58/1.34  tff(c_169, plain, (![A_75]: (u1_struct_0(k3_yellow_6(A_75, '#skF_2', '#skF_3'))=u1_struct_0(A_75) | ~l1_orders_2(A_75))), inference(resolution, [status(thm)], [c_44, c_164])).
% 2.58/1.34  tff(c_18, plain, (u1_struct_0(k3_yellow_6('#skF_1', '#skF_2', '#skF_3'))!=u1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.58/1.34  tff(c_211, plain, (~l1_orders_2('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_169, c_18])).
% 2.58/1.34  tff(c_229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_211])).
% 2.58/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.34  
% 2.58/1.34  Inference rules
% 2.58/1.34  ----------------------
% 2.58/1.34  #Ref     : 4
% 2.58/1.34  #Sup     : 50
% 2.58/1.34  #Fact    : 0
% 2.58/1.34  #Define  : 0
% 2.58/1.34  #Split   : 0
% 2.58/1.34  #Chain   : 0
% 2.58/1.34  #Close   : 0
% 2.58/1.34  
% 2.58/1.34  Ordering : KBO
% 2.58/1.34  
% 2.58/1.34  Simplification rules
% 2.58/1.34  ----------------------
% 2.58/1.34  #Subsume      : 6
% 2.58/1.34  #Demod        : 14
% 2.58/1.34  #Tautology    : 10
% 2.58/1.34  #SimpNegUnit  : 7
% 2.58/1.34  #BackRed      : 0
% 2.58/1.34  
% 2.58/1.34  #Partial instantiations: 0
% 2.58/1.34  #Strategies tried      : 1
% 2.58/1.34  
% 2.58/1.34  Timing (in seconds)
% 2.58/1.34  ----------------------
% 2.58/1.34  Preprocessing        : 0.32
% 2.58/1.34  Parsing              : 0.17
% 2.58/1.34  CNF conversion       : 0.03
% 2.58/1.34  Main loop            : 0.25
% 2.58/1.34  Inferencing          : 0.10
% 2.58/1.34  Reduction            : 0.06
% 2.58/1.34  Demodulation         : 0.05
% 2.58/1.34  BG Simplification    : 0.02
% 2.58/1.34  Subsumption          : 0.06
% 2.58/1.34  Abstraction          : 0.01
% 2.58/1.34  MUC search           : 0.00
% 2.58/1.34  Cooper               : 0.00
% 2.58/1.34  Total                : 0.60
% 2.58/1.34  Index Insertion      : 0.00
% 2.58/1.34  Index Deletion       : 0.00
% 2.58/1.34  Index Matching       : 0.00
% 2.58/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
