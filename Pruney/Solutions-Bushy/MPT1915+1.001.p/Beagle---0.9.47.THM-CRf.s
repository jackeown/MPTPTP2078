%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1915+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:41 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   48 (  59 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  104 ( 148 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :   15 (   5 average)
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

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => u1_struct_0(k3_yellow_6(A,B,C)) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_6)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & ~ v2_struct_0(B)
        & l1_struct_0(B)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( v6_waybel_0(k3_yellow_6(A,B,C),B)
        & l1_waybel_0(k3_yellow_6(A,B,C),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_6)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_46,axiom,(
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

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(c_26,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_39,plain,(
    ! [A_42,B_43,C_44] :
      ( l1_waybel_0(k3_yellow_6(A_42,B_43,C_44),B_43)
      | ~ m1_subset_1(C_44,u1_struct_0(B_43))
      | ~ l1_struct_0(B_43)
      | v2_struct_0(B_43)
      | ~ l1_orders_2(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_41,plain,(
    ! [A_42] :
      ( l1_waybel_0(k3_yellow_6(A_42,'#skF_2','#skF_3'),'#skF_2')
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_42) ) ),
    inference(resolution,[status(thm)],[c_20,c_39])).

tff(c_44,plain,(
    ! [A_42] :
      ( l1_waybel_0(k3_yellow_6(A_42,'#skF_2','#skF_3'),'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_41])).

tff(c_45,plain,(
    ! [A_42] :
      ( l1_waybel_0(k3_yellow_6(A_42,'#skF_2','#skF_3'),'#skF_2')
      | ~ l1_orders_2(A_42) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_44])).

tff(c_10,plain,(
    ! [A_16,B_17,C_18] :
      ( v6_waybel_0(k3_yellow_6(A_16,B_17,C_18),B_17)
      | ~ m1_subset_1(C_18,u1_struct_0(B_17))
      | ~ l1_struct_0(B_17)
      | v2_struct_0(B_17)
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_19] :
      ( m1_subset_1(u1_orders_2(A_19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19),u1_struct_0(A_19))))
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_47,plain,(
    ! [A_46,B_47,C_48] :
      ( g1_orders_2(u1_struct_0(k3_yellow_6(A_46,B_47,C_48)),u1_orders_2(k3_yellow_6(A_46,B_47,C_48))) = g1_orders_2(u1_struct_0(A_46),u1_orders_2(A_46))
      | ~ l1_waybel_0(k3_yellow_6(A_46,B_47,C_48),B_47)
      | ~ v6_waybel_0(k3_yellow_6(A_46,B_47,C_48),B_47)
      | ~ m1_subset_1(C_48,u1_struct_0(B_47))
      | ~ l1_struct_0(B_47)
      | v2_struct_0(B_47)
      | ~ l1_orders_2(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    ! [C_24,A_20,D_25,B_21] :
      ( C_24 = A_20
      | g1_orders_2(C_24,D_25) != g1_orders_2(A_20,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_52,plain,(
    ! [A_46,B_47,A_20,B_21,C_48] :
      ( u1_struct_0(k3_yellow_6(A_46,B_47,C_48)) = A_20
      | g1_orders_2(u1_struct_0(A_46),u1_orders_2(A_46)) != g1_orders_2(A_20,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ l1_waybel_0(k3_yellow_6(A_46,B_47,C_48),B_47)
      | ~ v6_waybel_0(k3_yellow_6(A_46,B_47,C_48),B_47)
      | ~ m1_subset_1(C_48,u1_struct_0(B_47))
      | ~ l1_struct_0(B_47)
      | v2_struct_0(B_47)
      | ~ l1_orders_2(A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_16])).

tff(c_72,plain,(
    ! [A_54,B_55,C_56] :
      ( u1_struct_0(k3_yellow_6(A_54,B_55,C_56)) = u1_struct_0(A_54)
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
      ( u1_struct_0(k3_yellow_6(A_57,B_58,C_59)) = u1_struct_0(A_57)
      | ~ l1_waybel_0(k3_yellow_6(A_57,B_58,C_59),B_58)
      | ~ v6_waybel_0(k3_yellow_6(A_57,B_58,C_59),B_58)
      | ~ m1_subset_1(C_59,u1_struct_0(B_58))
      | ~ l1_struct_0(B_58)
      | v2_struct_0(B_58)
      | ~ l1_orders_2(A_57) ) ),
    inference(resolution,[status(thm)],[c_12,c_72])).

tff(c_82,plain,(
    ! [A_63,B_64,C_65] :
      ( u1_struct_0(k3_yellow_6(A_63,B_64,C_65)) = u1_struct_0(A_63)
      | ~ l1_waybel_0(k3_yellow_6(A_63,B_64,C_65),B_64)
      | ~ m1_subset_1(C_65,u1_struct_0(B_64))
      | ~ l1_struct_0(B_64)
      | v2_struct_0(B_64)
      | ~ l1_orders_2(A_63) ) ),
    inference(resolution,[status(thm)],[c_10,c_76])).

tff(c_84,plain,(
    ! [A_42] :
      ( u1_struct_0(k3_yellow_6(A_42,'#skF_2','#skF_3')) = u1_struct_0(A_42)
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_42) ) ),
    inference(resolution,[status(thm)],[c_45,c_82])).

tff(c_87,plain,(
    ! [A_42] :
      ( u1_struct_0(k3_yellow_6(A_42,'#skF_2','#skF_3')) = u1_struct_0(A_42)
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_84])).

tff(c_89,plain,(
    ! [A_66] :
      ( u1_struct_0(k3_yellow_6(A_66,'#skF_2','#skF_3')) = u1_struct_0(A_66)
      | ~ l1_orders_2(A_66) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_87])).

tff(c_18,plain,(
    u1_struct_0(k3_yellow_6('#skF_1','#skF_2','#skF_3')) != u1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_120,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_18])).

tff(c_137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_120])).

%------------------------------------------------------------------------------
