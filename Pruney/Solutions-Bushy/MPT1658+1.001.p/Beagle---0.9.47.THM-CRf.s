%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1658+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:12 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 158 expanded)
%              Number of leaves         :   20 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  163 ( 699 expanded)
%              Number of equality atoms :   19 (  84 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_lattice3 > r2_yellow_0 > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_waybel_0 > k2_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k4_waybel_0,type,(
    k4_waybel_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_yellow_0(A,B)
             => k2_yellow_0(A,B) = k2_yellow_0(A,k4_waybel_0(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_waybel_0)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B,C] :
          ( ( r2_yellow_0(A,B)
            & ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r1_lattice3(A,B,D)
                <=> r1_lattice3(A,C,D) ) ) )
         => k2_yellow_0(A,B) = k2_yellow_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_yellow_0)).

tff(f_43,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattice3(A,B,C)
              <=> r1_lattice3(A,k4_waybel_0(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_waybel_0)).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    k2_yellow_0('#skF_2',k4_waybel_0('#skF_2','#skF_3')) != k2_yellow_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_18,plain,(
    r2_yellow_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [A_8,B_13,C_14] :
      ( m1_subset_1('#skF_1'(A_8,B_13,C_14),u1_struct_0(A_8))
      | k2_yellow_0(A_8,C_14) = k2_yellow_0(A_8,B_13)
      | ~ r2_yellow_0(A_8,B_13)
      | ~ l1_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    ! [A_8,B_13,C_14] :
      ( r1_lattice3(A_8,B_13,'#skF_1'(A_8,B_13,C_14))
      | r1_lattice3(A_8,C_14,'#skF_1'(A_8,B_13,C_14))
      | k2_yellow_0(A_8,C_14) = k2_yellow_0(A_8,B_13)
      | ~ r2_yellow_0(A_8,B_13)
      | ~ l1_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_67,plain,(
    ! [A_30,B_31,C_32] :
      ( r1_lattice3(A_30,B_31,C_32)
      | ~ r1_lattice3(A_30,k4_waybel_0(A_30,B_31),C_32)
      | ~ m1_subset_1(C_32,u1_struct_0(A_30))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_orders_2(A_30)
      | ~ v4_orders_2(A_30)
      | ~ v3_orders_2(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_96,plain,(
    ! [A_34,B_35,B_36] :
      ( r1_lattice3(A_34,B_35,'#skF_1'(A_34,B_36,k4_waybel_0(A_34,B_35)))
      | ~ m1_subset_1('#skF_1'(A_34,B_36,k4_waybel_0(A_34,B_35)),u1_struct_0(A_34))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ v4_orders_2(A_34)
      | ~ v3_orders_2(A_34)
      | r1_lattice3(A_34,B_36,'#skF_1'(A_34,B_36,k4_waybel_0(A_34,B_35)))
      | k2_yellow_0(A_34,k4_waybel_0(A_34,B_35)) = k2_yellow_0(A_34,B_36)
      | ~ r2_yellow_0(A_34,B_36)
      | ~ l1_orders_2(A_34)
      | v2_struct_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_14,c_67])).

tff(c_100,plain,(
    ! [A_8,B_35,B_13] :
      ( r1_lattice3(A_8,B_35,'#skF_1'(A_8,B_13,k4_waybel_0(A_8,B_35)))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | r1_lattice3(A_8,B_13,'#skF_1'(A_8,B_13,k4_waybel_0(A_8,B_35)))
      | k2_yellow_0(A_8,k4_waybel_0(A_8,B_35)) = k2_yellow_0(A_8,B_13)
      | ~ r2_yellow_0(A_8,B_13)
      | ~ l1_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_118,plain,(
    ! [B_35,A_8] :
      ( ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | k2_yellow_0(A_8,k4_waybel_0(A_8,B_35)) = k2_yellow_0(A_8,B_35)
      | ~ r2_yellow_0(A_8,B_35)
      | ~ l1_orders_2(A_8)
      | v2_struct_0(A_8)
      | r1_lattice3(A_8,B_35,'#skF_1'(A_8,B_35,k4_waybel_0(A_8,B_35))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_100])).

tff(c_142,plain,(
    ! [B_43,A_44] :
      ( ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ v4_orders_2(A_44)
      | ~ v3_orders_2(A_44)
      | k2_yellow_0(A_44,k4_waybel_0(A_44,B_43)) = k2_yellow_0(A_44,B_43)
      | ~ r2_yellow_0(A_44,B_43)
      | ~ l1_orders_2(A_44)
      | v2_struct_0(A_44)
      | r1_lattice3(A_44,B_43,'#skF_1'(A_44,B_43,k4_waybel_0(A_44,B_43))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_100])).

tff(c_52,plain,(
    ! [A_26,B_27,C_28] :
      ( r1_lattice3(A_26,k4_waybel_0(A_26,B_27),C_28)
      | ~ r1_lattice3(A_26,B_27,C_28)
      | ~ m1_subset_1(C_28,u1_struct_0(A_26))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_orders_2(A_26)
      | ~ v4_orders_2(A_26)
      | ~ v3_orders_2(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_54,plain,(
    ! [C_28] :
      ( r1_lattice3('#skF_2',k4_waybel_0('#skF_2','#skF_3'),C_28)
      | ~ r1_lattice3('#skF_2','#skF_3',C_28)
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_52])).

tff(c_57,plain,(
    ! [C_28] :
      ( r1_lattice3('#skF_2',k4_waybel_0('#skF_2','#skF_3'),C_28)
      | ~ r1_lattice3('#skF_2','#skF_3',C_28)
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_54])).

tff(c_59,plain,(
    ! [C_29] :
      ( r1_lattice3('#skF_2',k4_waybel_0('#skF_2','#skF_3'),C_29)
      | ~ r1_lattice3('#skF_2','#skF_3',C_29)
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_57])).

tff(c_8,plain,(
    ! [A_8,C_14,B_13] :
      ( ~ r1_lattice3(A_8,C_14,'#skF_1'(A_8,B_13,C_14))
      | ~ r1_lattice3(A_8,B_13,'#skF_1'(A_8,B_13,C_14))
      | k2_yellow_0(A_8,C_14) = k2_yellow_0(A_8,B_13)
      | ~ r2_yellow_0(A_8,B_13)
      | ~ l1_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_62,plain,(
    ! [B_13] :
      ( ~ r1_lattice3('#skF_2',B_13,'#skF_1'('#skF_2',B_13,k4_waybel_0('#skF_2','#skF_3')))
      | k2_yellow_0('#skF_2',k4_waybel_0('#skF_2','#skF_3')) = k2_yellow_0('#skF_2',B_13)
      | ~ r2_yellow_0('#skF_2',B_13)
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_lattice3('#skF_2','#skF_3','#skF_1'('#skF_2',B_13,k4_waybel_0('#skF_2','#skF_3')))
      | ~ m1_subset_1('#skF_1'('#skF_2',B_13,k4_waybel_0('#skF_2','#skF_3')),u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_59,c_8])).

tff(c_65,plain,(
    ! [B_13] :
      ( ~ r1_lattice3('#skF_2',B_13,'#skF_1'('#skF_2',B_13,k4_waybel_0('#skF_2','#skF_3')))
      | k2_yellow_0('#skF_2',k4_waybel_0('#skF_2','#skF_3')) = k2_yellow_0('#skF_2',B_13)
      | ~ r2_yellow_0('#skF_2',B_13)
      | v2_struct_0('#skF_2')
      | ~ r1_lattice3('#skF_2','#skF_3','#skF_1'('#skF_2',B_13,k4_waybel_0('#skF_2','#skF_3')))
      | ~ m1_subset_1('#skF_1'('#skF_2',B_13,k4_waybel_0('#skF_2','#skF_3')),u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_62])).

tff(c_66,plain,(
    ! [B_13] :
      ( ~ r1_lattice3('#skF_2',B_13,'#skF_1'('#skF_2',B_13,k4_waybel_0('#skF_2','#skF_3')))
      | k2_yellow_0('#skF_2',k4_waybel_0('#skF_2','#skF_3')) = k2_yellow_0('#skF_2',B_13)
      | ~ r2_yellow_0('#skF_2',B_13)
      | ~ r1_lattice3('#skF_2','#skF_3','#skF_1'('#skF_2',B_13,k4_waybel_0('#skF_2','#skF_3')))
      | ~ m1_subset_1('#skF_1'('#skF_2',B_13,k4_waybel_0('#skF_2','#skF_3')),u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_65])).

tff(c_145,plain,
    ( ~ r1_lattice3('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3',k4_waybel_0('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3',k4_waybel_0('#skF_2','#skF_3')),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | k2_yellow_0('#skF_2',k4_waybel_0('#skF_2','#skF_3')) = k2_yellow_0('#skF_2','#skF_3')
    | ~ r2_yellow_0('#skF_2','#skF_3')
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_142,c_66])).

tff(c_151,plain,
    ( ~ r1_lattice3('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3',k4_waybel_0('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3',k4_waybel_0('#skF_2','#skF_3')),u1_struct_0('#skF_2'))
    | k2_yellow_0('#skF_2',k4_waybel_0('#skF_2','#skF_3')) = k2_yellow_0('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_26,c_24,c_20,c_145])).

tff(c_152,plain,
    ( ~ r1_lattice3('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3',k4_waybel_0('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3',k4_waybel_0('#skF_2','#skF_3')),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_16,c_151])).

tff(c_154,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3',k4_waybel_0('#skF_2','#skF_3')),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_157,plain,
    ( k2_yellow_0('#skF_2',k4_waybel_0('#skF_2','#skF_3')) = k2_yellow_0('#skF_2','#skF_3')
    | ~ r2_yellow_0('#skF_2','#skF_3')
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_154])).

tff(c_160,plain,
    ( k2_yellow_0('#skF_2',k4_waybel_0('#skF_2','#skF_3')) = k2_yellow_0('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_157])).

tff(c_162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_16,c_160])).

tff(c_163,plain,(
    ~ r1_lattice3('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3',k4_waybel_0('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_167,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | k2_yellow_0('#skF_2',k4_waybel_0('#skF_2','#skF_3')) = k2_yellow_0('#skF_2','#skF_3')
    | ~ r2_yellow_0('#skF_2','#skF_3')
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_118,c_163])).

tff(c_173,plain,
    ( k2_yellow_0('#skF_2',k4_waybel_0('#skF_2','#skF_3')) = k2_yellow_0('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_26,c_24,c_20,c_167])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_16,c_173])).

%------------------------------------------------------------------------------
