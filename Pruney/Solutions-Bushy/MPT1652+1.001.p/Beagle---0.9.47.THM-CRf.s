%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1652+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:12 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 320 expanded)
%              Number of leaves         :   19 ( 124 expanded)
%              Depth                    :   14
%              Number of atoms          :  275 (1436 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_yellow_0 > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_waybel_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

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

tff(k3_waybel_0,type,(
    k3_waybel_0: ( $i * $i ) > $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

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
           => ( r1_yellow_0(A,B)
            <=> r1_yellow_0(A,k3_waybel_0(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_0)).

tff(f_60,axiom,(
    ! [A] :
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
             => ( r2_lattice3(A,B,C)
              <=> r2_lattice3(A,k3_waybel_0(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_0)).

tff(c_24,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,
    ( ~ r1_yellow_0('#skF_2',k3_waybel_0('#skF_2','#skF_3'))
    | ~ r1_yellow_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_33,plain,(
    ~ r1_yellow_0('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_18,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,
    ( r1_yellow_0('#skF_2','#skF_3')
    | r1_yellow_0('#skF_2',k3_waybel_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,(
    r1_yellow_0('#skF_2',k3_waybel_0('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_32])).

tff(c_22,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [A_8,B_13,C_14] :
      ( m1_subset_1('#skF_1'(A_8,B_13,C_14),u1_struct_0(A_8))
      | r1_yellow_0(A_8,C_14)
      | ~ r1_yellow_0(A_8,B_13)
      | ~ l1_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    ! [A_8,B_13,C_14] :
      ( r2_lattice3(A_8,B_13,'#skF_1'(A_8,B_13,C_14))
      | r2_lattice3(A_8,C_14,'#skF_1'(A_8,B_13,C_14))
      | r1_yellow_0(A_8,C_14)
      | ~ r1_yellow_0(A_8,B_13)
      | ~ l1_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_56,plain,(
    ! [A_26,B_27,C_28] :
      ( r2_lattice3(A_26,B_27,C_28)
      | ~ r2_lattice3(A_26,k3_waybel_0(A_26,B_27),C_28)
      | ~ m1_subset_1(C_28,u1_struct_0(A_26))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_orders_2(A_26)
      | ~ v4_orders_2(A_26)
      | ~ v3_orders_2(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    ! [A_36,B_37,C_38] :
      ( r2_lattice3(A_36,B_37,'#skF_1'(A_36,k3_waybel_0(A_36,B_37),C_38))
      | ~ m1_subset_1('#skF_1'(A_36,k3_waybel_0(A_36,B_37),C_38),u1_struct_0(A_36))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ v4_orders_2(A_36)
      | ~ v3_orders_2(A_36)
      | r2_lattice3(A_36,C_38,'#skF_1'(A_36,k3_waybel_0(A_36,B_37),C_38))
      | r1_yellow_0(A_36,C_38)
      | ~ r1_yellow_0(A_36,k3_waybel_0(A_36,B_37))
      | ~ l1_orders_2(A_36)
      | v2_struct_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_14,c_56])).

tff(c_95,plain,(
    ! [A_8,B_37,C_14] :
      ( r2_lattice3(A_8,B_37,'#skF_1'(A_8,k3_waybel_0(A_8,B_37),C_14))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | r2_lattice3(A_8,C_14,'#skF_1'(A_8,k3_waybel_0(A_8,B_37),C_14))
      | r1_yellow_0(A_8,C_14)
      | ~ r1_yellow_0(A_8,k3_waybel_0(A_8,B_37))
      | ~ l1_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(resolution,[status(thm)],[c_6,c_91])).

tff(c_140,plain,(
    ! [B_37,A_8] :
      ( ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | r1_yellow_0(A_8,B_37)
      | ~ r1_yellow_0(A_8,k3_waybel_0(A_8,B_37))
      | ~ l1_orders_2(A_8)
      | v2_struct_0(A_8)
      | r2_lattice3(A_8,B_37,'#skF_1'(A_8,k3_waybel_0(A_8,B_37),B_37)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_95])).

tff(c_65,plain,(
    ! [A_29,B_30,C_31] :
      ( r2_lattice3(A_29,k3_waybel_0(A_29,B_30),C_31)
      | ~ r2_lattice3(A_29,B_30,C_31)
      | ~ m1_subset_1(C_31,u1_struct_0(A_29))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_orders_2(A_29)
      | ~ v4_orders_2(A_29)
      | ~ v3_orders_2(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_67,plain,(
    ! [C_31] :
      ( r2_lattice3('#skF_2',k3_waybel_0('#skF_2','#skF_3'),C_31)
      | ~ r2_lattice3('#skF_2','#skF_3',C_31)
      | ~ m1_subset_1(C_31,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_65])).

tff(c_70,plain,(
    ! [C_31] :
      ( r2_lattice3('#skF_2',k3_waybel_0('#skF_2','#skF_3'),C_31)
      | ~ r2_lattice3('#skF_2','#skF_3',C_31)
      | ~ m1_subset_1(C_31,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_67])).

tff(c_71,plain,(
    ! [C_31] :
      ( r2_lattice3('#skF_2',k3_waybel_0('#skF_2','#skF_3'),C_31)
      | ~ r2_lattice3('#skF_2','#skF_3',C_31)
      | ~ m1_subset_1(C_31,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_70])).

tff(c_155,plain,(
    ! [B_47,A_48] :
      ( ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ v4_orders_2(A_48)
      | ~ v3_orders_2(A_48)
      | r1_yellow_0(A_48,B_47)
      | ~ r1_yellow_0(A_48,k3_waybel_0(A_48,B_47))
      | ~ l1_orders_2(A_48)
      | v2_struct_0(A_48)
      | r2_lattice3(A_48,B_47,'#skF_1'(A_48,k3_waybel_0(A_48,B_47),B_47)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_95])).

tff(c_8,plain,(
    ! [A_8,C_14,B_13] :
      ( ~ r2_lattice3(A_8,C_14,'#skF_1'(A_8,B_13,C_14))
      | ~ r2_lattice3(A_8,B_13,'#skF_1'(A_8,B_13,C_14))
      | r1_yellow_0(A_8,C_14)
      | ~ r1_yellow_0(A_8,B_13)
      | ~ l1_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_163,plain,(
    ! [A_49,B_50] :
      ( ~ r2_lattice3(A_49,k3_waybel_0(A_49,B_50),'#skF_1'(A_49,k3_waybel_0(A_49,B_50),B_50))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ v4_orders_2(A_49)
      | ~ v3_orders_2(A_49)
      | r1_yellow_0(A_49,B_50)
      | ~ r1_yellow_0(A_49,k3_waybel_0(A_49,B_50))
      | ~ l1_orders_2(A_49)
      | v2_struct_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_155,c_8])).

tff(c_171,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | r1_yellow_0('#skF_2','#skF_3')
    | ~ r1_yellow_0('#skF_2',k3_waybel_0('#skF_2','#skF_3'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ r2_lattice3('#skF_2','#skF_3','#skF_1'('#skF_2',k3_waybel_0('#skF_2','#skF_3'),'#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_2',k3_waybel_0('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_71,c_163])).

tff(c_179,plain,
    ( r1_yellow_0('#skF_2','#skF_3')
    | v2_struct_0('#skF_2')
    | ~ r2_lattice3('#skF_2','#skF_3','#skF_1'('#skF_2',k3_waybel_0('#skF_2','#skF_3'),'#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_2',k3_waybel_0('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_34,c_22,c_20,c_16,c_171])).

tff(c_180,plain,
    ( ~ r2_lattice3('#skF_2','#skF_3','#skF_1'('#skF_2',k3_waybel_0('#skF_2','#skF_3'),'#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_2',k3_waybel_0('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_33,c_179])).

tff(c_182,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2',k3_waybel_0('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_185,plain,
    ( r1_yellow_0('#skF_2','#skF_3')
    | ~ r1_yellow_0('#skF_2',k3_waybel_0('#skF_2','#skF_3'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_182])).

tff(c_188,plain,
    ( r1_yellow_0('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_34,c_185])).

tff(c_190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_33,c_188])).

tff(c_191,plain,(
    ~ r2_lattice3('#skF_2','#skF_3','#skF_1'('#skF_2',k3_waybel_0('#skF_2','#skF_3'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_228,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | r1_yellow_0('#skF_2','#skF_3')
    | ~ r1_yellow_0('#skF_2',k3_waybel_0('#skF_2','#skF_3'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_140,c_191])).

tff(c_234,plain,
    ( r1_yellow_0('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_34,c_22,c_20,c_16,c_228])).

tff(c_236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_33,c_234])).

tff(c_237,plain,(
    ~ r1_yellow_0('#skF_2',k3_waybel_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_238,plain,(
    r1_yellow_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_262,plain,(
    ! [A_63,B_64,C_65] :
      ( r2_lattice3(A_63,B_64,C_65)
      | ~ r2_lattice3(A_63,k3_waybel_0(A_63,B_64),C_65)
      | ~ m1_subset_1(C_65,u1_struct_0(A_63))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_orders_2(A_63)
      | ~ v4_orders_2(A_63)
      | ~ v3_orders_2(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_387,plain,(
    ! [A_84,B_85,B_86] :
      ( r2_lattice3(A_84,B_85,'#skF_1'(A_84,B_86,k3_waybel_0(A_84,B_85)))
      | ~ m1_subset_1('#skF_1'(A_84,B_86,k3_waybel_0(A_84,B_85)),u1_struct_0(A_84))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ v4_orders_2(A_84)
      | ~ v3_orders_2(A_84)
      | r2_lattice3(A_84,B_86,'#skF_1'(A_84,B_86,k3_waybel_0(A_84,B_85)))
      | r1_yellow_0(A_84,k3_waybel_0(A_84,B_85))
      | ~ r1_yellow_0(A_84,B_86)
      | ~ l1_orders_2(A_84)
      | v2_struct_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_14,c_262])).

tff(c_391,plain,(
    ! [A_8,B_85,B_13] :
      ( r2_lattice3(A_8,B_85,'#skF_1'(A_8,B_13,k3_waybel_0(A_8,B_85)))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | r2_lattice3(A_8,B_13,'#skF_1'(A_8,B_13,k3_waybel_0(A_8,B_85)))
      | r1_yellow_0(A_8,k3_waybel_0(A_8,B_85))
      | ~ r1_yellow_0(A_8,B_13)
      | ~ l1_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(resolution,[status(thm)],[c_6,c_387])).

tff(c_404,plain,(
    ! [B_85,A_8] :
      ( ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | r1_yellow_0(A_8,k3_waybel_0(A_8,B_85))
      | ~ r1_yellow_0(A_8,B_85)
      | ~ l1_orders_2(A_8)
      | v2_struct_0(A_8)
      | r2_lattice3(A_8,B_85,'#skF_1'(A_8,B_85,k3_waybel_0(A_8,B_85))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_391])).

tff(c_439,plain,(
    ! [B_90,A_91] :
      ( ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ v4_orders_2(A_91)
      | ~ v3_orders_2(A_91)
      | r1_yellow_0(A_91,k3_waybel_0(A_91,B_90))
      | ~ r1_yellow_0(A_91,B_90)
      | ~ l1_orders_2(A_91)
      | v2_struct_0(A_91)
      | r2_lattice3(A_91,B_90,'#skF_1'(A_91,B_90,k3_waybel_0(A_91,B_90))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_391])).

tff(c_271,plain,(
    ! [A_66,B_67,C_68] :
      ( r2_lattice3(A_66,k3_waybel_0(A_66,B_67),C_68)
      | ~ r2_lattice3(A_66,B_67,C_68)
      | ~ m1_subset_1(C_68,u1_struct_0(A_66))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_orders_2(A_66)
      | ~ v4_orders_2(A_66)
      | ~ v3_orders_2(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_273,plain,(
    ! [C_68] :
      ( r2_lattice3('#skF_2',k3_waybel_0('#skF_2','#skF_3'),C_68)
      | ~ r2_lattice3('#skF_2','#skF_3',C_68)
      | ~ m1_subset_1(C_68,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_271])).

tff(c_276,plain,(
    ! [C_68] :
      ( r2_lattice3('#skF_2',k3_waybel_0('#skF_2','#skF_3'),C_68)
      | ~ r2_lattice3('#skF_2','#skF_3',C_68)
      | ~ m1_subset_1(C_68,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_273])).

tff(c_278,plain,(
    ! [C_69] :
      ( r2_lattice3('#skF_2',k3_waybel_0('#skF_2','#skF_3'),C_69)
      | ~ r2_lattice3('#skF_2','#skF_3',C_69)
      | ~ m1_subset_1(C_69,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_276])).

tff(c_283,plain,(
    ! [B_13] :
      ( ~ r2_lattice3('#skF_2',B_13,'#skF_1'('#skF_2',B_13,k3_waybel_0('#skF_2','#skF_3')))
      | r1_yellow_0('#skF_2',k3_waybel_0('#skF_2','#skF_3'))
      | ~ r1_yellow_0('#skF_2',B_13)
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r2_lattice3('#skF_2','#skF_3','#skF_1'('#skF_2',B_13,k3_waybel_0('#skF_2','#skF_3')))
      | ~ m1_subset_1('#skF_1'('#skF_2',B_13,k3_waybel_0('#skF_2','#skF_3')),u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_278,c_8])).

tff(c_290,plain,(
    ! [B_13] :
      ( ~ r2_lattice3('#skF_2',B_13,'#skF_1'('#skF_2',B_13,k3_waybel_0('#skF_2','#skF_3')))
      | r1_yellow_0('#skF_2',k3_waybel_0('#skF_2','#skF_3'))
      | ~ r1_yellow_0('#skF_2',B_13)
      | v2_struct_0('#skF_2')
      | ~ r2_lattice3('#skF_2','#skF_3','#skF_1'('#skF_2',B_13,k3_waybel_0('#skF_2','#skF_3')))
      | ~ m1_subset_1('#skF_1'('#skF_2',B_13,k3_waybel_0('#skF_2','#skF_3')),u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_283])).

tff(c_291,plain,(
    ! [B_13] :
      ( ~ r2_lattice3('#skF_2',B_13,'#skF_1'('#skF_2',B_13,k3_waybel_0('#skF_2','#skF_3')))
      | ~ r1_yellow_0('#skF_2',B_13)
      | ~ r2_lattice3('#skF_2','#skF_3','#skF_1'('#skF_2',B_13,k3_waybel_0('#skF_2','#skF_3')))
      | ~ m1_subset_1('#skF_1'('#skF_2',B_13,k3_waybel_0('#skF_2','#skF_3')),u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_237,c_290])).

tff(c_446,plain,
    ( ~ r2_lattice3('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3',k3_waybel_0('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3',k3_waybel_0('#skF_2','#skF_3')),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | r1_yellow_0('#skF_2',k3_waybel_0('#skF_2','#skF_3'))
    | ~ r1_yellow_0('#skF_2','#skF_3')
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_439,c_291])).

tff(c_453,plain,
    ( ~ r2_lattice3('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3',k3_waybel_0('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3',k3_waybel_0('#skF_2','#skF_3')),u1_struct_0('#skF_2'))
    | r1_yellow_0('#skF_2',k3_waybel_0('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_238,c_22,c_20,c_16,c_446])).

tff(c_454,plain,
    ( ~ r2_lattice3('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3',k3_waybel_0('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3',k3_waybel_0('#skF_2','#skF_3')),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_237,c_453])).

tff(c_456,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3',k3_waybel_0('#skF_2','#skF_3')),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_454])).

tff(c_459,plain,
    ( r1_yellow_0('#skF_2',k3_waybel_0('#skF_2','#skF_3'))
    | ~ r1_yellow_0('#skF_2','#skF_3')
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_456])).

tff(c_462,plain,
    ( r1_yellow_0('#skF_2',k3_waybel_0('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_238,c_459])).

tff(c_464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_237,c_462])).

tff(c_465,plain,(
    ~ r2_lattice3('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3',k3_waybel_0('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_454])).

tff(c_469,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | r1_yellow_0('#skF_2',k3_waybel_0('#skF_2','#skF_3'))
    | ~ r1_yellow_0('#skF_2','#skF_3')
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_404,c_465])).

tff(c_475,plain,
    ( r1_yellow_0('#skF_2',k3_waybel_0('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_238,c_22,c_20,c_16,c_469])).

tff(c_477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_237,c_475])).

%------------------------------------------------------------------------------
