%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1688+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:14 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 276 expanded)
%              Number of leaves         :   26 ( 120 expanded)
%              Depth                    :   10
%              Number of atoms          :  220 (1473 expanded)
%              Number of equality atoms :   12 ( 114 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_orders_3 > v23_waybel_0 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v5_orders_3,type,(
    v5_orders_3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v23_waybel_0,type,(
    v23_waybel_0: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_orders_2(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( v23_waybel_0(C,A,B)
                 => ! [D] :
                      ( ( v1_funct_1(D)
                        & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                     => ( D = k2_funct_1(C)
                       => v23_waybel_0(D,B,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_waybel_0)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ~ ( ~ v2_struct_0(A)
                    & ~ v2_struct_0(B)
                    & ~ ( v23_waybel_0(C,A,B)
                      <=> ( v2_funct_1(C)
                          & v5_orders_3(C,A,B)
                          & ? [D] :
                              ( v1_funct_1(D)
                              & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A))))
                              & D = k2_funct_1(C)
                              & v5_orders_3(D,B,A) ) ) ) )
                & ( ~ ( ~ v2_struct_0(A)
                      & ~ v2_struct_0(B) )
                 => ( v23_waybel_0(C,A,B)
                  <=> ( v2_struct_0(A)
                      & v2_struct_0(B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d38_waybel_0)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_36,plain,(
    ~ v23_waybel_0('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_58,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_42,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_50,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_46,plain,(
    v23_waybel_0('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_38,plain,(
    k2_funct_1('#skF_4') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_294,plain,(
    ! [C_75,A_76,B_77] :
      ( k2_funct_1(C_75) = '#skF_1'(A_76,B_77,C_75)
      | ~ v23_waybel_0(C_75,A_76,B_77)
      | v2_struct_0(B_77)
      | v2_struct_0(A_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_76),u1_struct_0(B_77))))
      | ~ v1_funct_2(C_75,u1_struct_0(A_76),u1_struct_0(B_77))
      | ~ v1_funct_1(C_75)
      | ~ l1_orders_2(B_77)
      | ~ l1_orders_2(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_297,plain,
    ( k2_funct_1('#skF_4') = '#skF_1'('#skF_2','#skF_3','#skF_4')
    | ~ v23_waybel_0('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_orders_2('#skF_3')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_294])).

tff(c_303,plain,
    ( '#skF_1'('#skF_2','#skF_3','#skF_4') = '#skF_5'
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_50,c_46,c_38,c_297])).

tff(c_304,plain,(
    '#skF_1'('#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_303])).

tff(c_315,plain,(
    ! [A_78,B_79,C_80] :
      ( v5_orders_3('#skF_1'(A_78,B_79,C_80),B_79,A_78)
      | ~ v23_waybel_0(C_80,A_78,B_79)
      | v2_struct_0(B_79)
      | v2_struct_0(A_78)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_78),u1_struct_0(B_79))))
      | ~ v1_funct_2(C_80,u1_struct_0(A_78),u1_struct_0(B_79))
      | ~ v1_funct_1(C_80)
      | ~ l1_orders_2(B_79)
      | ~ l1_orders_2(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_317,plain,
    ( v5_orders_3('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3','#skF_2')
    | ~ v23_waybel_0('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_orders_2('#skF_3')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_315])).

tff(c_322,plain,
    ( v5_orders_3('#skF_5','#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_50,c_46,c_304,c_317])).

tff(c_323,plain,(
    v5_orders_3('#skF_5','#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_322])).

tff(c_264,plain,(
    ! [C_69,A_70,B_71] :
      ( v5_orders_3(C_69,A_70,B_71)
      | ~ v23_waybel_0(C_69,A_70,B_71)
      | v2_struct_0(B_71)
      | v2_struct_0(A_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_70),u1_struct_0(B_71))))
      | ~ v1_funct_2(C_69,u1_struct_0(A_70),u1_struct_0(B_71))
      | ~ v1_funct_1(C_69)
      | ~ l1_orders_2(B_71)
      | ~ l1_orders_2(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_267,plain,
    ( v5_orders_3('#skF_4','#skF_2','#skF_3')
    | ~ v23_waybel_0('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_orders_2('#skF_3')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_264])).

tff(c_273,plain,
    ( v5_orders_3('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_50,c_46,c_267])).

tff(c_274,plain,(
    v5_orders_3('#skF_4','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_273])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_65,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_72,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_65])).

tff(c_74,plain,(
    ! [A_42] :
      ( v2_funct_1(k2_funct_1(A_42))
      | ~ v2_funct_1(A_42)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_77,plain,
    ( v2_funct_1('#skF_5')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_74])).

tff(c_79,plain,
    ( v2_funct_1('#skF_5')
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_52,c_77])).

tff(c_80,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_150,plain,(
    ! [C_53,A_54,B_55] :
      ( v2_funct_1(C_53)
      | ~ v23_waybel_0(C_53,A_54,B_55)
      | v2_struct_0(B_55)
      | v2_struct_0(A_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_54),u1_struct_0(B_55))))
      | ~ v1_funct_2(C_53,u1_struct_0(A_54),u1_struct_0(B_55))
      | ~ v1_funct_1(C_53)
      | ~ l1_orders_2(B_55)
      | ~ l1_orders_2(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_153,plain,
    ( v2_funct_1('#skF_4')
    | ~ v23_waybel_0('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_orders_2('#skF_3')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_150])).

tff(c_159,plain,
    ( v2_funct_1('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_50,c_46,c_153])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_80,c_159])).

tff(c_162,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_163,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_164,plain,(
    ! [A_56] :
      ( k2_funct_1(k2_funct_1(A_56)) = A_56
      | ~ v2_funct_1(A_56)
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_182,plain,
    ( k2_funct_1('#skF_5') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_164])).

tff(c_188,plain,
    ( k2_funct_1('#skF_5') = '#skF_4'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_52,c_182])).

tff(c_190,plain,(
    k2_funct_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_188])).

tff(c_417,plain,(
    ! [C_96,A_97,B_98] :
      ( v23_waybel_0(C_96,A_97,B_98)
      | ~ v5_orders_3(k2_funct_1(C_96),B_98,A_97)
      | ~ m1_subset_1(k2_funct_1(C_96),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_98),u1_struct_0(A_97))))
      | ~ v1_funct_2(k2_funct_1(C_96),u1_struct_0(B_98),u1_struct_0(A_97))
      | ~ v1_funct_1(k2_funct_1(C_96))
      | ~ v5_orders_3(C_96,A_97,B_98)
      | ~ v2_funct_1(C_96)
      | v2_struct_0(B_98)
      | v2_struct_0(A_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_97),u1_struct_0(B_98))))
      | ~ v1_funct_2(C_96,u1_struct_0(A_97),u1_struct_0(B_98))
      | ~ v1_funct_1(C_96)
      | ~ l1_orders_2(B_98)
      | ~ l1_orders_2(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_420,plain,(
    ! [A_97,B_98] :
      ( v23_waybel_0('#skF_5',A_97,B_98)
      | ~ v5_orders_3(k2_funct_1('#skF_5'),B_98,A_97)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_98),u1_struct_0(A_97))))
      | ~ v1_funct_2(k2_funct_1('#skF_5'),u1_struct_0(B_98),u1_struct_0(A_97))
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v5_orders_3('#skF_5',A_97,B_98)
      | ~ v2_funct_1('#skF_5')
      | v2_struct_0(B_98)
      | v2_struct_0(A_97)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_97),u1_struct_0(B_98))))
      | ~ v1_funct_2('#skF_5',u1_struct_0(A_97),u1_struct_0(B_98))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_orders_2(B_98)
      | ~ l1_orders_2(A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_417])).

tff(c_439,plain,(
    ! [A_101,B_102] :
      ( v23_waybel_0('#skF_5',A_101,B_102)
      | ~ v5_orders_3('#skF_4',B_102,A_101)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_102),u1_struct_0(A_101))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(B_102),u1_struct_0(A_101))
      | ~ v5_orders_3('#skF_5',A_101,B_102)
      | v2_struct_0(B_102)
      | v2_struct_0(A_101)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_101),u1_struct_0(B_102))))
      | ~ v1_funct_2('#skF_5',u1_struct_0(A_101),u1_struct_0(B_102))
      | ~ l1_orders_2(B_102)
      | ~ l1_orders_2(A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_162,c_52,c_190,c_190,c_190,c_420])).

tff(c_442,plain,
    ( v23_waybel_0('#skF_5','#skF_3','#skF_2')
    | ~ v5_orders_3('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v5_orders_3('#skF_5','#skF_3','#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_439])).

tff(c_445,plain,
    ( v23_waybel_0('#skF_5','#skF_3','#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58,c_42,c_323,c_50,c_48,c_274,c_442])).

tff(c_447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_60,c_36,c_445])).

%------------------------------------------------------------------------------
