%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:17 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 858 expanded)
%              Number of leaves         :   37 ( 306 expanded)
%              Depth                    :   20
%              Number of atoms          :  282 (2921 expanded)
%              Number of equality atoms :   49 ( 440 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v14_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k6_lattices > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(k6_lattices,type,(
    k6_lattices: $i > $i )).

tff(k3_lattices,type,(
    k3_lattices: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v14_lattices,type,(
    v14_lattices: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_166,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v14_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k3_lattices(A,k6_lattices(A),B) = k6_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_lattices)).

tff(f_47,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v4_lattices(A)
          & v5_lattices(A)
          & v6_lattices(A)
          & v7_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_88,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k3_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => m1_subset_1(k6_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v8_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k1_lattices(A,k2_lattices(A,B,C),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

tff(f_151,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v14_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k4_lattices(A,k6_lattices(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattices)).

tff(f_137,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => r1_lattices(A,k4_lattices(A,B,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattices)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(f_120,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k2_lattices(A,B,C) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_46,plain,(
    l3_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_50,plain,(
    v10_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_58,plain,(
    ! [A_40] :
      ( l2_lattices(A_40)
      | ~ l3_lattices(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_62,plain,(
    l2_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_58])).

tff(c_102,plain,(
    ! [A_54,C_55,B_56] :
      ( k3_lattices(A_54,C_55,B_56) = k3_lattices(A_54,B_56,C_55)
      | ~ m1_subset_1(C_55,u1_struct_0(A_54))
      | ~ m1_subset_1(B_56,u1_struct_0(A_54))
      | ~ l2_lattices(A_54)
      | ~ v4_lattices(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_110,plain,(
    ! [B_56] :
      ( k3_lattices('#skF_3',B_56,'#skF_4') = k3_lattices('#skF_3','#skF_4',B_56)
      | ~ m1_subset_1(B_56,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_102])).

tff(c_116,plain,(
    ! [B_56] :
      ( k3_lattices('#skF_3',B_56,'#skF_4') = k3_lattices('#skF_3','#skF_4',B_56)
      | ~ m1_subset_1(B_56,u1_struct_0('#skF_3'))
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_110])).

tff(c_117,plain,(
    ! [B_56] :
      ( k3_lattices('#skF_3',B_56,'#skF_4') = k3_lattices('#skF_3','#skF_4',B_56)
      | ~ m1_subset_1(B_56,u1_struct_0('#skF_3'))
      | ~ v4_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_116])).

tff(c_118,plain,(
    ~ v4_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_137,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_118])).

tff(c_140,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_137])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_140])).

tff(c_144,plain,(
    v4_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_26,plain,(
    ! [A_16] :
      ( m1_subset_1(k6_lattices(A_16),u1_struct_0(A_16))
      | ~ l2_lattices(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_5] :
      ( m1_subset_1('#skF_2'(A_5),u1_struct_0(A_5))
      | v8_lattices(A_5)
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_145,plain,(
    ! [B_60] :
      ( k3_lattices('#skF_3',B_60,'#skF_4') = k3_lattices('#skF_3','#skF_4',B_60)
      | ~ m1_subset_1(B_60,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_153,plain,
    ( k3_lattices('#skF_3','#skF_2'('#skF_3'),'#skF_4') = k3_lattices('#skF_3','#skF_4','#skF_2'('#skF_3'))
    | v8_lattices('#skF_3')
    | ~ l3_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_145])).

tff(c_167,plain,
    ( k3_lattices('#skF_3','#skF_2'('#skF_3'),'#skF_4') = k3_lattices('#skF_3','#skF_4','#skF_2'('#skF_3'))
    | v8_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_153])).

tff(c_168,plain,
    ( k3_lattices('#skF_3','#skF_2'('#skF_3'),'#skF_4') = k3_lattices('#skF_3','#skF_4','#skF_2'('#skF_3'))
    | v8_lattices('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_167])).

tff(c_180,plain,(
    v8_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_48,plain,(
    v14_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_73,plain,(
    ! [A_51,B_52] :
      ( k4_lattices(A_51,k6_lattices(A_51),B_52) = B_52
      | ~ m1_subset_1(B_52,u1_struct_0(A_51))
      | ~ l3_lattices(A_51)
      | ~ v14_lattices(A_51)
      | ~ v10_lattices(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_81,plain,
    ( k4_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') = '#skF_4'
    | ~ l3_lattices('#skF_3')
    | ~ v14_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_73])).

tff(c_87,plain,
    ( k4_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_81])).

tff(c_88,plain,(
    k4_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_87])).

tff(c_311,plain,(
    ! [A_71,B_72,C_73] :
      ( r1_lattices(A_71,k4_lattices(A_71,B_72,C_73),B_72)
      | ~ m1_subset_1(C_73,u1_struct_0(A_71))
      | ~ m1_subset_1(B_72,u1_struct_0(A_71))
      | ~ l3_lattices(A_71)
      | ~ v8_lattices(A_71)
      | ~ v6_lattices(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_317,plain,
    ( r1_lattices('#skF_3','#skF_4',k6_lattices('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k6_lattices('#skF_3'),u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_311])).

tff(c_319,plain,
    ( r1_lattices('#skF_3','#skF_4',k6_lattices('#skF_3'))
    | ~ m1_subset_1(k6_lattices('#skF_3'),u1_struct_0('#skF_3'))
    | ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_46,c_44,c_317])).

tff(c_320,plain,
    ( r1_lattices('#skF_3','#skF_4',k6_lattices('#skF_3'))
    | ~ m1_subset_1(k6_lattices('#skF_3'),u1_struct_0('#skF_3'))
    | ~ v6_lattices('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_319])).

tff(c_321,plain,(
    ~ v6_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_320])).

tff(c_324,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_321])).

tff(c_327,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_324])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_327])).

tff(c_330,plain,
    ( ~ m1_subset_1(k6_lattices('#skF_3'),u1_struct_0('#skF_3'))
    | r1_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_320])).

tff(c_332,plain,(
    ~ m1_subset_1(k6_lattices('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_330])).

tff(c_335,plain,
    ( ~ l2_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_332])).

tff(c_338,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_335])).

tff(c_340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_338])).

tff(c_342,plain,(
    m1_subset_1(k6_lattices('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_32,plain,(
    ! [A_18,B_19,C_20] :
      ( k3_lattices(A_18,B_19,C_20) = k1_lattices(A_18,B_19,C_20)
      | ~ m1_subset_1(C_20,u1_struct_0(A_18))
      | ~ m1_subset_1(B_19,u1_struct_0(A_18))
      | ~ l2_lattices(A_18)
      | ~ v4_lattices(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_347,plain,(
    ! [B_19] :
      ( k3_lattices('#skF_3',B_19,k6_lattices('#skF_3')) = k1_lattices('#skF_3',B_19,k6_lattices('#skF_3'))
      | ~ m1_subset_1(B_19,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_342,c_32])).

tff(c_366,plain,(
    ! [B_19] :
      ( k3_lattices('#skF_3',B_19,k6_lattices('#skF_3')) = k1_lattices('#skF_3',B_19,k6_lattices('#skF_3'))
      | ~ m1_subset_1(B_19,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_62,c_347])).

tff(c_486,plain,(
    ! [B_78] :
      ( k3_lattices('#skF_3',B_78,k6_lattices('#skF_3')) = k1_lattices('#skF_3',B_78,k6_lattices('#skF_3'))
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_366])).

tff(c_518,plain,(
    k3_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) = k1_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_486])).

tff(c_157,plain,
    ( k3_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') = k3_lattices('#skF_3','#skF_4',k6_lattices('#skF_3'))
    | ~ l2_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_145])).

tff(c_171,plain,
    ( k3_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') = k3_lattices('#skF_3','#skF_4',k6_lattices('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_157])).

tff(c_172,plain,(
    k3_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') = k3_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_171])).

tff(c_252,plain,(
    ! [A_67,B_68,C_69] :
      ( k3_lattices(A_67,B_68,C_69) = k1_lattices(A_67,B_68,C_69)
      | ~ m1_subset_1(C_69,u1_struct_0(A_67))
      | ~ m1_subset_1(B_68,u1_struct_0(A_67))
      | ~ l2_lattices(A_67)
      | ~ v4_lattices(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_260,plain,(
    ! [B_68] :
      ( k3_lattices('#skF_3',B_68,'#skF_4') = k1_lattices('#skF_3',B_68,'#skF_4')
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_252])).

tff(c_266,plain,(
    ! [B_68] :
      ( k3_lattices('#skF_3',B_68,'#skF_4') = k1_lattices('#skF_3',B_68,'#skF_4')
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_62,c_260])).

tff(c_268,plain,(
    ! [B_70] :
      ( k3_lattices('#skF_3',B_70,'#skF_4') = k1_lattices('#skF_3',B_70,'#skF_4')
      | ~ m1_subset_1(B_70,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_266])).

tff(c_280,plain,
    ( k3_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') = k1_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4')
    | ~ l2_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_268])).

tff(c_294,plain,
    ( k3_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) = k1_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_172,c_280])).

tff(c_295,plain,(
    k3_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) = k1_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_294])).

tff(c_519,plain,(
    k1_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') = k1_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_295])).

tff(c_42,plain,(
    k3_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') != k6_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_175,plain,(
    k3_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) != k6_lattices('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_42])).

tff(c_301,plain,(
    k1_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') != k6_lattices('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_175])).

tff(c_525,plain,(
    k1_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) != k6_lattices('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_301])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_341,plain,(
    r1_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_413,plain,(
    ! [A_74,B_75,C_76] :
      ( k2_lattices(A_74,B_75,C_76) = B_75
      | ~ r1_lattices(A_74,B_75,C_76)
      | ~ m1_subset_1(C_76,u1_struct_0(A_74))
      | ~ m1_subset_1(B_75,u1_struct_0(A_74))
      | ~ l3_lattices(A_74)
      | ~ v9_lattices(A_74)
      | ~ v8_lattices(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_417,plain,
    ( k2_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) = '#skF_4'
    | ~ m1_subset_1(k6_lattices('#skF_3'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v9_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_341,c_413])).

tff(c_426,plain,
    ( k2_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) = '#skF_4'
    | ~ v9_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_46,c_44,c_342,c_417])).

tff(c_427,plain,
    ( k2_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) = '#skF_4'
    | ~ v9_lattices('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_426])).

tff(c_429,plain,(
    ~ v9_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_427])).

tff(c_432,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_429])).

tff(c_435,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_432])).

tff(c_437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_435])).

tff(c_438,plain,(
    k2_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_427])).

tff(c_18,plain,(
    ! [A_5,B_12,C_14] :
      ( k1_lattices(A_5,k2_lattices(A_5,B_12,C_14),C_14) = C_14
      | ~ m1_subset_1(C_14,u1_struct_0(A_5))
      | ~ m1_subset_1(B_12,u1_struct_0(A_5))
      | ~ v8_lattices(A_5)
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_352,plain,(
    ! [B_12] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_12,k6_lattices('#skF_3')),k6_lattices('#skF_3')) = k6_lattices('#skF_3')
      | ~ m1_subset_1(B_12,u1_struct_0('#skF_3'))
      | ~ v8_lattices('#skF_3')
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_342,c_18])).

tff(c_372,plain,(
    ! [B_12] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_12,k6_lattices('#skF_3')),k6_lattices('#skF_3')) = k6_lattices('#skF_3')
      | ~ m1_subset_1(B_12,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_180,c_352])).

tff(c_618,plain,(
    ! [B_85] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_85,k6_lattices('#skF_3')),k6_lattices('#skF_3')) = k6_lattices('#skF_3')
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_372])).

tff(c_627,plain,
    ( k1_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) = k6_lattices('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_618])).

tff(c_634,plain,(
    k1_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) = k6_lattices('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_627])).

tff(c_636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_525,c_634])).

tff(c_638,plain,(
    ~ v8_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_641,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_638])).

tff(c_644,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_641])).

tff(c_646,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_644])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.50  
% 3.04/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.50  %$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v14_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k6_lattices > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 3.04/1.50  
% 3.04/1.50  %Foreground sorts:
% 3.04/1.50  
% 3.04/1.50  
% 3.04/1.50  %Background operators:
% 3.04/1.50  
% 3.04/1.50  
% 3.04/1.50  %Foreground operators:
% 3.04/1.50  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.04/1.50  tff(k6_lattices, type, k6_lattices: $i > $i).
% 3.04/1.50  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 3.04/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.04/1.50  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 3.04/1.50  tff(l2_lattices, type, l2_lattices: $i > $o).
% 3.04/1.50  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.04/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.50  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 3.04/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.04/1.50  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 3.04/1.50  tff(l1_lattices, type, l1_lattices: $i > $o).
% 3.04/1.50  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 3.04/1.50  tff(v4_lattices, type, v4_lattices: $i > $o).
% 3.04/1.50  tff(v6_lattices, type, v6_lattices: $i > $o).
% 3.04/1.50  tff(v9_lattices, type, v9_lattices: $i > $o).
% 3.04/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.04/1.50  tff(v5_lattices, type, v5_lattices: $i > $o).
% 3.04/1.50  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.04/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.50  tff(v14_lattices, type, v14_lattices: $i > $o).
% 3.04/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.04/1.50  tff(v8_lattices, type, v8_lattices: $i > $o).
% 3.04/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.04/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.04/1.50  tff(v7_lattices, type, v7_lattices: $i > $o).
% 3.04/1.50  
% 3.20/1.53  tff(f_166, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v14_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_lattices(A, k6_lattices(A), B) = k6_lattices(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_lattices)).
% 3.20/1.53  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 3.20/1.53  tff(f_88, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 3.20/1.53  tff(f_60, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k3_lattices(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 3.20/1.53  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => m1_subset_1(k6_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_lattices)).
% 3.20/1.53  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v8_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k1_lattices(A, k2_lattices(A, B, C), C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattices)).
% 3.20/1.53  tff(f_151, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v14_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattices(A, k6_lattices(A), B) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_lattices)).
% 3.20/1.53  tff(f_137, axiom, (![A]: ((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => r1_lattices(A, k4_lattices(A, B, C), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_lattices)).
% 3.20/1.53  tff(f_101, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 3.20/1.53  tff(f_120, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 3.20/1.53  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.20/1.53  tff(c_46, plain, (l3_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.20/1.53  tff(c_50, plain, (v10_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.20/1.53  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.20/1.53  tff(c_44, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.20/1.53  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.20/1.53  tff(c_58, plain, (![A_40]: (l2_lattices(A_40) | ~l3_lattices(A_40))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.20/1.53  tff(c_62, plain, (l2_lattices('#skF_3')), inference(resolution, [status(thm)], [c_46, c_58])).
% 3.20/1.53  tff(c_102, plain, (![A_54, C_55, B_56]: (k3_lattices(A_54, C_55, B_56)=k3_lattices(A_54, B_56, C_55) | ~m1_subset_1(C_55, u1_struct_0(A_54)) | ~m1_subset_1(B_56, u1_struct_0(A_54)) | ~l2_lattices(A_54) | ~v4_lattices(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.20/1.53  tff(c_110, plain, (![B_56]: (k3_lattices('#skF_3', B_56, '#skF_4')=k3_lattices('#skF_3', '#skF_4', B_56) | ~m1_subset_1(B_56, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_102])).
% 3.20/1.53  tff(c_116, plain, (![B_56]: (k3_lattices('#skF_3', B_56, '#skF_4')=k3_lattices('#skF_3', '#skF_4', B_56) | ~m1_subset_1(B_56, u1_struct_0('#skF_3')) | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_110])).
% 3.20/1.53  tff(c_117, plain, (![B_56]: (k3_lattices('#skF_3', B_56, '#skF_4')=k3_lattices('#skF_3', '#skF_4', B_56) | ~m1_subset_1(B_56, u1_struct_0('#skF_3')) | ~v4_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_116])).
% 3.20/1.53  tff(c_118, plain, (~v4_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_117])).
% 3.20/1.53  tff(c_137, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_12, c_118])).
% 3.20/1.53  tff(c_140, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_137])).
% 3.20/1.53  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_140])).
% 3.20/1.53  tff(c_144, plain, (v4_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_117])).
% 3.20/1.53  tff(c_26, plain, (![A_16]: (m1_subset_1(k6_lattices(A_16), u1_struct_0(A_16)) | ~l2_lattices(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.20/1.53  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.20/1.53  tff(c_22, plain, (![A_5]: (m1_subset_1('#skF_2'(A_5), u1_struct_0(A_5)) | v8_lattices(A_5) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.20/1.53  tff(c_145, plain, (![B_60]: (k3_lattices('#skF_3', B_60, '#skF_4')=k3_lattices('#skF_3', '#skF_4', B_60) | ~m1_subset_1(B_60, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_117])).
% 3.20/1.53  tff(c_153, plain, (k3_lattices('#skF_3', '#skF_2'('#skF_3'), '#skF_4')=k3_lattices('#skF_3', '#skF_4', '#skF_2'('#skF_3')) | v8_lattices('#skF_3') | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_145])).
% 3.20/1.53  tff(c_167, plain, (k3_lattices('#skF_3', '#skF_2'('#skF_3'), '#skF_4')=k3_lattices('#skF_3', '#skF_4', '#skF_2'('#skF_3')) | v8_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_153])).
% 3.20/1.53  tff(c_168, plain, (k3_lattices('#skF_3', '#skF_2'('#skF_3'), '#skF_4')=k3_lattices('#skF_3', '#skF_4', '#skF_2'('#skF_3')) | v8_lattices('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_167])).
% 3.20/1.53  tff(c_180, plain, (v8_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_168])).
% 3.20/1.53  tff(c_48, plain, (v14_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.20/1.53  tff(c_73, plain, (![A_51, B_52]: (k4_lattices(A_51, k6_lattices(A_51), B_52)=B_52 | ~m1_subset_1(B_52, u1_struct_0(A_51)) | ~l3_lattices(A_51) | ~v14_lattices(A_51) | ~v10_lattices(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.20/1.53  tff(c_81, plain, (k4_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')='#skF_4' | ~l3_lattices('#skF_3') | ~v14_lattices('#skF_3') | ~v10_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_73])).
% 3.20/1.53  tff(c_87, plain, (k4_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_81])).
% 3.20/1.53  tff(c_88, plain, (k4_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_87])).
% 3.20/1.53  tff(c_311, plain, (![A_71, B_72, C_73]: (r1_lattices(A_71, k4_lattices(A_71, B_72, C_73), B_72) | ~m1_subset_1(C_73, u1_struct_0(A_71)) | ~m1_subset_1(B_72, u1_struct_0(A_71)) | ~l3_lattices(A_71) | ~v8_lattices(A_71) | ~v6_lattices(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.20/1.53  tff(c_317, plain, (r1_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(k6_lattices('#skF_3'), u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_88, c_311])).
% 3.20/1.53  tff(c_319, plain, (r1_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3')) | ~m1_subset_1(k6_lattices('#skF_3'), u1_struct_0('#skF_3')) | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_46, c_44, c_317])).
% 3.20/1.53  tff(c_320, plain, (r1_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3')) | ~m1_subset_1(k6_lattices('#skF_3'), u1_struct_0('#skF_3')) | ~v6_lattices('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_319])).
% 3.20/1.53  tff(c_321, plain, (~v6_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_320])).
% 3.20/1.53  tff(c_324, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_8, c_321])).
% 3.20/1.53  tff(c_327, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_324])).
% 3.20/1.53  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_327])).
% 3.20/1.53  tff(c_330, plain, (~m1_subset_1(k6_lattices('#skF_3'), u1_struct_0('#skF_3')) | r1_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))), inference(splitRight, [status(thm)], [c_320])).
% 3.20/1.53  tff(c_332, plain, (~m1_subset_1(k6_lattices('#skF_3'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_330])).
% 3.20/1.53  tff(c_335, plain, (~l2_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_26, c_332])).
% 3.20/1.53  tff(c_338, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_335])).
% 3.20/1.53  tff(c_340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_338])).
% 3.20/1.53  tff(c_342, plain, (m1_subset_1(k6_lattices('#skF_3'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_330])).
% 3.20/1.53  tff(c_32, plain, (![A_18, B_19, C_20]: (k3_lattices(A_18, B_19, C_20)=k1_lattices(A_18, B_19, C_20) | ~m1_subset_1(C_20, u1_struct_0(A_18)) | ~m1_subset_1(B_19, u1_struct_0(A_18)) | ~l2_lattices(A_18) | ~v4_lattices(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.20/1.53  tff(c_347, plain, (![B_19]: (k3_lattices('#skF_3', B_19, k6_lattices('#skF_3'))=k1_lattices('#skF_3', B_19, k6_lattices('#skF_3')) | ~m1_subset_1(B_19, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_342, c_32])).
% 3.20/1.53  tff(c_366, plain, (![B_19]: (k3_lattices('#skF_3', B_19, k6_lattices('#skF_3'))=k1_lattices('#skF_3', B_19, k6_lattices('#skF_3')) | ~m1_subset_1(B_19, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_62, c_347])).
% 3.20/1.53  tff(c_486, plain, (![B_78]: (k3_lattices('#skF_3', B_78, k6_lattices('#skF_3'))=k1_lattices('#skF_3', B_78, k6_lattices('#skF_3')) | ~m1_subset_1(B_78, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_366])).
% 3.20/1.53  tff(c_518, plain, (k3_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))=k1_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_486])).
% 3.20/1.53  tff(c_157, plain, (k3_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')=k3_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3')) | ~l2_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_26, c_145])).
% 3.20/1.53  tff(c_171, plain, (k3_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')=k3_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_157])).
% 3.20/1.53  tff(c_172, plain, (k3_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')=k3_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_171])).
% 3.20/1.53  tff(c_252, plain, (![A_67, B_68, C_69]: (k3_lattices(A_67, B_68, C_69)=k1_lattices(A_67, B_68, C_69) | ~m1_subset_1(C_69, u1_struct_0(A_67)) | ~m1_subset_1(B_68, u1_struct_0(A_67)) | ~l2_lattices(A_67) | ~v4_lattices(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.20/1.53  tff(c_260, plain, (![B_68]: (k3_lattices('#skF_3', B_68, '#skF_4')=k1_lattices('#skF_3', B_68, '#skF_4') | ~m1_subset_1(B_68, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_252])).
% 3.20/1.53  tff(c_266, plain, (![B_68]: (k3_lattices('#skF_3', B_68, '#skF_4')=k1_lattices('#skF_3', B_68, '#skF_4') | ~m1_subset_1(B_68, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_62, c_260])).
% 3.20/1.53  tff(c_268, plain, (![B_70]: (k3_lattices('#skF_3', B_70, '#skF_4')=k1_lattices('#skF_3', B_70, '#skF_4') | ~m1_subset_1(B_70, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_266])).
% 3.20/1.53  tff(c_280, plain, (k3_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')=k1_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4') | ~l2_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_26, c_268])).
% 3.20/1.53  tff(c_294, plain, (k3_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))=k1_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_172, c_280])).
% 3.20/1.53  tff(c_295, plain, (k3_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))=k1_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_294])).
% 3.20/1.53  tff(c_519, plain, (k1_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')=k1_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_518, c_295])).
% 3.20/1.53  tff(c_42, plain, (k3_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')!=k6_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.20/1.53  tff(c_175, plain, (k3_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))!=k6_lattices('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_42])).
% 3.20/1.53  tff(c_301, plain, (k1_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')!=k6_lattices('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_295, c_175])).
% 3.20/1.53  tff(c_525, plain, (k1_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))!=k6_lattices('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_519, c_301])).
% 3.20/1.53  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.20/1.53  tff(c_341, plain, (r1_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))), inference(splitRight, [status(thm)], [c_330])).
% 3.20/1.53  tff(c_413, plain, (![A_74, B_75, C_76]: (k2_lattices(A_74, B_75, C_76)=B_75 | ~r1_lattices(A_74, B_75, C_76) | ~m1_subset_1(C_76, u1_struct_0(A_74)) | ~m1_subset_1(B_75, u1_struct_0(A_74)) | ~l3_lattices(A_74) | ~v9_lattices(A_74) | ~v8_lattices(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.20/1.53  tff(c_417, plain, (k2_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))='#skF_4' | ~m1_subset_1(k6_lattices('#skF_3'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_341, c_413])).
% 3.20/1.53  tff(c_426, plain, (k2_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))='#skF_4' | ~v9_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_46, c_44, c_342, c_417])).
% 3.20/1.53  tff(c_427, plain, (k2_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))='#skF_4' | ~v9_lattices('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_426])).
% 3.20/1.53  tff(c_429, plain, (~v9_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_427])).
% 3.20/1.53  tff(c_432, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_2, c_429])).
% 3.20/1.53  tff(c_435, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_432])).
% 3.20/1.53  tff(c_437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_435])).
% 3.20/1.53  tff(c_438, plain, (k2_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))='#skF_4'), inference(splitRight, [status(thm)], [c_427])).
% 3.20/1.53  tff(c_18, plain, (![A_5, B_12, C_14]: (k1_lattices(A_5, k2_lattices(A_5, B_12, C_14), C_14)=C_14 | ~m1_subset_1(C_14, u1_struct_0(A_5)) | ~m1_subset_1(B_12, u1_struct_0(A_5)) | ~v8_lattices(A_5) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.20/1.53  tff(c_352, plain, (![B_12]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_12, k6_lattices('#skF_3')), k6_lattices('#skF_3'))=k6_lattices('#skF_3') | ~m1_subset_1(B_12, u1_struct_0('#skF_3')) | ~v8_lattices('#skF_3') | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_342, c_18])).
% 3.20/1.53  tff(c_372, plain, (![B_12]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_12, k6_lattices('#skF_3')), k6_lattices('#skF_3'))=k6_lattices('#skF_3') | ~m1_subset_1(B_12, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_180, c_352])).
% 3.20/1.53  tff(c_618, plain, (![B_85]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_85, k6_lattices('#skF_3')), k6_lattices('#skF_3'))=k6_lattices('#skF_3') | ~m1_subset_1(B_85, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_372])).
% 3.20/1.53  tff(c_627, plain, (k1_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))=k6_lattices('#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_438, c_618])).
% 3.20/1.53  tff(c_634, plain, (k1_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))=k6_lattices('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_627])).
% 3.20/1.53  tff(c_636, plain, $false, inference(negUnitSimplification, [status(thm)], [c_525, c_634])).
% 3.20/1.53  tff(c_638, plain, (~v8_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_168])).
% 3.20/1.53  tff(c_641, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_4, c_638])).
% 3.20/1.53  tff(c_644, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_641])).
% 3.20/1.53  tff(c_646, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_644])).
% 3.20/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.53  
% 3.20/1.53  Inference rules
% 3.20/1.53  ----------------------
% 3.20/1.53  #Ref     : 0
% 3.20/1.53  #Sup     : 118
% 3.20/1.53  #Fact    : 0
% 3.20/1.53  #Define  : 0
% 3.20/1.53  #Split   : 7
% 3.20/1.53  #Chain   : 0
% 3.20/1.53  #Close   : 0
% 3.20/1.53  
% 3.20/1.53  Ordering : KBO
% 3.20/1.53  
% 3.20/1.53  Simplification rules
% 3.20/1.53  ----------------------
% 3.20/1.53  #Subsume      : 3
% 3.20/1.53  #Demod        : 112
% 3.20/1.53  #Tautology    : 63
% 3.20/1.53  #SimpNegUnit  : 45
% 3.20/1.53  #BackRed      : 6
% 3.20/1.53  
% 3.20/1.53  #Partial instantiations: 0
% 3.20/1.53  #Strategies tried      : 1
% 3.20/1.53  
% 3.20/1.53  Timing (in seconds)
% 3.20/1.53  ----------------------
% 3.20/1.53  Preprocessing        : 0.37
% 3.20/1.53  Parsing              : 0.20
% 3.20/1.53  CNF conversion       : 0.03
% 3.20/1.53  Main loop            : 0.30
% 3.20/1.53  Inferencing          : 0.11
% 3.20/1.53  Reduction            : 0.09
% 3.20/1.53  Demodulation         : 0.06
% 3.20/1.53  BG Simplification    : 0.02
% 3.20/1.53  Subsumption          : 0.05
% 3.20/1.53  Abstraction          : 0.02
% 3.20/1.53  MUC search           : 0.00
% 3.20/1.53  Cooper               : 0.00
% 3.20/1.53  Total                : 0.72
% 3.20/1.53  Index Insertion      : 0.00
% 3.20/1.53  Index Deletion       : 0.00
% 3.20/1.53  Index Matching       : 0.00
% 3.20/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
