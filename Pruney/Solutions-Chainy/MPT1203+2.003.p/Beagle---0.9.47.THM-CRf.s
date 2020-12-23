%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:14 EST 2020

% Result     : Theorem 33.16s
% Output     : CNFRefutation 33.33s
% Verified   : 
% Statistics : Number of formulae       :  158 (1528 expanded)
%              Number of leaves         :   35 ( 543 expanded)
%              Depth                    :   22
%              Number of atoms          :  372 (6532 expanded)
%              Number of equality atoms :   90 (1451 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v11_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(k3_lattices,type,(
    k3_lattices: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_lattices,type,(
    k4_lattices: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(v11_lattices,type,(
    v11_lattices: $i > $o )).

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

tff(f_182,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v11_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( k4_lattices(A,B,C) = k4_lattices(A,B,D)
                        & k3_lattices(A,B,C) = k3_lattices(A,B,D) )
                     => C = D ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_lattices)).

tff(f_107,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

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

tff(f_101,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k4_lattices(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k4_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

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

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k1_lattices(A,B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k3_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(f_157,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v11_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => k3_lattices(A,B,k4_lattices(A,C,D)) = k4_lattices(A,k3_lattices(A,B,C),k3_lattices(A,B,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_lattices)).

tff(c_36,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_48,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_55,plain,(
    ! [A_55] :
      ( l2_lattices(A_55)
      | ~ l3_lattices(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_59,plain,(
    l2_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_55])).

tff(c_52,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_60,plain,(
    ! [A_56] :
      ( l1_lattices(A_56)
      | ~ l3_lattices(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_64,plain,(
    l1_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_60])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_40,plain,(
    k4_lattices('#skF_1','#skF_2','#skF_3') = k4_lattices('#skF_1','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_113,plain,(
    ! [A_70,B_71,C_72] :
      ( m1_subset_1(k4_lattices(A_70,B_71,C_72),u1_struct_0(A_70))
      | ~ m1_subset_1(C_72,u1_struct_0(A_70))
      | ~ m1_subset_1(B_71,u1_struct_0(A_70))
      | ~ l1_lattices(A_70)
      | ~ v6_lattices(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_122,plain,
    ( m1_subset_1(k4_lattices('#skF_1','#skF_2','#skF_4'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_113])).

tff(c_129,plain,
    ( m1_subset_1(k4_lattices('#skF_1','#skF_2','#skF_4'),u1_struct_0('#skF_1'))
    | ~ v6_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_46,c_44,c_122])).

tff(c_130,plain,
    ( m1_subset_1(k4_lattices('#skF_1','#skF_2','#skF_4'),u1_struct_0('#skF_1'))
    | ~ v6_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_129])).

tff(c_131,plain,(
    ~ v6_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_134,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_131])).

tff(c_137,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_134])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_137])).

tff(c_141,plain,(
    v6_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_236,plain,(
    ! [A_78,C_79,B_80] :
      ( k4_lattices(A_78,C_79,B_80) = k4_lattices(A_78,B_80,C_79)
      | ~ m1_subset_1(C_79,u1_struct_0(A_78))
      | ~ m1_subset_1(B_80,u1_struct_0(A_78))
      | ~ l1_lattices(A_78)
      | ~ v6_lattices(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_244,plain,(
    ! [B_80] :
      ( k4_lattices('#skF_1',B_80,'#skF_4') = k4_lattices('#skF_1','#skF_4',B_80)
      | ~ m1_subset_1(B_80,u1_struct_0('#skF_1'))
      | ~ l1_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_236])).

tff(c_258,plain,(
    ! [B_80] :
      ( k4_lattices('#skF_1',B_80,'#skF_4') = k4_lattices('#skF_1','#skF_4',B_80)
      | ~ m1_subset_1(B_80,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_64,c_244])).

tff(c_266,plain,(
    ! [B_81] :
      ( k4_lattices('#skF_1',B_81,'#skF_4') = k4_lattices('#skF_1','#skF_4',B_81)
      | ~ m1_subset_1(B_81,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_258])).

tff(c_291,plain,(
    k4_lattices('#skF_1','#skF_2','#skF_4') = k4_lattices('#skF_1','#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_266])).

tff(c_140,plain,(
    m1_subset_1(k4_lattices('#skF_1','#skF_2','#skF_4'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_336,plain,(
    m1_subset_1(k4_lattices('#skF_1','#skF_4','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_140])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_337,plain,(
    k4_lattices('#skF_1','#skF_2','#skF_3') = k4_lattices('#skF_1','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_40])).

tff(c_246,plain,(
    ! [B_80] :
      ( k4_lattices('#skF_1',B_80,'#skF_2') = k4_lattices('#skF_1','#skF_2',B_80)
      | ~ m1_subset_1(B_80,u1_struct_0('#skF_1'))
      | ~ l1_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_236])).

tff(c_262,plain,(
    ! [B_80] :
      ( k4_lattices('#skF_1',B_80,'#skF_2') = k4_lattices('#skF_1','#skF_2',B_80)
      | ~ m1_subset_1(B_80,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_64,c_246])).

tff(c_427,plain,(
    ! [B_85] :
      ( k4_lattices('#skF_1',B_85,'#skF_2') = k4_lattices('#skF_1','#skF_2',B_85)
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_262])).

tff(c_440,plain,(
    k4_lattices('#skF_1','#skF_2','#skF_3') = k4_lattices('#skF_1','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_427])).

tff(c_454,plain,(
    k4_lattices('#skF_1','#skF_3','#skF_2') = k4_lattices('#skF_1','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_440])).

tff(c_513,plain,(
    ! [A_87,B_88,C_89] :
      ( r1_lattices(A_87,k4_lattices(A_87,B_88,C_89),B_88)
      | ~ m1_subset_1(C_89,u1_struct_0(A_87))
      | ~ m1_subset_1(B_88,u1_struct_0(A_87))
      | ~ l3_lattices(A_87)
      | ~ v8_lattices(A_87)
      | ~ v6_lattices(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_518,plain,
    ( r1_lattices('#skF_1',k4_lattices('#skF_1','#skF_4','#skF_2'),'#skF_3')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_513])).

tff(c_530,plain,
    ( r1_lattices('#skF_1',k4_lattices('#skF_1','#skF_4','#skF_2'),'#skF_3')
    | ~ v8_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_48,c_44,c_46,c_518])).

tff(c_531,plain,
    ( r1_lattices('#skF_1',k4_lattices('#skF_1','#skF_4','#skF_2'),'#skF_3')
    | ~ v8_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_530])).

tff(c_541,plain,(
    ~ v8_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_531])).

tff(c_544,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_541])).

tff(c_547,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_544])).

tff(c_549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_547])).

tff(c_550,plain,(
    r1_lattices('#skF_1',k4_lattices('#skF_1','#skF_4','#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_531])).

tff(c_22,plain,(
    ! [A_8,B_12,C_14] :
      ( k1_lattices(A_8,B_12,C_14) = C_14
      | ~ r1_lattices(A_8,B_12,C_14)
      | ~ m1_subset_1(C_14,u1_struct_0(A_8))
      | ~ m1_subset_1(B_12,u1_struct_0(A_8))
      | ~ l2_lattices(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_561,plain,
    ( k1_lattices('#skF_1',k4_lattices('#skF_1','#skF_4','#skF_2'),'#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k4_lattices('#skF_1','#skF_4','#skF_2'),u1_struct_0('#skF_1'))
    | ~ l2_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_550,c_22])).

tff(c_564,plain,
    ( k1_lattices('#skF_1',k4_lattices('#skF_1','#skF_4','#skF_2'),'#skF_3') = '#skF_3'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_336,c_44,c_561])).

tff(c_565,plain,(
    k1_lattices('#skF_1',k4_lattices('#skF_1','#skF_4','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_564])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_382,plain,(
    ! [A_82,C_83,B_84] :
      ( k3_lattices(A_82,C_83,B_84) = k3_lattices(A_82,B_84,C_83)
      | ~ m1_subset_1(C_83,u1_struct_0(A_82))
      | ~ m1_subset_1(B_84,u1_struct_0(A_82))
      | ~ l2_lattices(A_82)
      | ~ v4_lattices(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_392,plain,(
    ! [B_84] :
      ( k3_lattices('#skF_1',B_84,'#skF_4') = k3_lattices('#skF_1','#skF_4',B_84)
      | ~ m1_subset_1(B_84,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_382])).

tff(c_410,plain,(
    ! [B_84] :
      ( k3_lattices('#skF_1',B_84,'#skF_4') = k3_lattices('#skF_1','#skF_4',B_84)
      | ~ m1_subset_1(B_84,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_392])).

tff(c_411,plain,(
    ! [B_84] :
      ( k3_lattices('#skF_1',B_84,'#skF_4') = k3_lattices('#skF_1','#skF_4',B_84)
      | ~ m1_subset_1(B_84,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_410])).

tff(c_502,plain,(
    ~ v4_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_411])).

tff(c_505,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_502])).

tff(c_508,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_505])).

tff(c_510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_508])).

tff(c_512,plain,(
    v4_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_411])).

tff(c_179,plain,(
    ! [A_74,B_75,C_76] :
      ( k3_lattices(A_74,B_75,C_76) = k1_lattices(A_74,B_75,C_76)
      | ~ m1_subset_1(C_76,u1_struct_0(A_74))
      | ~ m1_subset_1(B_75,u1_struct_0(A_74))
      | ~ l2_lattices(A_74)
      | ~ v4_lattices(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_185,plain,(
    ! [B_75] :
      ( k3_lattices('#skF_1',B_75,'#skF_3') = k1_lattices('#skF_1',B_75,'#skF_3')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_179])).

tff(c_197,plain,(
    ! [B_75] :
      ( k3_lattices('#skF_1',B_75,'#skF_3') = k1_lattices('#skF_1',B_75,'#skF_3')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_185])).

tff(c_198,plain,(
    ! [B_75] :
      ( k3_lattices('#skF_1',B_75,'#skF_3') = k1_lattices('#skF_1',B_75,'#skF_3')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_197])).

tff(c_777,plain,(
    ! [B_96] :
      ( k3_lattices('#skF_1',B_96,'#skF_3') = k1_lattices('#skF_1',B_96,'#skF_3')
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_198])).

tff(c_780,plain,(
    k3_lattices('#skF_1',k4_lattices('#skF_1','#skF_4','#skF_2'),'#skF_3') = k1_lattices('#skF_1',k4_lattices('#skF_1','#skF_4','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_336,c_777])).

tff(c_798,plain,(
    k3_lattices('#skF_1',k4_lattices('#skF_1','#skF_4','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_780])).

tff(c_390,plain,(
    ! [B_84] :
      ( k3_lattices('#skF_1',B_84,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_84)
      | ~ m1_subset_1(B_84,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_382])).

tff(c_406,plain,(
    ! [B_84] :
      ( k3_lattices('#skF_1',B_84,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_84)
      | ~ m1_subset_1(B_84,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_390])).

tff(c_407,plain,(
    ! [B_84] :
      ( k3_lattices('#skF_1',B_84,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_84)
      | ~ m1_subset_1(B_84,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_406])).

tff(c_1030,plain,(
    ! [B_98] :
      ( k3_lattices('#skF_1',B_98,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_98)
      | ~ m1_subset_1(B_98,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_407])).

tff(c_1050,plain,(
    k3_lattices('#skF_1',k4_lattices('#skF_1','#skF_4','#skF_2'),'#skF_3') = k3_lattices('#skF_1','#skF_3',k4_lattices('#skF_1','#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_336,c_1030])).

tff(c_1636,plain,(
    k3_lattices('#skF_1','#skF_3',k4_lattices('#skF_1','#skF_4','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_798,c_1050])).

tff(c_189,plain,(
    ! [B_75] :
      ( k3_lattices('#skF_1',B_75,'#skF_2') = k1_lattices('#skF_1',B_75,'#skF_2')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_179])).

tff(c_205,plain,(
    ! [B_75] :
      ( k3_lattices('#skF_1',B_75,'#skF_2') = k1_lattices('#skF_1',B_75,'#skF_2')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_189])).

tff(c_206,plain,(
    ! [B_75] :
      ( k3_lattices('#skF_1',B_75,'#skF_2') = k1_lattices('#skF_1',B_75,'#skF_2')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_205])).

tff(c_904,plain,(
    ! [B_97] :
      ( k3_lattices('#skF_1',B_97,'#skF_2') = k1_lattices('#skF_1',B_97,'#skF_2')
      | ~ m1_subset_1(B_97,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_206])).

tff(c_932,plain,(
    k3_lattices('#skF_1','#skF_4','#skF_2') = k1_lattices('#skF_1','#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_904])).

tff(c_187,plain,(
    ! [B_75] :
      ( k3_lattices('#skF_1',B_75,'#skF_4') = k1_lattices('#skF_1',B_75,'#skF_4')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_179])).

tff(c_201,plain,(
    ! [B_75] :
      ( k3_lattices('#skF_1',B_75,'#skF_4') = k1_lattices('#skF_1',B_75,'#skF_4')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_187])).

tff(c_202,plain,(
    ! [B_75] :
      ( k3_lattices('#skF_1',B_75,'#skF_4') = k1_lattices('#skF_1',B_75,'#skF_4')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_201])).

tff(c_696,plain,(
    ! [B_95] :
      ( k3_lattices('#skF_1',B_95,'#skF_4') = k1_lattices('#skF_1',B_95,'#skF_4')
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_202])).

tff(c_724,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_4') = k1_lattices('#skF_1','#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_696])).

tff(c_615,plain,(
    ! [B_94] :
      ( k3_lattices('#skF_1',B_94,'#skF_4') = k3_lattices('#skF_1','#skF_4',B_94)
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_411])).

tff(c_644,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_4') = k3_lattices('#skF_1','#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_615])).

tff(c_758,plain,(
    k3_lattices('#skF_1','#skF_4','#skF_2') = k1_lattices('#skF_1','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_724,c_644])).

tff(c_966,plain,(
    k1_lattices('#skF_1','#skF_2','#skF_4') = k1_lattices('#skF_1','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_758])).

tff(c_38,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_3') = k3_lattices('#skF_1','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_661,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_3') = k3_lattices('#skF_1','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_38])).

tff(c_824,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_3') = k1_lattices('#skF_1','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_661])).

tff(c_1001,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_3') = k1_lattices('#skF_1','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_966,c_824])).

tff(c_931,plain,(
    k3_lattices('#skF_1','#skF_3','#skF_2') = k1_lattices('#skF_1','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_904])).

tff(c_1049,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_3') = k3_lattices('#skF_1','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_1030])).

tff(c_1061,plain,(
    k1_lattices('#skF_1','#skF_3','#skF_2') = k1_lattices('#skF_1','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1001,c_931,c_1049])).

tff(c_1078,plain,(
    k3_lattices('#skF_1','#skF_3','#skF_2') = k1_lattices('#skF_1','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_931])).

tff(c_806,plain,(
    k3_lattices('#skF_1','#skF_4','#skF_3') = k1_lattices('#skF_1','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_777])).

tff(c_50,plain,(
    v11_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_641,plain,(
    k3_lattices('#skF_1','#skF_3','#skF_4') = k3_lattices('#skF_1','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_615])).

tff(c_34,plain,(
    ! [A_29,B_37,C_41,D_43] :
      ( k4_lattices(A_29,k3_lattices(A_29,B_37,C_41),k3_lattices(A_29,B_37,D_43)) = k3_lattices(A_29,B_37,k4_lattices(A_29,C_41,D_43))
      | ~ m1_subset_1(D_43,u1_struct_0(A_29))
      | ~ m1_subset_1(C_41,u1_struct_0(A_29))
      | ~ m1_subset_1(B_37,u1_struct_0(A_29))
      | ~ l3_lattices(A_29)
      | ~ v11_lattices(A_29)
      | ~ v10_lattices(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_651,plain,(
    ! [C_41] :
      ( k4_lattices('#skF_1',k3_lattices('#skF_1','#skF_3',C_41),k3_lattices('#skF_1','#skF_4','#skF_3')) = k3_lattices('#skF_1','#skF_3',k4_lattices('#skF_1',C_41,'#skF_4'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v11_lattices('#skF_1')
      | ~ v10_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_34])).

tff(c_658,plain,(
    ! [C_41] :
      ( k4_lattices('#skF_1',k3_lattices('#skF_1','#skF_3',C_41),k3_lattices('#skF_1','#skF_4','#skF_3')) = k3_lattices('#skF_1','#skF_3',k4_lattices('#skF_1',C_41,'#skF_4'))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_44,c_42,c_651])).

tff(c_659,plain,(
    ! [C_41] :
      ( k4_lattices('#skF_1',k3_lattices('#skF_1','#skF_3',C_41),k3_lattices('#skF_1','#skF_4','#skF_3')) = k3_lattices('#skF_1','#skF_3',k4_lattices('#skF_1',C_41,'#skF_4'))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_658])).

tff(c_50089,plain,(
    ! [C_350] :
      ( k4_lattices('#skF_1',k3_lattices('#skF_1','#skF_3',C_350),k1_lattices('#skF_1','#skF_4','#skF_3')) = k3_lattices('#skF_1','#skF_3',k4_lattices('#skF_1',C_350,'#skF_4'))
      | ~ m1_subset_1(C_350,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_659])).

tff(c_50246,plain,
    ( k4_lattices('#skF_1',k1_lattices('#skF_1','#skF_4','#skF_2'),k1_lattices('#skF_1','#skF_4','#skF_3')) = k3_lattices('#skF_1','#skF_3',k4_lattices('#skF_1','#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1078,c_50089])).

tff(c_50374,plain,(
    k4_lattices('#skF_1',k1_lattices('#skF_1','#skF_4','#skF_2'),k1_lattices('#skF_1','#skF_4','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1636,c_291,c_50246])).

tff(c_551,plain,(
    v8_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_531])).

tff(c_2052,plain,(
    ! [A_106,B_107,C_108] :
      ( k1_lattices(A_106,k4_lattices(A_106,B_107,C_108),B_107) = B_107
      | ~ m1_subset_1(k4_lattices(A_106,B_107,C_108),u1_struct_0(A_106))
      | ~ l2_lattices(A_106)
      | ~ m1_subset_1(C_108,u1_struct_0(A_106))
      | ~ m1_subset_1(B_107,u1_struct_0(A_106))
      | ~ l3_lattices(A_106)
      | ~ v8_lattices(A_106)
      | ~ v6_lattices(A_106)
      | v2_struct_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_513,c_22])).

tff(c_2090,plain,
    ( k1_lattices('#skF_1',k4_lattices('#skF_1','#skF_4','#skF_2'),'#skF_4') = '#skF_4'
    | ~ l2_lattices('#skF_1')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_336,c_2052])).

tff(c_2158,plain,
    ( k1_lattices('#skF_1',k4_lattices('#skF_1','#skF_4','#skF_2'),'#skF_4') = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_551,c_48,c_42,c_46,c_59,c_2090])).

tff(c_2159,plain,(
    k1_lattices('#skF_1',k4_lattices('#skF_1','#skF_4','#skF_2'),'#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2158])).

tff(c_716,plain,(
    k3_lattices('#skF_1',k4_lattices('#skF_1','#skF_4','#skF_2'),'#skF_4') = k1_lattices('#skF_1',k4_lattices('#skF_1','#skF_4','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_336,c_696])).

tff(c_635,plain,(
    k3_lattices('#skF_1',k4_lattices('#skF_1','#skF_4','#skF_2'),'#skF_4') = k3_lattices('#skF_1','#skF_4',k4_lattices('#skF_1','#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_336,c_615])).

tff(c_1451,plain,(
    k3_lattices('#skF_1','#skF_4',k4_lattices('#skF_1','#skF_4','#skF_2')) = k1_lattices('#skF_1',k4_lattices('#skF_1','#skF_4','#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_716,c_635])).

tff(c_2171,plain,(
    k3_lattices('#skF_1','#skF_4',k4_lattices('#skF_1','#skF_4','#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2159,c_1451])).

tff(c_722,plain,(
    k3_lattices('#skF_1','#skF_3','#skF_4') = k1_lattices('#skF_1','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_696])).

tff(c_725,plain,(
    k3_lattices('#skF_1','#skF_4','#skF_3') = k1_lattices('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_722,c_641])).

tff(c_857,plain,(
    k1_lattices('#skF_1','#skF_3','#skF_4') = k1_lattices('#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_725])).

tff(c_814,plain,(
    ! [C_41] :
      ( k4_lattices('#skF_1',k3_lattices('#skF_1','#skF_4',C_41),k1_lattices('#skF_1','#skF_3','#skF_4')) = k3_lattices('#skF_1','#skF_4',k4_lattices('#skF_1',C_41,'#skF_3'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v11_lattices('#skF_1')
      | ~ v10_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_725,c_34])).

tff(c_821,plain,(
    ! [C_41] :
      ( k4_lattices('#skF_1',k3_lattices('#skF_1','#skF_4',C_41),k1_lattices('#skF_1','#skF_3','#skF_4')) = k3_lattices('#skF_1','#skF_4',k4_lattices('#skF_1',C_41,'#skF_3'))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_42,c_44,c_814])).

tff(c_822,plain,(
    ! [C_41] :
      ( k4_lattices('#skF_1',k3_lattices('#skF_1','#skF_4',C_41),k1_lattices('#skF_1','#skF_3','#skF_4')) = k3_lattices('#skF_1','#skF_4',k4_lattices('#skF_1',C_41,'#skF_3'))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_821])).

tff(c_51926,plain,(
    ! [C_351] :
      ( k4_lattices('#skF_1',k3_lattices('#skF_1','#skF_4',C_351),k1_lattices('#skF_1','#skF_4','#skF_3')) = k3_lattices('#skF_1','#skF_4',k4_lattices('#skF_1',C_351,'#skF_3'))
      | ~ m1_subset_1(C_351,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_857,c_822])).

tff(c_52074,plain,
    ( k4_lattices('#skF_1',k1_lattices('#skF_1','#skF_4','#skF_2'),k1_lattices('#skF_1','#skF_4','#skF_3')) = k3_lattices('#skF_1','#skF_4',k4_lattices('#skF_1','#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_932,c_51926])).

tff(c_52196,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50374,c_2171,c_337,c_52074])).

tff(c_52198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_52196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:49:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 33.16/21.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 33.16/21.61  
% 33.16/21.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 33.16/21.61  %$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v11_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 33.16/21.61  
% 33.16/21.61  %Foreground sorts:
% 33.16/21.61  
% 33.16/21.61  
% 33.16/21.61  %Background operators:
% 33.16/21.61  
% 33.16/21.61  
% 33.16/21.61  %Foreground operators:
% 33.16/21.61  tff(l3_lattices, type, l3_lattices: $i > $o).
% 33.16/21.61  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 33.16/21.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 33.16/21.61  tff(l2_lattices, type, l2_lattices: $i > $o).
% 33.16/21.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 33.16/21.61  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 33.16/21.61  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 33.16/21.61  tff(l1_lattices, type, l1_lattices: $i > $o).
% 33.16/21.61  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 33.16/21.61  tff(v4_lattices, type, v4_lattices: $i > $o).
% 33.16/21.61  tff(v6_lattices, type, v6_lattices: $i > $o).
% 33.16/21.61  tff('#skF_2', type, '#skF_2': $i).
% 33.16/21.61  tff(v9_lattices, type, v9_lattices: $i > $o).
% 33.16/21.61  tff('#skF_3', type, '#skF_3': $i).
% 33.16/21.61  tff('#skF_1', type, '#skF_1': $i).
% 33.16/21.61  tff(v5_lattices, type, v5_lattices: $i > $o).
% 33.16/21.61  tff(v10_lattices, type, v10_lattices: $i > $o).
% 33.16/21.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 33.16/21.61  tff('#skF_4', type, '#skF_4': $i).
% 33.16/21.61  tff(v11_lattices, type, v11_lattices: $i > $o).
% 33.16/21.61  tff(v8_lattices, type, v8_lattices: $i > $o).
% 33.16/21.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 33.16/21.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 33.16/21.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 33.16/21.61  tff(v7_lattices, type, v7_lattices: $i > $o).
% 33.16/21.61  
% 33.33/21.64  tff(f_182, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v11_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((k4_lattices(A, B, C) = k4_lattices(A, B, D)) & (k3_lattices(A, B, C) = k3_lattices(A, B, D))) => (C = D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_lattices)).
% 33.33/21.64  tff(f_107, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 33.33/21.64  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 33.33/21.64  tff(f_101, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k4_lattices(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_lattices)).
% 33.33/21.64  tff(f_73, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k4_lattices(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 33.33/21.64  tff(f_137, axiom, (![A]: ((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => r1_lattices(A, k4_lattices(A, B, C), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_lattices)).
% 33.33/21.64  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 33.33/21.64  tff(f_60, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k3_lattices(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 33.33/21.64  tff(f_120, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 33.33/21.64  tff(f_157, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v11_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (k3_lattices(A, B, k4_lattices(A, C, D)) = k4_lattices(A, k3_lattices(A, B, C), k3_lattices(A, B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_lattices)).
% 33.33/21.64  tff(c_36, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_182])).
% 33.33/21.64  tff(c_46, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 33.33/21.64  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 33.33/21.64  tff(c_48, plain, (l3_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 33.33/21.64  tff(c_55, plain, (![A_55]: (l2_lattices(A_55) | ~l3_lattices(A_55))), inference(cnfTransformation, [status(thm)], [f_107])).
% 33.33/21.64  tff(c_59, plain, (l2_lattices('#skF_1')), inference(resolution, [status(thm)], [c_48, c_55])).
% 33.33/21.64  tff(c_52, plain, (v10_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 33.33/21.64  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 33.33/21.64  tff(c_60, plain, (![A_56]: (l1_lattices(A_56) | ~l3_lattices(A_56))), inference(cnfTransformation, [status(thm)], [f_107])).
% 33.33/21.64  tff(c_64, plain, (l1_lattices('#skF_1')), inference(resolution, [status(thm)], [c_48, c_60])).
% 33.33/21.64  tff(c_44, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 33.33/21.64  tff(c_40, plain, (k4_lattices('#skF_1', '#skF_2', '#skF_3')=k4_lattices('#skF_1', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_182])).
% 33.33/21.64  tff(c_113, plain, (![A_70, B_71, C_72]: (m1_subset_1(k4_lattices(A_70, B_71, C_72), u1_struct_0(A_70)) | ~m1_subset_1(C_72, u1_struct_0(A_70)) | ~m1_subset_1(B_71, u1_struct_0(A_70)) | ~l1_lattices(A_70) | ~v6_lattices(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_101])).
% 33.33/21.64  tff(c_122, plain, (m1_subset_1(k4_lattices('#skF_1', '#skF_2', '#skF_4'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40, c_113])).
% 33.33/21.64  tff(c_129, plain, (m1_subset_1(k4_lattices('#skF_1', '#skF_2', '#skF_4'), u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_46, c_44, c_122])).
% 33.33/21.64  tff(c_130, plain, (m1_subset_1(k4_lattices('#skF_1', '#skF_2', '#skF_4'), u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_129])).
% 33.33/21.64  tff(c_131, plain, (~v6_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_130])).
% 33.33/21.64  tff(c_134, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_8, c_131])).
% 33.33/21.64  tff(c_137, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_134])).
% 33.33/21.64  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_137])).
% 33.33/21.64  tff(c_141, plain, (v6_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_130])).
% 33.33/21.64  tff(c_42, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 33.33/21.64  tff(c_236, plain, (![A_78, C_79, B_80]: (k4_lattices(A_78, C_79, B_80)=k4_lattices(A_78, B_80, C_79) | ~m1_subset_1(C_79, u1_struct_0(A_78)) | ~m1_subset_1(B_80, u1_struct_0(A_78)) | ~l1_lattices(A_78) | ~v6_lattices(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_73])).
% 33.33/21.64  tff(c_244, plain, (![B_80]: (k4_lattices('#skF_1', B_80, '#skF_4')=k4_lattices('#skF_1', '#skF_4', B_80) | ~m1_subset_1(B_80, u1_struct_0('#skF_1')) | ~l1_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_236])).
% 33.33/21.64  tff(c_258, plain, (![B_80]: (k4_lattices('#skF_1', B_80, '#skF_4')=k4_lattices('#skF_1', '#skF_4', B_80) | ~m1_subset_1(B_80, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_64, c_244])).
% 33.33/21.64  tff(c_266, plain, (![B_81]: (k4_lattices('#skF_1', B_81, '#skF_4')=k4_lattices('#skF_1', '#skF_4', B_81) | ~m1_subset_1(B_81, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_258])).
% 33.33/21.64  tff(c_291, plain, (k4_lattices('#skF_1', '#skF_2', '#skF_4')=k4_lattices('#skF_1', '#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_266])).
% 33.33/21.64  tff(c_140, plain, (m1_subset_1(k4_lattices('#skF_1', '#skF_2', '#skF_4'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_130])).
% 33.33/21.64  tff(c_336, plain, (m1_subset_1(k4_lattices('#skF_1', '#skF_4', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_140])).
% 33.33/21.64  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 33.33/21.64  tff(c_337, plain, (k4_lattices('#skF_1', '#skF_2', '#skF_3')=k4_lattices('#skF_1', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_291, c_40])).
% 33.33/21.64  tff(c_246, plain, (![B_80]: (k4_lattices('#skF_1', B_80, '#skF_2')=k4_lattices('#skF_1', '#skF_2', B_80) | ~m1_subset_1(B_80, u1_struct_0('#skF_1')) | ~l1_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_236])).
% 33.33/21.64  tff(c_262, plain, (![B_80]: (k4_lattices('#skF_1', B_80, '#skF_2')=k4_lattices('#skF_1', '#skF_2', B_80) | ~m1_subset_1(B_80, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_64, c_246])).
% 33.33/21.64  tff(c_427, plain, (![B_85]: (k4_lattices('#skF_1', B_85, '#skF_2')=k4_lattices('#skF_1', '#skF_2', B_85) | ~m1_subset_1(B_85, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_262])).
% 33.33/21.64  tff(c_440, plain, (k4_lattices('#skF_1', '#skF_2', '#skF_3')=k4_lattices('#skF_1', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_427])).
% 33.33/21.64  tff(c_454, plain, (k4_lattices('#skF_1', '#skF_3', '#skF_2')=k4_lattices('#skF_1', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_337, c_440])).
% 33.33/21.64  tff(c_513, plain, (![A_87, B_88, C_89]: (r1_lattices(A_87, k4_lattices(A_87, B_88, C_89), B_88) | ~m1_subset_1(C_89, u1_struct_0(A_87)) | ~m1_subset_1(B_88, u1_struct_0(A_87)) | ~l3_lattices(A_87) | ~v8_lattices(A_87) | ~v6_lattices(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_137])).
% 33.33/21.64  tff(c_518, plain, (r1_lattices('#skF_1', k4_lattices('#skF_1', '#skF_4', '#skF_2'), '#skF_3') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_454, c_513])).
% 33.33/21.64  tff(c_530, plain, (r1_lattices('#skF_1', k4_lattices('#skF_1', '#skF_4', '#skF_2'), '#skF_3') | ~v8_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_48, c_44, c_46, c_518])).
% 33.33/21.64  tff(c_531, plain, (r1_lattices('#skF_1', k4_lattices('#skF_1', '#skF_4', '#skF_2'), '#skF_3') | ~v8_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_530])).
% 33.33/21.64  tff(c_541, plain, (~v8_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_531])).
% 33.33/21.64  tff(c_544, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_4, c_541])).
% 33.33/21.64  tff(c_547, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_544])).
% 33.33/21.64  tff(c_549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_547])).
% 33.33/21.64  tff(c_550, plain, (r1_lattices('#skF_1', k4_lattices('#skF_1', '#skF_4', '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_531])).
% 33.33/21.64  tff(c_22, plain, (![A_8, B_12, C_14]: (k1_lattices(A_8, B_12, C_14)=C_14 | ~r1_lattices(A_8, B_12, C_14) | ~m1_subset_1(C_14, u1_struct_0(A_8)) | ~m1_subset_1(B_12, u1_struct_0(A_8)) | ~l2_lattices(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_88])).
% 33.33/21.64  tff(c_561, plain, (k1_lattices('#skF_1', k4_lattices('#skF_1', '#skF_4', '#skF_2'), '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1(k4_lattices('#skF_1', '#skF_4', '#skF_2'), u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_550, c_22])).
% 33.33/21.64  tff(c_564, plain, (k1_lattices('#skF_1', k4_lattices('#skF_1', '#skF_4', '#skF_2'), '#skF_3')='#skF_3' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_336, c_44, c_561])).
% 33.33/21.64  tff(c_565, plain, (k1_lattices('#skF_1', k4_lattices('#skF_1', '#skF_4', '#skF_2'), '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_54, c_564])).
% 33.33/21.64  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 33.33/21.64  tff(c_382, plain, (![A_82, C_83, B_84]: (k3_lattices(A_82, C_83, B_84)=k3_lattices(A_82, B_84, C_83) | ~m1_subset_1(C_83, u1_struct_0(A_82)) | ~m1_subset_1(B_84, u1_struct_0(A_82)) | ~l2_lattices(A_82) | ~v4_lattices(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_60])).
% 33.33/21.64  tff(c_392, plain, (![B_84]: (k3_lattices('#skF_1', B_84, '#skF_4')=k3_lattices('#skF_1', '#skF_4', B_84) | ~m1_subset_1(B_84, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_382])).
% 33.33/21.64  tff(c_410, plain, (![B_84]: (k3_lattices('#skF_1', B_84, '#skF_4')=k3_lattices('#skF_1', '#skF_4', B_84) | ~m1_subset_1(B_84, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_392])).
% 33.33/21.64  tff(c_411, plain, (![B_84]: (k3_lattices('#skF_1', B_84, '#skF_4')=k3_lattices('#skF_1', '#skF_4', B_84) | ~m1_subset_1(B_84, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_54, c_410])).
% 33.33/21.64  tff(c_502, plain, (~v4_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_411])).
% 33.33/21.64  tff(c_505, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_12, c_502])).
% 33.33/21.64  tff(c_508, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_505])).
% 33.33/21.64  tff(c_510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_508])).
% 33.33/21.64  tff(c_512, plain, (v4_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_411])).
% 33.33/21.64  tff(c_179, plain, (![A_74, B_75, C_76]: (k3_lattices(A_74, B_75, C_76)=k1_lattices(A_74, B_75, C_76) | ~m1_subset_1(C_76, u1_struct_0(A_74)) | ~m1_subset_1(B_75, u1_struct_0(A_74)) | ~l2_lattices(A_74) | ~v4_lattices(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_120])).
% 33.33/21.64  tff(c_185, plain, (![B_75]: (k3_lattices('#skF_1', B_75, '#skF_3')=k1_lattices('#skF_1', B_75, '#skF_3') | ~m1_subset_1(B_75, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_179])).
% 33.33/21.64  tff(c_197, plain, (![B_75]: (k3_lattices('#skF_1', B_75, '#skF_3')=k1_lattices('#skF_1', B_75, '#skF_3') | ~m1_subset_1(B_75, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_185])).
% 33.33/21.64  tff(c_198, plain, (![B_75]: (k3_lattices('#skF_1', B_75, '#skF_3')=k1_lattices('#skF_1', B_75, '#skF_3') | ~m1_subset_1(B_75, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_54, c_197])).
% 33.33/21.64  tff(c_777, plain, (![B_96]: (k3_lattices('#skF_1', B_96, '#skF_3')=k1_lattices('#skF_1', B_96, '#skF_3') | ~m1_subset_1(B_96, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_512, c_198])).
% 33.33/21.64  tff(c_780, plain, (k3_lattices('#skF_1', k4_lattices('#skF_1', '#skF_4', '#skF_2'), '#skF_3')=k1_lattices('#skF_1', k4_lattices('#skF_1', '#skF_4', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_336, c_777])).
% 33.33/21.64  tff(c_798, plain, (k3_lattices('#skF_1', k4_lattices('#skF_1', '#skF_4', '#skF_2'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_565, c_780])).
% 33.33/21.64  tff(c_390, plain, (![B_84]: (k3_lattices('#skF_1', B_84, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_84) | ~m1_subset_1(B_84, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_382])).
% 33.33/21.64  tff(c_406, plain, (![B_84]: (k3_lattices('#skF_1', B_84, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_84) | ~m1_subset_1(B_84, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_390])).
% 33.33/21.64  tff(c_407, plain, (![B_84]: (k3_lattices('#skF_1', B_84, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_84) | ~m1_subset_1(B_84, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_54, c_406])).
% 33.33/21.64  tff(c_1030, plain, (![B_98]: (k3_lattices('#skF_1', B_98, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_98) | ~m1_subset_1(B_98, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_512, c_407])).
% 33.33/21.64  tff(c_1050, plain, (k3_lattices('#skF_1', k4_lattices('#skF_1', '#skF_4', '#skF_2'), '#skF_3')=k3_lattices('#skF_1', '#skF_3', k4_lattices('#skF_1', '#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_336, c_1030])).
% 33.33/21.64  tff(c_1636, plain, (k3_lattices('#skF_1', '#skF_3', k4_lattices('#skF_1', '#skF_4', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_798, c_1050])).
% 33.33/21.64  tff(c_189, plain, (![B_75]: (k3_lattices('#skF_1', B_75, '#skF_2')=k1_lattices('#skF_1', B_75, '#skF_2') | ~m1_subset_1(B_75, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_179])).
% 33.33/21.64  tff(c_205, plain, (![B_75]: (k3_lattices('#skF_1', B_75, '#skF_2')=k1_lattices('#skF_1', B_75, '#skF_2') | ~m1_subset_1(B_75, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_189])).
% 33.33/21.64  tff(c_206, plain, (![B_75]: (k3_lattices('#skF_1', B_75, '#skF_2')=k1_lattices('#skF_1', B_75, '#skF_2') | ~m1_subset_1(B_75, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_54, c_205])).
% 33.33/21.64  tff(c_904, plain, (![B_97]: (k3_lattices('#skF_1', B_97, '#skF_2')=k1_lattices('#skF_1', B_97, '#skF_2') | ~m1_subset_1(B_97, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_512, c_206])).
% 33.33/21.64  tff(c_932, plain, (k3_lattices('#skF_1', '#skF_4', '#skF_2')=k1_lattices('#skF_1', '#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_904])).
% 33.33/21.64  tff(c_187, plain, (![B_75]: (k3_lattices('#skF_1', B_75, '#skF_4')=k1_lattices('#skF_1', B_75, '#skF_4') | ~m1_subset_1(B_75, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_179])).
% 33.33/21.64  tff(c_201, plain, (![B_75]: (k3_lattices('#skF_1', B_75, '#skF_4')=k1_lattices('#skF_1', B_75, '#skF_4') | ~m1_subset_1(B_75, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_187])).
% 33.33/21.64  tff(c_202, plain, (![B_75]: (k3_lattices('#skF_1', B_75, '#skF_4')=k1_lattices('#skF_1', B_75, '#skF_4') | ~m1_subset_1(B_75, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_54, c_201])).
% 33.33/21.64  tff(c_696, plain, (![B_95]: (k3_lattices('#skF_1', B_95, '#skF_4')=k1_lattices('#skF_1', B_95, '#skF_4') | ~m1_subset_1(B_95, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_512, c_202])).
% 33.33/21.64  tff(c_724, plain, (k3_lattices('#skF_1', '#skF_2', '#skF_4')=k1_lattices('#skF_1', '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_696])).
% 33.33/21.64  tff(c_615, plain, (![B_94]: (k3_lattices('#skF_1', B_94, '#skF_4')=k3_lattices('#skF_1', '#skF_4', B_94) | ~m1_subset_1(B_94, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_411])).
% 33.33/21.64  tff(c_644, plain, (k3_lattices('#skF_1', '#skF_2', '#skF_4')=k3_lattices('#skF_1', '#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_615])).
% 33.33/21.64  tff(c_758, plain, (k3_lattices('#skF_1', '#skF_4', '#skF_2')=k1_lattices('#skF_1', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_724, c_644])).
% 33.33/21.64  tff(c_966, plain, (k1_lattices('#skF_1', '#skF_2', '#skF_4')=k1_lattices('#skF_1', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_932, c_758])).
% 33.33/21.64  tff(c_38, plain, (k3_lattices('#skF_1', '#skF_2', '#skF_3')=k3_lattices('#skF_1', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_182])).
% 33.33/21.64  tff(c_661, plain, (k3_lattices('#skF_1', '#skF_2', '#skF_3')=k3_lattices('#skF_1', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_644, c_38])).
% 33.33/21.64  tff(c_824, plain, (k3_lattices('#skF_1', '#skF_2', '#skF_3')=k1_lattices('#skF_1', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_758, c_661])).
% 33.33/21.64  tff(c_1001, plain, (k3_lattices('#skF_1', '#skF_2', '#skF_3')=k1_lattices('#skF_1', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_966, c_824])).
% 33.33/21.64  tff(c_931, plain, (k3_lattices('#skF_1', '#skF_3', '#skF_2')=k1_lattices('#skF_1', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_904])).
% 33.33/21.64  tff(c_1049, plain, (k3_lattices('#skF_1', '#skF_2', '#skF_3')=k3_lattices('#skF_1', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_1030])).
% 33.33/21.64  tff(c_1061, plain, (k1_lattices('#skF_1', '#skF_3', '#skF_2')=k1_lattices('#skF_1', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1001, c_931, c_1049])).
% 33.33/21.64  tff(c_1078, plain, (k3_lattices('#skF_1', '#skF_3', '#skF_2')=k1_lattices('#skF_1', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1061, c_931])).
% 33.33/21.64  tff(c_806, plain, (k3_lattices('#skF_1', '#skF_4', '#skF_3')=k1_lattices('#skF_1', '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_777])).
% 33.33/21.64  tff(c_50, plain, (v11_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 33.33/21.64  tff(c_641, plain, (k3_lattices('#skF_1', '#skF_3', '#skF_4')=k3_lattices('#skF_1', '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_615])).
% 33.33/21.64  tff(c_34, plain, (![A_29, B_37, C_41, D_43]: (k4_lattices(A_29, k3_lattices(A_29, B_37, C_41), k3_lattices(A_29, B_37, D_43))=k3_lattices(A_29, B_37, k4_lattices(A_29, C_41, D_43)) | ~m1_subset_1(D_43, u1_struct_0(A_29)) | ~m1_subset_1(C_41, u1_struct_0(A_29)) | ~m1_subset_1(B_37, u1_struct_0(A_29)) | ~l3_lattices(A_29) | ~v11_lattices(A_29) | ~v10_lattices(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_157])).
% 33.33/21.64  tff(c_651, plain, (![C_41]: (k4_lattices('#skF_1', k3_lattices('#skF_1', '#skF_3', C_41), k3_lattices('#skF_1', '#skF_4', '#skF_3'))=k3_lattices('#skF_1', '#skF_3', k4_lattices('#skF_1', C_41, '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~m1_subset_1(C_41, u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v11_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_641, c_34])).
% 33.33/21.64  tff(c_658, plain, (![C_41]: (k4_lattices('#skF_1', k3_lattices('#skF_1', '#skF_3', C_41), k3_lattices('#skF_1', '#skF_4', '#skF_3'))=k3_lattices('#skF_1', '#skF_3', k4_lattices('#skF_1', C_41, '#skF_4')) | ~m1_subset_1(C_41, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_44, c_42, c_651])).
% 33.33/21.64  tff(c_659, plain, (![C_41]: (k4_lattices('#skF_1', k3_lattices('#skF_1', '#skF_3', C_41), k3_lattices('#skF_1', '#skF_4', '#skF_3'))=k3_lattices('#skF_1', '#skF_3', k4_lattices('#skF_1', C_41, '#skF_4')) | ~m1_subset_1(C_41, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_658])).
% 33.33/21.64  tff(c_50089, plain, (![C_350]: (k4_lattices('#skF_1', k3_lattices('#skF_1', '#skF_3', C_350), k1_lattices('#skF_1', '#skF_4', '#skF_3'))=k3_lattices('#skF_1', '#skF_3', k4_lattices('#skF_1', C_350, '#skF_4')) | ~m1_subset_1(C_350, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_806, c_659])).
% 33.33/21.64  tff(c_50246, plain, (k4_lattices('#skF_1', k1_lattices('#skF_1', '#skF_4', '#skF_2'), k1_lattices('#skF_1', '#skF_4', '#skF_3'))=k3_lattices('#skF_1', '#skF_3', k4_lattices('#skF_1', '#skF_2', '#skF_4')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1078, c_50089])).
% 33.33/21.64  tff(c_50374, plain, (k4_lattices('#skF_1', k1_lattices('#skF_1', '#skF_4', '#skF_2'), k1_lattices('#skF_1', '#skF_4', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1636, c_291, c_50246])).
% 33.33/21.64  tff(c_551, plain, (v8_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_531])).
% 33.33/21.64  tff(c_2052, plain, (![A_106, B_107, C_108]: (k1_lattices(A_106, k4_lattices(A_106, B_107, C_108), B_107)=B_107 | ~m1_subset_1(k4_lattices(A_106, B_107, C_108), u1_struct_0(A_106)) | ~l2_lattices(A_106) | ~m1_subset_1(C_108, u1_struct_0(A_106)) | ~m1_subset_1(B_107, u1_struct_0(A_106)) | ~l3_lattices(A_106) | ~v8_lattices(A_106) | ~v6_lattices(A_106) | v2_struct_0(A_106))), inference(resolution, [status(thm)], [c_513, c_22])).
% 33.33/21.64  tff(c_2090, plain, (k1_lattices('#skF_1', k4_lattices('#skF_1', '#skF_4', '#skF_2'), '#skF_4')='#skF_4' | ~l2_lattices('#skF_1') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_336, c_2052])).
% 33.33/21.64  tff(c_2158, plain, (k1_lattices('#skF_1', k4_lattices('#skF_1', '#skF_4', '#skF_2'), '#skF_4')='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_551, c_48, c_42, c_46, c_59, c_2090])).
% 33.33/21.64  tff(c_2159, plain, (k1_lattices('#skF_1', k4_lattices('#skF_1', '#skF_4', '#skF_2'), '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_54, c_2158])).
% 33.33/21.64  tff(c_716, plain, (k3_lattices('#skF_1', k4_lattices('#skF_1', '#skF_4', '#skF_2'), '#skF_4')=k1_lattices('#skF_1', k4_lattices('#skF_1', '#skF_4', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_336, c_696])).
% 33.33/21.64  tff(c_635, plain, (k3_lattices('#skF_1', k4_lattices('#skF_1', '#skF_4', '#skF_2'), '#skF_4')=k3_lattices('#skF_1', '#skF_4', k4_lattices('#skF_1', '#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_336, c_615])).
% 33.33/21.64  tff(c_1451, plain, (k3_lattices('#skF_1', '#skF_4', k4_lattices('#skF_1', '#skF_4', '#skF_2'))=k1_lattices('#skF_1', k4_lattices('#skF_1', '#skF_4', '#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_716, c_635])).
% 33.33/21.64  tff(c_2171, plain, (k3_lattices('#skF_1', '#skF_4', k4_lattices('#skF_1', '#skF_4', '#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2159, c_1451])).
% 33.33/21.64  tff(c_722, plain, (k3_lattices('#skF_1', '#skF_3', '#skF_4')=k1_lattices('#skF_1', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_696])).
% 33.33/21.64  tff(c_725, plain, (k3_lattices('#skF_1', '#skF_4', '#skF_3')=k1_lattices('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_722, c_641])).
% 33.33/21.64  tff(c_857, plain, (k1_lattices('#skF_1', '#skF_3', '#skF_4')=k1_lattices('#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_806, c_725])).
% 33.33/21.64  tff(c_814, plain, (![C_41]: (k4_lattices('#skF_1', k3_lattices('#skF_1', '#skF_4', C_41), k1_lattices('#skF_1', '#skF_3', '#skF_4'))=k3_lattices('#skF_1', '#skF_4', k4_lattices('#skF_1', C_41, '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1(C_41, u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v11_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_725, c_34])).
% 33.33/21.64  tff(c_821, plain, (![C_41]: (k4_lattices('#skF_1', k3_lattices('#skF_1', '#skF_4', C_41), k1_lattices('#skF_1', '#skF_3', '#skF_4'))=k3_lattices('#skF_1', '#skF_4', k4_lattices('#skF_1', C_41, '#skF_3')) | ~m1_subset_1(C_41, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_42, c_44, c_814])).
% 33.33/21.64  tff(c_822, plain, (![C_41]: (k4_lattices('#skF_1', k3_lattices('#skF_1', '#skF_4', C_41), k1_lattices('#skF_1', '#skF_3', '#skF_4'))=k3_lattices('#skF_1', '#skF_4', k4_lattices('#skF_1', C_41, '#skF_3')) | ~m1_subset_1(C_41, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_821])).
% 33.33/21.64  tff(c_51926, plain, (![C_351]: (k4_lattices('#skF_1', k3_lattices('#skF_1', '#skF_4', C_351), k1_lattices('#skF_1', '#skF_4', '#skF_3'))=k3_lattices('#skF_1', '#skF_4', k4_lattices('#skF_1', C_351, '#skF_3')) | ~m1_subset_1(C_351, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_857, c_822])).
% 33.33/21.64  tff(c_52074, plain, (k4_lattices('#skF_1', k1_lattices('#skF_1', '#skF_4', '#skF_2'), k1_lattices('#skF_1', '#skF_4', '#skF_3'))=k3_lattices('#skF_1', '#skF_4', k4_lattices('#skF_1', '#skF_2', '#skF_3')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_932, c_51926])).
% 33.33/21.64  tff(c_52196, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50374, c_2171, c_337, c_52074])).
% 33.33/21.64  tff(c_52198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_52196])).
% 33.33/21.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 33.33/21.64  
% 33.33/21.64  Inference rules
% 33.33/21.64  ----------------------
% 33.33/21.64  #Ref     : 0
% 33.33/21.64  #Sup     : 10812
% 33.33/21.64  #Fact    : 0
% 33.33/21.64  #Define  : 0
% 33.33/21.64  #Split   : 27
% 33.33/21.64  #Chain   : 0
% 33.33/21.64  #Close   : 0
% 33.33/21.64  
% 33.33/21.64  Ordering : KBO
% 33.33/21.64  
% 33.33/21.64  Simplification rules
% 33.33/21.64  ----------------------
% 33.33/21.64  #Subsume      : 1303
% 33.33/21.64  #Demod        : 47455
% 33.33/21.64  #Tautology    : 1261
% 33.33/21.64  #SimpNegUnit  : 4839
% 33.33/21.64  #BackRed      : 66
% 33.33/21.64  
% 33.33/21.64  #Partial instantiations: 0
% 33.33/21.64  #Strategies tried      : 1
% 33.33/21.64  
% 33.33/21.64  Timing (in seconds)
% 33.33/21.64  ----------------------
% 33.33/21.64  Preprocessing        : 0.35
% 33.33/21.64  Parsing              : 0.18
% 33.33/21.64  CNF conversion       : 0.03
% 33.33/21.64  Main loop            : 20.50
% 33.33/21.64  Inferencing          : 2.22
% 33.33/21.64  Reduction            : 12.32
% 33.33/21.64  Demodulation         : 11.21
% 33.33/21.64  BG Simplification    : 0.32
% 33.33/21.64  Subsumption          : 5.13
% 33.33/21.64  Abstraction          : 0.79
% 33.33/21.64  MUC search           : 0.00
% 33.33/21.64  Cooper               : 0.00
% 33.33/21.64  Total                : 20.90
% 33.33/21.64  Index Insertion      : 0.00
% 33.33/21.64  Index Deletion       : 0.00
% 33.33/21.64  Index Matching       : 0.00
% 33.33/21.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
