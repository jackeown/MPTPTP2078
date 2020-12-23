%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:17 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 439 expanded)
%              Number of leaves         :   34 ( 166 expanded)
%              Depth                    :   16
%              Number of atoms          :  225 (1367 expanded)
%              Number of equality atoms :   48 ( 221 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v14_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k6_lattices > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(k6_lattices,type,(
    k6_lattices: $i > $i )).

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

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v14_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k4_lattices(A,k6_lattices(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattices)).

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

tff(f_107,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => m1_subset_1(k6_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k4_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v9_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k2_lattices(A,B,k1_lattices(A,B,C)) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ( v14_lattices(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( B = k6_lattices(A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( k1_lattices(A,B,C) = B
                    & k1_lattices(A,C,B) = B ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattices)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_46,plain,(
    l3_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_50,plain,(
    v10_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_58,plain,(
    ! [A_33] :
      ( l2_lattices(A_33)
      | ~ l3_lattices(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_62,plain,(
    l2_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_58])).

tff(c_34,plain,(
    ! [A_26] :
      ( m1_subset_1(k6_lattices(A_26),u1_struct_0(A_26))
      | ~ l2_lattices(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_53,plain,(
    ! [A_32] :
      ( l1_lattices(A_32)
      | ~ l3_lattices(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_57,plain,(
    l1_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_53])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_74,plain,(
    ! [A_46,C_47,B_48] :
      ( k4_lattices(A_46,C_47,B_48) = k4_lattices(A_46,B_48,C_47)
      | ~ m1_subset_1(C_47,u1_struct_0(A_46))
      | ~ m1_subset_1(B_48,u1_struct_0(A_46))
      | ~ l1_lattices(A_46)
      | ~ v6_lattices(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_84,plain,(
    ! [B_48] :
      ( k4_lattices('#skF_4',B_48,'#skF_5') = k4_lattices('#skF_4','#skF_5',B_48)
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_4'))
      | ~ l1_lattices('#skF_4')
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_74])).

tff(c_91,plain,(
    ! [B_48] :
      ( k4_lattices('#skF_4',B_48,'#skF_5') = k4_lattices('#skF_4','#skF_5',B_48)
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_4'))
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_84])).

tff(c_92,plain,(
    ! [B_48] :
      ( k4_lattices('#skF_4',B_48,'#skF_5') = k4_lattices('#skF_4','#skF_5',B_48)
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_4'))
      | ~ v6_lattices('#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_91])).

tff(c_93,plain,(
    ~ v6_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_96,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_93])).

tff(c_99,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_96])).

tff(c_101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_99])).

tff(c_123,plain,(
    ! [B_52] :
      ( k4_lattices('#skF_4',B_52,'#skF_5') = k4_lattices('#skF_4','#skF_5',B_52)
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_139,plain,
    ( k4_lattices('#skF_4',k6_lattices('#skF_4'),'#skF_5') = k4_lattices('#skF_4','#skF_5',k6_lattices('#skF_4'))
    | ~ l2_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_123])).

tff(c_157,plain,
    ( k4_lattices('#skF_4',k6_lattices('#skF_4'),'#skF_5') = k4_lattices('#skF_4','#skF_5',k6_lattices('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_139])).

tff(c_158,plain,(
    k4_lattices('#skF_4',k6_lattices('#skF_4'),'#skF_5') = k4_lattices('#skF_4','#skF_5',k6_lattices('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_157])).

tff(c_103,plain,(
    v6_lattices('#skF_4') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_104,plain,(
    ! [A_49,B_50,C_51] :
      ( k4_lattices(A_49,B_50,C_51) = k2_lattices(A_49,B_50,C_51)
      | ~ m1_subset_1(C_51,u1_struct_0(A_49))
      | ~ m1_subset_1(B_50,u1_struct_0(A_49))
      | ~ l1_lattices(A_49)
      | ~ v6_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_114,plain,(
    ! [B_50] :
      ( k4_lattices('#skF_4',B_50,'#skF_5') = k2_lattices('#skF_4',B_50,'#skF_5')
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_4'))
      | ~ l1_lattices('#skF_4')
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_104])).

tff(c_121,plain,(
    ! [B_50] :
      ( k4_lattices('#skF_4',B_50,'#skF_5') = k2_lattices('#skF_4',B_50,'#skF_5')
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_57,c_114])).

tff(c_166,plain,(
    ! [B_53] :
      ( k4_lattices('#skF_4',B_53,'#skF_5') = k2_lattices('#skF_4',B_53,'#skF_5')
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_121])).

tff(c_182,plain,
    ( k4_lattices('#skF_4',k6_lattices('#skF_4'),'#skF_5') = k2_lattices('#skF_4',k6_lattices('#skF_4'),'#skF_5')
    | ~ l2_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_166])).

tff(c_200,plain,
    ( k4_lattices('#skF_4','#skF_5',k6_lattices('#skF_4')) = k2_lattices('#skF_4',k6_lattices('#skF_4'),'#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_158,c_182])).

tff(c_201,plain,(
    k4_lattices('#skF_4','#skF_5',k6_lattices('#skF_4')) = k2_lattices('#skF_4',k6_lattices('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_200])).

tff(c_42,plain,(
    k4_lattices('#skF_4',k6_lattices('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_161,plain,(
    k4_lattices('#skF_4','#skF_5',k6_lattices('#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_42])).

tff(c_207,plain,(
    k2_lattices('#skF_4',k6_lattices('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_161])).

tff(c_30,plain,(
    ! [A_15] :
      ( m1_subset_1('#skF_3'(A_15),u1_struct_0(A_15))
      | v9_lattices(A_15)
      | ~ l3_lattices(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_178,plain,
    ( k4_lattices('#skF_4','#skF_3'('#skF_4'),'#skF_5') = k2_lattices('#skF_4','#skF_3'('#skF_4'),'#skF_5')
    | v9_lattices('#skF_4')
    | ~ l3_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_166])).

tff(c_196,plain,
    ( k4_lattices('#skF_4','#skF_3'('#skF_4'),'#skF_5') = k2_lattices('#skF_4','#skF_3'('#skF_4'),'#skF_5')
    | v9_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_178])).

tff(c_197,plain,
    ( k4_lattices('#skF_4','#skF_3'('#skF_4'),'#skF_5') = k2_lattices('#skF_4','#skF_3'('#skF_4'),'#skF_5')
    | v9_lattices('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_196])).

tff(c_217,plain,(
    v9_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_48,plain,(
    v14_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_431,plain,(
    ! [A_65,C_66] :
      ( k1_lattices(A_65,k6_lattices(A_65),C_66) = k6_lattices(A_65)
      | ~ m1_subset_1(C_66,u1_struct_0(A_65))
      | ~ m1_subset_1(k6_lattices(A_65),u1_struct_0(A_65))
      | ~ v14_lattices(A_65)
      | ~ l2_lattices(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_441,plain,
    ( k1_lattices('#skF_4',k6_lattices('#skF_4'),'#skF_5') = k6_lattices('#skF_4')
    | ~ m1_subset_1(k6_lattices('#skF_4'),u1_struct_0('#skF_4'))
    | ~ v14_lattices('#skF_4')
    | ~ l2_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_431])).

tff(c_448,plain,
    ( k1_lattices('#skF_4',k6_lattices('#skF_4'),'#skF_5') = k6_lattices('#skF_4')
    | ~ m1_subset_1(k6_lattices('#skF_4'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_48,c_441])).

tff(c_449,plain,
    ( k1_lattices('#skF_4',k6_lattices('#skF_4'),'#skF_5') = k6_lattices('#skF_4')
    | ~ m1_subset_1(k6_lattices('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_448])).

tff(c_450,plain,(
    ~ m1_subset_1(k6_lattices('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_449])).

tff(c_453,plain,
    ( ~ l2_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_450])).

tff(c_456,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_453])).

tff(c_458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_456])).

tff(c_460,plain,(
    m1_subset_1(k6_lattices('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_449])).

tff(c_602,plain,(
    ! [A_69,C_70] :
      ( k1_lattices(A_69,C_70,k6_lattices(A_69)) = k6_lattices(A_69)
      | ~ m1_subset_1(C_70,u1_struct_0(A_69))
      | ~ m1_subset_1(k6_lattices(A_69),u1_struct_0(A_69))
      | ~ v14_lattices(A_69)
      | ~ l2_lattices(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_614,plain,
    ( k1_lattices('#skF_4','#skF_5',k6_lattices('#skF_4')) = k6_lattices('#skF_4')
    | ~ m1_subset_1(k6_lattices('#skF_4'),u1_struct_0('#skF_4'))
    | ~ v14_lattices('#skF_4')
    | ~ l2_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_602])).

tff(c_625,plain,
    ( k1_lattices('#skF_4','#skF_5',k6_lattices('#skF_4')) = k6_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_48,c_460,c_614])).

tff(c_626,plain,(
    k1_lattices('#skF_4','#skF_5',k6_lattices('#skF_4')) = k6_lattices('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_625])).

tff(c_218,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_lattices(A_54,B_55,k1_lattices(A_54,B_55,C_56)) = B_55
      | ~ m1_subset_1(C_56,u1_struct_0(A_54))
      | ~ m1_subset_1(B_55,u1_struct_0(A_54))
      | ~ v9_lattices(A_54)
      | ~ l3_lattices(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_232,plain,(
    ! [A_26,B_55] :
      ( k2_lattices(A_26,B_55,k1_lattices(A_26,B_55,k6_lattices(A_26))) = B_55
      | ~ m1_subset_1(B_55,u1_struct_0(A_26))
      | ~ v9_lattices(A_26)
      | ~ l3_lattices(A_26)
      | ~ l2_lattices(A_26)
      | v2_struct_0(A_26) ) ),
    inference(resolution,[status(thm)],[c_34,c_218])).

tff(c_633,plain,
    ( k2_lattices('#skF_4','#skF_5',k6_lattices('#skF_4')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v9_lattices('#skF_4')
    | ~ l3_lattices('#skF_4')
    | ~ l2_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_626,c_232])).

tff(c_639,plain,
    ( k2_lattices('#skF_4','#skF_5',k6_lattices('#skF_4')) = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_46,c_217,c_44,c_633])).

tff(c_640,plain,(
    k2_lattices('#skF_4','#skF_5',k6_lattices('#skF_4')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_639])).

tff(c_40,plain,(
    ! [A_28,B_29,C_30] :
      ( k4_lattices(A_28,B_29,C_30) = k2_lattices(A_28,B_29,C_30)
      | ~ m1_subset_1(C_30,u1_struct_0(A_28))
      | ~ m1_subset_1(B_29,u1_struct_0(A_28))
      | ~ l1_lattices(A_28)
      | ~ v6_lattices(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_480,plain,(
    ! [B_29] :
      ( k4_lattices('#skF_4',B_29,k6_lattices('#skF_4')) = k2_lattices('#skF_4',B_29,k6_lattices('#skF_4'))
      | ~ m1_subset_1(B_29,u1_struct_0('#skF_4'))
      | ~ l1_lattices('#skF_4')
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_460,c_40])).

tff(c_503,plain,(
    ! [B_29] :
      ( k4_lattices('#skF_4',B_29,k6_lattices('#skF_4')) = k2_lattices('#skF_4',B_29,k6_lattices('#skF_4'))
      | ~ m1_subset_1(B_29,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_57,c_480])).

tff(c_647,plain,(
    ! [B_71] :
      ( k4_lattices('#skF_4',B_71,k6_lattices('#skF_4')) = k2_lattices('#skF_4',B_71,k6_lattices('#skF_4'))
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_503])).

tff(c_669,plain,(
    k4_lattices('#skF_4','#skF_5',k6_lattices('#skF_4')) = k2_lattices('#skF_4','#skF_5',k6_lattices('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_647])).

tff(c_689,plain,(
    k4_lattices('#skF_4','#skF_5',k6_lattices('#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_669])).

tff(c_690,plain,(
    k2_lattices('#skF_4',k6_lattices('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_201])).

tff(c_692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_690])).

tff(c_694,plain,(
    ~ v9_lattices('#skF_4') ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_697,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_694])).

tff(c_700,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_697])).

tff(c_702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_700])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:57:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.57  
% 2.91/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.57  %$ m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v14_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k6_lattices > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1
% 2.91/1.57  
% 2.91/1.57  %Foreground sorts:
% 2.91/1.57  
% 2.91/1.57  
% 2.91/1.57  %Background operators:
% 2.91/1.57  
% 2.91/1.57  
% 2.91/1.57  %Foreground operators:
% 2.91/1.57  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.91/1.57  tff(k6_lattices, type, k6_lattices: $i > $i).
% 2.91/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.91/1.57  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 2.91/1.57  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.91/1.57  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.91/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.57  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 2.91/1.57  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 2.91/1.57  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.91/1.57  tff('#skF_5', type, '#skF_5': $i).
% 2.91/1.57  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.91/1.57  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.91/1.57  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.91/1.57  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.91/1.57  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.91/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.57  tff(v14_lattices, type, v14_lattices: $i > $o).
% 2.91/1.57  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.57  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.91/1.57  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.91/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.91/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.91/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.91/1.57  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.91/1.57  
% 2.91/1.60  tff(f_135, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v14_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattices(A, k6_lattices(A), B) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_lattices)).
% 2.91/1.60  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 2.91/1.60  tff(f_107, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.91/1.60  tff(f_101, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => m1_subset_1(k6_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_lattices)).
% 2.91/1.60  tff(f_60, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k4_lattices(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 2.91/1.60  tff(f_120, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 2.91/1.60  tff(f_94, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v9_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, B, C)) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattices)).
% 2.91/1.60  tff(f_79, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (v14_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k6_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k1_lattices(A, B, C) = B) & (k1_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattices)).
% 2.91/1.60  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.91/1.60  tff(c_46, plain, (l3_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.91/1.60  tff(c_50, plain, (v10_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.91/1.60  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.91/1.60  tff(c_58, plain, (![A_33]: (l2_lattices(A_33) | ~l3_lattices(A_33))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.91/1.60  tff(c_62, plain, (l2_lattices('#skF_4')), inference(resolution, [status(thm)], [c_46, c_58])).
% 2.91/1.60  tff(c_34, plain, (![A_26]: (m1_subset_1(k6_lattices(A_26), u1_struct_0(A_26)) | ~l2_lattices(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.91/1.60  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.91/1.60  tff(c_53, plain, (![A_32]: (l1_lattices(A_32) | ~l3_lattices(A_32))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.91/1.60  tff(c_57, plain, (l1_lattices('#skF_4')), inference(resolution, [status(thm)], [c_46, c_53])).
% 2.91/1.60  tff(c_44, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.91/1.60  tff(c_74, plain, (![A_46, C_47, B_48]: (k4_lattices(A_46, C_47, B_48)=k4_lattices(A_46, B_48, C_47) | ~m1_subset_1(C_47, u1_struct_0(A_46)) | ~m1_subset_1(B_48, u1_struct_0(A_46)) | ~l1_lattices(A_46) | ~v6_lattices(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.91/1.60  tff(c_84, plain, (![B_48]: (k4_lattices('#skF_4', B_48, '#skF_5')=k4_lattices('#skF_4', '#skF_5', B_48) | ~m1_subset_1(B_48, u1_struct_0('#skF_4')) | ~l1_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_74])).
% 2.91/1.60  tff(c_91, plain, (![B_48]: (k4_lattices('#skF_4', B_48, '#skF_5')=k4_lattices('#skF_4', '#skF_5', B_48) | ~m1_subset_1(B_48, u1_struct_0('#skF_4')) | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_84])).
% 2.91/1.60  tff(c_92, plain, (![B_48]: (k4_lattices('#skF_4', B_48, '#skF_5')=k4_lattices('#skF_4', '#skF_5', B_48) | ~m1_subset_1(B_48, u1_struct_0('#skF_4')) | ~v6_lattices('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_91])).
% 2.91/1.60  tff(c_93, plain, (~v6_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_92])).
% 2.91/1.60  tff(c_96, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_8, c_93])).
% 2.91/1.60  tff(c_99, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_96])).
% 2.91/1.60  tff(c_101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_99])).
% 2.91/1.60  tff(c_123, plain, (![B_52]: (k4_lattices('#skF_4', B_52, '#skF_5')=k4_lattices('#skF_4', '#skF_5', B_52) | ~m1_subset_1(B_52, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_92])).
% 2.91/1.60  tff(c_139, plain, (k4_lattices('#skF_4', k6_lattices('#skF_4'), '#skF_5')=k4_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4')) | ~l2_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_123])).
% 2.91/1.60  tff(c_157, plain, (k4_lattices('#skF_4', k6_lattices('#skF_4'), '#skF_5')=k4_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_139])).
% 2.91/1.60  tff(c_158, plain, (k4_lattices('#skF_4', k6_lattices('#skF_4'), '#skF_5')=k4_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_157])).
% 2.91/1.60  tff(c_103, plain, (v6_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_92])).
% 2.91/1.60  tff(c_104, plain, (![A_49, B_50, C_51]: (k4_lattices(A_49, B_50, C_51)=k2_lattices(A_49, B_50, C_51) | ~m1_subset_1(C_51, u1_struct_0(A_49)) | ~m1_subset_1(B_50, u1_struct_0(A_49)) | ~l1_lattices(A_49) | ~v6_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.91/1.60  tff(c_114, plain, (![B_50]: (k4_lattices('#skF_4', B_50, '#skF_5')=k2_lattices('#skF_4', B_50, '#skF_5') | ~m1_subset_1(B_50, u1_struct_0('#skF_4')) | ~l1_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_104])).
% 2.91/1.60  tff(c_121, plain, (![B_50]: (k4_lattices('#skF_4', B_50, '#skF_5')=k2_lattices('#skF_4', B_50, '#skF_5') | ~m1_subset_1(B_50, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_57, c_114])).
% 2.91/1.60  tff(c_166, plain, (![B_53]: (k4_lattices('#skF_4', B_53, '#skF_5')=k2_lattices('#skF_4', B_53, '#skF_5') | ~m1_subset_1(B_53, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_121])).
% 2.91/1.60  tff(c_182, plain, (k4_lattices('#skF_4', k6_lattices('#skF_4'), '#skF_5')=k2_lattices('#skF_4', k6_lattices('#skF_4'), '#skF_5') | ~l2_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_166])).
% 2.91/1.60  tff(c_200, plain, (k4_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4'))=k2_lattices('#skF_4', k6_lattices('#skF_4'), '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_158, c_182])).
% 2.91/1.60  tff(c_201, plain, (k4_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4'))=k2_lattices('#skF_4', k6_lattices('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_200])).
% 2.91/1.60  tff(c_42, plain, (k4_lattices('#skF_4', k6_lattices('#skF_4'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.91/1.60  tff(c_161, plain, (k4_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_42])).
% 2.91/1.60  tff(c_207, plain, (k2_lattices('#skF_4', k6_lattices('#skF_4'), '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_201, c_161])).
% 2.91/1.60  tff(c_30, plain, (![A_15]: (m1_subset_1('#skF_3'(A_15), u1_struct_0(A_15)) | v9_lattices(A_15) | ~l3_lattices(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.91/1.60  tff(c_178, plain, (k4_lattices('#skF_4', '#skF_3'('#skF_4'), '#skF_5')=k2_lattices('#skF_4', '#skF_3'('#skF_4'), '#skF_5') | v9_lattices('#skF_4') | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_166])).
% 2.91/1.60  tff(c_196, plain, (k4_lattices('#skF_4', '#skF_3'('#skF_4'), '#skF_5')=k2_lattices('#skF_4', '#skF_3'('#skF_4'), '#skF_5') | v9_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_178])).
% 2.91/1.60  tff(c_197, plain, (k4_lattices('#skF_4', '#skF_3'('#skF_4'), '#skF_5')=k2_lattices('#skF_4', '#skF_3'('#skF_4'), '#skF_5') | v9_lattices('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_196])).
% 2.91/1.60  tff(c_217, plain, (v9_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_197])).
% 2.91/1.60  tff(c_48, plain, (v14_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.91/1.60  tff(c_431, plain, (![A_65, C_66]: (k1_lattices(A_65, k6_lattices(A_65), C_66)=k6_lattices(A_65) | ~m1_subset_1(C_66, u1_struct_0(A_65)) | ~m1_subset_1(k6_lattices(A_65), u1_struct_0(A_65)) | ~v14_lattices(A_65) | ~l2_lattices(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.91/1.60  tff(c_441, plain, (k1_lattices('#skF_4', k6_lattices('#skF_4'), '#skF_5')=k6_lattices('#skF_4') | ~m1_subset_1(k6_lattices('#skF_4'), u1_struct_0('#skF_4')) | ~v14_lattices('#skF_4') | ~l2_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_431])).
% 2.91/1.60  tff(c_448, plain, (k1_lattices('#skF_4', k6_lattices('#skF_4'), '#skF_5')=k6_lattices('#skF_4') | ~m1_subset_1(k6_lattices('#skF_4'), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_48, c_441])).
% 2.91/1.60  tff(c_449, plain, (k1_lattices('#skF_4', k6_lattices('#skF_4'), '#skF_5')=k6_lattices('#skF_4') | ~m1_subset_1(k6_lattices('#skF_4'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_448])).
% 2.91/1.60  tff(c_450, plain, (~m1_subset_1(k6_lattices('#skF_4'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_449])).
% 2.91/1.60  tff(c_453, plain, (~l2_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_450])).
% 2.91/1.60  tff(c_456, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_453])).
% 2.91/1.60  tff(c_458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_456])).
% 2.91/1.60  tff(c_460, plain, (m1_subset_1(k6_lattices('#skF_4'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_449])).
% 2.91/1.60  tff(c_602, plain, (![A_69, C_70]: (k1_lattices(A_69, C_70, k6_lattices(A_69))=k6_lattices(A_69) | ~m1_subset_1(C_70, u1_struct_0(A_69)) | ~m1_subset_1(k6_lattices(A_69), u1_struct_0(A_69)) | ~v14_lattices(A_69) | ~l2_lattices(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.91/1.60  tff(c_614, plain, (k1_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4'))=k6_lattices('#skF_4') | ~m1_subset_1(k6_lattices('#skF_4'), u1_struct_0('#skF_4')) | ~v14_lattices('#skF_4') | ~l2_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_602])).
% 2.91/1.60  tff(c_625, plain, (k1_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4'))=k6_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_48, c_460, c_614])).
% 2.91/1.60  tff(c_626, plain, (k1_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4'))=k6_lattices('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_625])).
% 2.91/1.60  tff(c_218, plain, (![A_54, B_55, C_56]: (k2_lattices(A_54, B_55, k1_lattices(A_54, B_55, C_56))=B_55 | ~m1_subset_1(C_56, u1_struct_0(A_54)) | ~m1_subset_1(B_55, u1_struct_0(A_54)) | ~v9_lattices(A_54) | ~l3_lattices(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.91/1.60  tff(c_232, plain, (![A_26, B_55]: (k2_lattices(A_26, B_55, k1_lattices(A_26, B_55, k6_lattices(A_26)))=B_55 | ~m1_subset_1(B_55, u1_struct_0(A_26)) | ~v9_lattices(A_26) | ~l3_lattices(A_26) | ~l2_lattices(A_26) | v2_struct_0(A_26))), inference(resolution, [status(thm)], [c_34, c_218])).
% 2.91/1.60  tff(c_633, plain, (k2_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4'))='#skF_5' | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v9_lattices('#skF_4') | ~l3_lattices('#skF_4') | ~l2_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_626, c_232])).
% 2.91/1.60  tff(c_639, plain, (k2_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4'))='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_46, c_217, c_44, c_633])).
% 2.91/1.60  tff(c_640, plain, (k2_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_52, c_639])).
% 2.91/1.60  tff(c_40, plain, (![A_28, B_29, C_30]: (k4_lattices(A_28, B_29, C_30)=k2_lattices(A_28, B_29, C_30) | ~m1_subset_1(C_30, u1_struct_0(A_28)) | ~m1_subset_1(B_29, u1_struct_0(A_28)) | ~l1_lattices(A_28) | ~v6_lattices(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.91/1.60  tff(c_480, plain, (![B_29]: (k4_lattices('#skF_4', B_29, k6_lattices('#skF_4'))=k2_lattices('#skF_4', B_29, k6_lattices('#skF_4')) | ~m1_subset_1(B_29, u1_struct_0('#skF_4')) | ~l1_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_460, c_40])).
% 2.91/1.60  tff(c_503, plain, (![B_29]: (k4_lattices('#skF_4', B_29, k6_lattices('#skF_4'))=k2_lattices('#skF_4', B_29, k6_lattices('#skF_4')) | ~m1_subset_1(B_29, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_57, c_480])).
% 2.91/1.60  tff(c_647, plain, (![B_71]: (k4_lattices('#skF_4', B_71, k6_lattices('#skF_4'))=k2_lattices('#skF_4', B_71, k6_lattices('#skF_4')) | ~m1_subset_1(B_71, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_503])).
% 2.91/1.60  tff(c_669, plain, (k4_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4'))=k2_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_647])).
% 2.91/1.60  tff(c_689, plain, (k4_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_640, c_669])).
% 2.91/1.60  tff(c_690, plain, (k2_lattices('#skF_4', k6_lattices('#skF_4'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_689, c_201])).
% 2.91/1.60  tff(c_692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_207, c_690])).
% 2.91/1.60  tff(c_694, plain, (~v9_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_197])).
% 2.91/1.60  tff(c_697, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_2, c_694])).
% 2.91/1.60  tff(c_700, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_697])).
% 2.91/1.60  tff(c_702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_700])).
% 2.91/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.60  
% 2.91/1.60  Inference rules
% 2.91/1.60  ----------------------
% 2.91/1.60  #Ref     : 0
% 2.91/1.60  #Sup     : 123
% 2.91/1.60  #Fact    : 0
% 2.91/1.60  #Define  : 0
% 2.91/1.60  #Split   : 4
% 2.91/1.60  #Chain   : 0
% 2.91/1.60  #Close   : 0
% 2.91/1.60  
% 2.91/1.60  Ordering : KBO
% 2.91/1.60  
% 2.91/1.60  Simplification rules
% 2.91/1.60  ----------------------
% 2.91/1.60  #Subsume      : 0
% 2.91/1.60  #Demod        : 132
% 2.91/1.60  #Tautology    : 71
% 2.91/1.60  #SimpNegUnit  : 50
% 2.91/1.60  #BackRed      : 11
% 2.91/1.60  
% 2.91/1.60  #Partial instantiations: 0
% 2.91/1.60  #Strategies tried      : 1
% 2.91/1.60  
% 2.91/1.60  Timing (in seconds)
% 2.91/1.60  ----------------------
% 2.91/1.60  Preprocessing        : 0.46
% 2.91/1.60  Parsing              : 0.26
% 2.91/1.60  CNF conversion       : 0.03
% 2.91/1.60  Main loop            : 0.32
% 2.91/1.60  Inferencing          : 0.11
% 2.91/1.60  Reduction            : 0.10
% 2.91/1.60  Demodulation         : 0.07
% 2.91/1.60  BG Simplification    : 0.03
% 2.91/1.60  Subsumption          : 0.06
% 2.91/1.60  Abstraction          : 0.03
% 2.91/1.60  MUC search           : 0.00
% 2.91/1.60  Cooper               : 0.00
% 2.91/1.60  Total                : 0.83
% 2.91/1.60  Index Insertion      : 0.00
% 2.91/1.60  Index Deletion       : 0.00
% 2.91/1.60  Index Matching       : 0.00
% 2.91/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
