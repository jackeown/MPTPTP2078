%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:16 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 229 expanded)
%              Number of leaves         :   32 (  94 expanded)
%              Depth                    :   12
%              Number of atoms          :  207 ( 785 expanded)
%              Number of equality atoms :   22 (  54 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_1

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

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_lattices,type,(
    k4_lattices: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v13_lattices,type,(
    v13_lattices: $i > $o )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_lattices,type,(
    k5_lattices: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_140,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v13_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r3_lattices(A,k5_lattices(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattices)).

tff(f_60,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_125,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v13_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k4_lattices(A,k5_lattices(A),B) = k5_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattices)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(f_111,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_lattices(A,B,C)
      <=> r1_lattices(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_34,plain,(
    ~ r3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_38,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_45,plain,(
    ! [A_21] :
      ( l1_lattices(A_21)
      | ~ l3_lattices(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_49,plain,(
    l1_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_45])).

tff(c_42,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_40,plain,(
    v13_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_62,plain,(
    ! [A_30,B_31] :
      ( k4_lattices(A_30,k5_lattices(A_30),B_31) = k5_lattices(A_30)
      | ~ m1_subset_1(B_31,u1_struct_0(A_30))
      | ~ l3_lattices(A_30)
      | ~ v13_lattices(A_30)
      | ~ v10_lattices(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_66,plain,
    ( k4_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = k5_lattices('#skF_1')
    | ~ l3_lattices('#skF_1')
    | ~ v13_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_62])).

tff(c_70,plain,
    ( k4_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = k5_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_66])).

tff(c_71,plain,(
    k4_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = k5_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_70])).

tff(c_16,plain,(
    ! [A_2] :
      ( m1_subset_1(k5_lattices(A_2),u1_struct_0(A_2))
      | ~ l1_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_76,plain,(
    ! [A_32,B_33,C_34] :
      ( k4_lattices(A_32,B_33,C_34) = k2_lattices(A_32,B_33,C_34)
      | ~ m1_subset_1(C_34,u1_struct_0(A_32))
      | ~ m1_subset_1(B_33,u1_struct_0(A_32))
      | ~ l1_lattices(A_32)
      | ~ v6_lattices(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_80,plain,(
    ! [B_33] :
      ( k4_lattices('#skF_1',B_33,'#skF_2') = k2_lattices('#skF_1',B_33,'#skF_2')
      | ~ m1_subset_1(B_33,u1_struct_0('#skF_1'))
      | ~ l1_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_76])).

tff(c_84,plain,(
    ! [B_33] :
      ( k4_lattices('#skF_1',B_33,'#skF_2') = k2_lattices('#skF_1',B_33,'#skF_2')
      | ~ m1_subset_1(B_33,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_80])).

tff(c_85,plain,(
    ! [B_33] :
      ( k4_lattices('#skF_1',B_33,'#skF_2') = k2_lattices('#skF_1',B_33,'#skF_2')
      | ~ m1_subset_1(B_33,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_84])).

tff(c_86,plain,(
    ~ v6_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_89,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_86])).

tff(c_92,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_89])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_92])).

tff(c_97,plain,(
    ! [B_35] :
      ( k4_lattices('#skF_1',B_35,'#skF_2') = k2_lattices('#skF_1',B_35,'#skF_2')
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_101,plain,
    ( k4_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = k2_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | ~ l1_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_97])).

tff(c_107,plain,
    ( k2_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = k5_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_71,c_101])).

tff(c_108,plain,(
    k2_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = k5_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_107])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_114,plain,(
    ! [A_36,B_37,C_38] :
      ( r1_lattices(A_36,B_37,C_38)
      | k2_lattices(A_36,B_37,C_38) != B_37
      | ~ m1_subset_1(C_38,u1_struct_0(A_36))
      | ~ m1_subset_1(B_37,u1_struct_0(A_36))
      | ~ l3_lattices(A_36)
      | ~ v9_lattices(A_36)
      | ~ v8_lattices(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_118,plain,(
    ! [B_37] :
      ( r1_lattices('#skF_1',B_37,'#skF_2')
      | k2_lattices('#skF_1',B_37,'#skF_2') != B_37
      | ~ m1_subset_1(B_37,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_114])).

tff(c_122,plain,(
    ! [B_37] :
      ( r1_lattices('#skF_1',B_37,'#skF_2')
      | k2_lattices('#skF_1',B_37,'#skF_2') != B_37
      | ~ m1_subset_1(B_37,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_118])).

tff(c_123,plain,(
    ! [B_37] :
      ( r1_lattices('#skF_1',B_37,'#skF_2')
      | k2_lattices('#skF_1',B_37,'#skF_2') != B_37
      | ~ m1_subset_1(B_37,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_122])).

tff(c_128,plain,(
    ~ v8_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_131,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_128])).

tff(c_134,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_131])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_134])).

tff(c_137,plain,(
    ! [B_37] :
      ( ~ v9_lattices('#skF_1')
      | r1_lattices('#skF_1',B_37,'#skF_2')
      | k2_lattices('#skF_1',B_37,'#skF_2') != B_37
      | ~ m1_subset_1(B_37,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_139,plain,(
    ~ v9_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_142,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_139])).

tff(c_145,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_142])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_145])).

tff(c_150,plain,(
    ! [B_39] :
      ( r1_lattices('#skF_1',B_39,'#skF_2')
      | k2_lattices('#skF_1',B_39,'#skF_2') != B_39
      | ~ m1_subset_1(B_39,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_154,plain,
    ( r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | k2_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') != k5_lattices('#skF_1')
    | ~ l1_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_150])).

tff(c_160,plain,
    ( r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_108,c_154])).

tff(c_161,plain,(
    r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_160])).

tff(c_96,plain,(
    v6_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_138,plain,(
    v8_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_149,plain,(
    v9_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_219,plain,(
    ! [A_51,B_52,C_53] :
      ( r3_lattices(A_51,B_52,C_53)
      | ~ r1_lattices(A_51,B_52,C_53)
      | ~ m1_subset_1(C_53,u1_struct_0(A_51))
      | ~ m1_subset_1(B_52,u1_struct_0(A_51))
      | ~ l3_lattices(A_51)
      | ~ v9_lattices(A_51)
      | ~ v8_lattices(A_51)
      | ~ v6_lattices(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_223,plain,(
    ! [B_52] :
      ( r3_lattices('#skF_1',B_52,'#skF_2')
      | ~ r1_lattices('#skF_1',B_52,'#skF_2')
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_219])).

tff(c_227,plain,(
    ! [B_52] :
      ( r3_lattices('#skF_1',B_52,'#skF_2')
      | ~ r1_lattices('#skF_1',B_52,'#skF_2')
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_138,c_149,c_38,c_223])).

tff(c_229,plain,(
    ! [B_54] :
      ( r3_lattices('#skF_1',B_54,'#skF_2')
      | ~ r1_lattices('#skF_1',B_54,'#skF_2')
      | ~ m1_subset_1(B_54,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_227])).

tff(c_233,plain,
    ( r3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | ~ r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | ~ l1_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_229])).

tff(c_239,plain,
    ( r3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_161,c_233])).

tff(c_241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_34,c_239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.32  
% 2.49/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.32  %$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_1
% 2.49/1.32  
% 2.49/1.32  %Foreground sorts:
% 2.49/1.32  
% 2.49/1.32  
% 2.49/1.32  %Background operators:
% 2.49/1.32  
% 2.49/1.32  
% 2.49/1.32  %Foreground operators:
% 2.49/1.32  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.49/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.49/1.32  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 2.49/1.32  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.49/1.32  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 2.49/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.32  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 2.49/1.32  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.49/1.32  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.49/1.32  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.49/1.32  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.49/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.32  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.49/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.32  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.49/1.32  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.49/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.32  tff(v13_lattices, type, v13_lattices: $i > $o).
% 2.49/1.32  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.49/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.32  tff(k5_lattices, type, k5_lattices: $i > $i).
% 2.49/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.49/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.32  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.49/1.32  
% 2.49/1.34  tff(f_140, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r3_lattices(A, k5_lattices(A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_lattices)).
% 2.49/1.34  tff(f_60, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.49/1.34  tff(f_125, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattices(A, k5_lattices(A), B) = k5_lattices(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_lattices)).
% 2.49/1.34  tff(f_54, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 2.49/1.34  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 2.49/1.34  tff(f_73, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 2.49/1.34  tff(f_111, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 2.49/1.34  tff(f_92, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 2.49/1.34  tff(c_44, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.49/1.34  tff(c_34, plain, (~r3_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.49/1.34  tff(c_38, plain, (l3_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.49/1.34  tff(c_45, plain, (![A_21]: (l1_lattices(A_21) | ~l3_lattices(A_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.49/1.34  tff(c_49, plain, (l1_lattices('#skF_1')), inference(resolution, [status(thm)], [c_38, c_45])).
% 2.49/1.34  tff(c_42, plain, (v10_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.49/1.34  tff(c_40, plain, (v13_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.49/1.34  tff(c_36, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.49/1.34  tff(c_62, plain, (![A_30, B_31]: (k4_lattices(A_30, k5_lattices(A_30), B_31)=k5_lattices(A_30) | ~m1_subset_1(B_31, u1_struct_0(A_30)) | ~l3_lattices(A_30) | ~v13_lattices(A_30) | ~v10_lattices(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.49/1.34  tff(c_66, plain, (k4_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')=k5_lattices('#skF_1') | ~l3_lattices('#skF_1') | ~v13_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_62])).
% 2.49/1.34  tff(c_70, plain, (k4_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')=k5_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_66])).
% 2.49/1.34  tff(c_71, plain, (k4_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')=k5_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_70])).
% 2.49/1.34  tff(c_16, plain, (![A_2]: (m1_subset_1(k5_lattices(A_2), u1_struct_0(A_2)) | ~l1_lattices(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.49/1.34  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.49/1.34  tff(c_76, plain, (![A_32, B_33, C_34]: (k4_lattices(A_32, B_33, C_34)=k2_lattices(A_32, B_33, C_34) | ~m1_subset_1(C_34, u1_struct_0(A_32)) | ~m1_subset_1(B_33, u1_struct_0(A_32)) | ~l1_lattices(A_32) | ~v6_lattices(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.49/1.34  tff(c_80, plain, (![B_33]: (k4_lattices('#skF_1', B_33, '#skF_2')=k2_lattices('#skF_1', B_33, '#skF_2') | ~m1_subset_1(B_33, u1_struct_0('#skF_1')) | ~l1_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_76])).
% 2.49/1.34  tff(c_84, plain, (![B_33]: (k4_lattices('#skF_1', B_33, '#skF_2')=k2_lattices('#skF_1', B_33, '#skF_2') | ~m1_subset_1(B_33, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_80])).
% 2.49/1.34  tff(c_85, plain, (![B_33]: (k4_lattices('#skF_1', B_33, '#skF_2')=k2_lattices('#skF_1', B_33, '#skF_2') | ~m1_subset_1(B_33, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_84])).
% 2.49/1.34  tff(c_86, plain, (~v6_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_85])).
% 2.49/1.34  tff(c_89, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_8, c_86])).
% 2.49/1.34  tff(c_92, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_89])).
% 2.49/1.34  tff(c_94, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_92])).
% 2.49/1.34  tff(c_97, plain, (![B_35]: (k4_lattices('#skF_1', B_35, '#skF_2')=k2_lattices('#skF_1', B_35, '#skF_2') | ~m1_subset_1(B_35, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_85])).
% 2.49/1.34  tff(c_101, plain, (k4_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')=k2_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | ~l1_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_97])).
% 2.49/1.34  tff(c_107, plain, (k2_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')=k5_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_71, c_101])).
% 2.49/1.34  tff(c_108, plain, (k2_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')=k5_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_107])).
% 2.49/1.34  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.49/1.34  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.49/1.34  tff(c_114, plain, (![A_36, B_37, C_38]: (r1_lattices(A_36, B_37, C_38) | k2_lattices(A_36, B_37, C_38)!=B_37 | ~m1_subset_1(C_38, u1_struct_0(A_36)) | ~m1_subset_1(B_37, u1_struct_0(A_36)) | ~l3_lattices(A_36) | ~v9_lattices(A_36) | ~v8_lattices(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.49/1.34  tff(c_118, plain, (![B_37]: (r1_lattices('#skF_1', B_37, '#skF_2') | k2_lattices('#skF_1', B_37, '#skF_2')!=B_37 | ~m1_subset_1(B_37, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_114])).
% 2.49/1.34  tff(c_122, plain, (![B_37]: (r1_lattices('#skF_1', B_37, '#skF_2') | k2_lattices('#skF_1', B_37, '#skF_2')!=B_37 | ~m1_subset_1(B_37, u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_118])).
% 2.49/1.34  tff(c_123, plain, (![B_37]: (r1_lattices('#skF_1', B_37, '#skF_2') | k2_lattices('#skF_1', B_37, '#skF_2')!=B_37 | ~m1_subset_1(B_37, u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_122])).
% 2.49/1.34  tff(c_128, plain, (~v8_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_123])).
% 2.49/1.34  tff(c_131, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_4, c_128])).
% 2.49/1.34  tff(c_134, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_131])).
% 2.49/1.34  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_134])).
% 2.49/1.34  tff(c_137, plain, (![B_37]: (~v9_lattices('#skF_1') | r1_lattices('#skF_1', B_37, '#skF_2') | k2_lattices('#skF_1', B_37, '#skF_2')!=B_37 | ~m1_subset_1(B_37, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_123])).
% 2.49/1.34  tff(c_139, plain, (~v9_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_137])).
% 2.49/1.34  tff(c_142, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_2, c_139])).
% 2.49/1.34  tff(c_145, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_142])).
% 2.49/1.34  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_145])).
% 2.49/1.34  tff(c_150, plain, (![B_39]: (r1_lattices('#skF_1', B_39, '#skF_2') | k2_lattices('#skF_1', B_39, '#skF_2')!=B_39 | ~m1_subset_1(B_39, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_137])).
% 2.49/1.34  tff(c_154, plain, (r1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | k2_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')!=k5_lattices('#skF_1') | ~l1_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_150])).
% 2.49/1.34  tff(c_160, plain, (r1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_108, c_154])).
% 2.49/1.34  tff(c_161, plain, (r1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44, c_160])).
% 2.49/1.34  tff(c_96, plain, (v6_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_85])).
% 2.49/1.34  tff(c_138, plain, (v8_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_123])).
% 2.49/1.34  tff(c_149, plain, (v9_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_137])).
% 2.49/1.34  tff(c_219, plain, (![A_51, B_52, C_53]: (r3_lattices(A_51, B_52, C_53) | ~r1_lattices(A_51, B_52, C_53) | ~m1_subset_1(C_53, u1_struct_0(A_51)) | ~m1_subset_1(B_52, u1_struct_0(A_51)) | ~l3_lattices(A_51) | ~v9_lattices(A_51) | ~v8_lattices(A_51) | ~v6_lattices(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.49/1.34  tff(c_223, plain, (![B_52]: (r3_lattices('#skF_1', B_52, '#skF_2') | ~r1_lattices('#skF_1', B_52, '#skF_2') | ~m1_subset_1(B_52, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_219])).
% 2.49/1.34  tff(c_227, plain, (![B_52]: (r3_lattices('#skF_1', B_52, '#skF_2') | ~r1_lattices('#skF_1', B_52, '#skF_2') | ~m1_subset_1(B_52, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_138, c_149, c_38, c_223])).
% 2.49/1.34  tff(c_229, plain, (![B_54]: (r3_lattices('#skF_1', B_54, '#skF_2') | ~r1_lattices('#skF_1', B_54, '#skF_2') | ~m1_subset_1(B_54, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_44, c_227])).
% 2.49/1.34  tff(c_233, plain, (r3_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | ~r1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | ~l1_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_229])).
% 2.49/1.34  tff(c_239, plain, (r3_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_161, c_233])).
% 2.49/1.34  tff(c_241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_34, c_239])).
% 2.49/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.34  
% 2.49/1.34  Inference rules
% 2.49/1.34  ----------------------
% 2.49/1.34  #Ref     : 0
% 2.49/1.34  #Sup     : 38
% 2.49/1.34  #Fact    : 0
% 2.49/1.34  #Define  : 0
% 2.49/1.34  #Split   : 4
% 2.49/1.34  #Chain   : 0
% 2.49/1.34  #Close   : 0
% 2.49/1.34  
% 2.49/1.34  Ordering : KBO
% 2.49/1.34  
% 2.49/1.34  Simplification rules
% 2.49/1.34  ----------------------
% 2.49/1.34  #Subsume      : 1
% 2.49/1.34  #Demod        : 28
% 2.49/1.34  #Tautology    : 16
% 2.49/1.34  #SimpNegUnit  : 12
% 2.49/1.34  #BackRed      : 0
% 2.49/1.34  
% 2.49/1.34  #Partial instantiations: 0
% 2.49/1.34  #Strategies tried      : 1
% 2.49/1.34  
% 2.49/1.34  Timing (in seconds)
% 2.49/1.34  ----------------------
% 2.49/1.34  Preprocessing        : 0.34
% 2.49/1.34  Parsing              : 0.18
% 2.49/1.34  CNF conversion       : 0.02
% 2.49/1.34  Main loop            : 0.21
% 2.64/1.34  Inferencing          : 0.09
% 2.64/1.34  Reduction            : 0.06
% 2.64/1.34  Demodulation         : 0.04
% 2.64/1.34  BG Simplification    : 0.02
% 2.64/1.35  Subsumption          : 0.04
% 2.64/1.35  Abstraction          : 0.01
% 2.64/1.35  MUC search           : 0.00
% 2.64/1.35  Cooper               : 0.00
% 2.64/1.35  Total                : 0.59
% 2.64/1.35  Index Insertion      : 0.00
% 2.64/1.35  Index Deletion       : 0.00
% 2.64/1.35  Index Matching       : 0.00
% 2.64/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
