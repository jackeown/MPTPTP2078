%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1207+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:35 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 387 expanded)
%              Number of leaves         :   32 ( 145 expanded)
%              Depth                    :   15
%              Number of atoms          :  239 (1489 expanded)
%              Number of equality atoms :   14 (  33 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k3_lattices > k1_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_1

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

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_141,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v13_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r3_lattices(A,k5_lattices(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattices)).

tff(f_59,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

tff(f_46,axiom,(
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

tff(f_91,axiom,(
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

tff(f_126,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v13_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k3_lattices(A,k5_lattices(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_lattices)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_lattices(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => r1_lattices(A,B,k1_lattices(A,B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_lattices)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_36,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_43,plain,(
    ! [A_21] :
      ( l1_lattices(A_21)
      | ~ l3_lattices(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_47,plain,(
    l1_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_43])).

tff(c_16,plain,(
    ! [A_2] :
      ( m1_subset_1(k5_lattices(A_2),u1_struct_0(A_2))
      | ~ l1_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_40,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_10,plain,(
    ! [A_1] :
      ( v5_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32,plain,(
    ~ r3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_112,plain,(
    ! [A_36,B_37,C_38] :
      ( r3_lattices(A_36,B_37,C_38)
      | ~ r1_lattices(A_36,B_37,C_38)
      | ~ m1_subset_1(C_38,u1_struct_0(A_36))
      | ~ m1_subset_1(B_37,u1_struct_0(A_36))
      | ~ l3_lattices(A_36)
      | ~ v9_lattices(A_36)
      | ~ v8_lattices(A_36)
      | ~ v6_lattices(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_116,plain,(
    ! [B_37] :
      ( r3_lattices('#skF_1',B_37,'#skF_2')
      | ~ r1_lattices('#skF_1',B_37,'#skF_2')
      | ~ m1_subset_1(B_37,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_112])).

tff(c_120,plain,(
    ! [B_37] :
      ( r3_lattices('#skF_1',B_37,'#skF_2')
      | ~ r1_lattices('#skF_1',B_37,'#skF_2')
      | ~ m1_subset_1(B_37,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_116])).

tff(c_121,plain,(
    ! [B_37] :
      ( r3_lattices('#skF_1',B_37,'#skF_2')
      | ~ r1_lattices('#skF_1',B_37,'#skF_2')
      | ~ m1_subset_1(B_37,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_120])).

tff(c_135,plain,(
    ~ v6_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_138,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_135])).

tff(c_141,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_40,c_138])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_141])).

tff(c_144,plain,(
    ! [B_37] :
      ( ~ v8_lattices('#skF_1')
      | ~ v9_lattices('#skF_1')
      | r3_lattices('#skF_1',B_37,'#skF_2')
      | ~ r1_lattices('#skF_1',B_37,'#skF_2')
      | ~ m1_subset_1(B_37,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_146,plain,(
    ~ v9_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_149,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_146])).

tff(c_152,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_40,c_149])).

tff(c_154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_152])).

tff(c_155,plain,(
    ! [B_37] :
      ( ~ v8_lattices('#skF_1')
      | r3_lattices('#skF_1',B_37,'#skF_2')
      | ~ r1_lattices('#skF_1',B_37,'#skF_2')
      | ~ m1_subset_1(B_37,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_157,plain,(
    ~ v8_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_161,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_157])).

tff(c_164,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_40,c_161])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_164])).

tff(c_169,plain,(
    ! [B_43] :
      ( r3_lattices('#skF_1',B_43,'#skF_2')
      | ~ r1_lattices('#skF_1',B_43,'#skF_2')
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_173,plain,
    ( r3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | ~ r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | ~ l1_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_169])).

tff(c_179,plain,
    ( r3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | ~ r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_173])).

tff(c_180,plain,(
    ~ r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_32,c_179])).

tff(c_145,plain,(
    v6_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_168,plain,(
    v8_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_156,plain,(
    v9_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_38,plain,(
    v13_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_60,plain,(
    ! [A_30,B_31] :
      ( k3_lattices(A_30,k5_lattices(A_30),B_31) = B_31
      | ~ m1_subset_1(B_31,u1_struct_0(A_30))
      | ~ l3_lattices(A_30)
      | ~ v13_lattices(A_30)
      | ~ v10_lattices(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_64,plain,
    ( k3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = '#skF_2'
    | ~ l3_lattices('#skF_1')
    | ~ v13_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_60])).

tff(c_68,plain,
    ( k3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = '#skF_2'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_64])).

tff(c_69,plain,(
    k3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_68])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,(
    ! [A_22] :
      ( l2_lattices(A_22)
      | ~ l3_lattices(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    l2_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_48])).

tff(c_74,plain,(
    ! [A_32,B_33,C_34] :
      ( k3_lattices(A_32,B_33,C_34) = k1_lattices(A_32,B_33,C_34)
      | ~ m1_subset_1(C_34,u1_struct_0(A_32))
      | ~ m1_subset_1(B_33,u1_struct_0(A_32))
      | ~ l2_lattices(A_32)
      | ~ v4_lattices(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_78,plain,(
    ! [B_33] :
      ( k3_lattices('#skF_1',B_33,'#skF_2') = k1_lattices('#skF_1',B_33,'#skF_2')
      | ~ m1_subset_1(B_33,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_74])).

tff(c_82,plain,(
    ! [B_33] :
      ( k3_lattices('#skF_1',B_33,'#skF_2') = k1_lattices('#skF_1',B_33,'#skF_2')
      | ~ m1_subset_1(B_33,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_78])).

tff(c_83,plain,(
    ! [B_33] :
      ( k3_lattices('#skF_1',B_33,'#skF_2') = k1_lattices('#skF_1',B_33,'#skF_2')
      | ~ m1_subset_1(B_33,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_82])).

tff(c_84,plain,(
    ~ v4_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_87,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_84])).

tff(c_90,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_40,c_87])).

tff(c_92,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_90])).

tff(c_95,plain,(
    ! [B_35] :
      ( k3_lattices('#skF_1',B_35,'#skF_2') = k1_lattices('#skF_1',B_35,'#skF_2')
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_99,plain,
    ( k3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = k1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | ~ l1_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_95])).

tff(c_105,plain,
    ( k1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = '#skF_2'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_69,c_99])).

tff(c_106,plain,(
    k1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_105])).

tff(c_226,plain,(
    ! [A_53,B_54,C_55] :
      ( r1_lattices(A_53,B_54,k1_lattices(A_53,B_54,C_55))
      | ~ m1_subset_1(C_55,u1_struct_0(A_53))
      | ~ m1_subset_1(B_54,u1_struct_0(A_53))
      | ~ l3_lattices(A_53)
      | ~ v9_lattices(A_53)
      | ~ v8_lattices(A_53)
      | ~ v6_lattices(A_53)
      | ~ v5_lattices(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_232,plain,
    ( r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k5_lattices('#skF_1'),u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | ~ v9_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | ~ v5_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_226])).

tff(c_234,plain,
    ( r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_1'),u1_struct_0('#skF_1'))
    | ~ v5_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_168,c_156,c_36,c_34,c_232])).

tff(c_235,plain,
    ( ~ m1_subset_1(k5_lattices('#skF_1'),u1_struct_0('#skF_1'))
    | ~ v5_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_180,c_234])).

tff(c_236,plain,(
    ~ v5_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_235])).

tff(c_239,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_236])).

tff(c_242,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_40,c_239])).

tff(c_244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_242])).

tff(c_245,plain,(
    ~ m1_subset_1(k5_lattices('#skF_1'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_249,plain,
    ( ~ l1_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_245])).

tff(c_252,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_249])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_252])).

%------------------------------------------------------------------------------
