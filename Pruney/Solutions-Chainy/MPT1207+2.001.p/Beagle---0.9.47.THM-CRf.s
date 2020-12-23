%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:16 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 755 expanded)
%              Number of leaves         :   31 ( 276 expanded)
%              Depth                    :   18
%              Number of atoms          :  213 (2606 expanded)
%              Number of equality atoms :   14 ( 178 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v13_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r3_lattices(A,k5_lattices(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattices)).

tff(f_73,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_67,axiom,(
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

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k4_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v13_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k4_lattices(A,k5_lattices(A),B) = k5_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattices)).

tff(f_109,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattices)).

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

tff(c_32,plain,(
    ~ r3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_36,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_43,plain,(
    ! [A_21] :
      ( l1_lattices(A_21)
      | ~ l3_lattices(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_47,plain,(
    l1_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_43])).

tff(c_18,plain,(
    ! [A_5] :
      ( m1_subset_1(k5_lattices(A_5),u1_struct_0(A_5))
      | ~ l1_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_74,plain,(
    ! [A_32,C_33,B_34] :
      ( k4_lattices(A_32,C_33,B_34) = k4_lattices(A_32,B_34,C_33)
      | ~ m1_subset_1(C_33,u1_struct_0(A_32))
      | ~ m1_subset_1(B_34,u1_struct_0(A_32))
      | ~ l1_lattices(A_32)
      | ~ v6_lattices(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_78,plain,(
    ! [B_34] :
      ( k4_lattices('#skF_1',B_34,'#skF_2') = k4_lattices('#skF_1','#skF_2',B_34)
      | ~ m1_subset_1(B_34,u1_struct_0('#skF_1'))
      | ~ l1_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_74])).

tff(c_82,plain,(
    ! [B_34] :
      ( k4_lattices('#skF_1',B_34,'#skF_2') = k4_lattices('#skF_1','#skF_2',B_34)
      | ~ m1_subset_1(B_34,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_78])).

tff(c_83,plain,(
    ! [B_34] :
      ( k4_lattices('#skF_1',B_34,'#skF_2') = k4_lattices('#skF_1','#skF_2',B_34)
      | ~ m1_subset_1(B_34,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_82])).

tff(c_84,plain,(
    ~ v6_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_87,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_84])).

tff(c_90,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_40,c_87])).

tff(c_92,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_90])).

tff(c_94,plain,(
    v6_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_38,plain,(
    v13_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_60,plain,(
    ! [A_30,B_31] :
      ( k4_lattices(A_30,k5_lattices(A_30),B_31) = k5_lattices(A_30)
      | ~ m1_subset_1(B_31,u1_struct_0(A_30))
      | ~ l3_lattices(A_30)
      | ~ v13_lattices(A_30)
      | ~ v10_lattices(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_64,plain,
    ( k4_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = k5_lattices('#skF_1')
    | ~ l3_lattices('#skF_1')
    | ~ v13_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_60])).

tff(c_68,plain,
    ( k4_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = k5_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_64])).

tff(c_69,plain,(
    k4_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = k5_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_68])).

tff(c_95,plain,(
    ! [B_35] :
      ( k4_lattices('#skF_1',B_35,'#skF_2') = k4_lattices('#skF_1','#skF_2',B_35)
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_99,plain,
    ( k4_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = k4_lattices('#skF_1','#skF_2',k5_lattices('#skF_1'))
    | ~ l1_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_95])).

tff(c_105,plain,
    ( k4_lattices('#skF_1','#skF_2',k5_lattices('#skF_1')) = k5_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_69,c_99])).

tff(c_106,plain,(
    k4_lattices('#skF_1','#skF_2',k5_lattices('#skF_1')) = k5_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_105])).

tff(c_113,plain,(
    ! [A_36,B_37,C_38] :
      ( r1_lattices(A_36,k4_lattices(A_36,B_37,C_38),B_37)
      | ~ m1_subset_1(C_38,u1_struct_0(A_36))
      | ~ m1_subset_1(B_37,u1_struct_0(A_36))
      | ~ l3_lattices(A_36)
      | ~ v8_lattices(A_36)
      | ~ v6_lattices(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_116,plain,
    ( r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_1'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_113])).

tff(c_121,plain,
    ( r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_1'),u1_struct_0('#skF_1'))
    | ~ v8_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_36,c_34,c_116])).

tff(c_122,plain,
    ( r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_1'),u1_struct_0('#skF_1'))
    | ~ v8_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_121])).

tff(c_126,plain,(
    ~ v8_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_129,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_126])).

tff(c_132,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_40,c_129])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_132])).

tff(c_136,plain,(
    v8_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_119,plain,
    ( r1_lattices('#skF_1',k5_lattices('#skF_1'),k5_lattices('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k5_lattices('#skF_1'),u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_113])).

tff(c_124,plain,
    ( r1_lattices('#skF_1',k5_lattices('#skF_1'),k5_lattices('#skF_1'))
    | ~ m1_subset_1(k5_lattices('#skF_1'),u1_struct_0('#skF_1'))
    | ~ v8_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_36,c_34,c_119])).

tff(c_125,plain,
    ( r1_lattices('#skF_1',k5_lattices('#skF_1'),k5_lattices('#skF_1'))
    | ~ m1_subset_1(k5_lattices('#skF_1'),u1_struct_0('#skF_1'))
    | ~ v8_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_124])).

tff(c_138,plain,
    ( r1_lattices('#skF_1',k5_lattices('#skF_1'),k5_lattices('#skF_1'))
    | ~ m1_subset_1(k5_lattices('#skF_1'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_125])).

tff(c_139,plain,(
    ~ m1_subset_1(k5_lattices('#skF_1'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_142,plain,
    ( ~ l1_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_139])).

tff(c_145,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_142])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_145])).

tff(c_149,plain,(
    m1_subset_1(k5_lattices('#skF_1'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_135,plain,
    ( ~ m1_subset_1(k5_lattices('#skF_1'),u1_struct_0('#skF_1'))
    | r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_178,plain,(
    r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_135])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_242,plain,(
    ! [A_46,B_47,C_48] :
      ( r3_lattices(A_46,B_47,C_48)
      | ~ r1_lattices(A_46,B_47,C_48)
      | ~ m1_subset_1(C_48,u1_struct_0(A_46))
      | ~ m1_subset_1(B_47,u1_struct_0(A_46))
      | ~ l3_lattices(A_46)
      | ~ v9_lattices(A_46)
      | ~ v8_lattices(A_46)
      | ~ v6_lattices(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_248,plain,(
    ! [B_47] :
      ( r3_lattices('#skF_1',B_47,'#skF_2')
      | ~ r1_lattices('#skF_1',B_47,'#skF_2')
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_242])).

tff(c_256,plain,(
    ! [B_47] :
      ( r3_lattices('#skF_1',B_47,'#skF_2')
      | ~ r1_lattices('#skF_1',B_47,'#skF_2')
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_136,c_36,c_248])).

tff(c_257,plain,(
    ! [B_47] :
      ( r3_lattices('#skF_1',B_47,'#skF_2')
      | ~ r1_lattices('#skF_1',B_47,'#skF_2')
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_256])).

tff(c_258,plain,(
    ~ v9_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_261,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_258])).

tff(c_264,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_40,c_261])).

tff(c_266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_264])).

tff(c_269,plain,(
    ! [B_49] :
      ( r3_lattices('#skF_1',B_49,'#skF_2')
      | ~ r1_lattices('#skF_1',B_49,'#skF_2')
      | ~ m1_subset_1(B_49,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_272,plain,
    ( r3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | ~ r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_149,c_269])).

tff(c_282,plain,(
    r3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_272])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.34  
% 2.24/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.34  %$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_1
% 2.24/1.34  
% 2.24/1.34  %Foreground sorts:
% 2.24/1.34  
% 2.24/1.34  
% 2.24/1.34  %Background operators:
% 2.24/1.34  
% 2.24/1.34  
% 2.24/1.34  %Foreground operators:
% 2.24/1.34  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.24/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.24/1.34  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.24/1.34  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 2.24/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.34  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 2.24/1.34  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.24/1.34  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.24/1.34  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.24/1.34  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.24/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.34  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.24/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.34  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.24/1.34  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.24/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.34  tff(v13_lattices, type, v13_lattices: $i > $o).
% 2.24/1.34  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.24/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.34  tff(k5_lattices, type, k5_lattices: $i > $i).
% 2.24/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.24/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.34  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.24/1.34  
% 2.24/1.35  tff(f_138, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r3_lattices(A, k5_lattices(A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_lattices)).
% 2.24/1.35  tff(f_73, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.24/1.35  tff(f_67, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 2.24/1.35  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 2.24/1.35  tff(f_60, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k4_lattices(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 2.24/1.35  tff(f_123, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattices(A, k5_lattices(A), B) = k5_lattices(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_lattices)).
% 2.24/1.35  tff(f_109, axiom, (![A]: ((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => r1_lattices(A, k4_lattices(A, B, C), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_lattices)).
% 2.24/1.35  tff(f_92, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 2.24/1.35  tff(c_32, plain, (~r3_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.24/1.35  tff(c_42, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.24/1.35  tff(c_36, plain, (l3_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.24/1.35  tff(c_43, plain, (![A_21]: (l1_lattices(A_21) | ~l3_lattices(A_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.24/1.35  tff(c_47, plain, (l1_lattices('#skF_1')), inference(resolution, [status(thm)], [c_36, c_43])).
% 2.24/1.35  tff(c_18, plain, (![A_5]: (m1_subset_1(k5_lattices(A_5), u1_struct_0(A_5)) | ~l1_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.24/1.35  tff(c_40, plain, (v10_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.24/1.35  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.24/1.35  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.24/1.35  tff(c_34, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.24/1.35  tff(c_74, plain, (![A_32, C_33, B_34]: (k4_lattices(A_32, C_33, B_34)=k4_lattices(A_32, B_34, C_33) | ~m1_subset_1(C_33, u1_struct_0(A_32)) | ~m1_subset_1(B_34, u1_struct_0(A_32)) | ~l1_lattices(A_32) | ~v6_lattices(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.24/1.35  tff(c_78, plain, (![B_34]: (k4_lattices('#skF_1', B_34, '#skF_2')=k4_lattices('#skF_1', '#skF_2', B_34) | ~m1_subset_1(B_34, u1_struct_0('#skF_1')) | ~l1_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_74])).
% 2.24/1.35  tff(c_82, plain, (![B_34]: (k4_lattices('#skF_1', B_34, '#skF_2')=k4_lattices('#skF_1', '#skF_2', B_34) | ~m1_subset_1(B_34, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_78])).
% 2.24/1.35  tff(c_83, plain, (![B_34]: (k4_lattices('#skF_1', B_34, '#skF_2')=k4_lattices('#skF_1', '#skF_2', B_34) | ~m1_subset_1(B_34, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_42, c_82])).
% 2.24/1.35  tff(c_84, plain, (~v6_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_83])).
% 2.24/1.35  tff(c_87, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_8, c_84])).
% 2.24/1.35  tff(c_90, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_40, c_87])).
% 2.24/1.35  tff(c_92, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_90])).
% 2.24/1.35  tff(c_94, plain, (v6_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_83])).
% 2.24/1.35  tff(c_38, plain, (v13_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.24/1.35  tff(c_60, plain, (![A_30, B_31]: (k4_lattices(A_30, k5_lattices(A_30), B_31)=k5_lattices(A_30) | ~m1_subset_1(B_31, u1_struct_0(A_30)) | ~l3_lattices(A_30) | ~v13_lattices(A_30) | ~v10_lattices(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.24/1.35  tff(c_64, plain, (k4_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')=k5_lattices('#skF_1') | ~l3_lattices('#skF_1') | ~v13_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_60])).
% 2.24/1.35  tff(c_68, plain, (k4_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')=k5_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_64])).
% 2.24/1.35  tff(c_69, plain, (k4_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')=k5_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_68])).
% 2.24/1.35  tff(c_95, plain, (![B_35]: (k4_lattices('#skF_1', B_35, '#skF_2')=k4_lattices('#skF_1', '#skF_2', B_35) | ~m1_subset_1(B_35, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_83])).
% 2.24/1.35  tff(c_99, plain, (k4_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')=k4_lattices('#skF_1', '#skF_2', k5_lattices('#skF_1')) | ~l1_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_95])).
% 2.24/1.35  tff(c_105, plain, (k4_lattices('#skF_1', '#skF_2', k5_lattices('#skF_1'))=k5_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_69, c_99])).
% 2.24/1.35  tff(c_106, plain, (k4_lattices('#skF_1', '#skF_2', k5_lattices('#skF_1'))=k5_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_105])).
% 2.24/1.35  tff(c_113, plain, (![A_36, B_37, C_38]: (r1_lattices(A_36, k4_lattices(A_36, B_37, C_38), B_37) | ~m1_subset_1(C_38, u1_struct_0(A_36)) | ~m1_subset_1(B_37, u1_struct_0(A_36)) | ~l3_lattices(A_36) | ~v8_lattices(A_36) | ~v6_lattices(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.24/1.35  tff(c_116, plain, (r1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | ~m1_subset_1(k5_lattices('#skF_1'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_106, c_113])).
% 2.24/1.35  tff(c_121, plain, (r1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | ~m1_subset_1(k5_lattices('#skF_1'), u1_struct_0('#skF_1')) | ~v8_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_36, c_34, c_116])).
% 2.24/1.35  tff(c_122, plain, (r1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | ~m1_subset_1(k5_lattices('#skF_1'), u1_struct_0('#skF_1')) | ~v8_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_121])).
% 2.24/1.35  tff(c_126, plain, (~v8_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_122])).
% 2.24/1.35  tff(c_129, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_4, c_126])).
% 2.24/1.35  tff(c_132, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_40, c_129])).
% 2.24/1.35  tff(c_134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_132])).
% 2.24/1.35  tff(c_136, plain, (v8_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_122])).
% 2.24/1.35  tff(c_119, plain, (r1_lattices('#skF_1', k5_lattices('#skF_1'), k5_lattices('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~m1_subset_1(k5_lattices('#skF_1'), u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_69, c_113])).
% 2.24/1.35  tff(c_124, plain, (r1_lattices('#skF_1', k5_lattices('#skF_1'), k5_lattices('#skF_1')) | ~m1_subset_1(k5_lattices('#skF_1'), u1_struct_0('#skF_1')) | ~v8_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_36, c_34, c_119])).
% 2.24/1.35  tff(c_125, plain, (r1_lattices('#skF_1', k5_lattices('#skF_1'), k5_lattices('#skF_1')) | ~m1_subset_1(k5_lattices('#skF_1'), u1_struct_0('#skF_1')) | ~v8_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_124])).
% 2.24/1.35  tff(c_138, plain, (r1_lattices('#skF_1', k5_lattices('#skF_1'), k5_lattices('#skF_1')) | ~m1_subset_1(k5_lattices('#skF_1'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_125])).
% 2.24/1.35  tff(c_139, plain, (~m1_subset_1(k5_lattices('#skF_1'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_138])).
% 2.24/1.35  tff(c_142, plain, (~l1_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_139])).
% 2.24/1.35  tff(c_145, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_142])).
% 2.24/1.35  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_145])).
% 2.24/1.35  tff(c_149, plain, (m1_subset_1(k5_lattices('#skF_1'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_138])).
% 2.24/1.35  tff(c_135, plain, (~m1_subset_1(k5_lattices('#skF_1'), u1_struct_0('#skF_1')) | r1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_122])).
% 2.24/1.35  tff(c_178, plain, (r1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_135])).
% 2.24/1.35  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.24/1.35  tff(c_242, plain, (![A_46, B_47, C_48]: (r3_lattices(A_46, B_47, C_48) | ~r1_lattices(A_46, B_47, C_48) | ~m1_subset_1(C_48, u1_struct_0(A_46)) | ~m1_subset_1(B_47, u1_struct_0(A_46)) | ~l3_lattices(A_46) | ~v9_lattices(A_46) | ~v8_lattices(A_46) | ~v6_lattices(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.24/1.35  tff(c_248, plain, (![B_47]: (r3_lattices('#skF_1', B_47, '#skF_2') | ~r1_lattices('#skF_1', B_47, '#skF_2') | ~m1_subset_1(B_47, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_242])).
% 2.24/1.35  tff(c_256, plain, (![B_47]: (r3_lattices('#skF_1', B_47, '#skF_2') | ~r1_lattices('#skF_1', B_47, '#skF_2') | ~m1_subset_1(B_47, u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_136, c_36, c_248])).
% 2.24/1.35  tff(c_257, plain, (![B_47]: (r3_lattices('#skF_1', B_47, '#skF_2') | ~r1_lattices('#skF_1', B_47, '#skF_2') | ~m1_subset_1(B_47, u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_42, c_256])).
% 2.24/1.35  tff(c_258, plain, (~v9_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_257])).
% 2.24/1.35  tff(c_261, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_2, c_258])).
% 2.24/1.35  tff(c_264, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_40, c_261])).
% 2.24/1.35  tff(c_266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_264])).
% 2.24/1.35  tff(c_269, plain, (![B_49]: (r3_lattices('#skF_1', B_49, '#skF_2') | ~r1_lattices('#skF_1', B_49, '#skF_2') | ~m1_subset_1(B_49, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_257])).
% 2.24/1.35  tff(c_272, plain, (r3_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | ~r1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_149, c_269])).
% 2.24/1.35  tff(c_282, plain, (r3_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_272])).
% 2.24/1.35  tff(c_284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_282])).
% 2.24/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.35  
% 2.24/1.35  Inference rules
% 2.24/1.35  ----------------------
% 2.24/1.35  #Ref     : 0
% 2.24/1.35  #Sup     : 41
% 2.24/1.35  #Fact    : 0
% 2.24/1.35  #Define  : 0
% 2.24/1.35  #Split   : 4
% 2.24/1.35  #Chain   : 0
% 2.24/1.35  #Close   : 0
% 2.24/1.35  
% 2.24/1.35  Ordering : KBO
% 2.24/1.35  
% 2.24/1.35  Simplification rules
% 2.24/1.35  ----------------------
% 2.24/1.35  #Subsume      : 0
% 2.24/1.35  #Demod        : 64
% 2.24/1.35  #Tautology    : 20
% 2.24/1.35  #SimpNegUnit  : 20
% 2.24/1.35  #BackRed      : 0
% 2.24/1.35  
% 2.24/1.35  #Partial instantiations: 0
% 2.24/1.35  #Strategies tried      : 1
% 2.24/1.35  
% 2.24/1.36  Timing (in seconds)
% 2.24/1.36  ----------------------
% 2.24/1.36  Preprocessing        : 0.33
% 2.24/1.36  Parsing              : 0.18
% 2.24/1.36  CNF conversion       : 0.02
% 2.24/1.36  Main loop            : 0.21
% 2.24/1.36  Inferencing          : 0.09
% 2.24/1.36  Reduction            : 0.06
% 2.24/1.36  Demodulation         : 0.04
% 2.24/1.36  BG Simplification    : 0.02
% 2.24/1.36  Subsumption          : 0.03
% 2.24/1.36  Abstraction          : 0.01
% 2.24/1.36  MUC search           : 0.00
% 2.24/1.36  Cooper               : 0.00
% 2.24/1.36  Total                : 0.58
% 2.24/1.36  Index Insertion      : 0.00
% 2.24/1.36  Index Deletion       : 0.00
% 2.24/1.36  Index Matching       : 0.00
% 2.24/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
