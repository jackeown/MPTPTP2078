%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:17 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 439 expanded)
%              Number of leaves         :   33 ( 167 expanded)
%              Depth                    :   14
%              Number of atoms          :  222 (1440 expanded)
%              Number of equality atoms :   35 ( 197 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v14_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k1_lattices > #nlpp > u1_struct_0 > k6_lattices > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v14_lattices,type,(
    v14_lattices: $i > $o )).

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

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v14_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k3_lattices(A,k6_lattices(A),B) = k6_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_lattices)).

tff(f_88,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

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
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k3_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => m1_subset_1(k6_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(f_132,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v14_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k4_lattices(A,k6_lattices(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattices)).

tff(f_118,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k1_lattices(A,B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_38,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_50,plain,(
    ! [A_29] :
      ( l2_lattices(A_29)
      | ~ l3_lattices(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_54,plain,(
    l2_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_50])).

tff(c_42,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_115,plain,(
    ! [A_49,C_50,B_51] :
      ( k3_lattices(A_49,C_50,B_51) = k3_lattices(A_49,B_51,C_50)
      | ~ m1_subset_1(C_50,u1_struct_0(A_49))
      | ~ m1_subset_1(B_51,u1_struct_0(A_49))
      | ~ l2_lattices(A_49)
      | ~ v4_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_119,plain,(
    ! [B_51] :
      ( k3_lattices('#skF_1',B_51,'#skF_2') = k3_lattices('#skF_1','#skF_2',B_51)
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_115])).

tff(c_123,plain,(
    ! [B_51] :
      ( k3_lattices('#skF_1',B_51,'#skF_2') = k3_lattices('#skF_1','#skF_2',B_51)
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_119])).

tff(c_124,plain,(
    ! [B_51] :
      ( k3_lattices('#skF_1',B_51,'#skF_2') = k3_lattices('#skF_1','#skF_2',B_51)
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_123])).

tff(c_125,plain,(
    ~ v4_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_128,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_125])).

tff(c_131,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_128])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_131])).

tff(c_135,plain,(
    v4_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_22,plain,(
    ! [A_12] :
      ( m1_subset_1(k6_lattices(A_12),u1_struct_0(A_12))
      | ~ l2_lattices(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_136,plain,(
    ! [B_52] :
      ( k3_lattices('#skF_1',B_52,'#skF_2') = k3_lattices('#skF_1','#skF_2',B_52)
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_140,plain,
    ( k3_lattices('#skF_1',k6_lattices('#skF_1'),'#skF_2') = k3_lattices('#skF_1','#skF_2',k6_lattices('#skF_1'))
    | ~ l2_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_136])).

tff(c_146,plain,
    ( k3_lattices('#skF_1',k6_lattices('#skF_1'),'#skF_2') = k3_lattices('#skF_1','#skF_2',k6_lattices('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_140])).

tff(c_147,plain,(
    k3_lattices('#skF_1',k6_lattices('#skF_1'),'#skF_2') = k3_lattices('#skF_1','#skF_2',k6_lattices('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_146])).

tff(c_155,plain,(
    ! [A_53,B_54,C_55] :
      ( k3_lattices(A_53,B_54,C_55) = k1_lattices(A_53,B_54,C_55)
      | ~ m1_subset_1(C_55,u1_struct_0(A_53))
      | ~ m1_subset_1(B_54,u1_struct_0(A_53))
      | ~ l2_lattices(A_53)
      | ~ v4_lattices(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_159,plain,(
    ! [B_54] :
      ( k3_lattices('#skF_1',B_54,'#skF_2') = k1_lattices('#skF_1',B_54,'#skF_2')
      | ~ m1_subset_1(B_54,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_155])).

tff(c_163,plain,(
    ! [B_54] :
      ( k3_lattices('#skF_1',B_54,'#skF_2') = k1_lattices('#skF_1',B_54,'#skF_2')
      | ~ m1_subset_1(B_54,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_54,c_159])).

tff(c_165,plain,(
    ! [B_56] :
      ( k3_lattices('#skF_1',B_56,'#skF_2') = k1_lattices('#skF_1',B_56,'#skF_2')
      | ~ m1_subset_1(B_56,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_163])).

tff(c_169,plain,
    ( k3_lattices('#skF_1',k6_lattices('#skF_1'),'#skF_2') = k1_lattices('#skF_1',k6_lattices('#skF_1'),'#skF_2')
    | ~ l2_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_165])).

tff(c_175,plain,
    ( k3_lattices('#skF_1','#skF_2',k6_lattices('#skF_1')) = k1_lattices('#skF_1',k6_lattices('#skF_1'),'#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_147,c_169])).

tff(c_176,plain,(
    k3_lattices('#skF_1','#skF_2',k6_lattices('#skF_1')) = k1_lattices('#skF_1',k6_lattices('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_175])).

tff(c_192,plain,(
    ! [A_57,B_58] :
      ( k3_lattices(A_57,B_58,k6_lattices(A_57)) = k1_lattices(A_57,B_58,k6_lattices(A_57))
      | ~ m1_subset_1(B_58,u1_struct_0(A_57))
      | ~ v4_lattices(A_57)
      | ~ l2_lattices(A_57)
      | v2_struct_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_22,c_155])).

tff(c_196,plain,
    ( k3_lattices('#skF_1','#skF_2',k6_lattices('#skF_1')) = k1_lattices('#skF_1','#skF_2',k6_lattices('#skF_1'))
    | ~ v4_lattices('#skF_1')
    | ~ l2_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_192])).

tff(c_200,plain,
    ( k1_lattices('#skF_1',k6_lattices('#skF_1'),'#skF_2') = k1_lattices('#skF_1','#skF_2',k6_lattices('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_135,c_176,c_196])).

tff(c_201,plain,(
    k1_lattices('#skF_1',k6_lattices('#skF_1'),'#skF_2') = k1_lattices('#skF_1','#skF_2',k6_lattices('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_200])).

tff(c_34,plain,(
    k3_lattices('#skF_1',k6_lattices('#skF_1'),'#skF_2') != k6_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_150,plain,(
    k3_lattices('#skF_1','#skF_2',k6_lattices('#skF_1')) != k6_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_34])).

tff(c_182,plain,(
    k1_lattices('#skF_1',k6_lattices('#skF_1'),'#skF_2') != k6_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_150])).

tff(c_203,plain,(
    k1_lattices('#skF_1','#skF_2',k6_lattices('#skF_1')) != k6_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_182])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_40,plain,(
    v14_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_62,plain,(
    ! [A_37,B_38] :
      ( k4_lattices(A_37,k6_lattices(A_37),B_38) = B_38
      | ~ m1_subset_1(B_38,u1_struct_0(A_37))
      | ~ l3_lattices(A_37)
      | ~ v14_lattices(A_37)
      | ~ v10_lattices(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_66,plain,
    ( k4_lattices('#skF_1',k6_lattices('#skF_1'),'#skF_2') = '#skF_2'
    | ~ l3_lattices('#skF_1')
    | ~ v14_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_62])).

tff(c_70,plain,
    ( k4_lattices('#skF_1',k6_lattices('#skF_1'),'#skF_2') = '#skF_2'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_66])).

tff(c_71,plain,(
    k4_lattices('#skF_1',k6_lattices('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_70])).

tff(c_210,plain,(
    ! [A_59,B_60,C_61] :
      ( r1_lattices(A_59,k4_lattices(A_59,B_60,C_61),B_60)
      | ~ m1_subset_1(C_61,u1_struct_0(A_59))
      | ~ m1_subset_1(B_60,u1_struct_0(A_59))
      | ~ l3_lattices(A_59)
      | ~ v8_lattices(A_59)
      | ~ v6_lattices(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_218,plain,
    ( r1_lattices('#skF_1','#skF_2',k6_lattices('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k6_lattices('#skF_1'),u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_210])).

tff(c_221,plain,
    ( r1_lattices('#skF_1','#skF_2',k6_lattices('#skF_1'))
    | ~ m1_subset_1(k6_lattices('#skF_1'),u1_struct_0('#skF_1'))
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_218])).

tff(c_222,plain,
    ( r1_lattices('#skF_1','#skF_2',k6_lattices('#skF_1'))
    | ~ m1_subset_1(k6_lattices('#skF_1'),u1_struct_0('#skF_1'))
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_221])).

tff(c_231,plain,(
    ~ v6_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_234,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_231])).

tff(c_237,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_234])).

tff(c_239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_237])).

tff(c_240,plain,
    ( ~ v8_lattices('#skF_1')
    | ~ m1_subset_1(k6_lattices('#skF_1'),u1_struct_0('#skF_1'))
    | r1_lattices('#skF_1','#skF_2',k6_lattices('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_242,plain,(
    ~ m1_subset_1(k6_lattices('#skF_1'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_240])).

tff(c_245,plain,
    ( ~ l2_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_242])).

tff(c_248,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_245])).

tff(c_250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_248])).

tff(c_252,plain,(
    m1_subset_1(k6_lattices('#skF_1'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_251,plain,
    ( ~ v8_lattices('#skF_1')
    | r1_lattices('#skF_1','#skF_2',k6_lattices('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_298,plain,(
    ~ v8_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_251])).

tff(c_319,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_298])).

tff(c_322,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_319])).

tff(c_324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_322])).

tff(c_325,plain,(
    r1_lattices('#skF_1','#skF_2',k6_lattices('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_20,plain,(
    ! [A_5,B_9,C_11] :
      ( k1_lattices(A_5,B_9,C_11) = C_11
      | ~ r1_lattices(A_5,B_9,C_11)
      | ~ m1_subset_1(C_11,u1_struct_0(A_5))
      | ~ m1_subset_1(B_9,u1_struct_0(A_5))
      | ~ l2_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_328,plain,
    ( k1_lattices('#skF_1','#skF_2',k6_lattices('#skF_1')) = k6_lattices('#skF_1')
    | ~ m1_subset_1(k6_lattices('#skF_1'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l2_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_325,c_20])).

tff(c_331,plain,
    ( k1_lattices('#skF_1','#skF_2',k6_lattices('#skF_1')) = k6_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36,c_252,c_328])).

tff(c_333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_203,c_331])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:21:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.31  
% 2.39/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.31  %$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v14_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k1_lattices > #nlpp > u1_struct_0 > k6_lattices > #skF_2 > #skF_1
% 2.39/1.31  
% 2.39/1.31  %Foreground sorts:
% 2.39/1.31  
% 2.39/1.31  
% 2.39/1.31  %Background operators:
% 2.39/1.31  
% 2.39/1.31  
% 2.39/1.31  %Foreground operators:
% 2.39/1.31  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.39/1.31  tff(k6_lattices, type, k6_lattices: $i > $i).
% 2.39/1.31  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 2.39/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.39/1.31  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.39/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.31  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 2.39/1.31  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 2.39/1.31  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.39/1.31  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.39/1.31  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.39/1.31  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.39/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.31  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.39/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.39/1.31  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.39/1.31  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.39/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.31  tff(v14_lattices, type, v14_lattices: $i > $o).
% 2.39/1.31  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.39/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.39/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.39/1.31  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.39/1.31  
% 2.39/1.33  tff(f_147, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v14_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_lattices(A, k6_lattices(A), B) = k6_lattices(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_lattices)).
% 2.39/1.33  tff(f_88, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.39/1.33  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 2.39/1.33  tff(f_60, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k3_lattices(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 2.39/1.33  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => m1_subset_1(k6_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_lattices)).
% 2.39/1.33  tff(f_101, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 2.39/1.33  tff(f_132, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v14_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattices(A, k6_lattices(A), B) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_lattices)).
% 2.39/1.33  tff(f_118, axiom, (![A]: ((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => r1_lattices(A, k4_lattices(A, B, C), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_lattices)).
% 2.39/1.33  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 2.39/1.33  tff(c_44, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.39/1.33  tff(c_38, plain, (l3_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.39/1.33  tff(c_50, plain, (![A_29]: (l2_lattices(A_29) | ~l3_lattices(A_29))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.39/1.33  tff(c_54, plain, (l2_lattices('#skF_1')), inference(resolution, [status(thm)], [c_38, c_50])).
% 2.39/1.33  tff(c_42, plain, (v10_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.39/1.33  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.39/1.33  tff(c_36, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.39/1.33  tff(c_115, plain, (![A_49, C_50, B_51]: (k3_lattices(A_49, C_50, B_51)=k3_lattices(A_49, B_51, C_50) | ~m1_subset_1(C_50, u1_struct_0(A_49)) | ~m1_subset_1(B_51, u1_struct_0(A_49)) | ~l2_lattices(A_49) | ~v4_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.39/1.33  tff(c_119, plain, (![B_51]: (k3_lattices('#skF_1', B_51, '#skF_2')=k3_lattices('#skF_1', '#skF_2', B_51) | ~m1_subset_1(B_51, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_115])).
% 2.39/1.33  tff(c_123, plain, (![B_51]: (k3_lattices('#skF_1', B_51, '#skF_2')=k3_lattices('#skF_1', '#skF_2', B_51) | ~m1_subset_1(B_51, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_119])).
% 2.39/1.33  tff(c_124, plain, (![B_51]: (k3_lattices('#skF_1', B_51, '#skF_2')=k3_lattices('#skF_1', '#skF_2', B_51) | ~m1_subset_1(B_51, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_123])).
% 2.39/1.33  tff(c_125, plain, (~v4_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_124])).
% 2.39/1.33  tff(c_128, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_12, c_125])).
% 2.39/1.33  tff(c_131, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_128])).
% 2.39/1.33  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_131])).
% 2.39/1.33  tff(c_135, plain, (v4_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_124])).
% 2.39/1.33  tff(c_22, plain, (![A_12]: (m1_subset_1(k6_lattices(A_12), u1_struct_0(A_12)) | ~l2_lattices(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.39/1.33  tff(c_136, plain, (![B_52]: (k3_lattices('#skF_1', B_52, '#skF_2')=k3_lattices('#skF_1', '#skF_2', B_52) | ~m1_subset_1(B_52, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_124])).
% 2.39/1.33  tff(c_140, plain, (k3_lattices('#skF_1', k6_lattices('#skF_1'), '#skF_2')=k3_lattices('#skF_1', '#skF_2', k6_lattices('#skF_1')) | ~l2_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_136])).
% 2.39/1.33  tff(c_146, plain, (k3_lattices('#skF_1', k6_lattices('#skF_1'), '#skF_2')=k3_lattices('#skF_1', '#skF_2', k6_lattices('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_140])).
% 2.39/1.33  tff(c_147, plain, (k3_lattices('#skF_1', k6_lattices('#skF_1'), '#skF_2')=k3_lattices('#skF_1', '#skF_2', k6_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_146])).
% 2.39/1.33  tff(c_155, plain, (![A_53, B_54, C_55]: (k3_lattices(A_53, B_54, C_55)=k1_lattices(A_53, B_54, C_55) | ~m1_subset_1(C_55, u1_struct_0(A_53)) | ~m1_subset_1(B_54, u1_struct_0(A_53)) | ~l2_lattices(A_53) | ~v4_lattices(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.39/1.33  tff(c_159, plain, (![B_54]: (k3_lattices('#skF_1', B_54, '#skF_2')=k1_lattices('#skF_1', B_54, '#skF_2') | ~m1_subset_1(B_54, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_155])).
% 2.39/1.33  tff(c_163, plain, (![B_54]: (k3_lattices('#skF_1', B_54, '#skF_2')=k1_lattices('#skF_1', B_54, '#skF_2') | ~m1_subset_1(B_54, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_54, c_159])).
% 2.39/1.33  tff(c_165, plain, (![B_56]: (k3_lattices('#skF_1', B_56, '#skF_2')=k1_lattices('#skF_1', B_56, '#skF_2') | ~m1_subset_1(B_56, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_44, c_163])).
% 2.39/1.33  tff(c_169, plain, (k3_lattices('#skF_1', k6_lattices('#skF_1'), '#skF_2')=k1_lattices('#skF_1', k6_lattices('#skF_1'), '#skF_2') | ~l2_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_165])).
% 2.39/1.33  tff(c_175, plain, (k3_lattices('#skF_1', '#skF_2', k6_lattices('#skF_1'))=k1_lattices('#skF_1', k6_lattices('#skF_1'), '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_147, c_169])).
% 2.39/1.33  tff(c_176, plain, (k3_lattices('#skF_1', '#skF_2', k6_lattices('#skF_1'))=k1_lattices('#skF_1', k6_lattices('#skF_1'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44, c_175])).
% 2.39/1.33  tff(c_192, plain, (![A_57, B_58]: (k3_lattices(A_57, B_58, k6_lattices(A_57))=k1_lattices(A_57, B_58, k6_lattices(A_57)) | ~m1_subset_1(B_58, u1_struct_0(A_57)) | ~v4_lattices(A_57) | ~l2_lattices(A_57) | v2_struct_0(A_57))), inference(resolution, [status(thm)], [c_22, c_155])).
% 2.39/1.33  tff(c_196, plain, (k3_lattices('#skF_1', '#skF_2', k6_lattices('#skF_1'))=k1_lattices('#skF_1', '#skF_2', k6_lattices('#skF_1')) | ~v4_lattices('#skF_1') | ~l2_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_192])).
% 2.39/1.33  tff(c_200, plain, (k1_lattices('#skF_1', k6_lattices('#skF_1'), '#skF_2')=k1_lattices('#skF_1', '#skF_2', k6_lattices('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_135, c_176, c_196])).
% 2.39/1.33  tff(c_201, plain, (k1_lattices('#skF_1', k6_lattices('#skF_1'), '#skF_2')=k1_lattices('#skF_1', '#skF_2', k6_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_200])).
% 2.39/1.33  tff(c_34, plain, (k3_lattices('#skF_1', k6_lattices('#skF_1'), '#skF_2')!=k6_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.39/1.33  tff(c_150, plain, (k3_lattices('#skF_1', '#skF_2', k6_lattices('#skF_1'))!=k6_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_34])).
% 2.39/1.33  tff(c_182, plain, (k1_lattices('#skF_1', k6_lattices('#skF_1'), '#skF_2')!=k6_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_150])).
% 2.39/1.33  tff(c_203, plain, (k1_lattices('#skF_1', '#skF_2', k6_lattices('#skF_1'))!=k6_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_201, c_182])).
% 2.39/1.33  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.39/1.33  tff(c_40, plain, (v14_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.39/1.33  tff(c_62, plain, (![A_37, B_38]: (k4_lattices(A_37, k6_lattices(A_37), B_38)=B_38 | ~m1_subset_1(B_38, u1_struct_0(A_37)) | ~l3_lattices(A_37) | ~v14_lattices(A_37) | ~v10_lattices(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.39/1.33  tff(c_66, plain, (k4_lattices('#skF_1', k6_lattices('#skF_1'), '#skF_2')='#skF_2' | ~l3_lattices('#skF_1') | ~v14_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_62])).
% 2.39/1.33  tff(c_70, plain, (k4_lattices('#skF_1', k6_lattices('#skF_1'), '#skF_2')='#skF_2' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_66])).
% 2.39/1.33  tff(c_71, plain, (k4_lattices('#skF_1', k6_lattices('#skF_1'), '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_44, c_70])).
% 2.39/1.33  tff(c_210, plain, (![A_59, B_60, C_61]: (r1_lattices(A_59, k4_lattices(A_59, B_60, C_61), B_60) | ~m1_subset_1(C_61, u1_struct_0(A_59)) | ~m1_subset_1(B_60, u1_struct_0(A_59)) | ~l3_lattices(A_59) | ~v8_lattices(A_59) | ~v6_lattices(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.39/1.33  tff(c_218, plain, (r1_lattices('#skF_1', '#skF_2', k6_lattices('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~m1_subset_1(k6_lattices('#skF_1'), u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_71, c_210])).
% 2.39/1.33  tff(c_221, plain, (r1_lattices('#skF_1', '#skF_2', k6_lattices('#skF_1')) | ~m1_subset_1(k6_lattices('#skF_1'), u1_struct_0('#skF_1')) | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_218])).
% 2.39/1.33  tff(c_222, plain, (r1_lattices('#skF_1', '#skF_2', k6_lattices('#skF_1')) | ~m1_subset_1(k6_lattices('#skF_1'), u1_struct_0('#skF_1')) | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_221])).
% 2.39/1.33  tff(c_231, plain, (~v6_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_222])).
% 2.39/1.33  tff(c_234, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_8, c_231])).
% 2.39/1.33  tff(c_237, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_234])).
% 2.39/1.33  tff(c_239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_237])).
% 2.39/1.33  tff(c_240, plain, (~v8_lattices('#skF_1') | ~m1_subset_1(k6_lattices('#skF_1'), u1_struct_0('#skF_1')) | r1_lattices('#skF_1', '#skF_2', k6_lattices('#skF_1'))), inference(splitRight, [status(thm)], [c_222])).
% 2.39/1.33  tff(c_242, plain, (~m1_subset_1(k6_lattices('#skF_1'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_240])).
% 2.39/1.33  tff(c_245, plain, (~l2_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_242])).
% 2.39/1.33  tff(c_248, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_245])).
% 2.39/1.33  tff(c_250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_248])).
% 2.39/1.33  tff(c_252, plain, (m1_subset_1(k6_lattices('#skF_1'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_240])).
% 2.39/1.33  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.39/1.33  tff(c_251, plain, (~v8_lattices('#skF_1') | r1_lattices('#skF_1', '#skF_2', k6_lattices('#skF_1'))), inference(splitRight, [status(thm)], [c_240])).
% 2.39/1.33  tff(c_298, plain, (~v8_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_251])).
% 2.39/1.33  tff(c_319, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_4, c_298])).
% 2.39/1.33  tff(c_322, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_319])).
% 2.39/1.33  tff(c_324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_322])).
% 2.39/1.33  tff(c_325, plain, (r1_lattices('#skF_1', '#skF_2', k6_lattices('#skF_1'))), inference(splitRight, [status(thm)], [c_251])).
% 2.39/1.33  tff(c_20, plain, (![A_5, B_9, C_11]: (k1_lattices(A_5, B_9, C_11)=C_11 | ~r1_lattices(A_5, B_9, C_11) | ~m1_subset_1(C_11, u1_struct_0(A_5)) | ~m1_subset_1(B_9, u1_struct_0(A_5)) | ~l2_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.39/1.33  tff(c_328, plain, (k1_lattices('#skF_1', '#skF_2', k6_lattices('#skF_1'))=k6_lattices('#skF_1') | ~m1_subset_1(k6_lattices('#skF_1'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_325, c_20])).
% 2.39/1.33  tff(c_331, plain, (k1_lattices('#skF_1', '#skF_2', k6_lattices('#skF_1'))=k6_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36, c_252, c_328])).
% 2.39/1.33  tff(c_333, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_203, c_331])).
% 2.39/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.33  
% 2.39/1.33  Inference rules
% 2.39/1.33  ----------------------
% 2.39/1.33  #Ref     : 0
% 2.39/1.33  #Sup     : 56
% 2.39/1.33  #Fact    : 0
% 2.39/1.33  #Define  : 0
% 2.39/1.33  #Split   : 6
% 2.39/1.33  #Chain   : 0
% 2.39/1.33  #Close   : 0
% 2.39/1.33  
% 2.39/1.33  Ordering : KBO
% 2.39/1.33  
% 2.39/1.33  Simplification rules
% 2.39/1.33  ----------------------
% 2.39/1.33  #Subsume      : 1
% 2.39/1.33  #Demod        : 54
% 2.39/1.33  #Tautology    : 26
% 2.39/1.33  #SimpNegUnit  : 21
% 2.39/1.33  #BackRed      : 7
% 2.39/1.33  
% 2.39/1.33  #Partial instantiations: 0
% 2.39/1.33  #Strategies tried      : 1
% 2.39/1.33  
% 2.39/1.33  Timing (in seconds)
% 2.39/1.33  ----------------------
% 2.39/1.33  Preprocessing        : 0.32
% 2.39/1.33  Parsing              : 0.17
% 2.39/1.33  CNF conversion       : 0.02
% 2.39/1.33  Main loop            : 0.23
% 2.39/1.33  Inferencing          : 0.09
% 2.39/1.33  Reduction            : 0.07
% 2.39/1.33  Demodulation         : 0.05
% 2.39/1.33  BG Simplification    : 0.02
% 2.39/1.33  Subsumption          : 0.04
% 2.39/1.33  Abstraction          : 0.02
% 2.39/1.33  MUC search           : 0.00
% 2.39/1.33  Cooper               : 0.00
% 2.39/1.33  Total                : 0.59
% 2.39/1.33  Index Insertion      : 0.00
% 2.39/1.33  Index Deletion       : 0.00
% 2.39/1.33  Index Matching       : 0.00
% 2.39/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
