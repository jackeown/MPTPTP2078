%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:16 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 246 expanded)
%              Number of leaves         :   32 (  99 expanded)
%              Depth                    :   10
%              Number of atoms          :  222 ( 835 expanded)
%              Number of equality atoms :   22 (  35 expanded)
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

tff(f_136,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v13_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r3_lattices(A,k5_lattices(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattices)).

tff(f_75,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

tff(f_62,axiom,(
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

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v13_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k3_lattices(A,k5_lattices(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_lattices)).

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
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(f_107,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_34,plain,(
    ~ r3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_38,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_45,plain,(
    ! [A_21] :
      ( l1_lattices(A_21)
      | ~ l3_lattices(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_49,plain,(
    l1_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_45])).

tff(c_20,plain,(
    ! [A_9] :
      ( m1_subset_1(k5_lattices(A_9),u1_struct_0(A_9))
      | ~ l1_lattices(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_50,plain,(
    ! [A_22] :
      ( l2_lattices(A_22)
      | ~ l3_lattices(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_54,plain,(
    l2_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_50])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_76,plain,(
    ! [A_32,B_33,C_34] :
      ( r1_lattices(A_32,B_33,C_34)
      | k1_lattices(A_32,B_33,C_34) != C_34
      | ~ m1_subset_1(C_34,u1_struct_0(A_32))
      | ~ m1_subset_1(B_33,u1_struct_0(A_32))
      | ~ l2_lattices(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_80,plain,(
    ! [B_33] :
      ( r1_lattices('#skF_1',B_33,'#skF_2')
      | k1_lattices('#skF_1',B_33,'#skF_2') != '#skF_2'
      | ~ m1_subset_1(B_33,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_76])).

tff(c_84,plain,(
    ! [B_33] :
      ( r1_lattices('#skF_1',B_33,'#skF_2')
      | k1_lattices('#skF_1',B_33,'#skF_2') != '#skF_2'
      | ~ m1_subset_1(B_33,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_80])).

tff(c_86,plain,(
    ! [B_35] :
      ( r1_lattices('#skF_1',B_35,'#skF_2')
      | k1_lattices('#skF_1',B_35,'#skF_2') != '#skF_2'
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_84])).

tff(c_90,plain,
    ( r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | k1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') != '#skF_2'
    | ~ l1_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_86])).

tff(c_96,plain,
    ( r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | k1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') != '#skF_2'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_90])).

tff(c_97,plain,
    ( r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | k1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_96])).

tff(c_100,plain,(
    k1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_42,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_40,plain,(
    v13_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_62,plain,(
    ! [A_30,B_31] :
      ( k3_lattices(A_30,k5_lattices(A_30),B_31) = B_31
      | ~ m1_subset_1(B_31,u1_struct_0(A_30))
      | ~ l3_lattices(A_30)
      | ~ v13_lattices(A_30)
      | ~ v10_lattices(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_66,plain,
    ( k3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = '#skF_2'
    | ~ l3_lattices('#skF_1')
    | ~ v13_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_62])).

tff(c_70,plain,
    ( k3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = '#skF_2'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_66])).

tff(c_71,plain,(
    k3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_70])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_111,plain,(
    ! [A_40,B_41,C_42] :
      ( k3_lattices(A_40,B_41,C_42) = k1_lattices(A_40,B_41,C_42)
      | ~ m1_subset_1(C_42,u1_struct_0(A_40))
      | ~ m1_subset_1(B_41,u1_struct_0(A_40))
      | ~ l2_lattices(A_40)
      | ~ v4_lattices(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_115,plain,(
    ! [B_41] :
      ( k3_lattices('#skF_1',B_41,'#skF_2') = k1_lattices('#skF_1',B_41,'#skF_2')
      | ~ m1_subset_1(B_41,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_111])).

tff(c_119,plain,(
    ! [B_41] :
      ( k3_lattices('#skF_1',B_41,'#skF_2') = k1_lattices('#skF_1',B_41,'#skF_2')
      | ~ m1_subset_1(B_41,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_115])).

tff(c_120,plain,(
    ! [B_41] :
      ( k3_lattices('#skF_1',B_41,'#skF_2') = k1_lattices('#skF_1',B_41,'#skF_2')
      | ~ m1_subset_1(B_41,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_119])).

tff(c_121,plain,(
    ~ v4_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_124,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_121])).

tff(c_127,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_124])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_127])).

tff(c_132,plain,(
    ! [B_43] :
      ( k3_lattices('#skF_1',B_43,'#skF_2') = k1_lattices('#skF_1',B_43,'#skF_2')
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_136,plain,
    ( k3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = k1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | ~ l1_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_132])).

tff(c_142,plain,
    ( k1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = '#skF_2'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_71,c_136])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_100,c_142])).

tff(c_145,plain,(
    r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
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

tff(c_239,plain,(
    ! [A_60,B_61,C_62] :
      ( r3_lattices(A_60,B_61,C_62)
      | ~ r1_lattices(A_60,B_61,C_62)
      | ~ m1_subset_1(C_62,u1_struct_0(A_60))
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l3_lattices(A_60)
      | ~ v9_lattices(A_60)
      | ~ v8_lattices(A_60)
      | ~ v6_lattices(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_243,plain,(
    ! [B_61] :
      ( r3_lattices('#skF_1',B_61,'#skF_2')
      | ~ r1_lattices('#skF_1',B_61,'#skF_2')
      | ~ m1_subset_1(B_61,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_239])).

tff(c_247,plain,(
    ! [B_61] :
      ( r3_lattices('#skF_1',B_61,'#skF_2')
      | ~ r1_lattices('#skF_1',B_61,'#skF_2')
      | ~ m1_subset_1(B_61,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_243])).

tff(c_248,plain,(
    ! [B_61] :
      ( r3_lattices('#skF_1',B_61,'#skF_2')
      | ~ r1_lattices('#skF_1',B_61,'#skF_2')
      | ~ m1_subset_1(B_61,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_247])).

tff(c_249,plain,(
    ~ v6_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_248])).

tff(c_252,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_249])).

tff(c_255,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_252])).

tff(c_257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_255])).

tff(c_258,plain,(
    ! [B_61] :
      ( ~ v8_lattices('#skF_1')
      | ~ v9_lattices('#skF_1')
      | r3_lattices('#skF_1',B_61,'#skF_2')
      | ~ r1_lattices('#skF_1',B_61,'#skF_2')
      | ~ m1_subset_1(B_61,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_248])).

tff(c_260,plain,(
    ~ v9_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_263,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_260])).

tff(c_266,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_263])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_266])).

tff(c_269,plain,(
    ! [B_61] :
      ( ~ v8_lattices('#skF_1')
      | r3_lattices('#skF_1',B_61,'#skF_2')
      | ~ r1_lattices('#skF_1',B_61,'#skF_2')
      | ~ m1_subset_1(B_61,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_271,plain,(
    ~ v8_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_274,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_271])).

tff(c_277,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_274])).

tff(c_279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_277])).

tff(c_282,plain,(
    ! [B_63] :
      ( r3_lattices('#skF_1',B_63,'#skF_2')
      | ~ r1_lattices('#skF_1',B_63,'#skF_2')
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_286,plain,
    ( r3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | ~ r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | ~ l1_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_282])).

tff(c_292,plain,
    ( r3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_145,c_286])).

tff(c_294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_34,c_292])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:13:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.70  
% 2.79/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.70  %$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k3_lattices > k1_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_1
% 2.79/1.70  
% 2.79/1.70  %Foreground sorts:
% 2.79/1.70  
% 2.79/1.70  
% 2.79/1.70  %Background operators:
% 2.79/1.70  
% 2.79/1.70  
% 2.79/1.70  %Foreground operators:
% 2.79/1.70  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.79/1.70  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 2.79/1.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.79/1.70  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.79/1.70  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 2.79/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.70  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 2.79/1.70  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.79/1.70  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.79/1.70  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.79/1.70  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.79/1.70  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.70  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.79/1.70  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.70  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.79/1.70  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.79/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.70  tff(v13_lattices, type, v13_lattices: $i > $o).
% 2.79/1.70  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.79/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.70  tff(k5_lattices, type, k5_lattices: $i > $i).
% 2.79/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.79/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.70  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.79/1.70  
% 2.79/1.72  tff(f_136, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r3_lattices(A, k5_lattices(A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_lattices)).
% 2.79/1.72  tff(f_75, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.79/1.72  tff(f_69, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 2.79/1.72  tff(f_62, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 2.79/1.72  tff(f_121, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_lattices(A, k5_lattices(A), B) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_lattices)).
% 2.79/1.72  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 2.79/1.72  tff(f_88, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 2.79/1.72  tff(f_107, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 2.79/1.72  tff(c_44, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.79/1.72  tff(c_34, plain, (~r3_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.79/1.72  tff(c_38, plain, (l3_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.79/1.72  tff(c_45, plain, (![A_21]: (l1_lattices(A_21) | ~l3_lattices(A_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.79/1.72  tff(c_49, plain, (l1_lattices('#skF_1')), inference(resolution, [status(thm)], [c_38, c_45])).
% 2.79/1.72  tff(c_20, plain, (![A_9]: (m1_subset_1(k5_lattices(A_9), u1_struct_0(A_9)) | ~l1_lattices(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.79/1.72  tff(c_50, plain, (![A_22]: (l2_lattices(A_22) | ~l3_lattices(A_22))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.79/1.72  tff(c_54, plain, (l2_lattices('#skF_1')), inference(resolution, [status(thm)], [c_38, c_50])).
% 2.79/1.72  tff(c_36, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.79/1.72  tff(c_76, plain, (![A_32, B_33, C_34]: (r1_lattices(A_32, B_33, C_34) | k1_lattices(A_32, B_33, C_34)!=C_34 | ~m1_subset_1(C_34, u1_struct_0(A_32)) | ~m1_subset_1(B_33, u1_struct_0(A_32)) | ~l2_lattices(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.79/1.72  tff(c_80, plain, (![B_33]: (r1_lattices('#skF_1', B_33, '#skF_2') | k1_lattices('#skF_1', B_33, '#skF_2')!='#skF_2' | ~m1_subset_1(B_33, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_76])).
% 2.79/1.72  tff(c_84, plain, (![B_33]: (r1_lattices('#skF_1', B_33, '#skF_2') | k1_lattices('#skF_1', B_33, '#skF_2')!='#skF_2' | ~m1_subset_1(B_33, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_80])).
% 2.79/1.72  tff(c_86, plain, (![B_35]: (r1_lattices('#skF_1', B_35, '#skF_2') | k1_lattices('#skF_1', B_35, '#skF_2')!='#skF_2' | ~m1_subset_1(B_35, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_44, c_84])).
% 2.79/1.72  tff(c_90, plain, (r1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | k1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')!='#skF_2' | ~l1_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_86])).
% 2.79/1.72  tff(c_96, plain, (r1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | k1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')!='#skF_2' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_90])).
% 2.79/1.72  tff(c_97, plain, (r1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | k1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_44, c_96])).
% 2.79/1.72  tff(c_100, plain, (k1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')!='#skF_2'), inference(splitLeft, [status(thm)], [c_97])).
% 2.79/1.72  tff(c_42, plain, (v10_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.79/1.72  tff(c_40, plain, (v13_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.79/1.72  tff(c_62, plain, (![A_30, B_31]: (k3_lattices(A_30, k5_lattices(A_30), B_31)=B_31 | ~m1_subset_1(B_31, u1_struct_0(A_30)) | ~l3_lattices(A_30) | ~v13_lattices(A_30) | ~v10_lattices(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.79/1.72  tff(c_66, plain, (k3_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')='#skF_2' | ~l3_lattices('#skF_1') | ~v13_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_62])).
% 2.79/1.72  tff(c_70, plain, (k3_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')='#skF_2' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_66])).
% 2.79/1.72  tff(c_71, plain, (k3_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_44, c_70])).
% 2.79/1.72  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.79/1.72  tff(c_111, plain, (![A_40, B_41, C_42]: (k3_lattices(A_40, B_41, C_42)=k1_lattices(A_40, B_41, C_42) | ~m1_subset_1(C_42, u1_struct_0(A_40)) | ~m1_subset_1(B_41, u1_struct_0(A_40)) | ~l2_lattices(A_40) | ~v4_lattices(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.79/1.72  tff(c_115, plain, (![B_41]: (k3_lattices('#skF_1', B_41, '#skF_2')=k1_lattices('#skF_1', B_41, '#skF_2') | ~m1_subset_1(B_41, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_111])).
% 2.79/1.72  tff(c_119, plain, (![B_41]: (k3_lattices('#skF_1', B_41, '#skF_2')=k1_lattices('#skF_1', B_41, '#skF_2') | ~m1_subset_1(B_41, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_115])).
% 2.79/1.72  tff(c_120, plain, (![B_41]: (k3_lattices('#skF_1', B_41, '#skF_2')=k1_lattices('#skF_1', B_41, '#skF_2') | ~m1_subset_1(B_41, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_119])).
% 2.79/1.72  tff(c_121, plain, (~v4_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_120])).
% 2.79/1.72  tff(c_124, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_12, c_121])).
% 2.79/1.72  tff(c_127, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_124])).
% 2.79/1.72  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_127])).
% 2.79/1.72  tff(c_132, plain, (![B_43]: (k3_lattices('#skF_1', B_43, '#skF_2')=k1_lattices('#skF_1', B_43, '#skF_2') | ~m1_subset_1(B_43, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_120])).
% 2.79/1.72  tff(c_136, plain, (k3_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')=k1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | ~l1_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_132])).
% 2.79/1.72  tff(c_142, plain, (k1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')='#skF_2' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_71, c_136])).
% 2.79/1.72  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_100, c_142])).
% 2.79/1.72  tff(c_145, plain, (r1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_97])).
% 2.79/1.72  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.79/1.72  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.79/1.72  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.79/1.72  tff(c_239, plain, (![A_60, B_61, C_62]: (r3_lattices(A_60, B_61, C_62) | ~r1_lattices(A_60, B_61, C_62) | ~m1_subset_1(C_62, u1_struct_0(A_60)) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l3_lattices(A_60) | ~v9_lattices(A_60) | ~v8_lattices(A_60) | ~v6_lattices(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.79/1.72  tff(c_243, plain, (![B_61]: (r3_lattices('#skF_1', B_61, '#skF_2') | ~r1_lattices('#skF_1', B_61, '#skF_2') | ~m1_subset_1(B_61, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_239])).
% 2.79/1.72  tff(c_247, plain, (![B_61]: (r3_lattices('#skF_1', B_61, '#skF_2') | ~r1_lattices('#skF_1', B_61, '#skF_2') | ~m1_subset_1(B_61, u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_243])).
% 2.79/1.72  tff(c_248, plain, (![B_61]: (r3_lattices('#skF_1', B_61, '#skF_2') | ~r1_lattices('#skF_1', B_61, '#skF_2') | ~m1_subset_1(B_61, u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_247])).
% 2.79/1.72  tff(c_249, plain, (~v6_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_248])).
% 2.79/1.72  tff(c_252, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_8, c_249])).
% 2.79/1.72  tff(c_255, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_252])).
% 2.79/1.72  tff(c_257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_255])).
% 2.79/1.72  tff(c_258, plain, (![B_61]: (~v8_lattices('#skF_1') | ~v9_lattices('#skF_1') | r3_lattices('#skF_1', B_61, '#skF_2') | ~r1_lattices('#skF_1', B_61, '#skF_2') | ~m1_subset_1(B_61, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_248])).
% 2.79/1.72  tff(c_260, plain, (~v9_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_258])).
% 2.79/1.72  tff(c_263, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_2, c_260])).
% 2.79/1.72  tff(c_266, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_263])).
% 2.79/1.72  tff(c_268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_266])).
% 2.79/1.72  tff(c_269, plain, (![B_61]: (~v8_lattices('#skF_1') | r3_lattices('#skF_1', B_61, '#skF_2') | ~r1_lattices('#skF_1', B_61, '#skF_2') | ~m1_subset_1(B_61, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_258])).
% 2.79/1.72  tff(c_271, plain, (~v8_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_269])).
% 2.79/1.72  tff(c_274, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_4, c_271])).
% 2.79/1.72  tff(c_277, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_274])).
% 2.79/1.72  tff(c_279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_277])).
% 2.79/1.72  tff(c_282, plain, (![B_63]: (r3_lattices('#skF_1', B_63, '#skF_2') | ~r1_lattices('#skF_1', B_63, '#skF_2') | ~m1_subset_1(B_63, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_269])).
% 2.79/1.72  tff(c_286, plain, (r3_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | ~r1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | ~l1_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_282])).
% 2.79/1.72  tff(c_292, plain, (r3_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_145, c_286])).
% 2.79/1.72  tff(c_294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_34, c_292])).
% 2.79/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.72  
% 2.79/1.72  Inference rules
% 2.79/1.72  ----------------------
% 2.79/1.72  #Ref     : 0
% 2.79/1.72  #Sup     : 45
% 2.79/1.72  #Fact    : 0
% 2.79/1.72  #Define  : 0
% 2.79/1.72  #Split   : 7
% 2.79/1.72  #Chain   : 0
% 2.79/1.72  #Close   : 0
% 2.79/1.72  
% 2.79/1.72  Ordering : KBO
% 2.79/1.72  
% 2.79/1.72  Simplification rules
% 2.79/1.72  ----------------------
% 2.79/1.72  #Subsume      : 0
% 2.79/1.72  #Demod        : 31
% 2.79/1.72  #Tautology    : 18
% 2.79/1.72  #SimpNegUnit  : 16
% 2.79/1.72  #BackRed      : 0
% 2.79/1.72  
% 2.79/1.72  #Partial instantiations: 0
% 2.79/1.72  #Strategies tried      : 1
% 2.79/1.72  
% 2.79/1.72  Timing (in seconds)
% 2.79/1.72  ----------------------
% 2.79/1.72  Preprocessing        : 0.50
% 2.79/1.72  Parsing              : 0.25
% 2.79/1.72  CNF conversion       : 0.03
% 2.79/1.72  Main loop            : 0.33
% 2.79/1.72  Inferencing          : 0.14
% 2.79/1.72  Reduction            : 0.09
% 2.79/1.72  Demodulation         : 0.06
% 2.79/1.72  BG Simplification    : 0.02
% 2.79/1.72  Subsumption          : 0.05
% 2.79/1.72  Abstraction          : 0.02
% 2.79/1.72  MUC search           : 0.00
% 2.79/1.72  Cooper               : 0.00
% 2.79/1.72  Total                : 0.87
% 2.79/1.72  Index Insertion      : 0.00
% 2.79/1.72  Index Deletion       : 0.00
% 2.79/1.72  Index Matching       : 0.00
% 2.79/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
