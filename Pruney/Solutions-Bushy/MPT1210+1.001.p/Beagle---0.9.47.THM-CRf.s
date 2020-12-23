%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1210+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:35 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 258 expanded)
%              Number of leaves         :   30 ( 107 expanded)
%              Depth                    :   15
%              Number of atoms          :  164 ( 895 expanded)
%              Number of equality atoms :    5 (  30 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v14_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > #nlpp > u1_struct_0 > k6_lattices > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(k6_lattices,type,(
    k6_lattices: $i > $i )).

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

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v14_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r3_lattices(A,B,k6_lattices(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_59,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v14_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k4_lattices(A,k6_lattices(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattices)).

tff(f_95,axiom,(
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

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => m1_subset_1(k6_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).

tff(f_78,axiom,(
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

tff(c_40,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_34,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_38,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_46,plain,(
    ! [A_19] :
      ( l2_lattices(A_19)
      | ~ l3_lattices(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_50,plain,(
    l2_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_46])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_36,plain,(
    v14_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_58,plain,(
    ! [A_27,B_28] :
      ( k4_lattices(A_27,k6_lattices(A_27),B_28) = B_28
      | ~ m1_subset_1(B_28,u1_struct_0(A_27))
      | ~ l3_lattices(A_27)
      | ~ v14_lattices(A_27)
      | ~ v10_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_62,plain,
    ( k4_lattices('#skF_1',k6_lattices('#skF_1'),'#skF_2') = '#skF_2'
    | ~ l3_lattices('#skF_1')
    | ~ v14_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_58])).

tff(c_66,plain,
    ( k4_lattices('#skF_1',k6_lattices('#skF_1'),'#skF_2') = '#skF_2'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_62])).

tff(c_67,plain,(
    k4_lattices('#skF_1',k6_lattices('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_66])).

tff(c_72,plain,(
    ! [A_29,B_30,C_31] :
      ( r1_lattices(A_29,k4_lattices(A_29,B_30,C_31),B_30)
      | ~ m1_subset_1(C_31,u1_struct_0(A_29))
      | ~ m1_subset_1(B_30,u1_struct_0(A_29))
      | ~ l3_lattices(A_29)
      | ~ v8_lattices(A_29)
      | ~ v6_lattices(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_75,plain,
    ( r1_lattices('#skF_1','#skF_2',k6_lattices('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k6_lattices('#skF_1'),u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_72])).

tff(c_77,plain,
    ( r1_lattices('#skF_1','#skF_2',k6_lattices('#skF_1'))
    | ~ m1_subset_1(k6_lattices('#skF_1'),u1_struct_0('#skF_1'))
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_75])).

tff(c_78,plain,
    ( r1_lattices('#skF_1','#skF_2',k6_lattices('#skF_1'))
    | ~ m1_subset_1(k6_lattices('#skF_1'),u1_struct_0('#skF_1'))
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_77])).

tff(c_79,plain,(
    ~ v6_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_82,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_79])).

tff(c_85,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38,c_82])).

tff(c_87,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_85])).

tff(c_89,plain,(
    v6_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    ! [A_2] :
      ( m1_subset_1(k6_lattices(A_2),u1_struct_0(A_2))
      | ~ l2_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_88,plain,
    ( ~ v8_lattices('#skF_1')
    | ~ m1_subset_1(k6_lattices('#skF_1'),u1_struct_0('#skF_1'))
    | r1_lattices('#skF_1','#skF_2',k6_lattices('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_90,plain,(
    ~ m1_subset_1(k6_lattices('#skF_1'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_93,plain,
    ( ~ l2_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_90])).

tff(c_96,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_93])).

tff(c_98,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_96])).

tff(c_99,plain,
    ( ~ v8_lattices('#skF_1')
    | r1_lattices('#skF_1','#skF_2',k6_lattices('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_108,plain,(
    ~ v8_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_111,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_108])).

tff(c_114,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38,c_111])).

tff(c_116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_114])).

tff(c_118,plain,(
    v8_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_117,plain,(
    r1_lattices('#skF_1','#skF_2',k6_lattices('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_157,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_173,plain,(
    ! [A_39,B_40] :
      ( r3_lattices(A_39,B_40,k6_lattices(A_39))
      | ~ r1_lattices(A_39,B_40,k6_lattices(A_39))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l3_lattices(A_39)
      | ~ v9_lattices(A_39)
      | ~ v8_lattices(A_39)
      | ~ v6_lattices(A_39)
      | ~ l2_lattices(A_39)
      | v2_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_16,c_157])).

tff(c_30,plain,(
    ~ r3_lattices('#skF_1','#skF_2',k6_lattices('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_178,plain,
    ( ~ r1_lattices('#skF_1','#skF_2',k6_lattices('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | ~ v9_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | ~ l2_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_173,c_30])).

tff(c_182,plain,
    ( ~ v9_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_89,c_118,c_34,c_32,c_117,c_178])).

tff(c_183,plain,(
    ~ v9_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_182])).

tff(c_186,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_183])).

tff(c_189,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38,c_186])).

tff(c_191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_189])).

%------------------------------------------------------------------------------
