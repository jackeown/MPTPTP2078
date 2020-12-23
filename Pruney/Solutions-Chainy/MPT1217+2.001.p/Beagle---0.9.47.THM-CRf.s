%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:19 EST 2020

% Result     : Theorem 5.22s
% Output     : CNFRefutation 5.22s
% Verified   : 
% Statistics : Number of formulae       :  198 (1274 expanded)
%              Number of leaves         :   38 ( 453 expanded)
%              Depth                    :   26
%              Number of atoms          :  551 (5197 expanded)
%              Number of equality atoms :   91 ( 376 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > k7_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(k3_lattices,type,(
    k3_lattices: ( $i * $i * $i ) > $i )).

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

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(v17_lattices,type,(
    v17_lattices: $i > $o )).

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

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k7_lattices,type,(
    k7_lattices: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_191,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v17_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r3_lattices(A,B,C)
                 => r3_lattices(A,k7_lattices(A,C),k7_lattices(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_lattices)).

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

tff(f_90,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k3_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k7_lattices(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

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

tff(f_154,axiom,(
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

tff(f_135,axiom,(
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

tff(f_171,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v17_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k7_lattices(A,k4_lattices(A,B,C)) = k3_lattices(A,k7_lattices(A,B),k7_lattices(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattices)).

tff(c_48,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_50,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_54,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_57,plain,(
    ! [A_42] :
      ( l1_lattices(A_42)
      | ~ l3_lattices(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_61,plain,(
    l1_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_57])).

tff(c_761,plain,(
    ! [A_110,B_111,C_112] :
      ( k4_lattices(A_110,B_111,C_112) = k2_lattices(A_110,B_111,C_112)
      | ~ m1_subset_1(C_112,u1_struct_0(A_110))
      | ~ m1_subset_1(B_111,u1_struct_0(A_110))
      | ~ l1_lattices(A_110)
      | ~ v6_lattices(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_765,plain,(
    ! [B_111] :
      ( k4_lattices('#skF_1',B_111,'#skF_3') = k2_lattices('#skF_1',B_111,'#skF_3')
      | ~ m1_subset_1(B_111,u1_struct_0('#skF_1'))
      | ~ l1_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_761])).

tff(c_771,plain,(
    ! [B_111] :
      ( k4_lattices('#skF_1',B_111,'#skF_3') = k2_lattices('#skF_1',B_111,'#skF_3')
      | ~ m1_subset_1(B_111,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_765])).

tff(c_772,plain,(
    ! [B_111] :
      ( k4_lattices('#skF_1',B_111,'#skF_3') = k2_lattices('#skF_1',B_111,'#skF_3')
      | ~ m1_subset_1(B_111,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_771])).

tff(c_777,plain,(
    ~ v6_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_772])).

tff(c_780,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_777])).

tff(c_783,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_780])).

tff(c_785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_783])).

tff(c_787,plain,(
    v6_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_772])).

tff(c_767,plain,(
    ! [B_111] :
      ( k4_lattices('#skF_1',B_111,'#skF_2') = k2_lattices('#skF_1',B_111,'#skF_2')
      | ~ m1_subset_1(B_111,u1_struct_0('#skF_1'))
      | ~ l1_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_761])).

tff(c_775,plain,(
    ! [B_111] :
      ( k4_lattices('#skF_1',B_111,'#skF_2') = k2_lattices('#skF_1',B_111,'#skF_2')
      | ~ m1_subset_1(B_111,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_767])).

tff(c_776,plain,(
    ! [B_111] :
      ( k4_lattices('#skF_1',B_111,'#skF_2') = k2_lattices('#skF_1',B_111,'#skF_2')
      | ~ m1_subset_1(B_111,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_775])).

tff(c_790,plain,(
    ! [B_113] :
      ( k4_lattices('#skF_1',B_113,'#skF_2') = k2_lattices('#skF_1',B_113,'#skF_2')
      | ~ m1_subset_1(B_113,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_776])).

tff(c_805,plain,(
    k4_lattices('#skF_1','#skF_3','#skF_2') = k2_lattices('#skF_1','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_790])).

tff(c_52,plain,(
    v17_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,(
    ! [A_43] :
      ( l2_lattices(A_43)
      | ~ l3_lattices(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_66,plain,(
    l2_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_62])).

tff(c_690,plain,(
    ! [A_105,C_106,B_107] :
      ( k3_lattices(A_105,C_106,B_107) = k3_lattices(A_105,B_107,C_106)
      | ~ m1_subset_1(C_106,u1_struct_0(A_105))
      | ~ m1_subset_1(B_107,u1_struct_0(A_105))
      | ~ l2_lattices(A_105)
      | ~ v4_lattices(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_694,plain,(
    ! [B_107] :
      ( k3_lattices('#skF_1',B_107,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_107)
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_690])).

tff(c_700,plain,(
    ! [B_107] :
      ( k3_lattices('#skF_1',B_107,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_107)
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_694])).

tff(c_701,plain,(
    ! [B_107] :
      ( k3_lattices('#skF_1',B_107,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_107)
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_700])).

tff(c_706,plain,(
    ~ v4_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_701])).

tff(c_710,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_706])).

tff(c_713,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_710])).

tff(c_715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_713])).

tff(c_717,plain,(
    v4_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_701])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k7_lattices(A_12,B_13),u1_struct_0(A_12))
      | ~ m1_subset_1(B_13,u1_struct_0(A_12))
      | ~ l3_lattices(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_143,plain,(
    ! [A_62,B_63,C_64] :
      ( k3_lattices(A_62,B_63,C_64) = k1_lattices(A_62,B_63,C_64)
      | ~ m1_subset_1(C_64,u1_struct_0(A_62))
      | ~ m1_subset_1(B_63,u1_struct_0(A_62))
      | ~ l2_lattices(A_62)
      | ~ v4_lattices(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_147,plain,(
    ! [B_63] :
      ( k3_lattices('#skF_1',B_63,'#skF_3') = k1_lattices('#skF_1',B_63,'#skF_3')
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_143])).

tff(c_153,plain,(
    ! [B_63] :
      ( k3_lattices('#skF_1',B_63,'#skF_3') = k1_lattices('#skF_1',B_63,'#skF_3')
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_147])).

tff(c_154,plain,(
    ! [B_63] :
      ( k3_lattices('#skF_1',B_63,'#skF_3') = k1_lattices('#skF_1',B_63,'#skF_3')
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_153])).

tff(c_159,plain,(
    ~ v4_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_178,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_159])).

tff(c_181,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_178])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_181])).

tff(c_186,plain,(
    ! [B_68] :
      ( k3_lattices('#skF_1',B_68,'#skF_3') = k1_lattices('#skF_1',B_68,'#skF_3')
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_202,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_3') = k1_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_186])).

tff(c_185,plain,(
    v4_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_149,plain,(
    ! [B_63] :
      ( k3_lattices('#skF_1',B_63,'#skF_2') = k1_lattices('#skF_1',B_63,'#skF_2')
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_143])).

tff(c_157,plain,(
    ! [B_63] :
      ( k3_lattices('#skF_1',B_63,'#skF_2') = k1_lattices('#skF_1',B_63,'#skF_2')
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_149])).

tff(c_158,plain,(
    ! [B_63] :
      ( k3_lattices('#skF_1',B_63,'#skF_2') = k1_lattices('#skF_1',B_63,'#skF_2')
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_157])).

tff(c_213,plain,(
    ! [B_69] :
      ( k3_lattices('#skF_1',B_69,'#skF_2') = k1_lattices('#skF_1',B_69,'#skF_2')
      | ~ m1_subset_1(B_69,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_158])).

tff(c_228,plain,(
    k3_lattices('#skF_1','#skF_3','#skF_2') = k1_lattices('#skF_1','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_213])).

tff(c_316,plain,(
    ! [A_75,C_76,B_77] :
      ( k3_lattices(A_75,C_76,B_77) = k3_lattices(A_75,B_77,C_76)
      | ~ m1_subset_1(C_76,u1_struct_0(A_75))
      | ~ m1_subset_1(B_77,u1_struct_0(A_75))
      | ~ l2_lattices(A_75)
      | ~ v4_lattices(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_320,plain,(
    ! [B_77] :
      ( k3_lattices('#skF_1',B_77,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_77)
      | ~ m1_subset_1(B_77,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_316])).

tff(c_326,plain,(
    ! [B_77] :
      ( k3_lattices('#skF_1',B_77,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_77)
      | ~ m1_subset_1(B_77,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_66,c_320])).

tff(c_332,plain,(
    ! [B_78] :
      ( k3_lattices('#skF_1',B_78,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_78)
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_326])).

tff(c_342,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_3') = k3_lattices('#skF_1','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_332])).

tff(c_350,plain,(
    k1_lattices('#skF_1','#skF_2','#skF_3') = k1_lattices('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_228,c_342])).

tff(c_74,plain,(
    ! [A_52,B_53,C_54] :
      ( r1_lattices(A_52,B_53,C_54)
      | k1_lattices(A_52,B_53,C_54) != C_54
      | ~ m1_subset_1(C_54,u1_struct_0(A_52))
      | ~ m1_subset_1(B_53,u1_struct_0(A_52))
      | ~ l2_lattices(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_78,plain,(
    ! [B_53] :
      ( r1_lattices('#skF_1',B_53,'#skF_3')
      | k1_lattices('#skF_1',B_53,'#skF_3') != '#skF_3'
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_74])).

tff(c_84,plain,(
    ! [B_53] :
      ( r1_lattices('#skF_1',B_53,'#skF_3')
      | k1_lattices('#skF_1',B_53,'#skF_3') != '#skF_3'
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_78])).

tff(c_90,plain,(
    ! [B_55] :
      ( r1_lattices('#skF_1',B_55,'#skF_3')
      | k1_lattices('#skF_1',B_55,'#skF_3') != '#skF_3'
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_84])).

tff(c_106,plain,
    ( r1_lattices('#skF_1','#skF_2','#skF_3')
    | k1_lattices('#skF_1','#skF_2','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_48,c_90])).

tff(c_108,plain,(
    k1_lattices('#skF_1','#skF_2','#skF_3') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_352,plain,(
    k1_lattices('#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_108])).

tff(c_255,plain,(
    ! [A_71,B_72,C_73] :
      ( k4_lattices(A_71,B_72,C_73) = k2_lattices(A_71,B_72,C_73)
      | ~ m1_subset_1(C_73,u1_struct_0(A_71))
      | ~ m1_subset_1(B_72,u1_struct_0(A_71))
      | ~ l1_lattices(A_71)
      | ~ v6_lattices(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_261,plain,(
    ! [B_72] :
      ( k4_lattices('#skF_1',B_72,'#skF_2') = k2_lattices('#skF_1',B_72,'#skF_2')
      | ~ m1_subset_1(B_72,u1_struct_0('#skF_1'))
      | ~ l1_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_255])).

tff(c_269,plain,(
    ! [B_72] :
      ( k4_lattices('#skF_1',B_72,'#skF_2') = k2_lattices('#skF_1',B_72,'#skF_2')
      | ~ m1_subset_1(B_72,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_261])).

tff(c_270,plain,(
    ! [B_72] :
      ( k4_lattices('#skF_1',B_72,'#skF_2') = k2_lattices('#skF_1',B_72,'#skF_2')
      | ~ m1_subset_1(B_72,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_269])).

tff(c_279,plain,(
    ~ v6_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_283,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_279])).

tff(c_286,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_283])).

tff(c_288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_286])).

tff(c_290,plain,(
    v6_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_408,plain,(
    ! [A_81,B_82,C_83] :
      ( r1_lattices(A_81,B_82,C_83)
      | k2_lattices(A_81,B_82,C_83) != B_82
      | ~ m1_subset_1(C_83,u1_struct_0(A_81))
      | ~ m1_subset_1(B_82,u1_struct_0(A_81))
      | ~ l3_lattices(A_81)
      | ~ v9_lattices(A_81)
      | ~ v8_lattices(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_412,plain,(
    ! [B_82] :
      ( r1_lattices('#skF_1',B_82,'#skF_3')
      | k2_lattices('#skF_1',B_82,'#skF_3') != B_82
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_408])).

tff(c_418,plain,(
    ! [B_82] :
      ( r1_lattices('#skF_1',B_82,'#skF_3')
      | k2_lattices('#skF_1',B_82,'#skF_3') != B_82
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_412])).

tff(c_419,plain,(
    ! [B_82] :
      ( r1_lattices('#skF_1',B_82,'#skF_3')
      | k2_lattices('#skF_1',B_82,'#skF_3') != B_82
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_418])).

tff(c_574,plain,(
    ~ v8_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_419])).

tff(c_584,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_574])).

tff(c_587,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_584])).

tff(c_589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_587])).

tff(c_591,plain,(
    v8_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_419])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_590,plain,(
    ! [B_82] :
      ( ~ v9_lattices('#skF_1')
      | r1_lattices('#skF_1',B_82,'#skF_3')
      | k2_lattices('#skF_1',B_82,'#skF_3') != B_82
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_419])).

tff(c_592,plain,(
    ~ v9_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_590])).

tff(c_598,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_592])).

tff(c_601,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_598])).

tff(c_603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_601])).

tff(c_605,plain,(
    v9_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_590])).

tff(c_44,plain,(
    r3_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_624,plain,(
    ! [A_96,B_97,C_98] :
      ( r1_lattices(A_96,B_97,C_98)
      | ~ r3_lattices(A_96,B_97,C_98)
      | ~ m1_subset_1(C_98,u1_struct_0(A_96))
      | ~ m1_subset_1(B_97,u1_struct_0(A_96))
      | ~ l3_lattices(A_96)
      | ~ v9_lattices(A_96)
      | ~ v8_lattices(A_96)
      | ~ v6_lattices(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_626,plain,
    ( r1_lattices('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | ~ v9_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_624])).

tff(c_629,plain,
    ( r1_lattices('#skF_1','#skF_2','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_591,c_605,c_50,c_48,c_46,c_626])).

tff(c_630,plain,(
    r1_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_629])).

tff(c_20,plain,(
    ! [A_5,B_9,C_11] :
      ( k1_lattices(A_5,B_9,C_11) = C_11
      | ~ r1_lattices(A_5,B_9,C_11)
      | ~ m1_subset_1(C_11,u1_struct_0(A_5))
      | ~ m1_subset_1(B_9,u1_struct_0(A_5))
      | ~ l2_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_634,plain,
    ( k1_lattices('#skF_1','#skF_2','#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l2_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_630,c_20])).

tff(c_641,plain,
    ( k1_lattices('#skF_1','#skF_3','#skF_2') = '#skF_3'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_48,c_46,c_350,c_634])).

tff(c_643,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_352,c_641])).

tff(c_644,plain,(
    r1_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_1024,plain,(
    ! [A_127,B_128,C_129] :
      ( k2_lattices(A_127,B_128,C_129) = B_128
      | ~ r1_lattices(A_127,B_128,C_129)
      | ~ m1_subset_1(C_129,u1_struct_0(A_127))
      | ~ m1_subset_1(B_128,u1_struct_0(A_127))
      | ~ l3_lattices(A_127)
      | ~ v9_lattices(A_127)
      | ~ v8_lattices(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1030,plain,
    ( k2_lattices('#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | ~ v9_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_644,c_1024])).

tff(c_1041,plain,
    ( k2_lattices('#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ v9_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_1030])).

tff(c_1042,plain,
    ( k2_lattices('#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ v9_lattices('#skF_1')
    | ~ v8_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1041])).

tff(c_1043,plain,(
    ~ v8_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1042])).

tff(c_1046,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_1043])).

tff(c_1049,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_1046])).

tff(c_1051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1049])).

tff(c_1053,plain,(
    v8_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1042])).

tff(c_1052,plain,
    ( ~ v9_lattices('#skF_1')
    | k2_lattices('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1042])).

tff(c_1071,plain,(
    ~ v9_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1052])).

tff(c_1074,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_1071])).

tff(c_1077,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_1074])).

tff(c_1079,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1077])).

tff(c_1081,plain,(
    v9_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1052])).

tff(c_1091,plain,(
    ! [A_131,B_132,C_133] :
      ( r3_lattices(A_131,B_132,C_133)
      | ~ r1_lattices(A_131,B_132,C_133)
      | ~ m1_subset_1(C_133,u1_struct_0(A_131))
      | ~ m1_subset_1(B_132,u1_struct_0(A_131))
      | ~ l3_lattices(A_131)
      | ~ v9_lattices(A_131)
      | ~ v8_lattices(A_131)
      | ~ v6_lattices(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1685,plain,(
    ! [A_186,B_187,B_188] :
      ( r3_lattices(A_186,B_187,k7_lattices(A_186,B_188))
      | ~ r1_lattices(A_186,B_187,k7_lattices(A_186,B_188))
      | ~ m1_subset_1(B_187,u1_struct_0(A_186))
      | ~ v9_lattices(A_186)
      | ~ v8_lattices(A_186)
      | ~ v6_lattices(A_186)
      | ~ m1_subset_1(B_188,u1_struct_0(A_186))
      | ~ l3_lattices(A_186)
      | v2_struct_0(A_186) ) ),
    inference(resolution,[status(thm)],[c_22,c_1091])).

tff(c_42,plain,(
    ~ r3_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1690,plain,
    ( ~ r1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2'))
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1'))
    | ~ v9_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1685,c_42])).

tff(c_1694,plain,
    ( ~ r1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2'))
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_787,c_1053,c_1081,c_1690])).

tff(c_1695,plain,
    ( ~ r1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2'))
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1694])).

tff(c_1696,plain,(
    ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1695])).

tff(c_1699,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1696])).

tff(c_1702,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_1699])).

tff(c_1704,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1702])).

tff(c_1706,plain,(
    m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1695])).

tff(c_840,plain,(
    ! [A_115,B_116,C_117] :
      ( k3_lattices(A_115,B_116,C_117) = k1_lattices(A_115,B_116,C_117)
      | ~ m1_subset_1(C_117,u1_struct_0(A_115))
      | ~ m1_subset_1(B_116,u1_struct_0(A_115))
      | ~ l2_lattices(A_115)
      | ~ v4_lattices(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_847,plain,(
    ! [A_12,B_116,B_13] :
      ( k3_lattices(A_12,B_116,k7_lattices(A_12,B_13)) = k1_lattices(A_12,B_116,k7_lattices(A_12,B_13))
      | ~ m1_subset_1(B_116,u1_struct_0(A_12))
      | ~ l2_lattices(A_12)
      | ~ v4_lattices(A_12)
      | ~ m1_subset_1(B_13,u1_struct_0(A_12))
      | ~ l3_lattices(A_12)
      | v2_struct_0(A_12) ) ),
    inference(resolution,[status(thm)],[c_22,c_840])).

tff(c_1717,plain,(
    ! [B_13] :
      ( k3_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1',B_13)) = k1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1',B_13))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1706,c_847])).

tff(c_1802,plain,(
    ! [B_13] :
      ( k3_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1',B_13)) = k1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1',B_13))
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_717,c_66,c_1717])).

tff(c_2492,plain,(
    ! [B_212] :
      ( k3_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1',B_212)) = k1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1',B_212))
      | ~ m1_subset_1(B_212,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1802])).

tff(c_40,plain,(
    ! [A_31,B_35,C_37] :
      ( k3_lattices(A_31,k7_lattices(A_31,B_35),k7_lattices(A_31,C_37)) = k7_lattices(A_31,k4_lattices(A_31,B_35,C_37))
      | ~ m1_subset_1(C_37,u1_struct_0(A_31))
      | ~ m1_subset_1(B_35,u1_struct_0(A_31))
      | ~ l3_lattices(A_31)
      | ~ v17_lattices(A_31)
      | ~ v10_lattices(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_2510,plain,(
    ! [B_212] :
      ( k1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1',B_212)) = k7_lattices('#skF_1',k4_lattices('#skF_1','#skF_3',B_212))
      | ~ m1_subset_1(B_212,u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v17_lattices('#skF_1')
      | ~ v10_lattices('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ m1_subset_1(B_212,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2492,c_40])).

tff(c_2547,plain,(
    ! [B_212] :
      ( k1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1',B_212)) = k7_lattices('#skF_1',k4_lattices('#skF_1','#skF_3',B_212))
      | v2_struct_0('#skF_1')
      | ~ m1_subset_1(B_212,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_46,c_2510])).

tff(c_2583,plain,(
    ! [B_214] :
      ( k1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1',B_214)) = k7_lattices('#skF_1',k4_lattices('#skF_1','#skF_3',B_214))
      | ~ m1_subset_1(B_214,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2547])).

tff(c_81,plain,(
    ! [A_12,B_53,B_13] :
      ( r1_lattices(A_12,B_53,k7_lattices(A_12,B_13))
      | k1_lattices(A_12,B_53,k7_lattices(A_12,B_13)) != k7_lattices(A_12,B_13)
      | ~ m1_subset_1(B_53,u1_struct_0(A_12))
      | ~ l2_lattices(A_12)
      | ~ m1_subset_1(B_13,u1_struct_0(A_12))
      | ~ l3_lattices(A_12)
      | v2_struct_0(A_12) ) ),
    inference(resolution,[status(thm)],[c_22,c_74])).

tff(c_1705,plain,(
    ~ r1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1695])).

tff(c_1894,plain,
    ( k1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2')) != k7_lattices('#skF_1','#skF_2')
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1'))
    | ~ l2_lattices('#skF_1')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_81,c_1705])).

tff(c_1901,plain,
    ( k1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2')) != k7_lattices('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_66,c_1706,c_1894])).

tff(c_1902,plain,(
    k1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2')) != k7_lattices('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1901])).

tff(c_2592,plain,
    ( k7_lattices('#skF_1',k4_lattices('#skF_1','#skF_3','#skF_2')) != k7_lattices('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2583,c_1902])).

tff(c_2603,plain,(
    k7_lattices('#skF_1',k2_lattices('#skF_1','#skF_3','#skF_2')) != k7_lattices('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_805,c_2592])).

tff(c_1080,plain,(
    k2_lattices('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1052])).

tff(c_815,plain,(
    ! [B_114] :
      ( k4_lattices('#skF_1',B_114,'#skF_3') = k2_lattices('#skF_1',B_114,'#skF_3')
      | ~ m1_subset_1(B_114,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_772])).

tff(c_831,plain,(
    k4_lattices('#skF_1','#skF_2','#skF_3') = k2_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_815])).

tff(c_1082,plain,(
    k4_lattices('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_831])).

tff(c_697,plain,(
    ! [A_12,B_13,B_107] :
      ( k3_lattices(A_12,k7_lattices(A_12,B_13),B_107) = k3_lattices(A_12,B_107,k7_lattices(A_12,B_13))
      | ~ m1_subset_1(B_107,u1_struct_0(A_12))
      | ~ l2_lattices(A_12)
      | ~ v4_lattices(A_12)
      | ~ m1_subset_1(B_13,u1_struct_0(A_12))
      | ~ l3_lattices(A_12)
      | v2_struct_0(A_12) ) ),
    inference(resolution,[status(thm)],[c_22,c_690])).

tff(c_1730,plain,(
    ! [B_13] :
      ( k3_lattices('#skF_1',k7_lattices('#skF_1',B_13),k7_lattices('#skF_1','#skF_3')) = k3_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1',B_13))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1706,c_697])).

tff(c_1813,plain,(
    ! [B_13] :
      ( k3_lattices('#skF_1',k7_lattices('#skF_1',B_13),k7_lattices('#skF_1','#skF_3')) = k3_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1',B_13))
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_717,c_66,c_1730])).

tff(c_2607,plain,(
    ! [B_215] :
      ( k3_lattices('#skF_1',k7_lattices('#skF_1',B_215),k7_lattices('#skF_1','#skF_3')) = k3_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1',B_215))
      | ~ m1_subset_1(B_215,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1813])).

tff(c_2637,plain,(
    ! [B_215] :
      ( k3_lattices('#skF_1',k7_lattices('#skF_1',B_215),k7_lattices('#skF_1','#skF_3')) = k7_lattices('#skF_1',k4_lattices('#skF_1','#skF_3',B_215))
      | ~ m1_subset_1(B_215,u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v17_lattices('#skF_1')
      | ~ v10_lattices('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ m1_subset_1(B_215,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2607,c_40])).

tff(c_2707,plain,(
    ! [B_215] :
      ( k3_lattices('#skF_1',k7_lattices('#skF_1',B_215),k7_lattices('#skF_1','#skF_3')) = k7_lattices('#skF_1',k4_lattices('#skF_1','#skF_3',B_215))
      | v2_struct_0('#skF_1')
      | ~ m1_subset_1(B_215,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_46,c_2637])).

tff(c_2742,plain,(
    ! [B_216] :
      ( k3_lattices('#skF_1',k7_lattices('#skF_1',B_216),k7_lattices('#skF_1','#skF_3')) = k7_lattices('#skF_1',k4_lattices('#skF_1','#skF_3',B_216))
      | ~ m1_subset_1(B_216,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2707])).

tff(c_2767,plain,(
    ! [B_216] :
      ( k7_lattices('#skF_1',k4_lattices('#skF_1',B_216,'#skF_3')) = k7_lattices('#skF_1',k4_lattices('#skF_1','#skF_3',B_216))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_216,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v17_lattices('#skF_1')
      | ~ v10_lattices('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ m1_subset_1(B_216,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2742,c_40])).

tff(c_2812,plain,(
    ! [B_216] :
      ( k7_lattices('#skF_1',k4_lattices('#skF_1',B_216,'#skF_3')) = k7_lattices('#skF_1',k4_lattices('#skF_1','#skF_3',B_216))
      | v2_struct_0('#skF_1')
      | ~ m1_subset_1(B_216,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_46,c_2767])).

tff(c_2831,plain,(
    ! [B_217] :
      ( k7_lattices('#skF_1',k4_lattices('#skF_1',B_217,'#skF_3')) = k7_lattices('#skF_1',k4_lattices('#skF_1','#skF_3',B_217))
      | ~ m1_subset_1(B_217,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2812])).

tff(c_2844,plain,(
    k7_lattices('#skF_1',k4_lattices('#skF_1','#skF_2','#skF_3')) = k7_lattices('#skF_1',k4_lattices('#skF_1','#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_2831])).

tff(c_2854,plain,(
    k7_lattices('#skF_1',k2_lattices('#skF_1','#skF_3','#skF_2')) = k7_lattices('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_805,c_1082,c_2844])).

tff(c_2856,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2603,c_2854])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:31:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.22/1.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.22/1.93  
% 5.22/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.22/1.93  %$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > k7_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1
% 5.22/1.93  
% 5.22/1.93  %Foreground sorts:
% 5.22/1.93  
% 5.22/1.93  
% 5.22/1.93  %Background operators:
% 5.22/1.93  
% 5.22/1.93  
% 5.22/1.93  %Foreground operators:
% 5.22/1.93  tff(l3_lattices, type, l3_lattices: $i > $o).
% 5.22/1.93  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 5.22/1.93  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.22/1.93  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 5.22/1.93  tff(l2_lattices, type, l2_lattices: $i > $o).
% 5.22/1.93  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 5.22/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.22/1.93  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 5.22/1.93  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 5.22/1.93  tff(l1_lattices, type, l1_lattices: $i > $o).
% 5.22/1.93  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 5.22/1.93  tff(v17_lattices, type, v17_lattices: $i > $o).
% 5.22/1.93  tff(v4_lattices, type, v4_lattices: $i > $o).
% 5.22/1.93  tff(v6_lattices, type, v6_lattices: $i > $o).
% 5.22/1.93  tff('#skF_2', type, '#skF_2': $i).
% 5.22/1.93  tff(v9_lattices, type, v9_lattices: $i > $o).
% 5.22/1.93  tff('#skF_3', type, '#skF_3': $i).
% 5.22/1.93  tff('#skF_1', type, '#skF_1': $i).
% 5.22/1.93  tff(v5_lattices, type, v5_lattices: $i > $o).
% 5.22/1.93  tff(v10_lattices, type, v10_lattices: $i > $o).
% 5.22/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.22/1.93  tff(v8_lattices, type, v8_lattices: $i > $o).
% 5.22/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.22/1.93  tff(k7_lattices, type, k7_lattices: ($i * $i) > $i).
% 5.22/1.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.22/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.22/1.93  tff(v7_lattices, type, v7_lattices: $i > $o).
% 5.22/1.93  
% 5.22/1.96  tff(f_191, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_lattices(A, B, C) => r3_lattices(A, k7_lattices(A, C), k7_lattices(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_lattices)).
% 5.22/1.96  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 5.22/1.96  tff(f_90, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 5.22/1.96  tff(f_116, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 5.22/1.96  tff(f_60, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k3_lattices(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 5.22/1.96  tff(f_84, axiom, (![A, B]: (((~v2_struct_0(A) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k7_lattices(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_lattices)).
% 5.22/1.96  tff(f_103, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 5.22/1.96  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 5.22/1.96  tff(f_154, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 5.22/1.96  tff(f_135, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 5.22/1.96  tff(f_171, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k7_lattices(A, k4_lattices(A, B, C)) = k3_lattices(A, k7_lattices(A, B), k7_lattices(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattices)).
% 5.22/1.96  tff(c_48, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.22/1.96  tff(c_46, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.22/1.96  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.22/1.96  tff(c_50, plain, (l3_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.22/1.96  tff(c_54, plain, (v10_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.22/1.96  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.22/1.96  tff(c_57, plain, (![A_42]: (l1_lattices(A_42) | ~l3_lattices(A_42))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.22/1.96  tff(c_61, plain, (l1_lattices('#skF_1')), inference(resolution, [status(thm)], [c_50, c_57])).
% 5.22/1.96  tff(c_761, plain, (![A_110, B_111, C_112]: (k4_lattices(A_110, B_111, C_112)=k2_lattices(A_110, B_111, C_112) | ~m1_subset_1(C_112, u1_struct_0(A_110)) | ~m1_subset_1(B_111, u1_struct_0(A_110)) | ~l1_lattices(A_110) | ~v6_lattices(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.22/1.96  tff(c_765, plain, (![B_111]: (k4_lattices('#skF_1', B_111, '#skF_3')=k2_lattices('#skF_1', B_111, '#skF_3') | ~m1_subset_1(B_111, u1_struct_0('#skF_1')) | ~l1_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_761])).
% 5.22/1.96  tff(c_771, plain, (![B_111]: (k4_lattices('#skF_1', B_111, '#skF_3')=k2_lattices('#skF_1', B_111, '#skF_3') | ~m1_subset_1(B_111, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_765])).
% 5.22/1.96  tff(c_772, plain, (![B_111]: (k4_lattices('#skF_1', B_111, '#skF_3')=k2_lattices('#skF_1', B_111, '#skF_3') | ~m1_subset_1(B_111, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_771])).
% 5.22/1.96  tff(c_777, plain, (~v6_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_772])).
% 5.22/1.96  tff(c_780, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_8, c_777])).
% 5.22/1.96  tff(c_783, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_780])).
% 5.22/1.96  tff(c_785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_783])).
% 5.22/1.96  tff(c_787, plain, (v6_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_772])).
% 5.22/1.96  tff(c_767, plain, (![B_111]: (k4_lattices('#skF_1', B_111, '#skF_2')=k2_lattices('#skF_1', B_111, '#skF_2') | ~m1_subset_1(B_111, u1_struct_0('#skF_1')) | ~l1_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_761])).
% 5.22/1.96  tff(c_775, plain, (![B_111]: (k4_lattices('#skF_1', B_111, '#skF_2')=k2_lattices('#skF_1', B_111, '#skF_2') | ~m1_subset_1(B_111, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_767])).
% 5.22/1.96  tff(c_776, plain, (![B_111]: (k4_lattices('#skF_1', B_111, '#skF_2')=k2_lattices('#skF_1', B_111, '#skF_2') | ~m1_subset_1(B_111, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_775])).
% 5.22/1.96  tff(c_790, plain, (![B_113]: (k4_lattices('#skF_1', B_113, '#skF_2')=k2_lattices('#skF_1', B_113, '#skF_2') | ~m1_subset_1(B_113, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_787, c_776])).
% 5.22/1.96  tff(c_805, plain, (k4_lattices('#skF_1', '#skF_3', '#skF_2')=k2_lattices('#skF_1', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_790])).
% 5.22/1.96  tff(c_52, plain, (v17_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.22/1.96  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.22/1.96  tff(c_62, plain, (![A_43]: (l2_lattices(A_43) | ~l3_lattices(A_43))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.22/1.96  tff(c_66, plain, (l2_lattices('#skF_1')), inference(resolution, [status(thm)], [c_50, c_62])).
% 5.22/1.96  tff(c_690, plain, (![A_105, C_106, B_107]: (k3_lattices(A_105, C_106, B_107)=k3_lattices(A_105, B_107, C_106) | ~m1_subset_1(C_106, u1_struct_0(A_105)) | ~m1_subset_1(B_107, u1_struct_0(A_105)) | ~l2_lattices(A_105) | ~v4_lattices(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.22/1.96  tff(c_694, plain, (![B_107]: (k3_lattices('#skF_1', B_107, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_107) | ~m1_subset_1(B_107, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_690])).
% 5.22/1.96  tff(c_700, plain, (![B_107]: (k3_lattices('#skF_1', B_107, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_107) | ~m1_subset_1(B_107, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_694])).
% 5.22/1.96  tff(c_701, plain, (![B_107]: (k3_lattices('#skF_1', B_107, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_107) | ~m1_subset_1(B_107, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_700])).
% 5.22/1.96  tff(c_706, plain, (~v4_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_701])).
% 5.22/1.96  tff(c_710, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_12, c_706])).
% 5.22/1.96  tff(c_713, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_710])).
% 5.22/1.96  tff(c_715, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_713])).
% 5.22/1.96  tff(c_717, plain, (v4_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_701])).
% 5.22/1.96  tff(c_22, plain, (![A_12, B_13]: (m1_subset_1(k7_lattices(A_12, B_13), u1_struct_0(A_12)) | ~m1_subset_1(B_13, u1_struct_0(A_12)) | ~l3_lattices(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.22/1.96  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.22/1.96  tff(c_143, plain, (![A_62, B_63, C_64]: (k3_lattices(A_62, B_63, C_64)=k1_lattices(A_62, B_63, C_64) | ~m1_subset_1(C_64, u1_struct_0(A_62)) | ~m1_subset_1(B_63, u1_struct_0(A_62)) | ~l2_lattices(A_62) | ~v4_lattices(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.22/1.96  tff(c_147, plain, (![B_63]: (k3_lattices('#skF_1', B_63, '#skF_3')=k1_lattices('#skF_1', B_63, '#skF_3') | ~m1_subset_1(B_63, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_143])).
% 5.22/1.96  tff(c_153, plain, (![B_63]: (k3_lattices('#skF_1', B_63, '#skF_3')=k1_lattices('#skF_1', B_63, '#skF_3') | ~m1_subset_1(B_63, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_147])).
% 5.22/1.96  tff(c_154, plain, (![B_63]: (k3_lattices('#skF_1', B_63, '#skF_3')=k1_lattices('#skF_1', B_63, '#skF_3') | ~m1_subset_1(B_63, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_153])).
% 5.22/1.96  tff(c_159, plain, (~v4_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_154])).
% 5.22/1.96  tff(c_178, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_12, c_159])).
% 5.22/1.96  tff(c_181, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_178])).
% 5.22/1.96  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_181])).
% 5.22/1.96  tff(c_186, plain, (![B_68]: (k3_lattices('#skF_1', B_68, '#skF_3')=k1_lattices('#skF_1', B_68, '#skF_3') | ~m1_subset_1(B_68, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_154])).
% 5.22/1.96  tff(c_202, plain, (k3_lattices('#skF_1', '#skF_2', '#skF_3')=k1_lattices('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_186])).
% 5.22/1.96  tff(c_185, plain, (v4_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_154])).
% 5.22/1.96  tff(c_149, plain, (![B_63]: (k3_lattices('#skF_1', B_63, '#skF_2')=k1_lattices('#skF_1', B_63, '#skF_2') | ~m1_subset_1(B_63, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_143])).
% 5.22/1.96  tff(c_157, plain, (![B_63]: (k3_lattices('#skF_1', B_63, '#skF_2')=k1_lattices('#skF_1', B_63, '#skF_2') | ~m1_subset_1(B_63, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_149])).
% 5.22/1.96  tff(c_158, plain, (![B_63]: (k3_lattices('#skF_1', B_63, '#skF_2')=k1_lattices('#skF_1', B_63, '#skF_2') | ~m1_subset_1(B_63, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_157])).
% 5.22/1.96  tff(c_213, plain, (![B_69]: (k3_lattices('#skF_1', B_69, '#skF_2')=k1_lattices('#skF_1', B_69, '#skF_2') | ~m1_subset_1(B_69, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_158])).
% 5.22/1.96  tff(c_228, plain, (k3_lattices('#skF_1', '#skF_3', '#skF_2')=k1_lattices('#skF_1', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_213])).
% 5.22/1.96  tff(c_316, plain, (![A_75, C_76, B_77]: (k3_lattices(A_75, C_76, B_77)=k3_lattices(A_75, B_77, C_76) | ~m1_subset_1(C_76, u1_struct_0(A_75)) | ~m1_subset_1(B_77, u1_struct_0(A_75)) | ~l2_lattices(A_75) | ~v4_lattices(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.22/1.96  tff(c_320, plain, (![B_77]: (k3_lattices('#skF_1', B_77, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_77) | ~m1_subset_1(B_77, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_316])).
% 5.22/1.96  tff(c_326, plain, (![B_77]: (k3_lattices('#skF_1', B_77, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_77) | ~m1_subset_1(B_77, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_66, c_320])).
% 5.22/1.96  tff(c_332, plain, (![B_78]: (k3_lattices('#skF_1', B_78, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_78) | ~m1_subset_1(B_78, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_326])).
% 5.22/1.96  tff(c_342, plain, (k3_lattices('#skF_1', '#skF_2', '#skF_3')=k3_lattices('#skF_1', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_332])).
% 5.22/1.96  tff(c_350, plain, (k1_lattices('#skF_1', '#skF_2', '#skF_3')=k1_lattices('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_202, c_228, c_342])).
% 5.22/1.96  tff(c_74, plain, (![A_52, B_53, C_54]: (r1_lattices(A_52, B_53, C_54) | k1_lattices(A_52, B_53, C_54)!=C_54 | ~m1_subset_1(C_54, u1_struct_0(A_52)) | ~m1_subset_1(B_53, u1_struct_0(A_52)) | ~l2_lattices(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.22/1.96  tff(c_78, plain, (![B_53]: (r1_lattices('#skF_1', B_53, '#skF_3') | k1_lattices('#skF_1', B_53, '#skF_3')!='#skF_3' | ~m1_subset_1(B_53, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_74])).
% 5.22/1.96  tff(c_84, plain, (![B_53]: (r1_lattices('#skF_1', B_53, '#skF_3') | k1_lattices('#skF_1', B_53, '#skF_3')!='#skF_3' | ~m1_subset_1(B_53, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_78])).
% 5.22/1.96  tff(c_90, plain, (![B_55]: (r1_lattices('#skF_1', B_55, '#skF_3') | k1_lattices('#skF_1', B_55, '#skF_3')!='#skF_3' | ~m1_subset_1(B_55, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_84])).
% 5.22/1.96  tff(c_106, plain, (r1_lattices('#skF_1', '#skF_2', '#skF_3') | k1_lattices('#skF_1', '#skF_2', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_48, c_90])).
% 5.22/1.96  tff(c_108, plain, (k1_lattices('#skF_1', '#skF_2', '#skF_3')!='#skF_3'), inference(splitLeft, [status(thm)], [c_106])).
% 5.22/1.96  tff(c_352, plain, (k1_lattices('#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_350, c_108])).
% 5.22/1.96  tff(c_255, plain, (![A_71, B_72, C_73]: (k4_lattices(A_71, B_72, C_73)=k2_lattices(A_71, B_72, C_73) | ~m1_subset_1(C_73, u1_struct_0(A_71)) | ~m1_subset_1(B_72, u1_struct_0(A_71)) | ~l1_lattices(A_71) | ~v6_lattices(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.22/1.96  tff(c_261, plain, (![B_72]: (k4_lattices('#skF_1', B_72, '#skF_2')=k2_lattices('#skF_1', B_72, '#skF_2') | ~m1_subset_1(B_72, u1_struct_0('#skF_1')) | ~l1_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_255])).
% 5.22/1.96  tff(c_269, plain, (![B_72]: (k4_lattices('#skF_1', B_72, '#skF_2')=k2_lattices('#skF_1', B_72, '#skF_2') | ~m1_subset_1(B_72, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_261])).
% 5.22/1.96  tff(c_270, plain, (![B_72]: (k4_lattices('#skF_1', B_72, '#skF_2')=k2_lattices('#skF_1', B_72, '#skF_2') | ~m1_subset_1(B_72, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_269])).
% 5.22/1.96  tff(c_279, plain, (~v6_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_270])).
% 5.22/1.96  tff(c_283, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_8, c_279])).
% 5.22/1.96  tff(c_286, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_283])).
% 5.22/1.96  tff(c_288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_286])).
% 5.22/1.96  tff(c_290, plain, (v6_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_270])).
% 5.22/1.96  tff(c_408, plain, (![A_81, B_82, C_83]: (r1_lattices(A_81, B_82, C_83) | k2_lattices(A_81, B_82, C_83)!=B_82 | ~m1_subset_1(C_83, u1_struct_0(A_81)) | ~m1_subset_1(B_82, u1_struct_0(A_81)) | ~l3_lattices(A_81) | ~v9_lattices(A_81) | ~v8_lattices(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.22/1.96  tff(c_412, plain, (![B_82]: (r1_lattices('#skF_1', B_82, '#skF_3') | k2_lattices('#skF_1', B_82, '#skF_3')!=B_82 | ~m1_subset_1(B_82, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_408])).
% 5.22/1.96  tff(c_418, plain, (![B_82]: (r1_lattices('#skF_1', B_82, '#skF_3') | k2_lattices('#skF_1', B_82, '#skF_3')!=B_82 | ~m1_subset_1(B_82, u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_412])).
% 5.22/1.96  tff(c_419, plain, (![B_82]: (r1_lattices('#skF_1', B_82, '#skF_3') | k2_lattices('#skF_1', B_82, '#skF_3')!=B_82 | ~m1_subset_1(B_82, u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_418])).
% 5.22/1.96  tff(c_574, plain, (~v8_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_419])).
% 5.22/1.96  tff(c_584, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_4, c_574])).
% 5.22/1.96  tff(c_587, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_584])).
% 5.22/1.96  tff(c_589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_587])).
% 5.22/1.96  tff(c_591, plain, (v8_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_419])).
% 5.22/1.96  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.22/1.96  tff(c_590, plain, (![B_82]: (~v9_lattices('#skF_1') | r1_lattices('#skF_1', B_82, '#skF_3') | k2_lattices('#skF_1', B_82, '#skF_3')!=B_82 | ~m1_subset_1(B_82, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_419])).
% 5.22/1.96  tff(c_592, plain, (~v9_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_590])).
% 5.22/1.96  tff(c_598, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_2, c_592])).
% 5.22/1.96  tff(c_601, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_598])).
% 5.22/1.96  tff(c_603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_601])).
% 5.22/1.96  tff(c_605, plain, (v9_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_590])).
% 5.22/1.96  tff(c_44, plain, (r3_lattices('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.22/1.96  tff(c_624, plain, (![A_96, B_97, C_98]: (r1_lattices(A_96, B_97, C_98) | ~r3_lattices(A_96, B_97, C_98) | ~m1_subset_1(C_98, u1_struct_0(A_96)) | ~m1_subset_1(B_97, u1_struct_0(A_96)) | ~l3_lattices(A_96) | ~v9_lattices(A_96) | ~v8_lattices(A_96) | ~v6_lattices(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.22/1.96  tff(c_626, plain, (r1_lattices('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_624])).
% 5.22/1.96  tff(c_629, plain, (r1_lattices('#skF_1', '#skF_2', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_290, c_591, c_605, c_50, c_48, c_46, c_626])).
% 5.22/1.96  tff(c_630, plain, (r1_lattices('#skF_1', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_629])).
% 5.22/1.96  tff(c_20, plain, (![A_5, B_9, C_11]: (k1_lattices(A_5, B_9, C_11)=C_11 | ~r1_lattices(A_5, B_9, C_11) | ~m1_subset_1(C_11, u1_struct_0(A_5)) | ~m1_subset_1(B_9, u1_struct_0(A_5)) | ~l2_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.22/1.96  tff(c_634, plain, (k1_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_630, c_20])).
% 5.22/1.96  tff(c_641, plain, (k1_lattices('#skF_1', '#skF_3', '#skF_2')='#skF_3' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_48, c_46, c_350, c_634])).
% 5.22/1.96  tff(c_643, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_352, c_641])).
% 5.22/1.96  tff(c_644, plain, (r1_lattices('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_106])).
% 5.22/1.96  tff(c_1024, plain, (![A_127, B_128, C_129]: (k2_lattices(A_127, B_128, C_129)=B_128 | ~r1_lattices(A_127, B_128, C_129) | ~m1_subset_1(C_129, u1_struct_0(A_127)) | ~m1_subset_1(B_128, u1_struct_0(A_127)) | ~l3_lattices(A_127) | ~v9_lattices(A_127) | ~v8_lattices(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.22/1.96  tff(c_1030, plain, (k2_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_644, c_1024])).
% 5.22/1.96  tff(c_1041, plain, (k2_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_1030])).
% 5.22/1.96  tff(c_1042, plain, (k2_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_1041])).
% 5.22/1.96  tff(c_1043, plain, (~v8_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_1042])).
% 5.22/1.96  tff(c_1046, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_4, c_1043])).
% 5.22/1.96  tff(c_1049, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_1046])).
% 5.22/1.96  tff(c_1051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1049])).
% 5.22/1.96  tff(c_1053, plain, (v8_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_1042])).
% 5.22/1.96  tff(c_1052, plain, (~v9_lattices('#skF_1') | k2_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_1042])).
% 5.22/1.96  tff(c_1071, plain, (~v9_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_1052])).
% 5.22/1.96  tff(c_1074, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_2, c_1071])).
% 5.22/1.96  tff(c_1077, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_1074])).
% 5.22/1.96  tff(c_1079, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1077])).
% 5.22/1.96  tff(c_1081, plain, (v9_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_1052])).
% 5.22/1.96  tff(c_1091, plain, (![A_131, B_132, C_133]: (r3_lattices(A_131, B_132, C_133) | ~r1_lattices(A_131, B_132, C_133) | ~m1_subset_1(C_133, u1_struct_0(A_131)) | ~m1_subset_1(B_132, u1_struct_0(A_131)) | ~l3_lattices(A_131) | ~v9_lattices(A_131) | ~v8_lattices(A_131) | ~v6_lattices(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.22/1.96  tff(c_1685, plain, (![A_186, B_187, B_188]: (r3_lattices(A_186, B_187, k7_lattices(A_186, B_188)) | ~r1_lattices(A_186, B_187, k7_lattices(A_186, B_188)) | ~m1_subset_1(B_187, u1_struct_0(A_186)) | ~v9_lattices(A_186) | ~v8_lattices(A_186) | ~v6_lattices(A_186) | ~m1_subset_1(B_188, u1_struct_0(A_186)) | ~l3_lattices(A_186) | v2_struct_0(A_186))), inference(resolution, [status(thm)], [c_22, c_1091])).
% 5.22/1.96  tff(c_42, plain, (~r3_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.22/1.96  tff(c_1690, plain, (~r1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2')) | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1685, c_42])).
% 5.22/1.96  tff(c_1694, plain, (~r1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2')) | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_787, c_1053, c_1081, c_1690])).
% 5.22/1.96  tff(c_1695, plain, (~r1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2')) | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_1694])).
% 5.22/1.96  tff(c_1696, plain, (~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1695])).
% 5.22/1.96  tff(c_1699, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1696])).
% 5.22/1.96  tff(c_1702, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_1699])).
% 5.22/1.96  tff(c_1704, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1702])).
% 5.22/1.96  tff(c_1706, plain, (m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_1695])).
% 5.22/1.96  tff(c_840, plain, (![A_115, B_116, C_117]: (k3_lattices(A_115, B_116, C_117)=k1_lattices(A_115, B_116, C_117) | ~m1_subset_1(C_117, u1_struct_0(A_115)) | ~m1_subset_1(B_116, u1_struct_0(A_115)) | ~l2_lattices(A_115) | ~v4_lattices(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.22/1.96  tff(c_847, plain, (![A_12, B_116, B_13]: (k3_lattices(A_12, B_116, k7_lattices(A_12, B_13))=k1_lattices(A_12, B_116, k7_lattices(A_12, B_13)) | ~m1_subset_1(B_116, u1_struct_0(A_12)) | ~l2_lattices(A_12) | ~v4_lattices(A_12) | ~m1_subset_1(B_13, u1_struct_0(A_12)) | ~l3_lattices(A_12) | v2_struct_0(A_12))), inference(resolution, [status(thm)], [c_22, c_840])).
% 5.22/1.96  tff(c_1717, plain, (![B_13]: (k3_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', B_13))=k1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', B_13)) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | ~m1_subset_1(B_13, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1706, c_847])).
% 5.22/1.96  tff(c_1802, plain, (![B_13]: (k3_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', B_13))=k1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', B_13)) | ~m1_subset_1(B_13, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_717, c_66, c_1717])).
% 5.22/1.96  tff(c_2492, plain, (![B_212]: (k3_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', B_212))=k1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', B_212)) | ~m1_subset_1(B_212, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_1802])).
% 5.22/1.96  tff(c_40, plain, (![A_31, B_35, C_37]: (k3_lattices(A_31, k7_lattices(A_31, B_35), k7_lattices(A_31, C_37))=k7_lattices(A_31, k4_lattices(A_31, B_35, C_37)) | ~m1_subset_1(C_37, u1_struct_0(A_31)) | ~m1_subset_1(B_35, u1_struct_0(A_31)) | ~l3_lattices(A_31) | ~v17_lattices(A_31) | ~v10_lattices(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.22/1.96  tff(c_2510, plain, (![B_212]: (k1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', B_212))=k7_lattices('#skF_1', k4_lattices('#skF_1', '#skF_3', B_212)) | ~m1_subset_1(B_212, u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~m1_subset_1(B_212, u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2492, c_40])).
% 5.22/1.96  tff(c_2547, plain, (![B_212]: (k1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', B_212))=k7_lattices('#skF_1', k4_lattices('#skF_1', '#skF_3', B_212)) | v2_struct_0('#skF_1') | ~m1_subset_1(B_212, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_46, c_2510])).
% 5.22/1.96  tff(c_2583, plain, (![B_214]: (k1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', B_214))=k7_lattices('#skF_1', k4_lattices('#skF_1', '#skF_3', B_214)) | ~m1_subset_1(B_214, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_2547])).
% 5.22/1.96  tff(c_81, plain, (![A_12, B_53, B_13]: (r1_lattices(A_12, B_53, k7_lattices(A_12, B_13)) | k1_lattices(A_12, B_53, k7_lattices(A_12, B_13))!=k7_lattices(A_12, B_13) | ~m1_subset_1(B_53, u1_struct_0(A_12)) | ~l2_lattices(A_12) | ~m1_subset_1(B_13, u1_struct_0(A_12)) | ~l3_lattices(A_12) | v2_struct_0(A_12))), inference(resolution, [status(thm)], [c_22, c_74])).
% 5.22/1.96  tff(c_1705, plain, (~r1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_1695])).
% 5.22/1.96  tff(c_1894, plain, (k1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2'))!=k7_lattices('#skF_1', '#skF_2') | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_81, c_1705])).
% 5.22/1.96  tff(c_1901, plain, (k1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2'))!=k7_lattices('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_66, c_1706, c_1894])).
% 5.22/1.96  tff(c_1902, plain, (k1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2'))!=k7_lattices('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_1901])).
% 5.22/1.96  tff(c_2592, plain, (k7_lattices('#skF_1', k4_lattices('#skF_1', '#skF_3', '#skF_2'))!=k7_lattices('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2583, c_1902])).
% 5.22/1.96  tff(c_2603, plain, (k7_lattices('#skF_1', k2_lattices('#skF_1', '#skF_3', '#skF_2'))!=k7_lattices('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_805, c_2592])).
% 5.22/1.96  tff(c_1080, plain, (k2_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_1052])).
% 5.22/1.96  tff(c_815, plain, (![B_114]: (k4_lattices('#skF_1', B_114, '#skF_3')=k2_lattices('#skF_1', B_114, '#skF_3') | ~m1_subset_1(B_114, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_772])).
% 5.22/1.96  tff(c_831, plain, (k4_lattices('#skF_1', '#skF_2', '#skF_3')=k2_lattices('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_815])).
% 5.22/1.96  tff(c_1082, plain, (k4_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1080, c_831])).
% 5.22/1.96  tff(c_697, plain, (![A_12, B_13, B_107]: (k3_lattices(A_12, k7_lattices(A_12, B_13), B_107)=k3_lattices(A_12, B_107, k7_lattices(A_12, B_13)) | ~m1_subset_1(B_107, u1_struct_0(A_12)) | ~l2_lattices(A_12) | ~v4_lattices(A_12) | ~m1_subset_1(B_13, u1_struct_0(A_12)) | ~l3_lattices(A_12) | v2_struct_0(A_12))), inference(resolution, [status(thm)], [c_22, c_690])).
% 5.22/1.96  tff(c_1730, plain, (![B_13]: (k3_lattices('#skF_1', k7_lattices('#skF_1', B_13), k7_lattices('#skF_1', '#skF_3'))=k3_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', B_13)) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | ~m1_subset_1(B_13, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1706, c_697])).
% 5.22/1.96  tff(c_1813, plain, (![B_13]: (k3_lattices('#skF_1', k7_lattices('#skF_1', B_13), k7_lattices('#skF_1', '#skF_3'))=k3_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', B_13)) | ~m1_subset_1(B_13, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_717, c_66, c_1730])).
% 5.22/1.96  tff(c_2607, plain, (![B_215]: (k3_lattices('#skF_1', k7_lattices('#skF_1', B_215), k7_lattices('#skF_1', '#skF_3'))=k3_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', B_215)) | ~m1_subset_1(B_215, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_1813])).
% 5.22/1.96  tff(c_2637, plain, (![B_215]: (k3_lattices('#skF_1', k7_lattices('#skF_1', B_215), k7_lattices('#skF_1', '#skF_3'))=k7_lattices('#skF_1', k4_lattices('#skF_1', '#skF_3', B_215)) | ~m1_subset_1(B_215, u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~m1_subset_1(B_215, u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2607, c_40])).
% 5.22/1.96  tff(c_2707, plain, (![B_215]: (k3_lattices('#skF_1', k7_lattices('#skF_1', B_215), k7_lattices('#skF_1', '#skF_3'))=k7_lattices('#skF_1', k4_lattices('#skF_1', '#skF_3', B_215)) | v2_struct_0('#skF_1') | ~m1_subset_1(B_215, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_46, c_2637])).
% 5.22/1.96  tff(c_2742, plain, (![B_216]: (k3_lattices('#skF_1', k7_lattices('#skF_1', B_216), k7_lattices('#skF_1', '#skF_3'))=k7_lattices('#skF_1', k4_lattices('#skF_1', '#skF_3', B_216)) | ~m1_subset_1(B_216, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_2707])).
% 5.22/1.96  tff(c_2767, plain, (![B_216]: (k7_lattices('#skF_1', k4_lattices('#skF_1', B_216, '#skF_3'))=k7_lattices('#skF_1', k4_lattices('#skF_1', '#skF_3', B_216)) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1(B_216, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~m1_subset_1(B_216, u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2742, c_40])).
% 5.22/1.96  tff(c_2812, plain, (![B_216]: (k7_lattices('#skF_1', k4_lattices('#skF_1', B_216, '#skF_3'))=k7_lattices('#skF_1', k4_lattices('#skF_1', '#skF_3', B_216)) | v2_struct_0('#skF_1') | ~m1_subset_1(B_216, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_46, c_2767])).
% 5.22/1.96  tff(c_2831, plain, (![B_217]: (k7_lattices('#skF_1', k4_lattices('#skF_1', B_217, '#skF_3'))=k7_lattices('#skF_1', k4_lattices('#skF_1', '#skF_3', B_217)) | ~m1_subset_1(B_217, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_2812])).
% 5.22/1.96  tff(c_2844, plain, (k7_lattices('#skF_1', k4_lattices('#skF_1', '#skF_2', '#skF_3'))=k7_lattices('#skF_1', k4_lattices('#skF_1', '#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_2831])).
% 5.22/1.96  tff(c_2854, plain, (k7_lattices('#skF_1', k2_lattices('#skF_1', '#skF_3', '#skF_2'))=k7_lattices('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_805, c_1082, c_2844])).
% 5.22/1.96  tff(c_2856, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2603, c_2854])).
% 5.22/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.22/1.96  
% 5.22/1.96  Inference rules
% 5.22/1.96  ----------------------
% 5.22/1.96  #Ref     : 0
% 5.22/1.96  #Sup     : 587
% 5.22/1.96  #Fact    : 0
% 5.22/1.96  #Define  : 0
% 5.22/1.96  #Split   : 30
% 5.22/1.96  #Chain   : 0
% 5.22/1.96  #Close   : 0
% 5.22/1.96  
% 5.22/1.96  Ordering : KBO
% 5.22/1.96  
% 5.22/1.96  Simplification rules
% 5.22/1.96  ----------------------
% 5.22/1.96  #Subsume      : 14
% 5.22/1.96  #Demod        : 612
% 5.22/1.96  #Tautology    : 314
% 5.22/1.96  #SimpNegUnit  : 174
% 5.22/1.96  #BackRed      : 18
% 5.22/1.96  
% 5.22/1.96  #Partial instantiations: 0
% 5.22/1.96  #Strategies tried      : 1
% 5.22/1.96  
% 5.22/1.96  Timing (in seconds)
% 5.22/1.96  ----------------------
% 5.22/1.97  Preprocessing        : 0.34
% 5.22/1.97  Parsing              : 0.18
% 5.22/1.97  CNF conversion       : 0.02
% 5.22/1.97  Main loop            : 0.84
% 5.22/1.97  Inferencing          : 0.31
% 5.22/1.97  Reduction            : 0.28
% 5.22/1.97  Demodulation         : 0.18
% 5.22/1.97  BG Simplification    : 0.04
% 5.22/1.97  Subsumption          : 0.16
% 5.22/1.97  Abstraction          : 0.05
% 5.22/1.97  MUC search           : 0.00
% 5.22/1.97  Cooper               : 0.00
% 5.22/1.97  Total                : 1.25
% 5.22/1.97  Index Insertion      : 0.00
% 5.22/1.97  Index Deletion       : 0.00
% 5.22/1.97  Index Matching       : 0.00
% 5.22/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
