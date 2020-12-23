%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:19 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 538 expanded)
%              Number of leaves         :   30 ( 211 expanded)
%              Depth                    :   20
%              Number of atoms          :  204 (2083 expanded)
%              Number of equality atoms :   23 ( 283 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k7_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1

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

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

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

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v17_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k7_lattices(A,k3_lattices(A,B,C)) = k4_lattices(A,k7_lattices(A,B),k7_lattices(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_lattices)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k7_lattices(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v17_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k7_lattices(A,k7_lattices(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_lattices)).

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

tff(f_75,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_106,axiom,(
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

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k4_lattices(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_34,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_18,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k7_lattices(A_5,B_6),u1_struct_0(A_5))
      | ~ m1_subset_1(B_6,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_36,plain,(
    v17_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_58,plain,(
    ! [A_32,B_33] :
      ( k7_lattices(A_32,k7_lattices(A_32,B_33)) = B_33
      | ~ m1_subset_1(B_33,u1_struct_0(A_32))
      | ~ l3_lattices(A_32)
      | ~ v17_lattices(A_32)
      | ~ v10_lattices(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_62,plain,
    ( k7_lattices('#skF_1',k7_lattices('#skF_1','#skF_3')) = '#skF_3'
    | ~ l3_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_58])).

tff(c_68,plain,
    ( k7_lattices('#skF_1',k7_lattices('#skF_1','#skF_3')) = '#skF_3'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_62])).

tff(c_69,plain,(
    k7_lattices('#skF_1',k7_lattices('#skF_1','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_68])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_41,plain,(
    ! [A_22] :
      ( l1_lattices(A_22)
      | ~ l3_lattices(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_45,plain,(
    l1_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_41])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_64,plain,
    ( k7_lattices('#skF_1',k7_lattices('#skF_1','#skF_2')) = '#skF_2'
    | ~ l3_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_58])).

tff(c_72,plain,
    ( k7_lattices('#skF_1',k7_lattices('#skF_1','#skF_2')) = '#skF_2'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_64])).

tff(c_73,plain,(
    k7_lattices('#skF_1',k7_lattices('#skF_1','#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_72])).

tff(c_152,plain,(
    ! [A_39,B_40,C_41] :
      ( k3_lattices(A_39,k7_lattices(A_39,B_40),k7_lattices(A_39,C_41)) = k7_lattices(A_39,k4_lattices(A_39,B_40,C_41))
      | ~ m1_subset_1(C_41,u1_struct_0(A_39))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l3_lattices(A_39)
      | ~ v17_lattices(A_39)
      | ~ v10_lattices(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_167,plain,(
    ! [C_41] :
      ( k7_lattices('#skF_1',k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),C_41)) = k3_lattices('#skF_1','#skF_2',k7_lattices('#skF_1',C_41))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(k7_lattices('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v17_lattices('#skF_1')
      | ~ v10_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_152])).

tff(c_180,plain,(
    ! [C_41] :
      ( k7_lattices('#skF_1',k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),C_41)) = k3_lattices('#skF_1','#skF_2',k7_lattices('#skF_1',C_41))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(k7_lattices('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_167])).

tff(c_181,plain,(
    ! [C_41] :
      ( k7_lattices('#skF_1',k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),C_41)) = k3_lattices('#skF_1','#skF_2',k7_lattices('#skF_1',C_41))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(k7_lattices('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_180])).

tff(c_191,plain,(
    ~ m1_subset_1(k7_lattices('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_220,plain,
    ( ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_191])).

tff(c_223,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_220])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_223])).

tff(c_227,plain,(
    m1_subset_1(k7_lattices('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_16,plain,(
    ! [A_2,B_3,C_4] :
      ( m1_subset_1(k4_lattices(A_2,B_3,C_4),u1_struct_0(A_2))
      | ~ m1_subset_1(C_4,u1_struct_0(A_2))
      | ~ m1_subset_1(B_3,u1_struct_0(A_2))
      | ~ l1_lattices(A_2)
      | ~ v6_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_234,plain,(
    ! [C_45] :
      ( k7_lattices('#skF_1',k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),C_45)) = k3_lattices('#skF_1','#skF_2',k7_lattices('#skF_1',C_45))
      | ~ m1_subset_1(C_45,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_249,plain,(
    ! [C_45] :
      ( m1_subset_1(k3_lattices('#skF_1','#skF_2',k7_lattices('#skF_1',C_45)),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),C_45),u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ m1_subset_1(C_45,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_18])).

tff(c_264,plain,(
    ! [C_45] :
      ( m1_subset_1(k3_lattices('#skF_1','#skF_2',k7_lattices('#skF_1',C_45)),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),C_45),u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1')
      | ~ m1_subset_1(C_45,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_249])).

tff(c_267,plain,(
    ! [C_46] :
      ( m1_subset_1(k3_lattices('#skF_1','#skF_2',k7_lattices('#skF_1',C_46)),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),C_46),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(C_46,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_264])).

tff(c_271,plain,(
    ! [C_4] :
      ( m1_subset_1(k3_lattices('#skF_1','#skF_2',k7_lattices('#skF_1',C_4)),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(C_4,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(k7_lattices('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
      | ~ l1_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_267])).

tff(c_274,plain,(
    ! [C_4] :
      ( m1_subset_1(k3_lattices('#skF_1','#skF_2',k7_lattices('#skF_1',C_4)),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(C_4,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_227,c_271])).

tff(c_275,plain,(
    ! [C_4] :
      ( m1_subset_1(k3_lattices('#skF_1','#skF_2',k7_lattices('#skF_1',C_4)),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(C_4,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_274])).

tff(c_276,plain,(
    ~ v6_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_275])).

tff(c_279,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_276])).

tff(c_282,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38,c_279])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_282])).

tff(c_287,plain,(
    ! [C_47] :
      ( m1_subset_1(k3_lattices('#skF_1','#skF_2',k7_lattices('#skF_1',C_47)),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(C_47,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_275])).

tff(c_302,plain,
    ( m1_subset_1(k3_lattices('#skF_1','#skF_2','#skF_3'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_287])).

tff(c_395,plain,(
    ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_302])).

tff(c_398,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_395])).

tff(c_401,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_398])).

tff(c_403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_401])).

tff(c_405,plain,(
    m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_302])).

tff(c_28,plain,(
    k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),k7_lattices('#skF_1','#skF_3')) != k7_lattices('#skF_1',k3_lattices('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_286,plain,(
    v6_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_275])).

tff(c_226,plain,(
    ! [C_41] :
      ( k7_lattices('#skF_1',k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),C_41)) = k3_lattices('#skF_1','#skF_2',k7_lattices('#skF_1',C_41))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_94,plain,(
    ! [A_34,B_35,C_36] :
      ( m1_subset_1(k4_lattices(A_34,B_35,C_36),u1_struct_0(A_34))
      | ~ m1_subset_1(C_36,u1_struct_0(A_34))
      | ~ m1_subset_1(B_35,u1_struct_0(A_34))
      | ~ l1_lattices(A_34)
      | ~ v6_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24,plain,(
    ! [A_8,B_10] :
      ( k7_lattices(A_8,k7_lattices(A_8,B_10)) = B_10
      | ~ m1_subset_1(B_10,u1_struct_0(A_8))
      | ~ l3_lattices(A_8)
      | ~ v17_lattices(A_8)
      | ~ v10_lattices(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_318,plain,(
    ! [A_48,B_49,C_50] :
      ( k7_lattices(A_48,k7_lattices(A_48,k4_lattices(A_48,B_49,C_50))) = k4_lattices(A_48,B_49,C_50)
      | ~ l3_lattices(A_48)
      | ~ v17_lattices(A_48)
      | ~ v10_lattices(A_48)
      | ~ m1_subset_1(C_50,u1_struct_0(A_48))
      | ~ m1_subset_1(B_49,u1_struct_0(A_48))
      | ~ l1_lattices(A_48)
      | ~ v6_lattices(A_48)
      | v2_struct_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_94,c_24])).

tff(c_346,plain,(
    ! [C_41] :
      ( k7_lattices('#skF_1',k3_lattices('#skF_1','#skF_2',k7_lattices('#skF_1',C_41))) = k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),C_41)
      | ~ l3_lattices('#skF_1')
      | ~ v17_lattices('#skF_1')
      | ~ v10_lattices('#skF_1')
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(k7_lattices('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
      | ~ l1_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_318])).

tff(c_355,plain,(
    ! [C_41] :
      ( k7_lattices('#skF_1',k3_lattices('#skF_1','#skF_2',k7_lattices('#skF_1',C_41))) = k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),C_41)
      | v2_struct_0('#skF_1')
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_45,c_227,c_38,c_36,c_34,c_346])).

tff(c_406,plain,(
    ! [C_51] :
      ( k7_lattices('#skF_1',k3_lattices('#skF_1','#skF_2',k7_lattices('#skF_1',C_51))) = k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),C_51)
      | ~ m1_subset_1(C_51,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_355])).

tff(c_453,plain,
    ( k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),k7_lattices('#skF_1','#skF_3')) = k7_lattices('#skF_1',k3_lattices('#skF_1','#skF_2','#skF_3'))
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_406])).

tff(c_476,plain,(
    ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_453])).

tff(c_484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_476])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:46:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.44  
% 2.74/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.44  %$ m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k7_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1
% 2.74/1.44  
% 2.74/1.44  %Foreground sorts:
% 2.74/1.44  
% 2.74/1.44  
% 2.74/1.44  %Background operators:
% 2.74/1.44  
% 2.74/1.44  
% 2.74/1.44  %Foreground operators:
% 2.74/1.44  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.74/1.44  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 2.74/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.74/1.44  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.74/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.44  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 2.74/1.44  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.74/1.44  tff(v17_lattices, type, v17_lattices: $i > $o).
% 2.74/1.44  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.74/1.44  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.74/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.44  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.74/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.74/1.44  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.74/1.44  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.74/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.44  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.74/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.44  tff(k7_lattices, type, k7_lattices: ($i * $i) > $i).
% 2.74/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.74/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.44  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.74/1.44  
% 2.89/1.46  tff(f_124, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k7_lattices(A, k3_lattices(A, B, C)) = k4_lattices(A, k7_lattices(A, B), k7_lattices(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_lattices)).
% 2.89/1.46  tff(f_69, axiom, (![A, B]: (((~v2_struct_0(A) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k7_lattices(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_lattices)).
% 2.89/1.46  tff(f_89, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k7_lattices(A, k7_lattices(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_lattices)).
% 2.89/1.46  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 2.89/1.46  tff(f_75, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.89/1.46  tff(f_106, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k7_lattices(A, k4_lattices(A, B, C)) = k3_lattices(A, k7_lattices(A, B), k7_lattices(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattices)).
% 2.89/1.46  tff(f_60, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k4_lattices(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_lattices)).
% 2.89/1.46  tff(c_40, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.89/1.46  tff(c_34, plain, (l3_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.89/1.46  tff(c_30, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.89/1.46  tff(c_18, plain, (![A_5, B_6]: (m1_subset_1(k7_lattices(A_5, B_6), u1_struct_0(A_5)) | ~m1_subset_1(B_6, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.89/1.46  tff(c_38, plain, (v10_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.89/1.46  tff(c_36, plain, (v17_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.89/1.46  tff(c_58, plain, (![A_32, B_33]: (k7_lattices(A_32, k7_lattices(A_32, B_33))=B_33 | ~m1_subset_1(B_33, u1_struct_0(A_32)) | ~l3_lattices(A_32) | ~v17_lattices(A_32) | ~v10_lattices(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.89/1.46  tff(c_62, plain, (k7_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'))='#skF_3' | ~l3_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_58])).
% 2.89/1.46  tff(c_68, plain, (k7_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'))='#skF_3' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_62])).
% 2.89/1.46  tff(c_69, plain, (k7_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_40, c_68])).
% 2.89/1.46  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.89/1.46  tff(c_41, plain, (![A_22]: (l1_lattices(A_22) | ~l3_lattices(A_22))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.89/1.46  tff(c_45, plain, (l1_lattices('#skF_1')), inference(resolution, [status(thm)], [c_34, c_41])).
% 2.89/1.46  tff(c_32, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.89/1.46  tff(c_64, plain, (k7_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'))='#skF_2' | ~l3_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_58])).
% 2.89/1.46  tff(c_72, plain, (k7_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'))='#skF_2' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_64])).
% 2.89/1.46  tff(c_73, plain, (k7_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_40, c_72])).
% 2.89/1.46  tff(c_152, plain, (![A_39, B_40, C_41]: (k3_lattices(A_39, k7_lattices(A_39, B_40), k7_lattices(A_39, C_41))=k7_lattices(A_39, k4_lattices(A_39, B_40, C_41)) | ~m1_subset_1(C_41, u1_struct_0(A_39)) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l3_lattices(A_39) | ~v17_lattices(A_39) | ~v10_lattices(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.89/1.46  tff(c_167, plain, (![C_41]: (k7_lattices('#skF_1', k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), C_41))=k3_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', C_41)) | ~m1_subset_1(C_41, u1_struct_0('#skF_1')) | ~m1_subset_1(k7_lattices('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_152])).
% 2.89/1.46  tff(c_180, plain, (![C_41]: (k7_lattices('#skF_1', k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), C_41))=k3_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', C_41)) | ~m1_subset_1(C_41, u1_struct_0('#skF_1')) | ~m1_subset_1(k7_lattices('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_167])).
% 2.89/1.46  tff(c_181, plain, (![C_41]: (k7_lattices('#skF_1', k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), C_41))=k3_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', C_41)) | ~m1_subset_1(C_41, u1_struct_0('#skF_1')) | ~m1_subset_1(k7_lattices('#skF_1', '#skF_2'), u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_40, c_180])).
% 2.89/1.46  tff(c_191, plain, (~m1_subset_1(k7_lattices('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_181])).
% 2.89/1.46  tff(c_220, plain, (~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_191])).
% 2.89/1.46  tff(c_223, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_220])).
% 2.89/1.46  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_223])).
% 2.89/1.46  tff(c_227, plain, (m1_subset_1(k7_lattices('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_181])).
% 2.89/1.46  tff(c_16, plain, (![A_2, B_3, C_4]: (m1_subset_1(k4_lattices(A_2, B_3, C_4), u1_struct_0(A_2)) | ~m1_subset_1(C_4, u1_struct_0(A_2)) | ~m1_subset_1(B_3, u1_struct_0(A_2)) | ~l1_lattices(A_2) | ~v6_lattices(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.89/1.46  tff(c_234, plain, (![C_45]: (k7_lattices('#skF_1', k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), C_45))=k3_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', C_45)) | ~m1_subset_1(C_45, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_181])).
% 2.89/1.46  tff(c_249, plain, (![C_45]: (m1_subset_1(k3_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', C_45)), u1_struct_0('#skF_1')) | ~m1_subset_1(k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), C_45), u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1') | ~m1_subset_1(C_45, u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_234, c_18])).
% 2.89/1.46  tff(c_264, plain, (![C_45]: (m1_subset_1(k3_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', C_45)), u1_struct_0('#skF_1')) | ~m1_subset_1(k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), C_45), u1_struct_0('#skF_1')) | v2_struct_0('#skF_1') | ~m1_subset_1(C_45, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_249])).
% 2.89/1.46  tff(c_267, plain, (![C_46]: (m1_subset_1(k3_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', C_46)), u1_struct_0('#skF_1')) | ~m1_subset_1(k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), C_46), u1_struct_0('#skF_1')) | ~m1_subset_1(C_46, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_40, c_264])).
% 2.89/1.46  tff(c_271, plain, (![C_4]: (m1_subset_1(k3_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', C_4)), u1_struct_0('#skF_1')) | ~m1_subset_1(C_4, u1_struct_0('#skF_1')) | ~m1_subset_1(k7_lattices('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~l1_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_267])).
% 2.89/1.46  tff(c_274, plain, (![C_4]: (m1_subset_1(k3_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', C_4)), u1_struct_0('#skF_1')) | ~m1_subset_1(C_4, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_227, c_271])).
% 2.89/1.46  tff(c_275, plain, (![C_4]: (m1_subset_1(k3_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', C_4)), u1_struct_0('#skF_1')) | ~m1_subset_1(C_4, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_40, c_274])).
% 2.89/1.46  tff(c_276, plain, (~v6_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_275])).
% 2.89/1.46  tff(c_279, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_8, c_276])).
% 2.89/1.46  tff(c_282, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38, c_279])).
% 2.89/1.46  tff(c_284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_282])).
% 2.89/1.46  tff(c_287, plain, (![C_47]: (m1_subset_1(k3_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', C_47)), u1_struct_0('#skF_1')) | ~m1_subset_1(C_47, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_275])).
% 2.89/1.46  tff(c_302, plain, (m1_subset_1(k3_lattices('#skF_1', '#skF_2', '#skF_3'), u1_struct_0('#skF_1')) | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_287])).
% 2.89/1.46  tff(c_395, plain, (~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_302])).
% 2.89/1.46  tff(c_398, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_395])).
% 2.89/1.46  tff(c_401, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_398])).
% 2.89/1.46  tff(c_403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_401])).
% 2.89/1.46  tff(c_405, plain, (m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_302])).
% 2.89/1.46  tff(c_28, plain, (k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), k7_lattices('#skF_1', '#skF_3'))!=k7_lattices('#skF_1', k3_lattices('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.89/1.46  tff(c_286, plain, (v6_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_275])).
% 2.89/1.46  tff(c_226, plain, (![C_41]: (k7_lattices('#skF_1', k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), C_41))=k3_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', C_41)) | ~m1_subset_1(C_41, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_181])).
% 2.89/1.46  tff(c_94, plain, (![A_34, B_35, C_36]: (m1_subset_1(k4_lattices(A_34, B_35, C_36), u1_struct_0(A_34)) | ~m1_subset_1(C_36, u1_struct_0(A_34)) | ~m1_subset_1(B_35, u1_struct_0(A_34)) | ~l1_lattices(A_34) | ~v6_lattices(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.89/1.46  tff(c_24, plain, (![A_8, B_10]: (k7_lattices(A_8, k7_lattices(A_8, B_10))=B_10 | ~m1_subset_1(B_10, u1_struct_0(A_8)) | ~l3_lattices(A_8) | ~v17_lattices(A_8) | ~v10_lattices(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.89/1.46  tff(c_318, plain, (![A_48, B_49, C_50]: (k7_lattices(A_48, k7_lattices(A_48, k4_lattices(A_48, B_49, C_50)))=k4_lattices(A_48, B_49, C_50) | ~l3_lattices(A_48) | ~v17_lattices(A_48) | ~v10_lattices(A_48) | ~m1_subset_1(C_50, u1_struct_0(A_48)) | ~m1_subset_1(B_49, u1_struct_0(A_48)) | ~l1_lattices(A_48) | ~v6_lattices(A_48) | v2_struct_0(A_48))), inference(resolution, [status(thm)], [c_94, c_24])).
% 2.89/1.46  tff(c_346, plain, (![C_41]: (k7_lattices('#skF_1', k3_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', C_41)))=k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), C_41) | ~l3_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~v10_lattices('#skF_1') | ~m1_subset_1(C_41, u1_struct_0('#skF_1')) | ~m1_subset_1(k7_lattices('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~l1_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1') | ~m1_subset_1(C_41, u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_226, c_318])).
% 2.89/1.46  tff(c_355, plain, (![C_41]: (k7_lattices('#skF_1', k3_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', C_41)))=k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), C_41) | v2_struct_0('#skF_1') | ~m1_subset_1(C_41, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_286, c_45, c_227, c_38, c_36, c_34, c_346])).
% 2.89/1.46  tff(c_406, plain, (![C_51]: (k7_lattices('#skF_1', k3_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', C_51)))=k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), C_51) | ~m1_subset_1(C_51, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_40, c_355])).
% 2.89/1.46  tff(c_453, plain, (k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), k7_lattices('#skF_1', '#skF_3'))=k7_lattices('#skF_1', k3_lattices('#skF_1', '#skF_2', '#skF_3')) | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_406])).
% 2.89/1.46  tff(c_476, plain, (~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_28, c_453])).
% 2.89/1.46  tff(c_484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_405, c_476])).
% 2.89/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.46  
% 2.89/1.46  Inference rules
% 2.89/1.46  ----------------------
% 2.89/1.46  #Ref     : 0
% 2.89/1.46  #Sup     : 88
% 2.89/1.46  #Fact    : 0
% 2.89/1.46  #Define  : 0
% 2.89/1.46  #Split   : 3
% 2.89/1.46  #Chain   : 0
% 2.89/1.46  #Close   : 0
% 2.89/1.46  
% 2.89/1.46  Ordering : KBO
% 2.89/1.46  
% 2.89/1.46  Simplification rules
% 2.89/1.46  ----------------------
% 2.89/1.46  #Subsume      : 5
% 2.89/1.46  #Demod        : 124
% 2.89/1.46  #Tautology    : 38
% 2.89/1.46  #SimpNegUnit  : 39
% 2.89/1.46  #BackRed      : 0
% 2.89/1.46  
% 2.89/1.46  #Partial instantiations: 0
% 2.89/1.46  #Strategies tried      : 1
% 2.89/1.46  
% 2.89/1.46  Timing (in seconds)
% 2.89/1.46  ----------------------
% 2.89/1.46  Preprocessing        : 0.31
% 2.89/1.46  Parsing              : 0.18
% 2.89/1.46  CNF conversion       : 0.02
% 2.89/1.46  Main loop            : 0.31
% 2.89/1.46  Inferencing          : 0.12
% 2.89/1.46  Reduction            : 0.09
% 2.89/1.46  Demodulation         : 0.07
% 2.89/1.46  BG Simplification    : 0.02
% 2.89/1.46  Subsumption          : 0.06
% 2.89/1.46  Abstraction          : 0.02
% 2.89/1.46  MUC search           : 0.00
% 2.89/1.46  Cooper               : 0.00
% 2.89/1.46  Total                : 0.66
% 2.89/1.46  Index Insertion      : 0.00
% 2.89/1.46  Index Deletion       : 0.00
% 2.89/1.46  Index Matching       : 0.00
% 2.89/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
