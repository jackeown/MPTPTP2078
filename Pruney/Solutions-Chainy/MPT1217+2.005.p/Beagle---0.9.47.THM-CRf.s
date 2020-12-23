%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:20 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 277 expanded)
%              Number of leaves         :   31 ( 113 expanded)
%              Depth                    :   17
%              Number of atoms          :  187 (1038 expanded)
%              Number of equality atoms :   31 (  79 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k7_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_3 > #skF_1

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

tff(k5_lattices,type,(
    k5_lattices: $i > $i )).

tff(k7_lattices,type,(
    k7_lattices: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_128,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_lattices)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k7_lattices(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

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

tff(f_75,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k4_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v17_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( k4_lattices(A,B,C) = k5_lattices(A)
              <=> r3_lattices(A,B,k7_lattices(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_lattices)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v17_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k7_lattices(A,k7_lattices(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_lattices)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_38,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_18,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k7_lattices(A_5,B_6),u1_struct_0(A_5))
      | ~ m1_subset_1(B_6,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_42,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_40,plain,(
    v17_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_50,plain,(
    ! [A_23] :
      ( l1_lattices(A_23)
      | ~ l3_lattices(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_54,plain,(
    l1_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_50])).

tff(c_98,plain,(
    ! [A_34,C_35,B_36] :
      ( k4_lattices(A_34,C_35,B_36) = k4_lattices(A_34,B_36,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_34))
      | ~ m1_subset_1(B_36,u1_struct_0(A_34))
      | ~ l1_lattices(A_34)
      | ~ v6_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_102,plain,(
    ! [B_36] :
      ( k4_lattices('#skF_1',B_36,'#skF_3') = k4_lattices('#skF_1','#skF_3',B_36)
      | ~ m1_subset_1(B_36,u1_struct_0('#skF_1'))
      | ~ l1_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_98])).

tff(c_108,plain,(
    ! [B_36] :
      ( k4_lattices('#skF_1',B_36,'#skF_3') = k4_lattices('#skF_1','#skF_3',B_36)
      | ~ m1_subset_1(B_36,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_102])).

tff(c_109,plain,(
    ! [B_36] :
      ( k4_lattices('#skF_1',B_36,'#skF_3') = k4_lattices('#skF_1','#skF_3',B_36)
      | ~ m1_subset_1(B_36,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_108])).

tff(c_114,plain,(
    ~ v6_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_117,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_114])).

tff(c_120,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_117])).

tff(c_122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_120])).

tff(c_124,plain,(
    v6_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_104,plain,(
    ! [B_36] :
      ( k4_lattices('#skF_1',B_36,'#skF_2') = k4_lattices('#skF_1','#skF_2',B_36)
      | ~ m1_subset_1(B_36,u1_struct_0('#skF_1'))
      | ~ l1_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_98])).

tff(c_112,plain,(
    ! [B_36] :
      ( k4_lattices('#skF_1',B_36,'#skF_2') = k4_lattices('#skF_1','#skF_2',B_36)
      | ~ m1_subset_1(B_36,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_104])).

tff(c_113,plain,(
    ! [B_36] :
      ( k4_lattices('#skF_1',B_36,'#skF_2') = k4_lattices('#skF_1','#skF_2',B_36)
      | ~ m1_subset_1(B_36,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_112])).

tff(c_162,plain,(
    ! [B_41] :
      ( k4_lattices('#skF_1',B_41,'#skF_2') = k4_lattices('#skF_1','#skF_2',B_41)
      | ~ m1_subset_1(B_41,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_113])).

tff(c_166,plain,(
    ! [B_6] :
      ( k4_lattices('#skF_1',k7_lattices('#skF_1',B_6),'#skF_2') = k4_lattices('#skF_1','#skF_2',k7_lattices('#skF_1',B_6))
      | ~ m1_subset_1(B_6,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_162])).

tff(c_175,plain,(
    ! [B_6] :
      ( k4_lattices('#skF_1',k7_lattices('#skF_1',B_6),'#skF_2') = k4_lattices('#skF_1','#skF_2',k7_lattices('#skF_1',B_6))
      | ~ m1_subset_1(B_6,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_166])).

tff(c_206,plain,(
    ! [B_43] :
      ( k4_lattices('#skF_1',k7_lattices('#skF_1',B_43),'#skF_2') = k4_lattices('#skF_1','#skF_2',k7_lattices('#skF_1',B_43))
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_175])).

tff(c_221,plain,(
    k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),'#skF_2') = k4_lattices('#skF_1','#skF_2',k7_lattices('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_206])).

tff(c_227,plain,(
    ! [A_44,B_45,C_46] :
      ( r3_lattices(A_44,B_45,k7_lattices(A_44,C_46))
      | k4_lattices(A_44,B_45,C_46) != k5_lattices(A_44)
      | ~ m1_subset_1(C_46,u1_struct_0(A_44))
      | ~ m1_subset_1(B_45,u1_struct_0(A_44))
      | ~ l3_lattices(A_44)
      | ~ v17_lattices(A_44)
      | ~ v10_lattices(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_30,plain,(
    ~ r3_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_233,plain,
    ( k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),'#skF_2') != k5_lattices('#skF_1')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_227,c_30])).

tff(c_243,plain,
    ( k4_lattices('#skF_1','#skF_2',k7_lattices('#skF_1','#skF_3')) != k5_lattices('#skF_1')
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_221,c_233])).

tff(c_244,plain,
    ( k4_lattices('#skF_1','#skF_2',k7_lattices('#skF_1','#skF_3')) != k5_lattices('#skF_1')
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_243])).

tff(c_255,plain,(
    ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_258,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_255])).

tff(c_261,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_258])).

tff(c_263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_261])).

tff(c_264,plain,(
    k4_lattices('#skF_1','#skF_2',k7_lattices('#skF_1','#skF_3')) != k5_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_32,plain,(
    r3_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_265,plain,(
    m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_62,plain,(
    ! [A_32,B_33] :
      ( k7_lattices(A_32,k7_lattices(A_32,B_33)) = B_33
      | ~ m1_subset_1(B_33,u1_struct_0(A_32))
      | ~ l3_lattices(A_32)
      | ~ v17_lattices(A_32)
      | ~ v10_lattices(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_66,plain,
    ( k7_lattices('#skF_1',k7_lattices('#skF_1','#skF_3')) = '#skF_3'
    | ~ l3_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_62])).

tff(c_72,plain,
    ( k7_lattices('#skF_1',k7_lattices('#skF_1','#skF_3')) = '#skF_3'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_66])).

tff(c_73,plain,(
    k7_lattices('#skF_1',k7_lattices('#skF_1','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_72])).

tff(c_125,plain,(
    ! [A_37,B_38,C_39] :
      ( k4_lattices(A_37,B_38,C_39) = k5_lattices(A_37)
      | ~ r3_lattices(A_37,B_38,k7_lattices(A_37,C_39))
      | ~ m1_subset_1(C_39,u1_struct_0(A_37))
      | ~ m1_subset_1(B_38,u1_struct_0(A_37))
      | ~ l3_lattices(A_37)
      | ~ v17_lattices(A_37)
      | ~ v10_lattices(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_131,plain,(
    ! [B_38] :
      ( k4_lattices('#skF_1',B_38,k7_lattices('#skF_1','#skF_3')) = k5_lattices('#skF_1')
      | ~ r3_lattices('#skF_1',B_38,'#skF_3')
      | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v17_lattices('#skF_1')
      | ~ v10_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_125])).

tff(c_136,plain,(
    ! [B_38] :
      ( k4_lattices('#skF_1',B_38,k7_lattices('#skF_1','#skF_3')) = k5_lattices('#skF_1')
      | ~ r3_lattices('#skF_1',B_38,'#skF_3')
      | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_131])).

tff(c_137,plain,(
    ! [B_38] :
      ( k4_lattices('#skF_1',B_38,k7_lattices('#skF_1','#skF_3')) = k5_lattices('#skF_1')
      | ~ r3_lattices('#skF_1',B_38,'#skF_3')
      | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_136])).

tff(c_741,plain,(
    ! [B_60] :
      ( k4_lattices('#skF_1',B_60,k7_lattices('#skF_1','#skF_3')) = k5_lattices('#skF_1')
      | ~ r3_lattices('#skF_1',B_60,'#skF_3')
      | ~ m1_subset_1(B_60,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_137])).

tff(c_757,plain,
    ( k4_lattices('#skF_1','#skF_2',k7_lattices('#skF_1','#skF_3')) = k5_lattices('#skF_1')
    | ~ r3_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_741])).

tff(c_768,plain,(
    k4_lattices('#skF_1','#skF_2',k7_lattices('#skF_1','#skF_3')) = k5_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_757])).

tff(c_770,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_264,c_768])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:21:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.41  
% 2.89/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.41  %$ r3_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k7_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_3 > #skF_1
% 2.89/1.41  
% 2.89/1.41  %Foreground sorts:
% 2.89/1.41  
% 2.89/1.41  
% 2.89/1.41  %Background operators:
% 2.89/1.41  
% 2.89/1.41  
% 2.89/1.41  %Foreground operators:
% 2.89/1.41  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.89/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.89/1.41  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.89/1.41  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 2.89/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.41  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 2.89/1.41  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.89/1.41  tff(v17_lattices, type, v17_lattices: $i > $o).
% 2.89/1.41  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.89/1.41  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.89/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.89/1.41  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.89/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.89/1.41  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.89/1.41  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.89/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.41  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.89/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.41  tff(k5_lattices, type, k5_lattices: $i > $i).
% 2.89/1.41  tff(k7_lattices, type, k7_lattices: ($i * $i) > $i).
% 2.89/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.89/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.41  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.89/1.41  
% 2.89/1.43  tff(f_128, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_lattices(A, B, C) => r3_lattices(A, k7_lattices(A, C), k7_lattices(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_lattices)).
% 2.89/1.43  tff(f_69, axiom, (![A, B]: (((~v2_struct_0(A) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k7_lattices(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_lattices)).
% 2.89/1.43  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 2.89/1.43  tff(f_75, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.89/1.43  tff(f_60, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k4_lattices(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 2.89/1.43  tff(f_108, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k4_lattices(A, B, C) = k5_lattices(A)) <=> r3_lattices(A, B, k7_lattices(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_lattices)).
% 2.89/1.43  tff(f_89, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k7_lattices(A, k7_lattices(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_lattices)).
% 2.89/1.43  tff(c_44, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.89/1.43  tff(c_38, plain, (l3_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.89/1.43  tff(c_34, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.89/1.43  tff(c_18, plain, (![A_5, B_6]: (m1_subset_1(k7_lattices(A_5, B_6), u1_struct_0(A_5)) | ~m1_subset_1(B_6, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.89/1.43  tff(c_42, plain, (v10_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.89/1.43  tff(c_40, plain, (v17_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.89/1.43  tff(c_36, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.89/1.43  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.89/1.43  tff(c_50, plain, (![A_23]: (l1_lattices(A_23) | ~l3_lattices(A_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.89/1.43  tff(c_54, plain, (l1_lattices('#skF_1')), inference(resolution, [status(thm)], [c_38, c_50])).
% 2.89/1.43  tff(c_98, plain, (![A_34, C_35, B_36]: (k4_lattices(A_34, C_35, B_36)=k4_lattices(A_34, B_36, C_35) | ~m1_subset_1(C_35, u1_struct_0(A_34)) | ~m1_subset_1(B_36, u1_struct_0(A_34)) | ~l1_lattices(A_34) | ~v6_lattices(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.89/1.43  tff(c_102, plain, (![B_36]: (k4_lattices('#skF_1', B_36, '#skF_3')=k4_lattices('#skF_1', '#skF_3', B_36) | ~m1_subset_1(B_36, u1_struct_0('#skF_1')) | ~l1_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_98])).
% 2.89/1.43  tff(c_108, plain, (![B_36]: (k4_lattices('#skF_1', B_36, '#skF_3')=k4_lattices('#skF_1', '#skF_3', B_36) | ~m1_subset_1(B_36, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_102])).
% 2.89/1.43  tff(c_109, plain, (![B_36]: (k4_lattices('#skF_1', B_36, '#skF_3')=k4_lattices('#skF_1', '#skF_3', B_36) | ~m1_subset_1(B_36, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_108])).
% 2.89/1.43  tff(c_114, plain, (~v6_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_109])).
% 2.89/1.43  tff(c_117, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_8, c_114])).
% 2.89/1.43  tff(c_120, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_117])).
% 2.89/1.43  tff(c_122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_120])).
% 2.89/1.43  tff(c_124, plain, (v6_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_109])).
% 2.89/1.43  tff(c_104, plain, (![B_36]: (k4_lattices('#skF_1', B_36, '#skF_2')=k4_lattices('#skF_1', '#skF_2', B_36) | ~m1_subset_1(B_36, u1_struct_0('#skF_1')) | ~l1_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_98])).
% 2.89/1.43  tff(c_112, plain, (![B_36]: (k4_lattices('#skF_1', B_36, '#skF_2')=k4_lattices('#skF_1', '#skF_2', B_36) | ~m1_subset_1(B_36, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_104])).
% 2.89/1.43  tff(c_113, plain, (![B_36]: (k4_lattices('#skF_1', B_36, '#skF_2')=k4_lattices('#skF_1', '#skF_2', B_36) | ~m1_subset_1(B_36, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_112])).
% 2.89/1.43  tff(c_162, plain, (![B_41]: (k4_lattices('#skF_1', B_41, '#skF_2')=k4_lattices('#skF_1', '#skF_2', B_41) | ~m1_subset_1(B_41, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_113])).
% 2.89/1.43  tff(c_166, plain, (![B_6]: (k4_lattices('#skF_1', k7_lattices('#skF_1', B_6), '#skF_2')=k4_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', B_6)) | ~m1_subset_1(B_6, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_162])).
% 2.89/1.43  tff(c_175, plain, (![B_6]: (k4_lattices('#skF_1', k7_lattices('#skF_1', B_6), '#skF_2')=k4_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', B_6)) | ~m1_subset_1(B_6, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_166])).
% 2.89/1.43  tff(c_206, plain, (![B_43]: (k4_lattices('#skF_1', k7_lattices('#skF_1', B_43), '#skF_2')=k4_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', B_43)) | ~m1_subset_1(B_43, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_44, c_175])).
% 2.89/1.43  tff(c_221, plain, (k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), '#skF_2')=k4_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_206])).
% 2.89/1.43  tff(c_227, plain, (![A_44, B_45, C_46]: (r3_lattices(A_44, B_45, k7_lattices(A_44, C_46)) | k4_lattices(A_44, B_45, C_46)!=k5_lattices(A_44) | ~m1_subset_1(C_46, u1_struct_0(A_44)) | ~m1_subset_1(B_45, u1_struct_0(A_44)) | ~l3_lattices(A_44) | ~v17_lattices(A_44) | ~v10_lattices(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.89/1.43  tff(c_30, plain, (~r3_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.89/1.43  tff(c_233, plain, (k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), '#skF_2')!=k5_lattices('#skF_1') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_227, c_30])).
% 2.89/1.43  tff(c_243, plain, (k4_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', '#skF_3'))!=k5_lattices('#skF_1') | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_221, c_233])).
% 2.89/1.43  tff(c_244, plain, (k4_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', '#skF_3'))!=k5_lattices('#skF_1') | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_243])).
% 2.89/1.43  tff(c_255, plain, (~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_244])).
% 2.89/1.43  tff(c_258, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_255])).
% 2.89/1.43  tff(c_261, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_258])).
% 2.89/1.43  tff(c_263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_261])).
% 2.89/1.43  tff(c_264, plain, (k4_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', '#skF_3'))!=k5_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_244])).
% 2.89/1.43  tff(c_32, plain, (r3_lattices('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.89/1.43  tff(c_265, plain, (m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_244])).
% 2.89/1.43  tff(c_62, plain, (![A_32, B_33]: (k7_lattices(A_32, k7_lattices(A_32, B_33))=B_33 | ~m1_subset_1(B_33, u1_struct_0(A_32)) | ~l3_lattices(A_32) | ~v17_lattices(A_32) | ~v10_lattices(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.89/1.43  tff(c_66, plain, (k7_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'))='#skF_3' | ~l3_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_62])).
% 2.89/1.43  tff(c_72, plain, (k7_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'))='#skF_3' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_66])).
% 2.89/1.43  tff(c_73, plain, (k7_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_44, c_72])).
% 2.89/1.43  tff(c_125, plain, (![A_37, B_38, C_39]: (k4_lattices(A_37, B_38, C_39)=k5_lattices(A_37) | ~r3_lattices(A_37, B_38, k7_lattices(A_37, C_39)) | ~m1_subset_1(C_39, u1_struct_0(A_37)) | ~m1_subset_1(B_38, u1_struct_0(A_37)) | ~l3_lattices(A_37) | ~v17_lattices(A_37) | ~v10_lattices(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.89/1.43  tff(c_131, plain, (![B_38]: (k4_lattices('#skF_1', B_38, k7_lattices('#skF_1', '#skF_3'))=k5_lattices('#skF_1') | ~r3_lattices('#skF_1', B_38, '#skF_3') | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1')) | ~m1_subset_1(B_38, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_125])).
% 2.89/1.43  tff(c_136, plain, (![B_38]: (k4_lattices('#skF_1', B_38, k7_lattices('#skF_1', '#skF_3'))=k5_lattices('#skF_1') | ~r3_lattices('#skF_1', B_38, '#skF_3') | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1')) | ~m1_subset_1(B_38, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_131])).
% 2.89/1.43  tff(c_137, plain, (![B_38]: (k4_lattices('#skF_1', B_38, k7_lattices('#skF_1', '#skF_3'))=k5_lattices('#skF_1') | ~r3_lattices('#skF_1', B_38, '#skF_3') | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1')) | ~m1_subset_1(B_38, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_44, c_136])).
% 2.89/1.43  tff(c_741, plain, (![B_60]: (k4_lattices('#skF_1', B_60, k7_lattices('#skF_1', '#skF_3'))=k5_lattices('#skF_1') | ~r3_lattices('#skF_1', B_60, '#skF_3') | ~m1_subset_1(B_60, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_137])).
% 2.89/1.43  tff(c_757, plain, (k4_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', '#skF_3'))=k5_lattices('#skF_1') | ~r3_lattices('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_741])).
% 2.89/1.43  tff(c_768, plain, (k4_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', '#skF_3'))=k5_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_757])).
% 2.89/1.43  tff(c_770, plain, $false, inference(negUnitSimplification, [status(thm)], [c_264, c_768])).
% 2.89/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.43  
% 2.89/1.43  Inference rules
% 2.89/1.43  ----------------------
% 2.89/1.43  #Ref     : 0
% 2.89/1.43  #Sup     : 140
% 2.89/1.43  #Fact    : 0
% 2.89/1.43  #Define  : 0
% 2.89/1.43  #Split   : 7
% 2.89/1.43  #Chain   : 0
% 2.89/1.43  #Close   : 0
% 2.89/1.43  
% 2.89/1.43  Ordering : KBO
% 2.89/1.43  
% 2.89/1.43  Simplification rules
% 2.89/1.43  ----------------------
% 2.89/1.43  #Subsume      : 7
% 2.89/1.43  #Demod        : 173
% 2.89/1.43  #Tautology    : 82
% 2.89/1.43  #SimpNegUnit  : 42
% 2.89/1.43  #BackRed      : 0
% 2.89/1.43  
% 2.89/1.43  #Partial instantiations: 0
% 2.89/1.43  #Strategies tried      : 1
% 2.89/1.43  
% 2.89/1.43  Timing (in seconds)
% 2.89/1.43  ----------------------
% 2.89/1.43  Preprocessing        : 0.31
% 2.89/1.43  Parsing              : 0.16
% 2.89/1.43  CNF conversion       : 0.02
% 2.89/1.43  Main loop            : 0.34
% 2.89/1.43  Inferencing          : 0.13
% 2.89/1.43  Reduction            : 0.11
% 2.89/1.43  Demodulation         : 0.08
% 2.89/1.43  BG Simplification    : 0.02
% 2.89/1.43  Subsumption          : 0.07
% 2.89/1.43  Abstraction          : 0.02
% 2.89/1.43  MUC search           : 0.00
% 2.89/1.43  Cooper               : 0.00
% 2.89/1.43  Total                : 0.69
% 2.89/1.43  Index Insertion      : 0.00
% 2.89/1.43  Index Deletion       : 0.00
% 2.89/1.43  Index Matching       : 0.00
% 2.89/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
