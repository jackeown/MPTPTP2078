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

% Result     : Theorem 4.59s
% Output     : CNFRefutation 4.78s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 494 expanded)
%              Number of leaves         :   33 ( 197 expanded)
%              Depth                    :   20
%              Number of atoms          :  255 (2030 expanded)
%              Number of equality atoms :   46 ( 150 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k7_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_3 > #skF_1

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

tff(f_145,negated_conjecture,(
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

tff(f_125,axiom,(
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
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k3_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

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
             => k7_lattices(A,k3_lattices(A,B,C)) = k4_lattices(A,k7_lattices(A,B),k7_lattices(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_lattices)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_40,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_18,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k7_lattices(A_5,B_6),u1_struct_0(A_5))
      | ~ m1_subset_1(B_6,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_44,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_42,plain,(
    v17_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_127,plain,(
    ! [A_44,B_45,C_46] :
      ( r3_lattices(A_44,B_45,k7_lattices(A_44,C_46))
      | k4_lattices(A_44,B_45,C_46) != k5_lattices(A_44)
      | ~ m1_subset_1(C_46,u1_struct_0(A_44))
      | ~ m1_subset_1(B_45,u1_struct_0(A_44))
      | ~ l3_lattices(A_44)
      | ~ v17_lattices(A_44)
      | ~ v10_lattices(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_32,plain,(
    ~ r3_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_130,plain,
    ( k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),'#skF_2') != k5_lattices('#skF_1')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_127,c_32])).

tff(c_139,plain,
    ( k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),'#skF_2') != k5_lattices('#skF_1')
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_130])).

tff(c_140,plain,
    ( k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),'#skF_2') != k5_lattices('#skF_1')
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_139])).

tff(c_169,plain,(
    ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_172,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_169])).

tff(c_175,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_172])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_175])).

tff(c_178,plain,(
    k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),'#skF_2') != k5_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_34,plain,(
    r3_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_47,plain,(
    ! [A_29] :
      ( l2_lattices(A_29)
      | ~ l3_lattices(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_51,plain,(
    l2_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_47])).

tff(c_100,plain,(
    ! [A_41,C_42,B_43] :
      ( k3_lattices(A_41,C_42,B_43) = k3_lattices(A_41,B_43,C_42)
      | ~ m1_subset_1(C_42,u1_struct_0(A_41))
      | ~ m1_subset_1(B_43,u1_struct_0(A_41))
      | ~ l2_lattices(A_41)
      | ~ v4_lattices(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_104,plain,(
    ! [B_43] :
      ( k3_lattices('#skF_1',B_43,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_43)
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_100])).

tff(c_110,plain,(
    ! [B_43] :
      ( k3_lattices('#skF_1',B_43,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_43)
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_104])).

tff(c_111,plain,(
    ! [B_43] :
      ( k3_lattices('#skF_1',B_43,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_43)
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_110])).

tff(c_116,plain,(
    ~ v4_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_119,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_116])).

tff(c_122,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_119])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_122])).

tff(c_147,plain,(
    ! [B_47] :
      ( k3_lattices('#skF_1',B_47,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_47)
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_151,plain,(
    ! [B_6] :
      ( k3_lattices('#skF_1',k7_lattices('#skF_1',B_6),'#skF_3') = k3_lattices('#skF_1','#skF_3',k7_lattices('#skF_1',B_6))
      | ~ m1_subset_1(B_6,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_147])).

tff(c_160,plain,(
    ! [B_6] :
      ( k3_lattices('#skF_1',k7_lattices('#skF_1',B_6),'#skF_3') = k3_lattices('#skF_1','#skF_3',k7_lattices('#skF_1',B_6))
      | ~ m1_subset_1(B_6,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_151])).

tff(c_270,plain,(
    ! [B_53] :
      ( k3_lattices('#skF_1',k7_lattices('#skF_1',B_53),'#skF_3') = k3_lattices('#skF_1','#skF_3',k7_lattices('#skF_1',B_53))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_160])).

tff(c_292,plain,(
    k3_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),'#skF_3') = k3_lattices('#skF_1','#skF_3',k7_lattices('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_270])).

tff(c_64,plain,(
    ! [A_39,B_40] :
      ( k7_lattices(A_39,k7_lattices(A_39,B_40)) = B_40
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l3_lattices(A_39)
      | ~ v17_lattices(A_39)
      | ~ v10_lattices(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_70,plain,
    ( k7_lattices('#skF_1',k7_lattices('#skF_1','#skF_2')) = '#skF_2'
    | ~ l3_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_64])).

tff(c_78,plain,
    ( k7_lattices('#skF_1',k7_lattices('#skF_1','#skF_2')) = '#skF_2'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_70])).

tff(c_79,plain,(
    k7_lattices('#skF_1',k7_lattices('#skF_1','#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_78])).

tff(c_179,plain,(
    m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_68,plain,
    ( k7_lattices('#skF_1',k7_lattices('#skF_1','#skF_3')) = '#skF_3'
    | ~ l3_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_64])).

tff(c_74,plain,
    ( k7_lattices('#skF_1',k7_lattices('#skF_1','#skF_3')) = '#skF_3'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_68])).

tff(c_75,plain,(
    k7_lattices('#skF_1',k7_lattices('#skF_1','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_74])).

tff(c_225,plain,(
    ! [A_49,B_50,C_51] :
      ( k4_lattices(A_49,B_50,C_51) = k5_lattices(A_49)
      | ~ r3_lattices(A_49,B_50,k7_lattices(A_49,C_51))
      | ~ m1_subset_1(C_51,u1_struct_0(A_49))
      | ~ m1_subset_1(B_50,u1_struct_0(A_49))
      | ~ l3_lattices(A_49)
      | ~ v17_lattices(A_49)
      | ~ v10_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_234,plain,(
    ! [B_50] :
      ( k4_lattices('#skF_1',B_50,k7_lattices('#skF_1','#skF_3')) = k5_lattices('#skF_1')
      | ~ r3_lattices('#skF_1',B_50,'#skF_3')
      | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v17_lattices('#skF_1')
      | ~ v10_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_225])).

tff(c_240,plain,(
    ! [B_50] :
      ( k4_lattices('#skF_1',B_50,k7_lattices('#skF_1','#skF_3')) = k5_lattices('#skF_1')
      | ~ r3_lattices('#skF_1',B_50,'#skF_3')
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_179,c_234])).

tff(c_324,plain,(
    ! [B_55] :
      ( k4_lattices('#skF_1',B_55,k7_lattices('#skF_1','#skF_3')) = k5_lattices('#skF_1')
      | ~ r3_lattices('#skF_1',B_55,'#skF_3')
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_240])).

tff(c_331,plain,(
    ! [B_6] :
      ( k4_lattices('#skF_1',k7_lattices('#skF_1',B_6),k7_lattices('#skF_1','#skF_3')) = k5_lattices('#skF_1')
      | ~ r3_lattices('#skF_1',k7_lattices('#skF_1',B_6),'#skF_3')
      | ~ m1_subset_1(B_6,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_324])).

tff(c_341,plain,(
    ! [B_6] :
      ( k4_lattices('#skF_1',k7_lattices('#skF_1',B_6),k7_lattices('#skF_1','#skF_3')) = k5_lattices('#skF_1')
      | ~ r3_lattices('#skF_1',k7_lattices('#skF_1',B_6),'#skF_3')
      | ~ m1_subset_1(B_6,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_331])).

tff(c_788,plain,(
    ! [B_65] :
      ( k4_lattices('#skF_1',k7_lattices('#skF_1',B_65),k7_lattices('#skF_1','#skF_3')) = k5_lattices('#skF_1')
      | ~ r3_lattices('#skF_1',k7_lattices('#skF_1',B_65),'#skF_3')
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_341])).

tff(c_26,plain,(
    ! [A_11,B_15,C_17] :
      ( k4_lattices(A_11,k7_lattices(A_11,B_15),k7_lattices(A_11,C_17)) = k7_lattices(A_11,k3_lattices(A_11,B_15,C_17))
      | ~ m1_subset_1(C_17,u1_struct_0(A_11))
      | ~ m1_subset_1(B_15,u1_struct_0(A_11))
      | ~ l3_lattices(A_11)
      | ~ v17_lattices(A_11)
      | ~ v10_lattices(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_794,plain,(
    ! [B_65] :
      ( k7_lattices('#skF_1',k3_lattices('#skF_1',B_65,'#skF_3')) = k5_lattices('#skF_1')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v17_lattices('#skF_1')
      | ~ v10_lattices('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ r3_lattices('#skF_1',k7_lattices('#skF_1',B_65),'#skF_3')
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_788,c_26])).

tff(c_826,plain,(
    ! [B_65] :
      ( k7_lattices('#skF_1',k3_lattices('#skF_1',B_65,'#skF_3')) = k5_lattices('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ r3_lattices('#skF_1',k7_lattices('#skF_1',B_65),'#skF_3')
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_36,c_794])).

tff(c_863,plain,(
    ! [B_69] :
      ( k7_lattices('#skF_1',k3_lattices('#skF_1',B_69,'#skF_3')) = k5_lattices('#skF_1')
      | ~ r3_lattices('#skF_1',k7_lattices('#skF_1',B_69),'#skF_3')
      | ~ m1_subset_1(B_69,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_826])).

tff(c_882,plain,
    ( k7_lattices('#skF_1',k3_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),'#skF_3')) = k5_lattices('#skF_1')
    | ~ r3_lattices('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_863])).

tff(c_890,plain,
    ( k7_lattices('#skF_1',k3_lattices('#skF_1','#skF_3',k7_lattices('#skF_1','#skF_2'))) = k5_lattices('#skF_1')
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_292,c_882])).

tff(c_893,plain,(
    ~ m1_subset_1(k7_lattices('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_890])).

tff(c_896,plain,
    ( ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_893])).

tff(c_899,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_896])).

tff(c_901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_899])).

tff(c_903,plain,(
    m1_subset_1(k7_lattices('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_890])).

tff(c_352,plain,(
    ! [A_56,B_57,C_58] :
      ( k4_lattices(A_56,k7_lattices(A_56,B_57),k7_lattices(A_56,C_58)) = k7_lattices(A_56,k3_lattices(A_56,B_57,C_58))
      | ~ m1_subset_1(C_58,u1_struct_0(A_56))
      | ~ m1_subset_1(B_57,u1_struct_0(A_56))
      | ~ l3_lattices(A_56)
      | ~ v17_lattices(A_56)
      | ~ v10_lattices(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_364,plain,(
    ! [B_57] :
      ( k7_lattices('#skF_1',k3_lattices('#skF_1',B_57,k7_lattices('#skF_1','#skF_2'))) = k4_lattices('#skF_1',k7_lattices('#skF_1',B_57),'#skF_2')
      | ~ m1_subset_1(k7_lattices('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_57,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v17_lattices('#skF_1')
      | ~ v10_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_352])).

tff(c_377,plain,(
    ! [B_57] :
      ( k7_lattices('#skF_1',k3_lattices('#skF_1',B_57,k7_lattices('#skF_1','#skF_2'))) = k4_lattices('#skF_1',k7_lattices('#skF_1',B_57),'#skF_2')
      | ~ m1_subset_1(k7_lattices('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_57,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_364])).

tff(c_378,plain,(
    ! [B_57] :
      ( k7_lattices('#skF_1',k3_lattices('#skF_1',B_57,k7_lattices('#skF_1','#skF_2'))) = k4_lattices('#skF_1',k7_lattices('#skF_1',B_57),'#skF_2')
      | ~ m1_subset_1(k7_lattices('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_57,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_377])).

tff(c_2117,plain,(
    ! [B_84] :
      ( k7_lattices('#skF_1',k3_lattices('#skF_1',B_84,k7_lattices('#skF_1','#skF_2'))) = k4_lattices('#skF_1',k7_lattices('#skF_1',B_84),'#skF_2')
      | ~ m1_subset_1(B_84,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_903,c_378])).

tff(c_902,plain,(
    k7_lattices('#skF_1',k3_lattices('#skF_1','#skF_3',k7_lattices('#skF_1','#skF_2'))) = k5_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_890])).

tff(c_2160,plain,
    ( k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),'#skF_2') = k5_lattices('#skF_1')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2117,c_902])).

tff(c_2226,plain,(
    k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),'#skF_2') = k5_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2160])).

tff(c_2228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_2226])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:44:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.59/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.80  
% 4.66/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.80  %$ r3_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k7_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_3 > #skF_1
% 4.66/1.80  
% 4.66/1.80  %Foreground sorts:
% 4.66/1.80  
% 4.66/1.80  
% 4.66/1.80  %Background operators:
% 4.66/1.80  
% 4.66/1.80  
% 4.66/1.80  %Foreground operators:
% 4.66/1.80  tff(l3_lattices, type, l3_lattices: $i > $o).
% 4.66/1.80  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 4.66/1.80  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.66/1.80  tff(l2_lattices, type, l2_lattices: $i > $o).
% 4.66/1.80  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 4.66/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.66/1.80  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 4.66/1.80  tff(l1_lattices, type, l1_lattices: $i > $o).
% 4.66/1.80  tff(v17_lattices, type, v17_lattices: $i > $o).
% 4.66/1.80  tff(v4_lattices, type, v4_lattices: $i > $o).
% 4.66/1.80  tff(v6_lattices, type, v6_lattices: $i > $o).
% 4.66/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.66/1.80  tff(v9_lattices, type, v9_lattices: $i > $o).
% 4.66/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.66/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.66/1.80  tff(v5_lattices, type, v5_lattices: $i > $o).
% 4.66/1.80  tff(v10_lattices, type, v10_lattices: $i > $o).
% 4.66/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.66/1.80  tff(v8_lattices, type, v8_lattices: $i > $o).
% 4.66/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.66/1.80  tff(k5_lattices, type, k5_lattices: $i > $i).
% 4.66/1.80  tff(k7_lattices, type, k7_lattices: ($i * $i) > $i).
% 4.66/1.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.66/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.66/1.80  tff(v7_lattices, type, v7_lattices: $i > $o).
% 4.66/1.80  
% 4.78/1.82  tff(f_145, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_lattices(A, B, C) => r3_lattices(A, k7_lattices(A, C), k7_lattices(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_lattices)).
% 4.78/1.82  tff(f_69, axiom, (![A, B]: (((~v2_struct_0(A) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k7_lattices(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_lattices)).
% 4.78/1.82  tff(f_125, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k4_lattices(A, B, C) = k5_lattices(A)) <=> r3_lattices(A, B, k7_lattices(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_lattices)).
% 4.78/1.82  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 4.78/1.82  tff(f_75, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 4.78/1.82  tff(f_60, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k3_lattices(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 4.78/1.82  tff(f_89, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k7_lattices(A, k7_lattices(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_lattices)).
% 4.78/1.82  tff(f_106, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k7_lattices(A, k3_lattices(A, B, C)) = k4_lattices(A, k7_lattices(A, B), k7_lattices(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_lattices)).
% 4.78/1.82  tff(c_46, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.78/1.82  tff(c_40, plain, (l3_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.78/1.82  tff(c_36, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.78/1.82  tff(c_18, plain, (![A_5, B_6]: (m1_subset_1(k7_lattices(A_5, B_6), u1_struct_0(A_5)) | ~m1_subset_1(B_6, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.78/1.82  tff(c_44, plain, (v10_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.78/1.82  tff(c_42, plain, (v17_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.78/1.82  tff(c_38, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.78/1.82  tff(c_127, plain, (![A_44, B_45, C_46]: (r3_lattices(A_44, B_45, k7_lattices(A_44, C_46)) | k4_lattices(A_44, B_45, C_46)!=k5_lattices(A_44) | ~m1_subset_1(C_46, u1_struct_0(A_44)) | ~m1_subset_1(B_45, u1_struct_0(A_44)) | ~l3_lattices(A_44) | ~v17_lattices(A_44) | ~v10_lattices(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.78/1.82  tff(c_32, plain, (~r3_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.78/1.82  tff(c_130, plain, (k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), '#skF_2')!=k5_lattices('#skF_1') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_127, c_32])).
% 4.78/1.82  tff(c_139, plain, (k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), '#skF_2')!=k5_lattices('#skF_1') | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_130])).
% 4.78/1.82  tff(c_140, plain, (k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), '#skF_2')!=k5_lattices('#skF_1') | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_46, c_139])).
% 4.78/1.82  tff(c_169, plain, (~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_140])).
% 4.78/1.82  tff(c_172, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_169])).
% 4.78/1.82  tff(c_175, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_172])).
% 4.78/1.82  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_175])).
% 4.78/1.82  tff(c_178, plain, (k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), '#skF_2')!=k5_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_140])).
% 4.78/1.82  tff(c_34, plain, (r3_lattices('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.78/1.82  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.78/1.82  tff(c_47, plain, (![A_29]: (l2_lattices(A_29) | ~l3_lattices(A_29))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.78/1.82  tff(c_51, plain, (l2_lattices('#skF_1')), inference(resolution, [status(thm)], [c_40, c_47])).
% 4.78/1.82  tff(c_100, plain, (![A_41, C_42, B_43]: (k3_lattices(A_41, C_42, B_43)=k3_lattices(A_41, B_43, C_42) | ~m1_subset_1(C_42, u1_struct_0(A_41)) | ~m1_subset_1(B_43, u1_struct_0(A_41)) | ~l2_lattices(A_41) | ~v4_lattices(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.78/1.82  tff(c_104, plain, (![B_43]: (k3_lattices('#skF_1', B_43, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_43) | ~m1_subset_1(B_43, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_100])).
% 4.78/1.82  tff(c_110, plain, (![B_43]: (k3_lattices('#skF_1', B_43, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_43) | ~m1_subset_1(B_43, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_104])).
% 4.78/1.82  tff(c_111, plain, (![B_43]: (k3_lattices('#skF_1', B_43, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_43) | ~m1_subset_1(B_43, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_46, c_110])).
% 4.78/1.82  tff(c_116, plain, (~v4_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_111])).
% 4.78/1.82  tff(c_119, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_12, c_116])).
% 4.78/1.82  tff(c_122, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_119])).
% 4.78/1.82  tff(c_124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_122])).
% 4.78/1.82  tff(c_147, plain, (![B_47]: (k3_lattices('#skF_1', B_47, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_47) | ~m1_subset_1(B_47, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_111])).
% 4.78/1.82  tff(c_151, plain, (![B_6]: (k3_lattices('#skF_1', k7_lattices('#skF_1', B_6), '#skF_3')=k3_lattices('#skF_1', '#skF_3', k7_lattices('#skF_1', B_6)) | ~m1_subset_1(B_6, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_147])).
% 4.78/1.82  tff(c_160, plain, (![B_6]: (k3_lattices('#skF_1', k7_lattices('#skF_1', B_6), '#skF_3')=k3_lattices('#skF_1', '#skF_3', k7_lattices('#skF_1', B_6)) | ~m1_subset_1(B_6, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_151])).
% 4.78/1.82  tff(c_270, plain, (![B_53]: (k3_lattices('#skF_1', k7_lattices('#skF_1', B_53), '#skF_3')=k3_lattices('#skF_1', '#skF_3', k7_lattices('#skF_1', B_53)) | ~m1_subset_1(B_53, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_46, c_160])).
% 4.78/1.82  tff(c_292, plain, (k3_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), '#skF_3')=k3_lattices('#skF_1', '#skF_3', k7_lattices('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_270])).
% 4.78/1.82  tff(c_64, plain, (![A_39, B_40]: (k7_lattices(A_39, k7_lattices(A_39, B_40))=B_40 | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l3_lattices(A_39) | ~v17_lattices(A_39) | ~v10_lattices(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.78/1.82  tff(c_70, plain, (k7_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'))='#skF_2' | ~l3_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_64])).
% 4.78/1.82  tff(c_78, plain, (k7_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'))='#skF_2' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_70])).
% 4.78/1.82  tff(c_79, plain, (k7_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_46, c_78])).
% 4.78/1.82  tff(c_179, plain, (m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_140])).
% 4.78/1.82  tff(c_68, plain, (k7_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'))='#skF_3' | ~l3_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_64])).
% 4.78/1.82  tff(c_74, plain, (k7_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'))='#skF_3' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_68])).
% 4.78/1.82  tff(c_75, plain, (k7_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_46, c_74])).
% 4.78/1.82  tff(c_225, plain, (![A_49, B_50, C_51]: (k4_lattices(A_49, B_50, C_51)=k5_lattices(A_49) | ~r3_lattices(A_49, B_50, k7_lattices(A_49, C_51)) | ~m1_subset_1(C_51, u1_struct_0(A_49)) | ~m1_subset_1(B_50, u1_struct_0(A_49)) | ~l3_lattices(A_49) | ~v17_lattices(A_49) | ~v10_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.78/1.82  tff(c_234, plain, (![B_50]: (k4_lattices('#skF_1', B_50, k7_lattices('#skF_1', '#skF_3'))=k5_lattices('#skF_1') | ~r3_lattices('#skF_1', B_50, '#skF_3') | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1')) | ~m1_subset_1(B_50, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_225])).
% 4.78/1.82  tff(c_240, plain, (![B_50]: (k4_lattices('#skF_1', B_50, k7_lattices('#skF_1', '#skF_3'))=k5_lattices('#skF_1') | ~r3_lattices('#skF_1', B_50, '#skF_3') | ~m1_subset_1(B_50, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_179, c_234])).
% 4.78/1.82  tff(c_324, plain, (![B_55]: (k4_lattices('#skF_1', B_55, k7_lattices('#skF_1', '#skF_3'))=k5_lattices('#skF_1') | ~r3_lattices('#skF_1', B_55, '#skF_3') | ~m1_subset_1(B_55, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_46, c_240])).
% 4.78/1.82  tff(c_331, plain, (![B_6]: (k4_lattices('#skF_1', k7_lattices('#skF_1', B_6), k7_lattices('#skF_1', '#skF_3'))=k5_lattices('#skF_1') | ~r3_lattices('#skF_1', k7_lattices('#skF_1', B_6), '#skF_3') | ~m1_subset_1(B_6, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_324])).
% 4.78/1.82  tff(c_341, plain, (![B_6]: (k4_lattices('#skF_1', k7_lattices('#skF_1', B_6), k7_lattices('#skF_1', '#skF_3'))=k5_lattices('#skF_1') | ~r3_lattices('#skF_1', k7_lattices('#skF_1', B_6), '#skF_3') | ~m1_subset_1(B_6, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_331])).
% 4.78/1.82  tff(c_788, plain, (![B_65]: (k4_lattices('#skF_1', k7_lattices('#skF_1', B_65), k7_lattices('#skF_1', '#skF_3'))=k5_lattices('#skF_1') | ~r3_lattices('#skF_1', k7_lattices('#skF_1', B_65), '#skF_3') | ~m1_subset_1(B_65, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_46, c_341])).
% 4.78/1.82  tff(c_26, plain, (![A_11, B_15, C_17]: (k4_lattices(A_11, k7_lattices(A_11, B_15), k7_lattices(A_11, C_17))=k7_lattices(A_11, k3_lattices(A_11, B_15, C_17)) | ~m1_subset_1(C_17, u1_struct_0(A_11)) | ~m1_subset_1(B_15, u1_struct_0(A_11)) | ~l3_lattices(A_11) | ~v17_lattices(A_11) | ~v10_lattices(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.78/1.82  tff(c_794, plain, (![B_65]: (k7_lattices('#skF_1', k3_lattices('#skF_1', B_65, '#skF_3'))=k5_lattices('#skF_1') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1(B_65, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~r3_lattices('#skF_1', k7_lattices('#skF_1', B_65), '#skF_3') | ~m1_subset_1(B_65, u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_788, c_26])).
% 4.78/1.82  tff(c_826, plain, (![B_65]: (k7_lattices('#skF_1', k3_lattices('#skF_1', B_65, '#skF_3'))=k5_lattices('#skF_1') | v2_struct_0('#skF_1') | ~r3_lattices('#skF_1', k7_lattices('#skF_1', B_65), '#skF_3') | ~m1_subset_1(B_65, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_36, c_794])).
% 4.78/1.82  tff(c_863, plain, (![B_69]: (k7_lattices('#skF_1', k3_lattices('#skF_1', B_69, '#skF_3'))=k5_lattices('#skF_1') | ~r3_lattices('#skF_1', k7_lattices('#skF_1', B_69), '#skF_3') | ~m1_subset_1(B_69, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_46, c_826])).
% 4.78/1.82  tff(c_882, plain, (k7_lattices('#skF_1', k3_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), '#skF_3'))=k5_lattices('#skF_1') | ~r3_lattices('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1(k7_lattices('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_79, c_863])).
% 4.78/1.82  tff(c_890, plain, (k7_lattices('#skF_1', k3_lattices('#skF_1', '#skF_3', k7_lattices('#skF_1', '#skF_2')))=k5_lattices('#skF_1') | ~m1_subset_1(k7_lattices('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_292, c_882])).
% 4.78/1.82  tff(c_893, plain, (~m1_subset_1(k7_lattices('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_890])).
% 4.78/1.82  tff(c_896, plain, (~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_893])).
% 4.78/1.82  tff(c_899, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_896])).
% 4.78/1.82  tff(c_901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_899])).
% 4.78/1.82  tff(c_903, plain, (m1_subset_1(k7_lattices('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_890])).
% 4.78/1.82  tff(c_352, plain, (![A_56, B_57, C_58]: (k4_lattices(A_56, k7_lattices(A_56, B_57), k7_lattices(A_56, C_58))=k7_lattices(A_56, k3_lattices(A_56, B_57, C_58)) | ~m1_subset_1(C_58, u1_struct_0(A_56)) | ~m1_subset_1(B_57, u1_struct_0(A_56)) | ~l3_lattices(A_56) | ~v17_lattices(A_56) | ~v10_lattices(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.78/1.82  tff(c_364, plain, (![B_57]: (k7_lattices('#skF_1', k3_lattices('#skF_1', B_57, k7_lattices('#skF_1', '#skF_2')))=k4_lattices('#skF_1', k7_lattices('#skF_1', B_57), '#skF_2') | ~m1_subset_1(k7_lattices('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(B_57, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_79, c_352])).
% 4.78/1.82  tff(c_377, plain, (![B_57]: (k7_lattices('#skF_1', k3_lattices('#skF_1', B_57, k7_lattices('#skF_1', '#skF_2')))=k4_lattices('#skF_1', k7_lattices('#skF_1', B_57), '#skF_2') | ~m1_subset_1(k7_lattices('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(B_57, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_364])).
% 4.78/1.82  tff(c_378, plain, (![B_57]: (k7_lattices('#skF_1', k3_lattices('#skF_1', B_57, k7_lattices('#skF_1', '#skF_2')))=k4_lattices('#skF_1', k7_lattices('#skF_1', B_57), '#skF_2') | ~m1_subset_1(k7_lattices('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(B_57, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_46, c_377])).
% 4.78/1.82  tff(c_2117, plain, (![B_84]: (k7_lattices('#skF_1', k3_lattices('#skF_1', B_84, k7_lattices('#skF_1', '#skF_2')))=k4_lattices('#skF_1', k7_lattices('#skF_1', B_84), '#skF_2') | ~m1_subset_1(B_84, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_903, c_378])).
% 4.78/1.82  tff(c_902, plain, (k7_lattices('#skF_1', k3_lattices('#skF_1', '#skF_3', k7_lattices('#skF_1', '#skF_2')))=k5_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_890])).
% 4.78/1.82  tff(c_2160, plain, (k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), '#skF_2')=k5_lattices('#skF_1') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2117, c_902])).
% 4.78/1.82  tff(c_2226, plain, (k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), '#skF_2')=k5_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2160])).
% 4.78/1.82  tff(c_2228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_2226])).
% 4.78/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.82  
% 4.78/1.82  Inference rules
% 4.78/1.82  ----------------------
% 4.78/1.82  #Ref     : 0
% 4.78/1.82  #Sup     : 461
% 4.78/1.82  #Fact    : 0
% 4.78/1.82  #Define  : 0
% 4.78/1.82  #Split   : 16
% 4.78/1.82  #Chain   : 0
% 4.78/1.82  #Close   : 0
% 4.78/1.82  
% 4.78/1.82  Ordering : KBO
% 4.78/1.82  
% 4.78/1.82  Simplification rules
% 4.78/1.82  ----------------------
% 4.78/1.82  #Subsume      : 77
% 4.78/1.82  #Demod        : 579
% 4.78/1.82  #Tautology    : 136
% 4.78/1.82  #SimpNegUnit  : 139
% 4.78/1.82  #BackRed      : 1
% 4.78/1.82  
% 4.78/1.82  #Partial instantiations: 0
% 4.78/1.82  #Strategies tried      : 1
% 4.78/1.82  
% 4.78/1.82  Timing (in seconds)
% 4.78/1.82  ----------------------
% 4.78/1.82  Preprocessing        : 0.33
% 4.78/1.82  Parsing              : 0.18
% 4.78/1.82  CNF conversion       : 0.02
% 4.78/1.82  Main loop            : 0.72
% 4.78/1.82  Inferencing          : 0.22
% 4.78/1.82  Reduction            : 0.25
% 4.78/1.82  Demodulation         : 0.18
% 4.78/1.82  BG Simplification    : 0.03
% 4.78/1.82  Subsumption          : 0.15
% 4.78/1.82  Abstraction          : 0.06
% 4.78/1.82  MUC search           : 0.00
% 4.78/1.82  Cooper               : 0.00
% 4.78/1.82  Total                : 1.09
% 4.78/1.82  Index Insertion      : 0.00
% 4.78/1.82  Index Deletion       : 0.00
% 4.78/1.82  Index Matching       : 0.00
% 4.78/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
