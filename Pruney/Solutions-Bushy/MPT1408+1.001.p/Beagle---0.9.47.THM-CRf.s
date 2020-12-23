%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1408+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:55 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 326 expanded)
%              Number of leaves         :   30 ( 126 expanded)
%              Depth                    :   18
%              Number of atoms          :  274 (1361 expanded)
%              Number of equality atoms :    8 ( 167 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_filter_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff(k2_filter_0,type,(
    k2_filter_0: ( $i * $i ) > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_142,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( k2_filter_0(A,B) = k2_filter_0(A,C)
                 => B = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_filter_1)).

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

tff(f_52,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_lattices(A,B,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_lattices)).

tff(f_105,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(B,k2_filter_0(A,C))
              <=> r3_lattices(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_filter_0)).

tff(f_71,axiom,(
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

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_lattices(A,B,C)
                  & r1_lattices(A,C,B) )
               => B = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_40,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_42,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_45,plain,(
    ! [A_27] :
      ( l2_lattices(A_27)
      | ~ l3_lattices(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_49,plain,(
    l2_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_45])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_65,plain,(
    ! [A_35,B_36,C_37] :
      ( r3_lattices(A_35,B_36,B_36)
      | ~ m1_subset_1(C_37,u1_struct_0(A_35))
      | ~ m1_subset_1(B_36,u1_struct_0(A_35))
      | ~ l3_lattices(A_35)
      | ~ v9_lattices(A_35)
      | ~ v8_lattices(A_35)
      | ~ v6_lattices(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_67,plain,(
    ! [B_36] :
      ( r3_lattices('#skF_1',B_36,B_36)
      | ~ m1_subset_1(B_36,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_65])).

tff(c_72,plain,(
    ! [B_36] :
      ( r3_lattices('#skF_1',B_36,B_36)
      | ~ m1_subset_1(B_36,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_67])).

tff(c_73,plain,(
    ! [B_36] :
      ( r3_lattices('#skF_1',B_36,B_36)
      | ~ m1_subset_1(B_36,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_72])).

tff(c_78,plain,(
    ~ v6_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_82,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_78])).

tff(c_85,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_82])).

tff(c_87,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_85])).

tff(c_89,plain,(
    v6_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_73])).

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

tff(c_88,plain,(
    ! [B_36] :
      ( ~ v8_lattices('#skF_1')
      | ~ v9_lattices('#skF_1')
      | r3_lattices('#skF_1',B_36,B_36)
      | ~ m1_subset_1(B_36,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_90,plain,(
    ~ v9_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_93,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_90])).

tff(c_96,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_93])).

tff(c_98,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_96])).

tff(c_99,plain,(
    ! [B_36] :
      ( ~ v8_lattices('#skF_1')
      | r3_lattices('#skF_1',B_36,B_36)
      | ~ m1_subset_1(B_36,u1_struct_0('#skF_1')) ) ),
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
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_111])).

tff(c_116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_114])).

tff(c_118,plain,(
    v8_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_100,plain,(
    v9_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_120,plain,(
    ! [B_42] :
      ( r3_lattices('#skF_1',B_42,B_42)
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_126,plain,(
    r3_lattices('#skF_1','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_120])).

tff(c_34,plain,(
    k2_filter_0('#skF_1','#skF_2') = k2_filter_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_129,plain,(
    ! [B_43,A_44,C_45] :
      ( r2_hidden(B_43,k2_filter_0(A_44,C_45))
      | ~ r3_lattices(A_44,C_45,B_43)
      | ~ m1_subset_1(C_45,u1_struct_0(A_44))
      | ~ m1_subset_1(B_43,u1_struct_0(A_44))
      | ~ l3_lattices(A_44)
      | ~ v10_lattices(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_139,plain,(
    ! [B_43] :
      ( r2_hidden(B_43,k2_filter_0('#skF_1','#skF_3'))
      | ~ r3_lattices('#skF_1','#skF_2',B_43)
      | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v10_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_129])).

tff(c_146,plain,(
    ! [B_43] :
      ( r2_hidden(B_43,k2_filter_0('#skF_1','#skF_3'))
      | ~ r3_lattices('#skF_1','#skF_2',B_43)
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_139])).

tff(c_161,plain,(
    ! [B_50] :
      ( r2_hidden(B_50,k2_filter_0('#skF_1','#skF_3'))
      | ~ r3_lattices('#skF_1','#skF_2',B_50)
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_146])).

tff(c_28,plain,(
    ! [A_9,C_15,B_13] :
      ( r3_lattices(A_9,C_15,B_13)
      | ~ r2_hidden(B_13,k2_filter_0(A_9,C_15))
      | ~ m1_subset_1(C_15,u1_struct_0(A_9))
      | ~ m1_subset_1(B_13,u1_struct_0(A_9))
      | ~ l3_lattices(A_9)
      | ~ v10_lattices(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_167,plain,(
    ! [B_50] :
      ( r3_lattices('#skF_1','#skF_3',B_50)
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v10_lattices('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ r3_lattices('#skF_1','#skF_2',B_50)
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_161,c_28])).

tff(c_171,plain,(
    ! [B_50] :
      ( r3_lattices('#skF_1','#skF_3',B_50)
      | v2_struct_0('#skF_1')
      | ~ r3_lattices('#skF_1','#skF_2',B_50)
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_167])).

tff(c_173,plain,(
    ! [B_51] :
      ( r3_lattices('#skF_1','#skF_3',B_51)
      | ~ r3_lattices('#skF_1','#skF_2',B_51)
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_171])).

tff(c_179,plain,
    ( r3_lattices('#skF_1','#skF_3','#skF_2')
    | ~ r3_lattices('#skF_1','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_173])).

tff(c_185,plain,(
    r3_lattices('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_179])).

tff(c_186,plain,(
    ! [A_52,B_53,C_54] :
      ( r1_lattices(A_52,B_53,C_54)
      | ~ r3_lattices(A_52,B_53,C_54)
      | ~ m1_subset_1(C_54,u1_struct_0(A_52))
      | ~ m1_subset_1(B_53,u1_struct_0(A_52))
      | ~ l3_lattices(A_52)
      | ~ v9_lattices(A_52)
      | ~ v8_lattices(A_52)
      | ~ v6_lattices(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_188,plain,
    ( r1_lattices('#skF_1','#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | ~ v9_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_185,c_186])).

tff(c_197,plain,
    ( r1_lattices('#skF_1','#skF_3','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_118,c_100,c_40,c_36,c_38,c_188])).

tff(c_198,plain,(
    r1_lattices('#skF_1','#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_197])).

tff(c_125,plain,(
    r3_lattices('#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_120])).

tff(c_101,plain,(
    ! [A_38,C_39,B_40] :
      ( r3_lattices(A_38,C_39,B_40)
      | ~ r2_hidden(B_40,k2_filter_0(A_38,C_39))
      | ~ m1_subset_1(C_39,u1_struct_0(A_38))
      | ~ m1_subset_1(B_40,u1_struct_0(A_38))
      | ~ l3_lattices(A_38)
      | ~ v10_lattices(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_104,plain,(
    ! [B_40] :
      ( r3_lattices('#skF_1','#skF_2',B_40)
      | ~ r2_hidden(B_40,k2_filter_0('#skF_1','#skF_3'))
      | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_40,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v10_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_101])).

tff(c_106,plain,(
    ! [B_40] :
      ( r3_lattices('#skF_1','#skF_2',B_40)
      | ~ r2_hidden(B_40,k2_filter_0('#skF_1','#skF_3'))
      | ~ m1_subset_1(B_40,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_104])).

tff(c_107,plain,(
    ! [B_40] :
      ( r3_lattices('#skF_1','#skF_2',B_40)
      | ~ r2_hidden(B_40,k2_filter_0('#skF_1','#skF_3'))
      | ~ m1_subset_1(B_40,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_106])).

tff(c_133,plain,(
    ! [B_43] :
      ( r3_lattices('#skF_1','#skF_2',B_43)
      | ~ r3_lattices('#skF_1','#skF_3',B_43)
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v10_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_129,c_107])).

tff(c_142,plain,(
    ! [B_43] :
      ( r3_lattices('#skF_1','#skF_2',B_43)
      | ~ r3_lattices('#skF_1','#skF_3',B_43)
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_133])).

tff(c_149,plain,(
    ! [B_49] :
      ( r3_lattices('#skF_1','#skF_2',B_49)
      | ~ r3_lattices('#skF_1','#skF_3',B_49)
      | ~ m1_subset_1(B_49,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_142])).

tff(c_152,plain,
    ( r3_lattices('#skF_1','#skF_2','#skF_3')
    | ~ r3_lattices('#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_149])).

tff(c_158,plain,(
    r3_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_152])).

tff(c_190,plain,
    ( r1_lattices('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | ~ v9_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_158,c_186])).

tff(c_201,plain,
    ( r1_lattices('#skF_1','#skF_2','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_118,c_100,c_40,c_38,c_36,c_190])).

tff(c_202,plain,(
    r1_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_201])).

tff(c_30,plain,(
    ! [C_22,B_20,A_16] :
      ( C_22 = B_20
      | ~ r1_lattices(A_16,C_22,B_20)
      | ~ r1_lattices(A_16,B_20,C_22)
      | ~ m1_subset_1(C_22,u1_struct_0(A_16))
      | ~ m1_subset_1(B_20,u1_struct_0(A_16))
      | ~ l2_lattices(A_16)
      | ~ v4_lattices(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_245,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_lattices('#skF_1','#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l2_lattices('#skF_1')
    | ~ v4_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_202,c_30])).

tff(c_248,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v4_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_36,c_38,c_198,c_245])).

tff(c_249,plain,(
    ~ v4_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_32,c_248])).

tff(c_252,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_249])).

tff(c_255,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_252])).

tff(c_257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_255])).

%------------------------------------------------------------------------------
