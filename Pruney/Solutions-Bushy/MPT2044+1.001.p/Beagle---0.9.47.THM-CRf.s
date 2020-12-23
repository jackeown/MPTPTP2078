%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2044+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:48 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 152 expanded)
%              Number of leaves         :   20 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  132 ( 460 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_yellow19 > a_2_0_yellow19 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_yellow19,type,(
    k1_yellow19: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(a_2_0_yellow19,type,(
    a_2_0_yellow19: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( r2_hidden(C,k1_yellow19(A,B))
              <=> m1_connsp_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow19)).

tff(f_36,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k1_yellow19(A,B) = a_2_0_yellow19(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow19)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( r2_hidden(A,a_2_0_yellow19(B,C))
      <=> ? [D] :
            ( m1_connsp_2(D,B,C)
            & A = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_yellow19)).

tff(c_16,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_connsp_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_25,plain,(
    ~ m1_connsp_2('#skF_5','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( k1_yellow19(A_14,B_15) = a_2_0_yellow19(A_14,B_15)
      | ~ m1_subset_1(B_15,u1_struct_0(A_14))
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_31,plain,
    ( k1_yellow19('#skF_2','#skF_3') = a_2_0_yellow19('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_28])).

tff(c_34,plain,
    ( k1_yellow19('#skF_2','#skF_3') = a_2_0_yellow19('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_31])).

tff(c_35,plain,(
    k1_yellow19('#skF_2','#skF_3') = a_2_0_yellow19('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_34])).

tff(c_24,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | r2_hidden('#skF_5',k1_yellow19('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    r2_hidden('#skF_5',k1_yellow19('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_36,plain,(
    r2_hidden('#skF_5',a_2_0_yellow19('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_26])).

tff(c_42,plain,(
    ! [A_19,B_20,C_21] :
      ( '#skF_1'(A_19,B_20,C_21) = A_19
      | ~ r2_hidden(A_19,a_2_0_yellow19(B_20,C_21))
      | ~ m1_subset_1(C_21,u1_struct_0(B_20))
      | ~ l1_pre_topc(B_20)
      | ~ v2_pre_topc(B_20)
      | v2_struct_0(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_48,plain,
    ( '#skF_1'('#skF_5','#skF_2','#skF_3') = '#skF_5'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_42])).

tff(c_52,plain,
    ( '#skF_1'('#skF_5','#skF_2','#skF_3') = '#skF_5'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_10,c_48])).

tff(c_53,plain,(
    '#skF_1'('#skF_5','#skF_2','#skF_3') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_52])).

tff(c_8,plain,(
    ! [A_4,B_5,C_6] :
      ( m1_connsp_2('#skF_1'(A_4,B_5,C_6),B_5,C_6)
      | ~ r2_hidden(A_4,a_2_0_yellow19(B_5,C_6))
      | ~ m1_subset_1(C_6,u1_struct_0(B_5))
      | ~ l1_pre_topc(B_5)
      | ~ v2_pre_topc(B_5)
      | v2_struct_0(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_58,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | ~ r2_hidden('#skF_5',a_2_0_yellow19('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_8])).

tff(c_62,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_10,c_36,c_58])).

tff(c_64,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_25,c_62])).

tff(c_65,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_82,plain,(
    ! [D_27,B_28,C_29] :
      ( r2_hidden(D_27,a_2_0_yellow19(B_28,C_29))
      | ~ m1_connsp_2(D_27,B_28,C_29)
      | ~ m1_subset_1(C_29,u1_struct_0(B_28))
      | ~ l1_pre_topc(B_28)
      | ~ v2_pre_topc(B_28)
      | v2_struct_0(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_68,plain,(
    ! [A_25,B_26] :
      ( k1_yellow19(A_25,B_26) = a_2_0_yellow19(A_25,B_26)
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_71,plain,
    ( k1_yellow19('#skF_2','#skF_3') = a_2_0_yellow19('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_68])).

tff(c_74,plain,
    ( k1_yellow19('#skF_2','#skF_3') = a_2_0_yellow19('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_71])).

tff(c_75,plain,(
    k1_yellow19('#skF_2','#skF_3') = a_2_0_yellow19('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_74])).

tff(c_66,plain,(
    ~ r2_hidden('#skF_5',k1_yellow19('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_22,plain,
    ( ~ r2_hidden('#skF_4',k1_yellow19('#skF_2','#skF_3'))
    | r2_hidden('#skF_5',k1_yellow19('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_67,plain,(
    ~ r2_hidden('#skF_4',k1_yellow19('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_22])).

tff(c_76,plain,(
    ~ r2_hidden('#skF_4',a_2_0_yellow19('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_67])).

tff(c_88,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_76])).

tff(c_95,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_10,c_65,c_88])).

tff(c_97,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_95])).

tff(c_98,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_116,plain,(
    ! [D_32,B_33,C_34] :
      ( r2_hidden(D_32,a_2_0_yellow19(B_33,C_34))
      | ~ m1_connsp_2(D_32,B_33,C_34)
      | ~ m1_subset_1(C_34,u1_struct_0(B_33))
      | ~ l1_pre_topc(B_33)
      | ~ v2_pre_topc(B_33)
      | v2_struct_0(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_103,plain,(
    ! [A_30,B_31] :
      ( k1_yellow19(A_30,B_31) = a_2_0_yellow19(A_30,B_31)
      | ~ m1_subset_1(B_31,u1_struct_0(A_30))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_106,plain,
    ( k1_yellow19('#skF_2','#skF_3') = a_2_0_yellow19('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_103])).

tff(c_109,plain,
    ( k1_yellow19('#skF_2','#skF_3') = a_2_0_yellow19('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_106])).

tff(c_110,plain,(
    k1_yellow19('#skF_2','#skF_3') = a_2_0_yellow19('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_109])).

tff(c_99,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_18,plain,
    ( ~ r2_hidden('#skF_4',k1_yellow19('#skF_2','#skF_3'))
    | ~ m1_connsp_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_101,plain,(
    ~ r2_hidden('#skF_4',k1_yellow19('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_18])).

tff(c_111,plain,(
    ~ r2_hidden('#skF_4',a_2_0_yellow19('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_101])).

tff(c_119,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_116,c_111])).

tff(c_122,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_10,c_98,c_119])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_122])).

%------------------------------------------------------------------------------
