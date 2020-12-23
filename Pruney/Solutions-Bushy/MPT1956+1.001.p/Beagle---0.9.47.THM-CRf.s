%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1956+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:42 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 263 expanded)
%              Number of leaves         :   30 ( 106 expanded)
%              Depth                    :   13
%              Number of atoms          :  173 (1059 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r2_yellow_0 > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v3_lattice3 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k2_yellow_0 > k1_yellow_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_lattice3,type,(
    v3_lattice3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & v3_lattice3(A)
          & l1_orders_2(A) )
       => ! [B,C] :
            ( r1_tarski(B,C)
           => ( r3_orders_2(A,k1_yellow_0(A,B),k1_yellow_0(A,C))
              & r1_orders_2(A,k2_yellow_0(A,C),k2_yellow_0(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_waybel_7)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v3_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r1_yellow_0(A,B)
          & r2_yellow_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_0)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( ( r1_tarski(B,C)
            & r2_yellow_0(A,B)
            & r2_yellow_0(A,C) )
         => r1_orders_2(A,k2_yellow_0(A,C),k2_yellow_0(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_yellow_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( ( r1_tarski(B,C)
            & r1_yellow_0(A,B)
            & r1_yellow_0(A,C) )
         => r1_orders_2(A,k1_yellow_0(A,B),k1_yellow_0(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).

tff(c_22,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_26,plain,(
    v2_lattice3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_30,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_24,plain,(
    v3_lattice3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_12,plain,(
    ! [A_7,B_9] :
      ( r2_yellow_0(A_7,B_9)
      | ~ l1_orders_2(A_7)
      | ~ v3_lattice3(A_7)
      | ~ v5_orders_2(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_126,plain,(
    ! [A_50,C_51,B_52] :
      ( r1_orders_2(A_50,k2_yellow_0(A_50,C_51),k2_yellow_0(A_50,B_52))
      | ~ r2_yellow_0(A_50,C_51)
      | ~ r2_yellow_0(A_50,B_52)
      | ~ r1_tarski(B_52,C_51)
      | ~ l1_orders_2(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(k1_yellow_0(A_2,B_3),u1_struct_0(A_2))
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_43,plain,(
    ! [A_38,B_39,C_40] :
      ( r3_orders_2(A_38,B_39,C_40)
      | ~ r1_orders_2(A_38,B_39,C_40)
      | ~ m1_subset_1(C_40,u1_struct_0(A_38))
      | ~ m1_subset_1(B_39,u1_struct_0(A_38))
      | ~ l1_orders_2(A_38)
      | ~ v3_orders_2(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_47,plain,(
    ! [A_41,B_42,B_43] :
      ( r3_orders_2(A_41,B_42,k1_yellow_0(A_41,B_43))
      | ~ r1_orders_2(A_41,B_42,k1_yellow_0(A_41,B_43))
      | ~ m1_subset_1(B_42,u1_struct_0(A_41))
      | ~ v3_orders_2(A_41)
      | v2_struct_0(A_41)
      | ~ l1_orders_2(A_41) ) ),
    inference(resolution,[status(thm)],[c_4,c_43])).

tff(c_18,plain,
    ( ~ r1_orders_2('#skF_1',k2_yellow_0('#skF_1','#skF_3'),k2_yellow_0('#skF_1','#skF_2'))
    | ~ r3_orders_2('#skF_1',k1_yellow_0('#skF_1','#skF_2'),k1_yellow_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36,plain,(
    ~ r3_orders_2('#skF_1',k1_yellow_0('#skF_1','#skF_2'),k1_yellow_0('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_52,plain,
    ( ~ r1_orders_2('#skF_1',k1_yellow_0('#skF_1','#skF_2'),k1_yellow_0('#skF_1','#skF_3'))
    | ~ m1_subset_1(k1_yellow_0('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_47,c_36])).

tff(c_56,plain,
    ( ~ r1_orders_2('#skF_1',k1_yellow_0('#skF_1','#skF_2'),k1_yellow_0('#skF_1','#skF_3'))
    | ~ m1_subset_1(k1_yellow_0('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_34,c_52])).

tff(c_57,plain,(
    ~ m1_subset_1(k1_yellow_0('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_60,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_57])).

tff(c_64,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_60])).

tff(c_66,plain,(
    m1_subset_1(k1_yellow_0('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] :
      ( r3_orders_2(A_4,B_5,C_6)
      | ~ r1_orders_2(A_4,B_5,C_6)
      | ~ m1_subset_1(C_6,u1_struct_0(A_4))
      | ~ m1_subset_1(B_5,u1_struct_0(A_4))
      | ~ l1_orders_2(A_4)
      | ~ v3_orders_2(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_68,plain,(
    ! [B_5] :
      ( r3_orders_2('#skF_1',B_5,k1_yellow_0('#skF_1','#skF_2'))
      | ~ r1_orders_2('#skF_1',B_5,k1_yellow_0('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_5,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_66,c_6])).

tff(c_71,plain,(
    ! [B_5] :
      ( r3_orders_2('#skF_1',B_5,k1_yellow_0('#skF_1','#skF_2'))
      | ~ r1_orders_2('#skF_1',B_5,k1_yellow_0('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_5,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_22,c_68])).

tff(c_101,plain,(
    v2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v2_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,
    ( ~ v2_lattice3('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_101,c_2])).

tff(c_108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26,c_104])).

tff(c_110,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_10,plain,(
    ! [A_7,B_9] :
      ( r1_yellow_0(A_7,B_9)
      | ~ l1_orders_2(A_7)
      | ~ v3_lattice3(A_7)
      | ~ v5_orders_2(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [A_10,B_13,C_14] :
      ( r1_orders_2(A_10,k1_yellow_0(A_10,B_13),k1_yellow_0(A_10,C_14))
      | ~ r1_yellow_0(A_10,C_14)
      | ~ r1_yellow_0(A_10,B_13)
      | ~ r1_tarski(B_13,C_14)
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_65,plain,
    ( ~ r1_orders_2('#skF_1',k1_yellow_0('#skF_1','#skF_2'),k1_yellow_0('#skF_1','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_72,plain,(
    ~ r1_orders_2('#skF_1',k1_yellow_0('#skF_1','#skF_2'),k1_yellow_0('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_75,plain,
    ( ~ r1_yellow_0('#skF_1','#skF_3')
    | ~ r1_yellow_0('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2','#skF_3')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_72])).

tff(c_78,plain,
    ( ~ r1_yellow_0('#skF_1','#skF_3')
    | ~ r1_yellow_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_75])).

tff(c_79,plain,(
    ~ r1_yellow_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_82,plain,
    ( ~ l1_orders_2('#skF_1')
    | ~ v3_lattice3('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_79])).

tff(c_85,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_22,c_82])).

tff(c_88,plain,
    ( ~ v2_lattice3('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_85,c_2])).

tff(c_92,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26,c_88])).

tff(c_93,plain,(
    ~ r1_yellow_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_97,plain,
    ( ~ l1_orders_2('#skF_1')
    | ~ v3_lattice3('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_93])).

tff(c_100,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_22,c_97])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_100])).

tff(c_112,plain,(
    v2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_116,plain,
    ( ~ v2_lattice3('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26,c_116])).

tff(c_121,plain,(
    ~ r1_orders_2('#skF_1',k2_yellow_0('#skF_1','#skF_3'),k2_yellow_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_129,plain,
    ( ~ r2_yellow_0('#skF_1','#skF_3')
    | ~ r2_yellow_0('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2','#skF_3')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_126,c_121])).

tff(c_132,plain,
    ( ~ r2_yellow_0('#skF_1','#skF_3')
    | ~ r2_yellow_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_129])).

tff(c_133,plain,(
    ~ r2_yellow_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_136,plain,
    ( ~ l1_orders_2('#skF_1')
    | ~ v3_lattice3('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_133])).

tff(c_139,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_22,c_136])).

tff(c_142,plain,
    ( ~ v2_lattice3('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_139,c_2])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26,c_142])).

tff(c_147,plain,(
    ~ r2_yellow_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_151,plain,
    ( ~ l1_orders_2('#skF_1')
    | ~ v3_lattice3('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_147])).

tff(c_154,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_22,c_151])).

tff(c_157,plain,
    ( ~ v2_lattice3('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_154,c_2])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26,c_157])).

%------------------------------------------------------------------------------
