%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:20 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 560 expanded)
%              Number of leaves         :   35 ( 206 expanded)
%              Depth                    :   15
%              Number of atoms          :  367 (2581 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k1_lattices > k7_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_163,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k7_lattices(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

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

tff(f_109,axiom,(
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

tff(f_77,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(f_143,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_lattices)).

tff(f_126,axiom,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_44,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k7_lattices(A_9,B_10),u1_struct_0(A_9))
      | ~ m1_subset_1(B_10,u1_struct_0(A_9))
      | ~ l3_lattices(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_48,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_561,plain,(
    ! [A_98,B_99,C_100] :
      ( r3_lattices(A_98,B_99,C_100)
      | ~ r1_lattices(A_98,B_99,C_100)
      | ~ m1_subset_1(C_100,u1_struct_0(A_98))
      | ~ m1_subset_1(B_99,u1_struct_0(A_98))
      | ~ l3_lattices(A_98)
      | ~ v9_lattices(A_98)
      | ~ v8_lattices(A_98)
      | ~ v6_lattices(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_565,plain,(
    ! [B_99] :
      ( r3_lattices('#skF_1',B_99,'#skF_3')
      | ~ r1_lattices('#skF_1',B_99,'#skF_3')
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_561])).

tff(c_571,plain,(
    ! [B_99] :
      ( r3_lattices('#skF_1',B_99,'#skF_3')
      | ~ r1_lattices('#skF_1',B_99,'#skF_3')
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_565])).

tff(c_572,plain,(
    ! [B_99] :
      ( r3_lattices('#skF_1',B_99,'#skF_3')
      | ~ r1_lattices('#skF_1',B_99,'#skF_3')
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_571])).

tff(c_577,plain,(
    ~ v6_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_572])).

tff(c_580,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_577])).

tff(c_583,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_580])).

tff(c_585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_583])).

tff(c_587,plain,(
    v6_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_572])).

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

tff(c_567,plain,(
    ! [B_99] :
      ( r3_lattices('#skF_1',B_99,'#skF_2')
      | ~ r1_lattices('#skF_1',B_99,'#skF_2')
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_561])).

tff(c_575,plain,(
    ! [B_99] :
      ( r3_lattices('#skF_1',B_99,'#skF_2')
      | ~ r1_lattices('#skF_1',B_99,'#skF_2')
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_567])).

tff(c_576,plain,(
    ! [B_99] :
      ( r3_lattices('#skF_1',B_99,'#skF_2')
      | ~ r1_lattices('#skF_1',B_99,'#skF_2')
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_575])).

tff(c_588,plain,(
    ~ v6_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_576])).

tff(c_590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_588])).

tff(c_591,plain,(
    ! [B_99] :
      ( ~ v8_lattices('#skF_1')
      | ~ v9_lattices('#skF_1')
      | r3_lattices('#skF_1',B_99,'#skF_2')
      | ~ r1_lattices('#skF_1',B_99,'#skF_2')
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_576])).

tff(c_594,plain,(
    ~ v9_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_591])).

tff(c_609,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_594])).

tff(c_612,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_609])).

tff(c_614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_612])).

tff(c_615,plain,(
    ! [B_99] :
      ( ~ v8_lattices('#skF_1')
      | r3_lattices('#skF_1',B_99,'#skF_2')
      | ~ r1_lattices('#skF_1',B_99,'#skF_2')
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_591])).

tff(c_617,plain,(
    ~ v8_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_615])).

tff(c_623,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_617])).

tff(c_626,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_623])).

tff(c_628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_626])).

tff(c_630,plain,(
    v8_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_615])).

tff(c_616,plain,(
    v9_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_591])).

tff(c_786,plain,(
    ! [A_121,B_122,B_123] :
      ( r3_lattices(A_121,B_122,k7_lattices(A_121,B_123))
      | ~ r1_lattices(A_121,B_122,k7_lattices(A_121,B_123))
      | ~ m1_subset_1(B_122,u1_struct_0(A_121))
      | ~ v9_lattices(A_121)
      | ~ v8_lattices(A_121)
      | ~ v6_lattices(A_121)
      | ~ m1_subset_1(B_123,u1_struct_0(A_121))
      | ~ l3_lattices(A_121)
      | v2_struct_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_20,c_561])).

tff(c_36,plain,(
    ~ r3_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_791,plain,
    ( ~ r1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2'))
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1'))
    | ~ v9_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_786,c_36])).

tff(c_795,plain,
    ( ~ r1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2'))
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_587,c_630,c_616,c_791])).

tff(c_796,plain,
    ( ~ r1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2'))
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_795])).

tff(c_797,plain,(
    ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_796])).

tff(c_803,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_797])).

tff(c_806,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_803])).

tff(c_808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_806])).

tff(c_809,plain,(
    ~ r1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_796])).

tff(c_46,plain,(
    v17_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_810,plain,(
    m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_796])).

tff(c_51,plain,(
    ! [A_36] :
      ( l2_lattices(A_36)
      | ~ l3_lattices(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_55,plain,(
    l2_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_51])).

tff(c_68,plain,(
    ! [A_46,B_47,C_48] :
      ( r1_lattices(A_46,B_47,C_48)
      | k1_lattices(A_46,B_47,C_48) != C_48
      | ~ m1_subset_1(C_48,u1_struct_0(A_46))
      | ~ m1_subset_1(B_47,u1_struct_0(A_46))
      | ~ l2_lattices(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_72,plain,(
    ! [B_47] :
      ( r1_lattices('#skF_1',B_47,'#skF_3')
      | k1_lattices('#skF_1',B_47,'#skF_3') != '#skF_3'
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_68])).

tff(c_78,plain,(
    ! [B_47] :
      ( r1_lattices('#skF_1',B_47,'#skF_3')
      | k1_lattices('#skF_1',B_47,'#skF_3') != '#skF_3'
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_72])).

tff(c_84,plain,(
    ! [B_49] :
      ( r1_lattices('#skF_1',B_49,'#skF_3')
      | k1_lattices('#skF_1',B_49,'#skF_3') != '#skF_3'
      | ~ m1_subset_1(B_49,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_78])).

tff(c_100,plain,
    ( r1_lattices('#skF_1','#skF_2','#skF_3')
    | k1_lattices('#skF_1','#skF_2','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_84])).

tff(c_102,plain,(
    k1_lattices('#skF_1','#skF_2','#skF_3') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_38,plain,(
    r3_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_292,plain,(
    ! [A_71,B_72,C_73] :
      ( r1_lattices(A_71,B_72,C_73)
      | ~ r3_lattices(A_71,B_72,C_73)
      | ~ m1_subset_1(C_73,u1_struct_0(A_71))
      | ~ m1_subset_1(B_72,u1_struct_0(A_71))
      | ~ l3_lattices(A_71)
      | ~ v9_lattices(A_71)
      | ~ v8_lattices(A_71)
      | ~ v6_lattices(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_294,plain,
    ( r1_lattices('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | ~ v9_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_292])).

tff(c_297,plain,
    ( r1_lattices('#skF_1','#skF_2','#skF_3')
    | ~ v9_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_294])).

tff(c_298,plain,
    ( r1_lattices('#skF_1','#skF_2','#skF_3')
    | ~ v9_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_297])).

tff(c_299,plain,(
    ~ v6_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_318,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_299])).

tff(c_321,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_318])).

tff(c_323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_321])).

tff(c_324,plain,
    ( ~ v8_lattices('#skF_1')
    | ~ v9_lattices('#skF_1')
    | r1_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_326,plain,(
    ~ v9_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_324])).

tff(c_329,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_326])).

tff(c_332,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_329])).

tff(c_334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_332])).

tff(c_335,plain,
    ( ~ v8_lattices('#skF_1')
    | r1_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_324])).

tff(c_337,plain,(
    ~ v8_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_335])).

tff(c_340,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_337])).

tff(c_343,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_340])).

tff(c_345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_343])).

tff(c_346,plain,(
    r1_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_18,plain,(
    ! [A_2,B_6,C_8] :
      ( k1_lattices(A_2,B_6,C_8) = C_8
      | ~ r1_lattices(A_2,B_6,C_8)
      | ~ m1_subset_1(C_8,u1_struct_0(A_2))
      | ~ m1_subset_1(B_6,u1_struct_0(A_2))
      | ~ l2_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_349,plain,
    ( k1_lattices('#skF_1','#skF_2','#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l2_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_346,c_18])).

tff(c_352,plain,
    ( k1_lattices('#skF_1','#skF_2','#skF_3') = '#skF_3'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_42,c_40,c_349])).

tff(c_354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_102,c_352])).

tff(c_356,plain,(
    k1_lattices('#skF_1','#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_395,plain,(
    ! [A_82,B_83,C_84] :
      ( k3_lattices(A_82,B_83,C_84) = k1_lattices(A_82,B_83,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l2_lattices(A_82)
      | ~ v4_lattices(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_399,plain,(
    ! [B_83] :
      ( k3_lattices('#skF_1',B_83,'#skF_3') = k1_lattices('#skF_1',B_83,'#skF_3')
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_395])).

tff(c_405,plain,(
    ! [B_83] :
      ( k3_lattices('#skF_1',B_83,'#skF_3') = k1_lattices('#skF_1',B_83,'#skF_3')
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_399])).

tff(c_406,plain,(
    ! [B_83] :
      ( k3_lattices('#skF_1',B_83,'#skF_3') = k1_lattices('#skF_1',B_83,'#skF_3')
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_405])).

tff(c_411,plain,(
    ~ v4_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_406])).

tff(c_414,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_411])).

tff(c_417,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_414])).

tff(c_419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_417])).

tff(c_449,plain,(
    ! [B_86] :
      ( k3_lattices('#skF_1',B_86,'#skF_3') = k1_lattices('#skF_1',B_86,'#skF_3')
      | ~ m1_subset_1(B_86,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_406])).

tff(c_459,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_3') = k1_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_449])).

tff(c_466,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_459])).

tff(c_649,plain,(
    ! [A_105,B_106,C_107] :
      ( k4_lattices(A_105,k7_lattices(A_105,B_106),k7_lattices(A_105,C_107)) = k7_lattices(A_105,k3_lattices(A_105,B_106,C_107))
      | ~ m1_subset_1(C_107,u1_struct_0(A_105))
      | ~ m1_subset_1(B_106,u1_struct_0(A_105))
      | ~ l3_lattices(A_105)
      | ~ v17_lattices(A_105)
      | ~ v10_lattices(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_32,plain,(
    ! [A_18,B_22,C_24] :
      ( r1_lattices(A_18,k4_lattices(A_18,B_22,C_24),B_22)
      | ~ m1_subset_1(C_24,u1_struct_0(A_18))
      | ~ m1_subset_1(B_22,u1_struct_0(A_18))
      | ~ l3_lattices(A_18)
      | ~ v8_lattices(A_18)
      | ~ v6_lattices(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_997,plain,(
    ! [A_132,B_133,C_134] :
      ( r1_lattices(A_132,k7_lattices(A_132,k3_lattices(A_132,B_133,C_134)),k7_lattices(A_132,B_133))
      | ~ m1_subset_1(k7_lattices(A_132,C_134),u1_struct_0(A_132))
      | ~ m1_subset_1(k7_lattices(A_132,B_133),u1_struct_0(A_132))
      | ~ l3_lattices(A_132)
      | ~ v8_lattices(A_132)
      | ~ v6_lattices(A_132)
      | v2_struct_0(A_132)
      | ~ m1_subset_1(C_134,u1_struct_0(A_132))
      | ~ m1_subset_1(B_133,u1_struct_0(A_132))
      | ~ l3_lattices(A_132)
      | ~ v17_lattices(A_132)
      | ~ v10_lattices(A_132)
      | v2_struct_0(A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_649,c_32])).

tff(c_1053,plain,
    ( r1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2'))
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_997])).

tff(c_1113,plain,
    ( r1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2'))
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_587,c_630,c_44,c_810,c_1053])).

tff(c_1114,plain,(
    ~ m1_subset_1(k7_lattices('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_809,c_1113])).

tff(c_1123,plain,
    ( ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_1114])).

tff(c_1126,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1123])).

tff(c_1128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.64  
% 3.48/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.64  %$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k1_lattices > k7_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1
% 3.48/1.64  
% 3.48/1.64  %Foreground sorts:
% 3.48/1.64  
% 3.48/1.64  
% 3.48/1.64  %Background operators:
% 3.48/1.64  
% 3.48/1.64  
% 3.48/1.64  %Foreground operators:
% 3.48/1.64  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.48/1.64  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 3.48/1.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.48/1.64  tff(l2_lattices, type, l2_lattices: $i > $o).
% 3.48/1.64  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 3.48/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.64  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 3.48/1.64  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 3.48/1.64  tff(l1_lattices, type, l1_lattices: $i > $o).
% 3.48/1.64  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 3.48/1.64  tff(v17_lattices, type, v17_lattices: $i > $o).
% 3.48/1.64  tff(v4_lattices, type, v4_lattices: $i > $o).
% 3.48/1.64  tff(v6_lattices, type, v6_lattices: $i > $o).
% 3.48/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.48/1.64  tff(v9_lattices, type, v9_lattices: $i > $o).
% 3.48/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.48/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.48/1.64  tff(v5_lattices, type, v5_lattices: $i > $o).
% 3.48/1.64  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.48/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.64  tff(v8_lattices, type, v8_lattices: $i > $o).
% 3.48/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.64  tff(k7_lattices, type, k7_lattices: ($i * $i) > $i).
% 3.48/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.48/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.48/1.64  tff(v7_lattices, type, v7_lattices: $i > $o).
% 3.48/1.64  
% 3.84/1.67  tff(f_163, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_lattices(A, B, C) => r3_lattices(A, k7_lattices(A, C), k7_lattices(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_lattices)).
% 3.84/1.67  tff(f_71, axiom, (![A, B]: (((~v2_struct_0(A) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k7_lattices(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_lattices)).
% 3.84/1.67  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 3.84/1.67  tff(f_109, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 3.84/1.67  tff(f_77, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 3.84/1.67  tff(f_62, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 3.84/1.67  tff(f_90, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 3.84/1.67  tff(f_143, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k7_lattices(A, k3_lattices(A, B, C)) = k4_lattices(A, k7_lattices(A, B), k7_lattices(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_lattices)).
% 3.84/1.67  tff(f_126, axiom, (![A]: ((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => r1_lattices(A, k4_lattices(A, B, C), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_lattices)).
% 3.84/1.67  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.84/1.67  tff(c_44, plain, (l3_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.84/1.67  tff(c_42, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.84/1.67  tff(c_20, plain, (![A_9, B_10]: (m1_subset_1(k7_lattices(A_9, B_10), u1_struct_0(A_9)) | ~m1_subset_1(B_10, u1_struct_0(A_9)) | ~l3_lattices(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.84/1.67  tff(c_40, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.84/1.67  tff(c_48, plain, (v10_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.84/1.67  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.84/1.67  tff(c_561, plain, (![A_98, B_99, C_100]: (r3_lattices(A_98, B_99, C_100) | ~r1_lattices(A_98, B_99, C_100) | ~m1_subset_1(C_100, u1_struct_0(A_98)) | ~m1_subset_1(B_99, u1_struct_0(A_98)) | ~l3_lattices(A_98) | ~v9_lattices(A_98) | ~v8_lattices(A_98) | ~v6_lattices(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.84/1.67  tff(c_565, plain, (![B_99]: (r3_lattices('#skF_1', B_99, '#skF_3') | ~r1_lattices('#skF_1', B_99, '#skF_3') | ~m1_subset_1(B_99, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_561])).
% 3.84/1.67  tff(c_571, plain, (![B_99]: (r3_lattices('#skF_1', B_99, '#skF_3') | ~r1_lattices('#skF_1', B_99, '#skF_3') | ~m1_subset_1(B_99, u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_565])).
% 3.84/1.67  tff(c_572, plain, (![B_99]: (r3_lattices('#skF_1', B_99, '#skF_3') | ~r1_lattices('#skF_1', B_99, '#skF_3') | ~m1_subset_1(B_99, u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_50, c_571])).
% 3.84/1.67  tff(c_577, plain, (~v6_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_572])).
% 3.84/1.67  tff(c_580, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_8, c_577])).
% 3.84/1.67  tff(c_583, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_580])).
% 3.84/1.67  tff(c_585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_583])).
% 3.84/1.67  tff(c_587, plain, (v6_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_572])).
% 3.84/1.67  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.84/1.67  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.84/1.67  tff(c_567, plain, (![B_99]: (r3_lattices('#skF_1', B_99, '#skF_2') | ~r1_lattices('#skF_1', B_99, '#skF_2') | ~m1_subset_1(B_99, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_561])).
% 3.84/1.67  tff(c_575, plain, (![B_99]: (r3_lattices('#skF_1', B_99, '#skF_2') | ~r1_lattices('#skF_1', B_99, '#skF_2') | ~m1_subset_1(B_99, u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_567])).
% 3.84/1.67  tff(c_576, plain, (![B_99]: (r3_lattices('#skF_1', B_99, '#skF_2') | ~r1_lattices('#skF_1', B_99, '#skF_2') | ~m1_subset_1(B_99, u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_50, c_575])).
% 3.84/1.67  tff(c_588, plain, (~v6_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_576])).
% 3.84/1.67  tff(c_590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_587, c_588])).
% 3.84/1.67  tff(c_591, plain, (![B_99]: (~v8_lattices('#skF_1') | ~v9_lattices('#skF_1') | r3_lattices('#skF_1', B_99, '#skF_2') | ~r1_lattices('#skF_1', B_99, '#skF_2') | ~m1_subset_1(B_99, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_576])).
% 3.84/1.67  tff(c_594, plain, (~v9_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_591])).
% 3.84/1.67  tff(c_609, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_2, c_594])).
% 3.84/1.67  tff(c_612, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_609])).
% 3.84/1.67  tff(c_614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_612])).
% 3.84/1.67  tff(c_615, plain, (![B_99]: (~v8_lattices('#skF_1') | r3_lattices('#skF_1', B_99, '#skF_2') | ~r1_lattices('#skF_1', B_99, '#skF_2') | ~m1_subset_1(B_99, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_591])).
% 3.84/1.67  tff(c_617, plain, (~v8_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_615])).
% 3.84/1.67  tff(c_623, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_4, c_617])).
% 3.84/1.67  tff(c_626, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_623])).
% 3.84/1.67  tff(c_628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_626])).
% 3.84/1.67  tff(c_630, plain, (v8_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_615])).
% 3.84/1.67  tff(c_616, plain, (v9_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_591])).
% 3.84/1.67  tff(c_786, plain, (![A_121, B_122, B_123]: (r3_lattices(A_121, B_122, k7_lattices(A_121, B_123)) | ~r1_lattices(A_121, B_122, k7_lattices(A_121, B_123)) | ~m1_subset_1(B_122, u1_struct_0(A_121)) | ~v9_lattices(A_121) | ~v8_lattices(A_121) | ~v6_lattices(A_121) | ~m1_subset_1(B_123, u1_struct_0(A_121)) | ~l3_lattices(A_121) | v2_struct_0(A_121))), inference(resolution, [status(thm)], [c_20, c_561])).
% 3.84/1.67  tff(c_36, plain, (~r3_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.84/1.67  tff(c_791, plain, (~r1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2')) | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_786, c_36])).
% 3.84/1.67  tff(c_795, plain, (~r1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2')) | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_587, c_630, c_616, c_791])).
% 3.84/1.67  tff(c_796, plain, (~r1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2')) | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_50, c_795])).
% 3.84/1.67  tff(c_797, plain, (~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_796])).
% 3.84/1.67  tff(c_803, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_797])).
% 3.84/1.67  tff(c_806, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_803])).
% 3.84/1.67  tff(c_808, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_806])).
% 3.84/1.67  tff(c_809, plain, (~r1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_796])).
% 3.84/1.67  tff(c_46, plain, (v17_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.84/1.67  tff(c_810, plain, (m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_796])).
% 3.84/1.67  tff(c_51, plain, (![A_36]: (l2_lattices(A_36) | ~l3_lattices(A_36))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.84/1.67  tff(c_55, plain, (l2_lattices('#skF_1')), inference(resolution, [status(thm)], [c_44, c_51])).
% 3.84/1.67  tff(c_68, plain, (![A_46, B_47, C_48]: (r1_lattices(A_46, B_47, C_48) | k1_lattices(A_46, B_47, C_48)!=C_48 | ~m1_subset_1(C_48, u1_struct_0(A_46)) | ~m1_subset_1(B_47, u1_struct_0(A_46)) | ~l2_lattices(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.84/1.67  tff(c_72, plain, (![B_47]: (r1_lattices('#skF_1', B_47, '#skF_3') | k1_lattices('#skF_1', B_47, '#skF_3')!='#skF_3' | ~m1_subset_1(B_47, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_68])).
% 3.84/1.67  tff(c_78, plain, (![B_47]: (r1_lattices('#skF_1', B_47, '#skF_3') | k1_lattices('#skF_1', B_47, '#skF_3')!='#skF_3' | ~m1_subset_1(B_47, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_72])).
% 3.84/1.67  tff(c_84, plain, (![B_49]: (r1_lattices('#skF_1', B_49, '#skF_3') | k1_lattices('#skF_1', B_49, '#skF_3')!='#skF_3' | ~m1_subset_1(B_49, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_78])).
% 3.84/1.67  tff(c_100, plain, (r1_lattices('#skF_1', '#skF_2', '#skF_3') | k1_lattices('#skF_1', '#skF_2', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_42, c_84])).
% 3.84/1.67  tff(c_102, plain, (k1_lattices('#skF_1', '#skF_2', '#skF_3')!='#skF_3'), inference(splitLeft, [status(thm)], [c_100])).
% 3.84/1.67  tff(c_38, plain, (r3_lattices('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.84/1.67  tff(c_292, plain, (![A_71, B_72, C_73]: (r1_lattices(A_71, B_72, C_73) | ~r3_lattices(A_71, B_72, C_73) | ~m1_subset_1(C_73, u1_struct_0(A_71)) | ~m1_subset_1(B_72, u1_struct_0(A_71)) | ~l3_lattices(A_71) | ~v9_lattices(A_71) | ~v8_lattices(A_71) | ~v6_lattices(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.84/1.67  tff(c_294, plain, (r1_lattices('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_292])).
% 3.84/1.67  tff(c_297, plain, (r1_lattices('#skF_1', '#skF_2', '#skF_3') | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_294])).
% 3.84/1.67  tff(c_298, plain, (r1_lattices('#skF_1', '#skF_2', '#skF_3') | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_297])).
% 3.84/1.67  tff(c_299, plain, (~v6_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_298])).
% 3.84/1.67  tff(c_318, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_8, c_299])).
% 3.84/1.67  tff(c_321, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_318])).
% 3.84/1.67  tff(c_323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_321])).
% 3.84/1.67  tff(c_324, plain, (~v8_lattices('#skF_1') | ~v9_lattices('#skF_1') | r1_lattices('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_298])).
% 3.84/1.67  tff(c_326, plain, (~v9_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_324])).
% 3.84/1.67  tff(c_329, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_2, c_326])).
% 3.84/1.67  tff(c_332, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_329])).
% 3.84/1.67  tff(c_334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_332])).
% 3.84/1.67  tff(c_335, plain, (~v8_lattices('#skF_1') | r1_lattices('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_324])).
% 3.84/1.67  tff(c_337, plain, (~v8_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_335])).
% 3.84/1.67  tff(c_340, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_4, c_337])).
% 3.84/1.67  tff(c_343, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_340])).
% 3.84/1.67  tff(c_345, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_343])).
% 3.84/1.67  tff(c_346, plain, (r1_lattices('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_335])).
% 3.84/1.67  tff(c_18, plain, (![A_2, B_6, C_8]: (k1_lattices(A_2, B_6, C_8)=C_8 | ~r1_lattices(A_2, B_6, C_8) | ~m1_subset_1(C_8, u1_struct_0(A_2)) | ~m1_subset_1(B_6, u1_struct_0(A_2)) | ~l2_lattices(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.84/1.67  tff(c_349, plain, (k1_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_346, c_18])).
% 3.84/1.67  tff(c_352, plain, (k1_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_3' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_42, c_40, c_349])).
% 3.84/1.67  tff(c_354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_102, c_352])).
% 3.84/1.67  tff(c_356, plain, (k1_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_100])).
% 3.84/1.67  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.84/1.67  tff(c_395, plain, (![A_82, B_83, C_84]: (k3_lattices(A_82, B_83, C_84)=k1_lattices(A_82, B_83, C_84) | ~m1_subset_1(C_84, u1_struct_0(A_82)) | ~m1_subset_1(B_83, u1_struct_0(A_82)) | ~l2_lattices(A_82) | ~v4_lattices(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.84/1.67  tff(c_399, plain, (![B_83]: (k3_lattices('#skF_1', B_83, '#skF_3')=k1_lattices('#skF_1', B_83, '#skF_3') | ~m1_subset_1(B_83, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_395])).
% 3.84/1.67  tff(c_405, plain, (![B_83]: (k3_lattices('#skF_1', B_83, '#skF_3')=k1_lattices('#skF_1', B_83, '#skF_3') | ~m1_subset_1(B_83, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_399])).
% 3.84/1.67  tff(c_406, plain, (![B_83]: (k3_lattices('#skF_1', B_83, '#skF_3')=k1_lattices('#skF_1', B_83, '#skF_3') | ~m1_subset_1(B_83, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_50, c_405])).
% 3.84/1.67  tff(c_411, plain, (~v4_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_406])).
% 3.84/1.67  tff(c_414, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_12, c_411])).
% 3.84/1.67  tff(c_417, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_414])).
% 3.84/1.67  tff(c_419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_417])).
% 3.84/1.67  tff(c_449, plain, (![B_86]: (k3_lattices('#skF_1', B_86, '#skF_3')=k1_lattices('#skF_1', B_86, '#skF_3') | ~m1_subset_1(B_86, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_406])).
% 3.84/1.67  tff(c_459, plain, (k3_lattices('#skF_1', '#skF_2', '#skF_3')=k1_lattices('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_449])).
% 3.84/1.67  tff(c_466, plain, (k3_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_356, c_459])).
% 3.84/1.67  tff(c_649, plain, (![A_105, B_106, C_107]: (k4_lattices(A_105, k7_lattices(A_105, B_106), k7_lattices(A_105, C_107))=k7_lattices(A_105, k3_lattices(A_105, B_106, C_107)) | ~m1_subset_1(C_107, u1_struct_0(A_105)) | ~m1_subset_1(B_106, u1_struct_0(A_105)) | ~l3_lattices(A_105) | ~v17_lattices(A_105) | ~v10_lattices(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.84/1.67  tff(c_32, plain, (![A_18, B_22, C_24]: (r1_lattices(A_18, k4_lattices(A_18, B_22, C_24), B_22) | ~m1_subset_1(C_24, u1_struct_0(A_18)) | ~m1_subset_1(B_22, u1_struct_0(A_18)) | ~l3_lattices(A_18) | ~v8_lattices(A_18) | ~v6_lattices(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.84/1.67  tff(c_997, plain, (![A_132, B_133, C_134]: (r1_lattices(A_132, k7_lattices(A_132, k3_lattices(A_132, B_133, C_134)), k7_lattices(A_132, B_133)) | ~m1_subset_1(k7_lattices(A_132, C_134), u1_struct_0(A_132)) | ~m1_subset_1(k7_lattices(A_132, B_133), u1_struct_0(A_132)) | ~l3_lattices(A_132) | ~v8_lattices(A_132) | ~v6_lattices(A_132) | v2_struct_0(A_132) | ~m1_subset_1(C_134, u1_struct_0(A_132)) | ~m1_subset_1(B_133, u1_struct_0(A_132)) | ~l3_lattices(A_132) | ~v17_lattices(A_132) | ~v10_lattices(A_132) | v2_struct_0(A_132))), inference(superposition, [status(thm), theory('equality')], [c_649, c_32])).
% 3.84/1.67  tff(c_1053, plain, (r1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2')) | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1')) | ~m1_subset_1(k7_lattices('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_466, c_997])).
% 3.84/1.67  tff(c_1113, plain, (r1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2')) | ~m1_subset_1(k7_lattices('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_587, c_630, c_44, c_810, c_1053])).
% 3.84/1.67  tff(c_1114, plain, (~m1_subset_1(k7_lattices('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_50, c_809, c_1113])).
% 3.84/1.67  tff(c_1123, plain, (~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_1114])).
% 3.84/1.67  tff(c_1126, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1123])).
% 3.84/1.67  tff(c_1128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1126])).
% 3.84/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.67  
% 3.84/1.67  Inference rules
% 3.84/1.67  ----------------------
% 3.84/1.67  #Ref     : 0
% 3.84/1.67  #Sup     : 212
% 3.84/1.67  #Fact    : 0
% 3.84/1.67  #Define  : 0
% 3.84/1.67  #Split   : 22
% 3.84/1.67  #Chain   : 0
% 3.84/1.67  #Close   : 0
% 3.84/1.67  
% 3.84/1.67  Ordering : KBO
% 3.84/1.67  
% 3.84/1.67  Simplification rules
% 3.84/1.67  ----------------------
% 3.84/1.67  #Subsume      : 2
% 3.84/1.67  #Demod        : 292
% 3.84/1.67  #Tautology    : 92
% 3.84/1.67  #SimpNegUnit  : 77
% 3.84/1.67  #BackRed      : 0
% 3.84/1.67  
% 3.84/1.67  #Partial instantiations: 0
% 3.84/1.67  #Strategies tried      : 1
% 3.84/1.67  
% 3.84/1.67  Timing (in seconds)
% 3.84/1.67  ----------------------
% 3.84/1.67  Preprocessing        : 0.35
% 3.84/1.67  Parsing              : 0.19
% 3.84/1.67  CNF conversion       : 0.02
% 3.84/1.67  Main loop            : 0.48
% 3.84/1.67  Inferencing          : 0.17
% 3.84/1.67  Reduction            : 0.16
% 3.84/1.67  Demodulation         : 0.11
% 3.84/1.67  BG Simplification    : 0.02
% 3.84/1.67  Subsumption          : 0.08
% 3.84/1.67  Abstraction          : 0.03
% 3.84/1.67  MUC search           : 0.00
% 3.84/1.67  Cooper               : 0.00
% 3.84/1.67  Total                : 0.87
% 3.84/1.67  Index Insertion      : 0.00
% 3.84/1.67  Index Deletion       : 0.00
% 3.84/1.67  Index Matching       : 0.00
% 3.84/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
