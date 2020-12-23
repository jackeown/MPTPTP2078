%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:15 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 482 expanded)
%              Number of leaves         :   35 ( 183 expanded)
%              Depth                    :   17
%              Number of atoms          :  262 (1557 expanded)
%              Number of equality atoms :   45 ( 245 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v13_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k3_lattices(A,k5_lattices(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_lattices)).

tff(f_94,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

tff(f_81,axiom,(
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

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => ( v13_lattices(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( B = k5_lattices(A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( k2_lattices(A,B,C) = B
                    & k2_lattices(A,C,B) = B ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

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

tff(f_120,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(f_137,axiom,(
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

tff(f_107,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_40,plain,(
    k3_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_44,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_51,plain,(
    ! [A_35] :
      ( l1_lattices(A_35)
      | ~ l3_lattices(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_55,plain,(
    l1_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_51])).

tff(c_28,plain,(
    ! [A_19] :
      ( m1_subset_1(k5_lattices(A_19),u1_struct_0(A_19))
      | ~ l1_lattices(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_56,plain,(
    ! [A_36] :
      ( l2_lattices(A_36)
      | ~ l3_lattices(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_60,plain,(
    l2_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_56])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_70,plain,(
    ! [A_49,B_50,C_51] :
      ( r1_lattices(A_49,B_50,C_51)
      | k1_lattices(A_49,B_50,C_51) != C_51
      | ~ m1_subset_1(C_51,u1_struct_0(A_49))
      | ~ m1_subset_1(B_50,u1_struct_0(A_49))
      | ~ l2_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_76,plain,(
    ! [B_50] :
      ( r1_lattices('#skF_2',B_50,'#skF_3')
      | k1_lattices('#skF_2',B_50,'#skF_3') != '#skF_3'
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_2'))
      | ~ l2_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_70])).

tff(c_81,plain,(
    ! [B_50] :
      ( r1_lattices('#skF_2',B_50,'#skF_3')
      | k1_lattices('#skF_2',B_50,'#skF_3') != '#skF_3'
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_76])).

tff(c_83,plain,(
    ! [B_52] :
      ( r1_lattices('#skF_2',B_52,'#skF_3')
      | k1_lattices('#skF_2',B_52,'#skF_3') != '#skF_3'
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_81])).

tff(c_91,plain,
    ( r1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3')
    | k1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') != '#skF_3'
    | ~ l1_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_83])).

tff(c_101,plain,
    ( r1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3')
    | k1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') != '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_91])).

tff(c_102,plain,
    ( r1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3')
    | k1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_101])).

tff(c_105,plain,(
    k1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_46,plain,(
    v13_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_597,plain,(
    ! [A_91,C_92] :
      ( k2_lattices(A_91,k5_lattices(A_91),C_92) = k5_lattices(A_91)
      | ~ m1_subset_1(C_92,u1_struct_0(A_91))
      | ~ m1_subset_1(k5_lattices(A_91),u1_struct_0(A_91))
      | ~ v13_lattices(A_91)
      | ~ l1_lattices(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_603,plain,
    ( k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v13_lattices('#skF_2')
    | ~ l1_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_597])).

tff(c_608,plain,
    ( k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_46,c_603])).

tff(c_609,plain,
    ( k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_608])).

tff(c_610,plain,(
    ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_609])).

tff(c_613,plain,
    ( ~ l1_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_610])).

tff(c_616,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_613])).

tff(c_618,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_616])).

tff(c_620,plain,(
    m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_609])).

tff(c_48,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
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

tff(c_507,plain,(
    ! [A_85,B_86,C_87] :
      ( k4_lattices(A_85,B_86,C_87) = k2_lattices(A_85,B_86,C_87)
      | ~ m1_subset_1(C_87,u1_struct_0(A_85))
      | ~ m1_subset_1(B_86,u1_struct_0(A_85))
      | ~ l1_lattices(A_85)
      | ~ v6_lattices(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_513,plain,(
    ! [B_86] :
      ( k4_lattices('#skF_2',B_86,'#skF_3') = k2_lattices('#skF_2',B_86,'#skF_3')
      | ~ m1_subset_1(B_86,u1_struct_0('#skF_2'))
      | ~ l1_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_507])).

tff(c_518,plain,(
    ! [B_86] :
      ( k4_lattices('#skF_2',B_86,'#skF_3') = k2_lattices('#skF_2',B_86,'#skF_3')
      | ~ m1_subset_1(B_86,u1_struct_0('#skF_2'))
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_513])).

tff(c_519,plain,(
    ! [B_86] :
      ( k4_lattices('#skF_2',B_86,'#skF_3') = k2_lattices('#skF_2',B_86,'#skF_3')
      | ~ m1_subset_1(B_86,u1_struct_0('#skF_2'))
      | ~ v6_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_518])).

tff(c_524,plain,(
    ~ v6_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_519])).

tff(c_527,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_524])).

tff(c_530,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_527])).

tff(c_532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_530])).

tff(c_534,plain,(
    v6_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_519])).

tff(c_715,plain,(
    ! [A_94,C_95] :
      ( k2_lattices(A_94,C_95,k5_lattices(A_94)) = k5_lattices(A_94)
      | ~ m1_subset_1(C_95,u1_struct_0(A_94))
      | ~ m1_subset_1(k5_lattices(A_94),u1_struct_0(A_94))
      | ~ v13_lattices(A_94)
      | ~ l1_lattices(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_723,plain,
    ( k2_lattices('#skF_2','#skF_3',k5_lattices('#skF_2')) = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v13_lattices('#skF_2')
    | ~ l1_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_715])).

tff(c_732,plain,
    ( k2_lattices('#skF_2','#skF_3',k5_lattices('#skF_2')) = k5_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_46,c_620,c_723])).

tff(c_733,plain,(
    k2_lattices('#skF_2','#skF_3',k5_lattices('#skF_2')) = k5_lattices('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_732])).

tff(c_36,plain,(
    ! [A_24,B_25,C_26] :
      ( k4_lattices(A_24,B_25,C_26) = k2_lattices(A_24,B_25,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_24))
      | ~ m1_subset_1(B_25,u1_struct_0(A_24))
      | ~ l1_lattices(A_24)
      | ~ v6_lattices(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_630,plain,(
    ! [B_25] :
      ( k4_lattices('#skF_2',B_25,k5_lattices('#skF_2')) = k2_lattices('#skF_2',B_25,k5_lattices('#skF_2'))
      | ~ m1_subset_1(B_25,u1_struct_0('#skF_2'))
      | ~ l1_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_620,c_36])).

tff(c_654,plain,(
    ! [B_25] :
      ( k4_lattices('#skF_2',B_25,k5_lattices('#skF_2')) = k2_lattices('#skF_2',B_25,k5_lattices('#skF_2'))
      | ~ m1_subset_1(B_25,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_55,c_630])).

tff(c_743,plain,(
    ! [B_96] :
      ( k4_lattices('#skF_2',B_96,k5_lattices('#skF_2')) = k2_lattices('#skF_2',B_96,k5_lattices('#skF_2'))
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_654])).

tff(c_757,plain,(
    k4_lattices('#skF_2','#skF_3',k5_lattices('#skF_2')) = k2_lattices('#skF_2','#skF_3',k5_lattices('#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_743])).

tff(c_769,plain,(
    k4_lattices('#skF_2','#skF_3',k5_lattices('#skF_2')) = k5_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_733,c_757])).

tff(c_796,plain,(
    ! [A_99,B_100,C_101] :
      ( r1_lattices(A_99,k4_lattices(A_99,B_100,C_101),B_100)
      | ~ m1_subset_1(C_101,u1_struct_0(A_99))
      | ~ m1_subset_1(B_100,u1_struct_0(A_99))
      | ~ l3_lattices(A_99)
      | ~ v8_lattices(A_99)
      | ~ v6_lattices(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_804,plain,
    ( r1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v8_lattices('#skF_2')
    | ~ v6_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_796])).

tff(c_819,plain,
    ( r1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3')
    | ~ v8_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_44,c_42,c_620,c_804])).

tff(c_820,plain,
    ( r1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3')
    | ~ v8_lattices('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_819])).

tff(c_830,plain,(
    ~ v8_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_820])).

tff(c_833,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_830])).

tff(c_836,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_833])).

tff(c_838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_836])).

tff(c_839,plain,(
    r1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_820])).

tff(c_26,plain,(
    ! [A_12,B_16,C_18] :
      ( k1_lattices(A_12,B_16,C_18) = C_18
      | ~ r1_lattices(A_12,B_16,C_18)
      | ~ m1_subset_1(C_18,u1_struct_0(A_12))
      | ~ m1_subset_1(B_16,u1_struct_0(A_12))
      | ~ l2_lattices(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_850,plain,
    ( k1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | ~ l2_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_839,c_26])).

tff(c_853,plain,
    ( k1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_620,c_42,c_850])).

tff(c_855,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_105,c_853])).

tff(c_857,plain,(
    k1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_876,plain,(
    ! [A_103,B_104,C_105] :
      ( k3_lattices(A_103,B_104,C_105) = k1_lattices(A_103,B_104,C_105)
      | ~ m1_subset_1(C_105,u1_struct_0(A_103))
      | ~ m1_subset_1(B_104,u1_struct_0(A_103))
      | ~ l2_lattices(A_103)
      | ~ v4_lattices(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_882,plain,(
    ! [B_104] :
      ( k3_lattices('#skF_2',B_104,'#skF_3') = k1_lattices('#skF_2',B_104,'#skF_3')
      | ~ m1_subset_1(B_104,u1_struct_0('#skF_2'))
      | ~ l2_lattices('#skF_2')
      | ~ v4_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_876])).

tff(c_887,plain,(
    ! [B_104] :
      ( k3_lattices('#skF_2',B_104,'#skF_3') = k1_lattices('#skF_2',B_104,'#skF_3')
      | ~ m1_subset_1(B_104,u1_struct_0('#skF_2'))
      | ~ v4_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_882])).

tff(c_888,plain,(
    ! [B_104] :
      ( k3_lattices('#skF_2',B_104,'#skF_3') = k1_lattices('#skF_2',B_104,'#skF_3')
      | ~ m1_subset_1(B_104,u1_struct_0('#skF_2'))
      | ~ v4_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_887])).

tff(c_889,plain,(
    ~ v4_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_888])).

tff(c_892,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_889])).

tff(c_895,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_892])).

tff(c_897,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_895])).

tff(c_900,plain,(
    ! [B_106] :
      ( k3_lattices('#skF_2',B_106,'#skF_3') = k1_lattices('#skF_2',B_106,'#skF_3')
      | ~ m1_subset_1(B_106,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_888])).

tff(c_908,plain,
    ( k3_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3')
    | ~ l1_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_900])).

tff(c_918,plain,
    ( k3_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_857,c_908])).

tff(c_920,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40,c_918])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:08:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.57  
% 3.28/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.57  %$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_3 > #skF_1
% 3.28/1.57  
% 3.28/1.57  %Foreground sorts:
% 3.28/1.57  
% 3.28/1.57  
% 3.28/1.57  %Background operators:
% 3.28/1.57  
% 3.28/1.57  
% 3.28/1.57  %Foreground operators:
% 3.28/1.57  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.28/1.57  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 3.28/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.28/1.57  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 3.28/1.57  tff(l2_lattices, type, l2_lattices: $i > $o).
% 3.28/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.57  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 3.28/1.57  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 3.28/1.57  tff(l1_lattices, type, l1_lattices: $i > $o).
% 3.28/1.57  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 3.28/1.57  tff(v4_lattices, type, v4_lattices: $i > $o).
% 3.28/1.57  tff(v6_lattices, type, v6_lattices: $i > $o).
% 3.28/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.28/1.57  tff(v9_lattices, type, v9_lattices: $i > $o).
% 3.28/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.57  tff(v5_lattices, type, v5_lattices: $i > $o).
% 3.28/1.57  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.28/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.57  tff(v13_lattices, type, v13_lattices: $i > $o).
% 3.28/1.57  tff(v8_lattices, type, v8_lattices: $i > $o).
% 3.28/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.57  tff(k5_lattices, type, k5_lattices: $i > $i).
% 3.28/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.28/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.28/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.57  tff(v7_lattices, type, v7_lattices: $i > $o).
% 3.28/1.57  
% 3.28/1.59  tff(f_152, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_lattices(A, k5_lattices(A), B) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_lattices)).
% 3.28/1.59  tff(f_94, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 3.28/1.59  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 3.28/1.59  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 3.28/1.59  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 3.28/1.59  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 3.28/1.59  tff(f_120, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 3.28/1.59  tff(f_137, axiom, (![A]: ((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => r1_lattices(A, k4_lattices(A, B, C), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_lattices)).
% 3.28/1.59  tff(f_107, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 3.28/1.59  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.28/1.59  tff(c_40, plain, (k3_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.28/1.59  tff(c_44, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.28/1.59  tff(c_51, plain, (![A_35]: (l1_lattices(A_35) | ~l3_lattices(A_35))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.28/1.59  tff(c_55, plain, (l1_lattices('#skF_2')), inference(resolution, [status(thm)], [c_44, c_51])).
% 3.28/1.59  tff(c_28, plain, (![A_19]: (m1_subset_1(k5_lattices(A_19), u1_struct_0(A_19)) | ~l1_lattices(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.28/1.59  tff(c_56, plain, (![A_36]: (l2_lattices(A_36) | ~l3_lattices(A_36))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.28/1.59  tff(c_60, plain, (l2_lattices('#skF_2')), inference(resolution, [status(thm)], [c_44, c_56])).
% 3.28/1.59  tff(c_42, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.28/1.59  tff(c_70, plain, (![A_49, B_50, C_51]: (r1_lattices(A_49, B_50, C_51) | k1_lattices(A_49, B_50, C_51)!=C_51 | ~m1_subset_1(C_51, u1_struct_0(A_49)) | ~m1_subset_1(B_50, u1_struct_0(A_49)) | ~l2_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.28/1.59  tff(c_76, plain, (![B_50]: (r1_lattices('#skF_2', B_50, '#skF_3') | k1_lattices('#skF_2', B_50, '#skF_3')!='#skF_3' | ~m1_subset_1(B_50, u1_struct_0('#skF_2')) | ~l2_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_70])).
% 3.28/1.59  tff(c_81, plain, (![B_50]: (r1_lattices('#skF_2', B_50, '#skF_3') | k1_lattices('#skF_2', B_50, '#skF_3')!='#skF_3' | ~m1_subset_1(B_50, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_76])).
% 3.28/1.59  tff(c_83, plain, (![B_52]: (r1_lattices('#skF_2', B_52, '#skF_3') | k1_lattices('#skF_2', B_52, '#skF_3')!='#skF_3' | ~m1_subset_1(B_52, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_81])).
% 3.28/1.59  tff(c_91, plain, (r1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3') | k1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')!='#skF_3' | ~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_83])).
% 3.28/1.59  tff(c_101, plain, (r1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3') | k1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')!='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_91])).
% 3.28/1.59  tff(c_102, plain, (r1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3') | k1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_50, c_101])).
% 3.28/1.59  tff(c_105, plain, (k1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')!='#skF_3'), inference(splitLeft, [status(thm)], [c_102])).
% 3.28/1.59  tff(c_46, plain, (v13_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.28/1.59  tff(c_597, plain, (![A_91, C_92]: (k2_lattices(A_91, k5_lattices(A_91), C_92)=k5_lattices(A_91) | ~m1_subset_1(C_92, u1_struct_0(A_91)) | ~m1_subset_1(k5_lattices(A_91), u1_struct_0(A_91)) | ~v13_lattices(A_91) | ~l1_lattices(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.28/1.59  tff(c_603, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | ~v13_lattices('#skF_2') | ~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_597])).
% 3.28/1.59  tff(c_608, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_46, c_603])).
% 3.28/1.59  tff(c_609, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_608])).
% 3.28/1.59  tff(c_610, plain, (~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_609])).
% 3.28/1.59  tff(c_613, plain, (~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_610])).
% 3.28/1.59  tff(c_616, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_613])).
% 3.28/1.59  tff(c_618, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_616])).
% 3.28/1.59  tff(c_620, plain, (m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_609])).
% 3.28/1.59  tff(c_48, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.28/1.59  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.28/1.59  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.28/1.59  tff(c_507, plain, (![A_85, B_86, C_87]: (k4_lattices(A_85, B_86, C_87)=k2_lattices(A_85, B_86, C_87) | ~m1_subset_1(C_87, u1_struct_0(A_85)) | ~m1_subset_1(B_86, u1_struct_0(A_85)) | ~l1_lattices(A_85) | ~v6_lattices(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.28/1.59  tff(c_513, plain, (![B_86]: (k4_lattices('#skF_2', B_86, '#skF_3')=k2_lattices('#skF_2', B_86, '#skF_3') | ~m1_subset_1(B_86, u1_struct_0('#skF_2')) | ~l1_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_507])).
% 3.28/1.59  tff(c_518, plain, (![B_86]: (k4_lattices('#skF_2', B_86, '#skF_3')=k2_lattices('#skF_2', B_86, '#skF_3') | ~m1_subset_1(B_86, u1_struct_0('#skF_2')) | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_513])).
% 3.28/1.59  tff(c_519, plain, (![B_86]: (k4_lattices('#skF_2', B_86, '#skF_3')=k2_lattices('#skF_2', B_86, '#skF_3') | ~m1_subset_1(B_86, u1_struct_0('#skF_2')) | ~v6_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_518])).
% 3.28/1.59  tff(c_524, plain, (~v6_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_519])).
% 3.28/1.59  tff(c_527, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_8, c_524])).
% 3.28/1.59  tff(c_530, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_527])).
% 3.28/1.59  tff(c_532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_530])).
% 3.28/1.59  tff(c_534, plain, (v6_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_519])).
% 3.28/1.59  tff(c_715, plain, (![A_94, C_95]: (k2_lattices(A_94, C_95, k5_lattices(A_94))=k5_lattices(A_94) | ~m1_subset_1(C_95, u1_struct_0(A_94)) | ~m1_subset_1(k5_lattices(A_94), u1_struct_0(A_94)) | ~v13_lattices(A_94) | ~l1_lattices(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.28/1.59  tff(c_723, plain, (k2_lattices('#skF_2', '#skF_3', k5_lattices('#skF_2'))=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | ~v13_lattices('#skF_2') | ~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_715])).
% 3.28/1.59  tff(c_732, plain, (k2_lattices('#skF_2', '#skF_3', k5_lattices('#skF_2'))=k5_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_46, c_620, c_723])).
% 3.28/1.59  tff(c_733, plain, (k2_lattices('#skF_2', '#skF_3', k5_lattices('#skF_2'))=k5_lattices('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_732])).
% 3.28/1.59  tff(c_36, plain, (![A_24, B_25, C_26]: (k4_lattices(A_24, B_25, C_26)=k2_lattices(A_24, B_25, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_24)) | ~m1_subset_1(B_25, u1_struct_0(A_24)) | ~l1_lattices(A_24) | ~v6_lattices(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.28/1.59  tff(c_630, plain, (![B_25]: (k4_lattices('#skF_2', B_25, k5_lattices('#skF_2'))=k2_lattices('#skF_2', B_25, k5_lattices('#skF_2')) | ~m1_subset_1(B_25, u1_struct_0('#skF_2')) | ~l1_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_620, c_36])).
% 3.28/1.59  tff(c_654, plain, (![B_25]: (k4_lattices('#skF_2', B_25, k5_lattices('#skF_2'))=k2_lattices('#skF_2', B_25, k5_lattices('#skF_2')) | ~m1_subset_1(B_25, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_534, c_55, c_630])).
% 3.28/1.59  tff(c_743, plain, (![B_96]: (k4_lattices('#skF_2', B_96, k5_lattices('#skF_2'))=k2_lattices('#skF_2', B_96, k5_lattices('#skF_2')) | ~m1_subset_1(B_96, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_654])).
% 3.28/1.59  tff(c_757, plain, (k4_lattices('#skF_2', '#skF_3', k5_lattices('#skF_2'))=k2_lattices('#skF_2', '#skF_3', k5_lattices('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_743])).
% 3.28/1.59  tff(c_769, plain, (k4_lattices('#skF_2', '#skF_3', k5_lattices('#skF_2'))=k5_lattices('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_733, c_757])).
% 3.28/1.59  tff(c_796, plain, (![A_99, B_100, C_101]: (r1_lattices(A_99, k4_lattices(A_99, B_100, C_101), B_100) | ~m1_subset_1(C_101, u1_struct_0(A_99)) | ~m1_subset_1(B_100, u1_struct_0(A_99)) | ~l3_lattices(A_99) | ~v8_lattices(A_99) | ~v6_lattices(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.28/1.59  tff(c_804, plain, (r1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_769, c_796])).
% 3.28/1.59  tff(c_819, plain, (r1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3') | ~v8_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_534, c_44, c_42, c_620, c_804])).
% 3.28/1.59  tff(c_820, plain, (r1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3') | ~v8_lattices('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_819])).
% 3.28/1.59  tff(c_830, plain, (~v8_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_820])).
% 3.28/1.59  tff(c_833, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_4, c_830])).
% 3.28/1.59  tff(c_836, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_833])).
% 3.28/1.59  tff(c_838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_836])).
% 3.28/1.59  tff(c_839, plain, (r1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_820])).
% 3.28/1.59  tff(c_26, plain, (![A_12, B_16, C_18]: (k1_lattices(A_12, B_16, C_18)=C_18 | ~r1_lattices(A_12, B_16, C_18) | ~m1_subset_1(C_18, u1_struct_0(A_12)) | ~m1_subset_1(B_16, u1_struct_0(A_12)) | ~l2_lattices(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.28/1.59  tff(c_850, plain, (k1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | ~l2_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_839, c_26])).
% 3.28/1.59  tff(c_853, plain, (k1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_620, c_42, c_850])).
% 3.28/1.59  tff(c_855, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_105, c_853])).
% 3.28/1.59  tff(c_857, plain, (k1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_102])).
% 3.28/1.59  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.28/1.59  tff(c_876, plain, (![A_103, B_104, C_105]: (k3_lattices(A_103, B_104, C_105)=k1_lattices(A_103, B_104, C_105) | ~m1_subset_1(C_105, u1_struct_0(A_103)) | ~m1_subset_1(B_104, u1_struct_0(A_103)) | ~l2_lattices(A_103) | ~v4_lattices(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.28/1.59  tff(c_882, plain, (![B_104]: (k3_lattices('#skF_2', B_104, '#skF_3')=k1_lattices('#skF_2', B_104, '#skF_3') | ~m1_subset_1(B_104, u1_struct_0('#skF_2')) | ~l2_lattices('#skF_2') | ~v4_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_876])).
% 3.28/1.59  tff(c_887, plain, (![B_104]: (k3_lattices('#skF_2', B_104, '#skF_3')=k1_lattices('#skF_2', B_104, '#skF_3') | ~m1_subset_1(B_104, u1_struct_0('#skF_2')) | ~v4_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_882])).
% 3.28/1.59  tff(c_888, plain, (![B_104]: (k3_lattices('#skF_2', B_104, '#skF_3')=k1_lattices('#skF_2', B_104, '#skF_3') | ~m1_subset_1(B_104, u1_struct_0('#skF_2')) | ~v4_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_887])).
% 3.28/1.59  tff(c_889, plain, (~v4_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_888])).
% 3.28/1.59  tff(c_892, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_12, c_889])).
% 3.28/1.59  tff(c_895, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_892])).
% 3.28/1.59  tff(c_897, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_895])).
% 3.28/1.59  tff(c_900, plain, (![B_106]: (k3_lattices('#skF_2', B_106, '#skF_3')=k1_lattices('#skF_2', B_106, '#skF_3') | ~m1_subset_1(B_106, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_888])).
% 3.28/1.59  tff(c_908, plain, (k3_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3') | ~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_900])).
% 3.28/1.59  tff(c_918, plain, (k3_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_857, c_908])).
% 3.28/1.59  tff(c_920, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_40, c_918])).
% 3.28/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.59  
% 3.28/1.59  Inference rules
% 3.28/1.59  ----------------------
% 3.28/1.59  #Ref     : 0
% 3.28/1.59  #Sup     : 168
% 3.28/1.59  #Fact    : 0
% 3.28/1.59  #Define  : 0
% 3.28/1.59  #Split   : 10
% 3.28/1.59  #Chain   : 0
% 3.28/1.59  #Close   : 0
% 3.28/1.59  
% 3.28/1.59  Ordering : KBO
% 3.28/1.59  
% 3.28/1.59  Simplification rules
% 3.28/1.59  ----------------------
% 3.28/1.59  #Subsume      : 7
% 3.28/1.59  #Demod        : 223
% 3.28/1.59  #Tautology    : 84
% 3.28/1.59  #SimpNegUnit  : 71
% 3.28/1.59  #BackRed      : 7
% 3.28/1.59  
% 3.28/1.59  #Partial instantiations: 0
% 3.28/1.59  #Strategies tried      : 1
% 3.28/1.59  
% 3.28/1.59  Timing (in seconds)
% 3.28/1.59  ----------------------
% 3.28/1.59  Preprocessing        : 0.35
% 3.28/1.59  Parsing              : 0.19
% 3.28/1.59  CNF conversion       : 0.02
% 3.28/1.59  Main loop            : 0.38
% 3.28/1.59  Inferencing          : 0.14
% 3.28/1.59  Reduction            : 0.12
% 3.28/1.59  Demodulation         : 0.08
% 3.28/1.59  BG Simplification    : 0.03
% 3.28/1.59  Subsumption          : 0.07
% 3.28/1.59  Abstraction          : 0.03
% 3.28/1.59  MUC search           : 0.00
% 3.28/1.59  Cooper               : 0.00
% 3.28/1.59  Total                : 0.77
% 3.28/1.59  Index Insertion      : 0.00
% 3.28/1.59  Index Deletion       : 0.00
% 3.28/1.59  Index Matching       : 0.00
% 3.28/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
