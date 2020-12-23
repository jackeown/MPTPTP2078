%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:15 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 394 expanded)
%              Number of leaves         :   33 ( 149 expanded)
%              Depth                    :   16
%              Number of atoms          :  266 (1327 expanded)
%              Number of equality atoms :   47 ( 209 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k3_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_3 > #skF_1

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

tff(f_141,negated_conjecture,(
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

tff(f_126,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(c_40,plain,(
    k3_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_44,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_51,plain,(
    ! [A_32] :
      ( l1_lattices(A_32)
      | ~ l3_lattices(A_32) ) ),
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
    ! [A_33] :
      ( l2_lattices(A_33)
      | ~ l3_lattices(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_60,plain,(
    l2_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_56])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_70,plain,(
    ! [A_46,B_47,C_48] :
      ( r1_lattices(A_46,B_47,C_48)
      | k1_lattices(A_46,B_47,C_48) != C_48
      | ~ m1_subset_1(C_48,u1_struct_0(A_46))
      | ~ m1_subset_1(B_47,u1_struct_0(A_46))
      | ~ l2_lattices(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_76,plain,(
    ! [B_47] :
      ( r1_lattices('#skF_2',B_47,'#skF_3')
      | k1_lattices('#skF_2',B_47,'#skF_3') != '#skF_3'
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2'))
      | ~ l2_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_70])).

tff(c_81,plain,(
    ! [B_47] :
      ( r1_lattices('#skF_2',B_47,'#skF_3')
      | k1_lattices('#skF_2',B_47,'#skF_3') != '#skF_3'
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_76])).

tff(c_83,plain,(
    ! [B_49] :
      ( r1_lattices('#skF_2',B_49,'#skF_3')
      | k1_lattices('#skF_2',B_49,'#skF_3') != '#skF_3'
      | ~ m1_subset_1(B_49,u1_struct_0('#skF_2')) ) ),
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
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_106,plain,(
    ! [A_50,C_51] :
      ( k2_lattices(A_50,k5_lattices(A_50),C_51) = k5_lattices(A_50)
      | ~ m1_subset_1(C_51,u1_struct_0(A_50))
      | ~ m1_subset_1(k5_lattices(A_50),u1_struct_0(A_50))
      | ~ v13_lattices(A_50)
      | ~ l1_lattices(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_112,plain,
    ( k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v13_lattices('#skF_2')
    | ~ l1_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_106])).

tff(c_117,plain,
    ( k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_46,c_112])).

tff(c_118,plain,
    ( k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_117])).

tff(c_119,plain,(
    ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_122,plain,
    ( ~ l1_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_119])).

tff(c_125,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_122])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_125])).

tff(c_129,plain,(
    m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_128,plain,(
    k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_48,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_571,plain,(
    ! [A_81,B_82,C_83] :
      ( r1_lattices(A_81,B_82,C_83)
      | k2_lattices(A_81,B_82,C_83) != B_82
      | ~ m1_subset_1(C_83,u1_struct_0(A_81))
      | ~ m1_subset_1(B_82,u1_struct_0(A_81))
      | ~ l3_lattices(A_81)
      | ~ v9_lattices(A_81)
      | ~ v8_lattices(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_579,plain,(
    ! [B_82] :
      ( r1_lattices('#skF_2',B_82,'#skF_3')
      | k2_lattices('#skF_2',B_82,'#skF_3') != B_82
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_2'))
      | ~ l3_lattices('#skF_2')
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_571])).

tff(c_588,plain,(
    ! [B_82] :
      ( r1_lattices('#skF_2',B_82,'#skF_3')
      | k2_lattices('#skF_2',B_82,'#skF_3') != B_82
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_579])).

tff(c_589,plain,(
    ! [B_82] :
      ( r1_lattices('#skF_2',B_82,'#skF_3')
      | k2_lattices('#skF_2',B_82,'#skF_3') != B_82
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_588])).

tff(c_590,plain,(
    ~ v8_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_589])).

tff(c_593,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_590])).

tff(c_596,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_593])).

tff(c_598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_596])).

tff(c_600,plain,(
    v8_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_589])).

tff(c_573,plain,(
    ! [B_82] :
      ( r1_lattices('#skF_2',B_82,k5_lattices('#skF_2'))
      | k2_lattices('#skF_2',B_82,k5_lattices('#skF_2')) != B_82
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_2'))
      | ~ l3_lattices('#skF_2')
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_129,c_571])).

tff(c_582,plain,(
    ! [B_82] :
      ( r1_lattices('#skF_2',B_82,k5_lattices('#skF_2'))
      | k2_lattices('#skF_2',B_82,k5_lattices('#skF_2')) != B_82
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_573])).

tff(c_583,plain,(
    ! [B_82] :
      ( r1_lattices('#skF_2',B_82,k5_lattices('#skF_2'))
      | k2_lattices('#skF_2',B_82,k5_lattices('#skF_2')) != B_82
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_582])).

tff(c_602,plain,(
    ! [B_82] :
      ( r1_lattices('#skF_2',B_82,k5_lattices('#skF_2'))
      | k2_lattices('#skF_2',B_82,k5_lattices('#skF_2')) != B_82
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_583])).

tff(c_603,plain,(
    ~ v9_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_602])).

tff(c_606,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_603])).

tff(c_609,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_606])).

tff(c_611,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_609])).

tff(c_613,plain,(
    v9_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_602])).

tff(c_599,plain,(
    ! [B_82] :
      ( ~ v9_lattices('#skF_2')
      | r1_lattices('#skF_2',B_82,'#skF_3')
      | k2_lattices('#skF_2',B_82,'#skF_3') != B_82
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_589])).

tff(c_616,plain,(
    ! [B_84] :
      ( r1_lattices('#skF_2',B_84,'#skF_3')
      | k2_lattices('#skF_2',B_84,'#skF_3') != B_84
      | ~ m1_subset_1(B_84,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_599])).

tff(c_619,plain,
    ( r1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3')
    | k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') != k5_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_129,c_616])).

tff(c_633,plain,(
    r1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_619])).

tff(c_26,plain,(
    ! [A_12,B_16,C_18] :
      ( k1_lattices(A_12,B_16,C_18) = C_18
      | ~ r1_lattices(A_12,B_16,C_18)
      | ~ m1_subset_1(C_18,u1_struct_0(A_12))
      | ~ m1_subset_1(B_16,u1_struct_0(A_12))
      | ~ l2_lattices(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_646,plain,
    ( k1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | ~ l2_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_633,c_26])).

tff(c_653,plain,
    ( k1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_129,c_42,c_646])).

tff(c_655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_105,c_653])).

tff(c_657,plain,(
    k1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_664,plain,(
    ! [A_85,C_86] :
      ( k2_lattices(A_85,k5_lattices(A_85),C_86) = k5_lattices(A_85)
      | ~ m1_subset_1(C_86,u1_struct_0(A_85))
      | ~ m1_subset_1(k5_lattices(A_85),u1_struct_0(A_85))
      | ~ v13_lattices(A_85)
      | ~ l1_lattices(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_670,plain,
    ( k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v13_lattices('#skF_2')
    | ~ l1_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_664])).

tff(c_675,plain,
    ( k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_46,c_670])).

tff(c_676,plain,
    ( k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_675])).

tff(c_682,plain,(
    ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_676])).

tff(c_692,plain,
    ( ~ l1_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_682])).

tff(c_695,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_692])).

tff(c_697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_695])).

tff(c_699,plain,(
    m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_676])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_796,plain,(
    ! [A_94,B_95,C_96] :
      ( k3_lattices(A_94,B_95,C_96) = k1_lattices(A_94,B_95,C_96)
      | ~ m1_subset_1(C_96,u1_struct_0(A_94))
      | ~ m1_subset_1(B_95,u1_struct_0(A_94))
      | ~ l2_lattices(A_94)
      | ~ v4_lattices(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_804,plain,(
    ! [B_95] :
      ( k3_lattices('#skF_2',B_95,'#skF_3') = k1_lattices('#skF_2',B_95,'#skF_3')
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_2'))
      | ~ l2_lattices('#skF_2')
      | ~ v4_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_796])).

tff(c_813,plain,(
    ! [B_95] :
      ( k3_lattices('#skF_2',B_95,'#skF_3') = k1_lattices('#skF_2',B_95,'#skF_3')
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_2'))
      | ~ v4_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_804])).

tff(c_814,plain,(
    ! [B_95] :
      ( k3_lattices('#skF_2',B_95,'#skF_3') = k1_lattices('#skF_2',B_95,'#skF_3')
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_2'))
      | ~ v4_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_813])).

tff(c_815,plain,(
    ~ v4_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_814])).

tff(c_818,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_815])).

tff(c_821,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_818])).

tff(c_823,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_821])).

tff(c_845,plain,(
    ! [B_100] :
      ( k3_lattices('#skF_2',B_100,'#skF_3') = k1_lattices('#skF_2',B_100,'#skF_3')
      | ~ m1_subset_1(B_100,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_814])).

tff(c_848,plain,(
    k3_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_699,c_845])).

tff(c_861,plain,(
    k3_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_848])).

tff(c_863,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_861])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:41:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.45  
% 3.06/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.45  %$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k3_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_3 > #skF_1
% 3.06/1.45  
% 3.06/1.45  %Foreground sorts:
% 3.06/1.45  
% 3.06/1.45  
% 3.06/1.45  %Background operators:
% 3.06/1.45  
% 3.06/1.45  
% 3.06/1.45  %Foreground operators:
% 3.06/1.45  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.06/1.45  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 3.06/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.06/1.45  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 3.06/1.45  tff(l2_lattices, type, l2_lattices: $i > $o).
% 3.06/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.45  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 3.06/1.45  tff(l1_lattices, type, l1_lattices: $i > $o).
% 3.06/1.45  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 3.06/1.45  tff(v4_lattices, type, v4_lattices: $i > $o).
% 3.06/1.45  tff(v6_lattices, type, v6_lattices: $i > $o).
% 3.06/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.06/1.45  tff(v9_lattices, type, v9_lattices: $i > $o).
% 3.06/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.45  tff(v5_lattices, type, v5_lattices: $i > $o).
% 3.06/1.45  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.06/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.45  tff(v13_lattices, type, v13_lattices: $i > $o).
% 3.06/1.45  tff(v8_lattices, type, v8_lattices: $i > $o).
% 3.06/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.45  tff(k5_lattices, type, k5_lattices: $i > $i).
% 3.06/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.06/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.06/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.45  tff(v7_lattices, type, v7_lattices: $i > $o).
% 3.06/1.45  
% 3.21/1.47  tff(f_141, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_lattices(A, k5_lattices(A), B) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_lattices)).
% 3.21/1.47  tff(f_94, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 3.21/1.47  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 3.21/1.47  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 3.21/1.47  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 3.21/1.47  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 3.21/1.47  tff(f_126, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 3.21/1.47  tff(f_107, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 3.21/1.47  tff(c_40, plain, (k3_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.21/1.47  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.21/1.47  tff(c_44, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.21/1.47  tff(c_51, plain, (![A_32]: (l1_lattices(A_32) | ~l3_lattices(A_32))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.21/1.47  tff(c_55, plain, (l1_lattices('#skF_2')), inference(resolution, [status(thm)], [c_44, c_51])).
% 3.21/1.47  tff(c_28, plain, (![A_19]: (m1_subset_1(k5_lattices(A_19), u1_struct_0(A_19)) | ~l1_lattices(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.21/1.47  tff(c_56, plain, (![A_33]: (l2_lattices(A_33) | ~l3_lattices(A_33))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.21/1.47  tff(c_60, plain, (l2_lattices('#skF_2')), inference(resolution, [status(thm)], [c_44, c_56])).
% 3.21/1.47  tff(c_42, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.21/1.47  tff(c_70, plain, (![A_46, B_47, C_48]: (r1_lattices(A_46, B_47, C_48) | k1_lattices(A_46, B_47, C_48)!=C_48 | ~m1_subset_1(C_48, u1_struct_0(A_46)) | ~m1_subset_1(B_47, u1_struct_0(A_46)) | ~l2_lattices(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.21/1.47  tff(c_76, plain, (![B_47]: (r1_lattices('#skF_2', B_47, '#skF_3') | k1_lattices('#skF_2', B_47, '#skF_3')!='#skF_3' | ~m1_subset_1(B_47, u1_struct_0('#skF_2')) | ~l2_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_70])).
% 3.21/1.47  tff(c_81, plain, (![B_47]: (r1_lattices('#skF_2', B_47, '#skF_3') | k1_lattices('#skF_2', B_47, '#skF_3')!='#skF_3' | ~m1_subset_1(B_47, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_76])).
% 3.21/1.47  tff(c_83, plain, (![B_49]: (r1_lattices('#skF_2', B_49, '#skF_3') | k1_lattices('#skF_2', B_49, '#skF_3')!='#skF_3' | ~m1_subset_1(B_49, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_81])).
% 3.21/1.47  tff(c_91, plain, (r1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3') | k1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')!='#skF_3' | ~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_83])).
% 3.21/1.47  tff(c_101, plain, (r1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3') | k1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')!='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_91])).
% 3.21/1.47  tff(c_102, plain, (r1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3') | k1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_50, c_101])).
% 3.21/1.47  tff(c_105, plain, (k1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')!='#skF_3'), inference(splitLeft, [status(thm)], [c_102])).
% 3.21/1.47  tff(c_46, plain, (v13_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.21/1.47  tff(c_106, plain, (![A_50, C_51]: (k2_lattices(A_50, k5_lattices(A_50), C_51)=k5_lattices(A_50) | ~m1_subset_1(C_51, u1_struct_0(A_50)) | ~m1_subset_1(k5_lattices(A_50), u1_struct_0(A_50)) | ~v13_lattices(A_50) | ~l1_lattices(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.21/1.47  tff(c_112, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | ~v13_lattices('#skF_2') | ~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_106])).
% 3.21/1.47  tff(c_117, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_46, c_112])).
% 3.21/1.47  tff(c_118, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_117])).
% 3.21/1.47  tff(c_119, plain, (~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_118])).
% 3.21/1.47  tff(c_122, plain, (~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_119])).
% 3.21/1.47  tff(c_125, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_122])).
% 3.21/1.47  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_125])).
% 3.21/1.47  tff(c_129, plain, (m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_118])).
% 3.21/1.47  tff(c_128, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_118])).
% 3.21/1.47  tff(c_48, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.21/1.47  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.21/1.47  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.21/1.47  tff(c_571, plain, (![A_81, B_82, C_83]: (r1_lattices(A_81, B_82, C_83) | k2_lattices(A_81, B_82, C_83)!=B_82 | ~m1_subset_1(C_83, u1_struct_0(A_81)) | ~m1_subset_1(B_82, u1_struct_0(A_81)) | ~l3_lattices(A_81) | ~v9_lattices(A_81) | ~v8_lattices(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.21/1.47  tff(c_579, plain, (![B_82]: (r1_lattices('#skF_2', B_82, '#skF_3') | k2_lattices('#skF_2', B_82, '#skF_3')!=B_82 | ~m1_subset_1(B_82, u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_571])).
% 3.21/1.47  tff(c_588, plain, (![B_82]: (r1_lattices('#skF_2', B_82, '#skF_3') | k2_lattices('#skF_2', B_82, '#skF_3')!=B_82 | ~m1_subset_1(B_82, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_579])).
% 3.21/1.47  tff(c_589, plain, (![B_82]: (r1_lattices('#skF_2', B_82, '#skF_3') | k2_lattices('#skF_2', B_82, '#skF_3')!=B_82 | ~m1_subset_1(B_82, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_588])).
% 3.21/1.47  tff(c_590, plain, (~v8_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_589])).
% 3.21/1.47  tff(c_593, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_4, c_590])).
% 3.21/1.47  tff(c_596, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_593])).
% 3.21/1.47  tff(c_598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_596])).
% 3.21/1.47  tff(c_600, plain, (v8_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_589])).
% 3.21/1.47  tff(c_573, plain, (![B_82]: (r1_lattices('#skF_2', B_82, k5_lattices('#skF_2')) | k2_lattices('#skF_2', B_82, k5_lattices('#skF_2'))!=B_82 | ~m1_subset_1(B_82, u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_129, c_571])).
% 3.21/1.47  tff(c_582, plain, (![B_82]: (r1_lattices('#skF_2', B_82, k5_lattices('#skF_2')) | k2_lattices('#skF_2', B_82, k5_lattices('#skF_2'))!=B_82 | ~m1_subset_1(B_82, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_573])).
% 3.21/1.47  tff(c_583, plain, (![B_82]: (r1_lattices('#skF_2', B_82, k5_lattices('#skF_2')) | k2_lattices('#skF_2', B_82, k5_lattices('#skF_2'))!=B_82 | ~m1_subset_1(B_82, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_582])).
% 3.21/1.47  tff(c_602, plain, (![B_82]: (r1_lattices('#skF_2', B_82, k5_lattices('#skF_2')) | k2_lattices('#skF_2', B_82, k5_lattices('#skF_2'))!=B_82 | ~m1_subset_1(B_82, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_600, c_583])).
% 3.21/1.47  tff(c_603, plain, (~v9_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_602])).
% 3.21/1.47  tff(c_606, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_2, c_603])).
% 3.21/1.47  tff(c_609, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_606])).
% 3.21/1.47  tff(c_611, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_609])).
% 3.21/1.47  tff(c_613, plain, (v9_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_602])).
% 3.21/1.47  tff(c_599, plain, (![B_82]: (~v9_lattices('#skF_2') | r1_lattices('#skF_2', B_82, '#skF_3') | k2_lattices('#skF_2', B_82, '#skF_3')!=B_82 | ~m1_subset_1(B_82, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_589])).
% 3.21/1.47  tff(c_616, plain, (![B_84]: (r1_lattices('#skF_2', B_84, '#skF_3') | k2_lattices('#skF_2', B_84, '#skF_3')!=B_84 | ~m1_subset_1(B_84, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_613, c_599])).
% 3.21/1.47  tff(c_619, plain, (r1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3') | k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')!=k5_lattices('#skF_2')), inference(resolution, [status(thm)], [c_129, c_616])).
% 3.21/1.47  tff(c_633, plain, (r1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_619])).
% 3.21/1.47  tff(c_26, plain, (![A_12, B_16, C_18]: (k1_lattices(A_12, B_16, C_18)=C_18 | ~r1_lattices(A_12, B_16, C_18) | ~m1_subset_1(C_18, u1_struct_0(A_12)) | ~m1_subset_1(B_16, u1_struct_0(A_12)) | ~l2_lattices(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.21/1.47  tff(c_646, plain, (k1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | ~l2_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_633, c_26])).
% 3.21/1.47  tff(c_653, plain, (k1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_129, c_42, c_646])).
% 3.21/1.47  tff(c_655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_105, c_653])).
% 3.21/1.47  tff(c_657, plain, (k1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_102])).
% 3.21/1.47  tff(c_664, plain, (![A_85, C_86]: (k2_lattices(A_85, k5_lattices(A_85), C_86)=k5_lattices(A_85) | ~m1_subset_1(C_86, u1_struct_0(A_85)) | ~m1_subset_1(k5_lattices(A_85), u1_struct_0(A_85)) | ~v13_lattices(A_85) | ~l1_lattices(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.21/1.47  tff(c_670, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | ~v13_lattices('#skF_2') | ~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_664])).
% 3.21/1.47  tff(c_675, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_46, c_670])).
% 3.21/1.47  tff(c_676, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_675])).
% 3.21/1.47  tff(c_682, plain, (~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_676])).
% 3.21/1.47  tff(c_692, plain, (~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_682])).
% 3.21/1.47  tff(c_695, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_692])).
% 3.21/1.47  tff(c_697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_695])).
% 3.21/1.47  tff(c_699, plain, (m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_676])).
% 3.21/1.47  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.21/1.47  tff(c_796, plain, (![A_94, B_95, C_96]: (k3_lattices(A_94, B_95, C_96)=k1_lattices(A_94, B_95, C_96) | ~m1_subset_1(C_96, u1_struct_0(A_94)) | ~m1_subset_1(B_95, u1_struct_0(A_94)) | ~l2_lattices(A_94) | ~v4_lattices(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.21/1.47  tff(c_804, plain, (![B_95]: (k3_lattices('#skF_2', B_95, '#skF_3')=k1_lattices('#skF_2', B_95, '#skF_3') | ~m1_subset_1(B_95, u1_struct_0('#skF_2')) | ~l2_lattices('#skF_2') | ~v4_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_796])).
% 3.21/1.47  tff(c_813, plain, (![B_95]: (k3_lattices('#skF_2', B_95, '#skF_3')=k1_lattices('#skF_2', B_95, '#skF_3') | ~m1_subset_1(B_95, u1_struct_0('#skF_2')) | ~v4_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_804])).
% 3.21/1.47  tff(c_814, plain, (![B_95]: (k3_lattices('#skF_2', B_95, '#skF_3')=k1_lattices('#skF_2', B_95, '#skF_3') | ~m1_subset_1(B_95, u1_struct_0('#skF_2')) | ~v4_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_813])).
% 3.21/1.47  tff(c_815, plain, (~v4_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_814])).
% 3.21/1.47  tff(c_818, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_12, c_815])).
% 3.21/1.47  tff(c_821, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_818])).
% 3.21/1.47  tff(c_823, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_821])).
% 3.21/1.47  tff(c_845, plain, (![B_100]: (k3_lattices('#skF_2', B_100, '#skF_3')=k1_lattices('#skF_2', B_100, '#skF_3') | ~m1_subset_1(B_100, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_814])).
% 3.21/1.47  tff(c_848, plain, (k3_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_699, c_845])).
% 3.21/1.47  tff(c_861, plain, (k3_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_657, c_848])).
% 3.21/1.47  tff(c_863, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_861])).
% 3.21/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.47  
% 3.21/1.47  Inference rules
% 3.21/1.47  ----------------------
% 3.21/1.47  #Ref     : 0
% 3.21/1.47  #Sup     : 148
% 3.21/1.47  #Fact    : 0
% 3.21/1.47  #Define  : 0
% 3.21/1.47  #Split   : 11
% 3.21/1.47  #Chain   : 0
% 3.21/1.47  #Close   : 0
% 3.21/1.47  
% 3.21/1.47  Ordering : KBO
% 3.21/1.47  
% 3.21/1.47  Simplification rules
% 3.21/1.47  ----------------------
% 3.21/1.47  #Subsume      : 9
% 3.21/1.47  #Demod        : 198
% 3.21/1.47  #Tautology    : 74
% 3.21/1.47  #SimpNegUnit  : 68
% 3.21/1.47  #BackRed      : 13
% 3.21/1.47  
% 3.21/1.47  #Partial instantiations: 0
% 3.21/1.47  #Strategies tried      : 1
% 3.21/1.47  
% 3.21/1.47  Timing (in seconds)
% 3.21/1.47  ----------------------
% 3.21/1.47  Preprocessing        : 0.34
% 3.21/1.47  Parsing              : 0.17
% 3.21/1.48  CNF conversion       : 0.02
% 3.21/1.48  Main loop            : 0.37
% 3.21/1.48  Inferencing          : 0.13
% 3.21/1.48  Reduction            : 0.12
% 3.21/1.48  Demodulation         : 0.08
% 3.21/1.48  BG Simplification    : 0.02
% 3.21/1.48  Subsumption          : 0.07
% 3.21/1.48  Abstraction          : 0.03
% 3.21/1.48  MUC search           : 0.00
% 3.21/1.48  Cooper               : 0.00
% 3.21/1.48  Total                : 0.75
% 3.21/1.48  Index Insertion      : 0.00
% 3.21/1.48  Index Deletion       : 0.00
% 3.21/1.48  Index Matching       : 0.00
% 3.21/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
