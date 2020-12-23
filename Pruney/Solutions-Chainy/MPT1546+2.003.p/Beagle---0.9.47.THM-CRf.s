%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:00 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 264 expanded)
%              Number of leaves         :   25 ( 109 expanded)
%              Depth                    :   14
%              Number of atoms          :  251 (1072 expanded)
%              Number of equality atoms :   35 ( 127 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k13_lattice3,type,(
    k13_lattice3: ( $i * $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k10_lattice3,type,(
    k10_lattice3: ( $i * $i * $i ) > $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( B = k13_lattice3(A,B,C)
                <=> r1_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_119,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k10_lattice3(A,B,C) = k10_lattice3(A,C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_lattice3)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k10_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,B,D)
                      & r1_orders_2(A,C,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,B,E)
                              & r1_orders_2(A,C,E) )
                           => r1_orders_2(A,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).

tff(c_32,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_34,plain,(
    v1_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_38,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_348,plain,(
    ! [A_113,B_114,C_115] :
      ( r3_orders_2(A_113,B_114,B_114)
      | ~ m1_subset_1(C_115,u1_struct_0(A_113))
      | ~ m1_subset_1(B_114,u1_struct_0(A_113))
      | ~ l1_orders_2(A_113)
      | ~ v3_orders_2(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_350,plain,(
    ! [B_114] :
      ( r3_orders_2('#skF_2',B_114,B_114)
      | ~ m1_subset_1(B_114,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_348])).

tff(c_355,plain,(
    ! [B_114] :
      ( r3_orders_2('#skF_2',B_114,B_114)
      | ~ m1_subset_1(B_114,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_350])).

tff(c_359,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_355])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ v2_struct_0(A_7)
      | ~ v1_lattice3(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_362,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_359,c_8])).

tff(c_366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_362])).

tff(c_368,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_355])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_36,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_116,plain,(
    ! [A_78,C_79,B_80] :
      ( k10_lattice3(A_78,C_79,B_80) = k10_lattice3(A_78,B_80,C_79)
      | ~ m1_subset_1(C_79,u1_struct_0(A_78))
      | ~ m1_subset_1(B_80,u1_struct_0(A_78))
      | ~ l1_orders_2(A_78)
      | ~ v1_lattice3(A_78)
      | ~ v5_orders_2(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_118,plain,(
    ! [B_80] :
      ( k10_lattice3('#skF_2',B_80,'#skF_3') = k10_lattice3('#skF_2','#skF_3',B_80)
      | ~ m1_subset_1(B_80,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_116])).

tff(c_146,plain,(
    ! [B_84] :
      ( k10_lattice3('#skF_2',B_84,'#skF_3') = k10_lattice3('#skF_2','#skF_3',B_84)
      | ~ m1_subset_1(B_84,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_118])).

tff(c_155,plain,(
    k10_lattice3('#skF_2','#skF_3','#skF_4') = k10_lattice3('#skF_2','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_146])).

tff(c_171,plain,(
    ! [A_86,B_87,C_88] :
      ( k13_lattice3(A_86,B_87,C_88) = k10_lattice3(A_86,B_87,C_88)
      | ~ m1_subset_1(C_88,u1_struct_0(A_86))
      | ~ m1_subset_1(B_87,u1_struct_0(A_86))
      | ~ l1_orders_2(A_86)
      | ~ v1_lattice3(A_86)
      | ~ v5_orders_2(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_175,plain,(
    ! [B_87] :
      ( k13_lattice3('#skF_2',B_87,'#skF_4') = k10_lattice3('#skF_2',B_87,'#skF_4')
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_171])).

tff(c_205,plain,(
    ! [B_93] :
      ( k13_lattice3('#skF_2',B_93,'#skF_4') = k10_lattice3('#skF_2',B_93,'#skF_4')
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_175])).

tff(c_208,plain,(
    k13_lattice3('#skF_2','#skF_3','#skF_4') = k10_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_205])).

tff(c_213,plain,(
    k13_lattice3('#skF_2','#skF_3','#skF_4') = k10_lattice3('#skF_2','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_208])).

tff(c_46,plain,
    ( k13_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3'
    | r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_48,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_40,plain,
    ( ~ r1_orders_2('#skF_2','#skF_4','#skF_3')
    | k13_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_50,plain,(
    k13_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40])).

tff(c_215,plain,(
    k10_lattice3('#skF_2','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_50])).

tff(c_51,plain,(
    ! [A_69,B_70,C_71] :
      ( r3_orders_2(A_69,B_70,B_70)
      | ~ m1_subset_1(C_71,u1_struct_0(A_69))
      | ~ m1_subset_1(B_70,u1_struct_0(A_69))
      | ~ l1_orders_2(A_69)
      | ~ v3_orders_2(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_53,plain,(
    ! [B_70] :
      ( r3_orders_2('#skF_2',B_70,B_70)
      | ~ m1_subset_1(B_70,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_51])).

tff(c_58,plain,(
    ! [B_70] :
      ( r3_orders_2('#skF_2',B_70,B_70)
      | ~ m1_subset_1(B_70,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_53])).

tff(c_62,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_65,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_8])).

tff(c_69,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_65])).

tff(c_71,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_72,plain,(
    ! [B_72] :
      ( r3_orders_2('#skF_2',B_72,B_72)
      | ~ m1_subset_1(B_72,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_77,plain,(
    r3_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_72])).

tff(c_127,plain,(
    ! [A_81,B_82,C_83] :
      ( r1_orders_2(A_81,B_82,C_83)
      | ~ r3_orders_2(A_81,B_82,C_83)
      | ~ m1_subset_1(C_83,u1_struct_0(A_81))
      | ~ m1_subset_1(B_82,u1_struct_0(A_81))
      | ~ l1_orders_2(A_81)
      | ~ v3_orders_2(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_133,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_127])).

tff(c_144,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_30,c_133])).

tff(c_145,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_144])).

tff(c_300,plain,(
    ! [A_105,C_106,B_107,D_108] :
      ( r1_orders_2(A_105,C_106,'#skF_1'(A_105,B_107,C_106,D_108))
      | k10_lattice3(A_105,B_107,C_106) = D_108
      | ~ r1_orders_2(A_105,C_106,D_108)
      | ~ r1_orders_2(A_105,B_107,D_108)
      | ~ m1_subset_1(D_108,u1_struct_0(A_105))
      | ~ m1_subset_1(C_106,u1_struct_0(A_105))
      | ~ m1_subset_1(B_107,u1_struct_0(A_105))
      | ~ l1_orders_2(A_105)
      | ~ v1_lattice3(A_105)
      | ~ v5_orders_2(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10,plain,(
    ! [A_8,D_50,B_32,C_44] :
      ( ~ r1_orders_2(A_8,D_50,'#skF_1'(A_8,B_32,C_44,D_50))
      | k10_lattice3(A_8,B_32,C_44) = D_50
      | ~ r1_orders_2(A_8,C_44,D_50)
      | ~ r1_orders_2(A_8,B_32,D_50)
      | ~ m1_subset_1(D_50,u1_struct_0(A_8))
      | ~ m1_subset_1(C_44,u1_struct_0(A_8))
      | ~ m1_subset_1(B_32,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8)
      | ~ v1_lattice3(A_8)
      | ~ v5_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_306,plain,(
    ! [A_109,B_110,D_111] :
      ( k10_lattice3(A_109,B_110,D_111) = D_111
      | ~ r1_orders_2(A_109,D_111,D_111)
      | ~ r1_orders_2(A_109,B_110,D_111)
      | ~ m1_subset_1(D_111,u1_struct_0(A_109))
      | ~ m1_subset_1(B_110,u1_struct_0(A_109))
      | ~ l1_orders_2(A_109)
      | ~ v1_lattice3(A_109)
      | ~ v5_orders_2(A_109)
      | v2_struct_0(A_109) ) ),
    inference(resolution,[status(thm)],[c_300,c_10])).

tff(c_308,plain,(
    ! [B_110] :
      ( k10_lattice3('#skF_2',B_110,'#skF_3') = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_110,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_110,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_145,c_306])).

tff(c_313,plain,(
    ! [B_110] :
      ( k10_lattice3('#skF_2',B_110,'#skF_3') = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_110,'#skF_3')
      | ~ m1_subset_1(B_110,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_308])).

tff(c_319,plain,(
    ! [B_112] :
      ( k10_lattice3('#skF_2',B_112,'#skF_3') = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_112,'#skF_3')
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_313])).

tff(c_329,plain,
    ( k10_lattice3('#skF_2','#skF_4','#skF_3') = '#skF_3'
    | ~ r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_319])).

tff(c_339,plain,(
    k10_lattice3('#skF_2','#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_329])).

tff(c_341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_215,c_339])).

tff(c_343,plain,(
    ~ r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_411,plain,(
    ! [A_122,C_123,B_124] :
      ( k10_lattice3(A_122,C_123,B_124) = k10_lattice3(A_122,B_124,C_123)
      | ~ m1_subset_1(C_123,u1_struct_0(A_122))
      | ~ m1_subset_1(B_124,u1_struct_0(A_122))
      | ~ l1_orders_2(A_122)
      | ~ v1_lattice3(A_122)
      | ~ v5_orders_2(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_413,plain,(
    ! [B_124] :
      ( k10_lattice3('#skF_2',B_124,'#skF_3') = k10_lattice3('#skF_2','#skF_3',B_124)
      | ~ m1_subset_1(B_124,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_411])).

tff(c_433,plain,(
    ! [B_128] :
      ( k10_lattice3('#skF_2',B_128,'#skF_3') = k10_lattice3('#skF_2','#skF_3',B_128)
      | ~ m1_subset_1(B_128,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_413])).

tff(c_442,plain,(
    k10_lattice3('#skF_2','#skF_3','#skF_4') = k10_lattice3('#skF_2','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_433])).

tff(c_342,plain,(
    k13_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_422,plain,(
    ! [A_125,B_126,C_127] :
      ( k13_lattice3(A_125,B_126,C_127) = k10_lattice3(A_125,B_126,C_127)
      | ~ m1_subset_1(C_127,u1_struct_0(A_125))
      | ~ m1_subset_1(B_126,u1_struct_0(A_125))
      | ~ l1_orders_2(A_125)
      | ~ v1_lattice3(A_125)
      | ~ v5_orders_2(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_426,plain,(
    ! [B_126] :
      ( k13_lattice3('#skF_2',B_126,'#skF_4') = k10_lattice3('#skF_2',B_126,'#skF_4')
      | ~ m1_subset_1(B_126,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_422])).

tff(c_464,plain,(
    ! [B_130] :
      ( k13_lattice3('#skF_2',B_130,'#skF_4') = k10_lattice3('#skF_2',B_130,'#skF_4')
      | ~ m1_subset_1(B_130,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_426])).

tff(c_467,plain,(
    k13_lattice3('#skF_2','#skF_3','#skF_4') = k10_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_464])).

tff(c_472,plain,(
    k10_lattice3('#skF_2','#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_342,c_467])).

tff(c_516,plain,(
    ! [A_135,B_136,C_137] :
      ( r1_orders_2(A_135,B_136,k10_lattice3(A_135,B_136,C_137))
      | ~ m1_subset_1(k10_lattice3(A_135,B_136,C_137),u1_struct_0(A_135))
      | ~ m1_subset_1(C_137,u1_struct_0(A_135))
      | ~ m1_subset_1(B_136,u1_struct_0(A_135))
      | ~ l1_orders_2(A_135)
      | ~ v1_lattice3(A_135)
      | ~ v5_orders_2(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_520,plain,
    ( r1_orders_2('#skF_2','#skF_4',k10_lattice3('#skF_2','#skF_4','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v1_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_472,c_516])).

tff(c_525,plain,
    ( r1_orders_2('#skF_2','#skF_4','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_28,c_30,c_30,c_472,c_520])).

tff(c_527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_368,c_343,c_525])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:19:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.37  
% 2.81/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.37  %$ r3_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.81/1.37  
% 2.81/1.37  %Foreground sorts:
% 2.81/1.37  
% 2.81/1.37  
% 2.81/1.37  %Background operators:
% 2.81/1.37  
% 2.81/1.37  
% 2.81/1.37  %Foreground operators:
% 2.81/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.81/1.37  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.81/1.37  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.81/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.37  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 2.81/1.37  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.81/1.37  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 2.81/1.37  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 2.81/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.37  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.81/1.37  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.81/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.81/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.81/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.37  
% 2.81/1.39  tff(f_138, negated_conjecture, ~(![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((B = k13_lattice3(A, B, C)) <=> r1_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow_0)).
% 2.81/1.39  tff(f_53, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_orders_2(A, B, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 2.81/1.39  tff(f_60, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 2.81/1.39  tff(f_119, axiom, (![A]: (((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k10_lattice3(A, B, C) = k10_lattice3(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_lattice3)).
% 2.81/1.39  tff(f_105, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 2.81/1.39  tff(f_40, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 2.81/1.39  tff(f_93, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l26_lattice3)).
% 2.81/1.39  tff(c_32, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.81/1.39  tff(c_34, plain, (v1_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.81/1.39  tff(c_38, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.81/1.39  tff(c_30, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.81/1.39  tff(c_348, plain, (![A_113, B_114, C_115]: (r3_orders_2(A_113, B_114, B_114) | ~m1_subset_1(C_115, u1_struct_0(A_113)) | ~m1_subset_1(B_114, u1_struct_0(A_113)) | ~l1_orders_2(A_113) | ~v3_orders_2(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.81/1.39  tff(c_350, plain, (![B_114]: (r3_orders_2('#skF_2', B_114, B_114) | ~m1_subset_1(B_114, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_348])).
% 2.81/1.39  tff(c_355, plain, (![B_114]: (r3_orders_2('#skF_2', B_114, B_114) | ~m1_subset_1(B_114, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_350])).
% 2.81/1.39  tff(c_359, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_355])).
% 2.81/1.39  tff(c_8, plain, (![A_7]: (~v2_struct_0(A_7) | ~v1_lattice3(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.81/1.39  tff(c_362, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_359, c_8])).
% 2.81/1.39  tff(c_366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_362])).
% 2.81/1.39  tff(c_368, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_355])).
% 2.81/1.39  tff(c_28, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.81/1.39  tff(c_36, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.81/1.39  tff(c_116, plain, (![A_78, C_79, B_80]: (k10_lattice3(A_78, C_79, B_80)=k10_lattice3(A_78, B_80, C_79) | ~m1_subset_1(C_79, u1_struct_0(A_78)) | ~m1_subset_1(B_80, u1_struct_0(A_78)) | ~l1_orders_2(A_78) | ~v1_lattice3(A_78) | ~v5_orders_2(A_78))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.81/1.39  tff(c_118, plain, (![B_80]: (k10_lattice3('#skF_2', B_80, '#skF_3')=k10_lattice3('#skF_2', '#skF_3', B_80) | ~m1_subset_1(B_80, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_116])).
% 2.81/1.39  tff(c_146, plain, (![B_84]: (k10_lattice3('#skF_2', B_84, '#skF_3')=k10_lattice3('#skF_2', '#skF_3', B_84) | ~m1_subset_1(B_84, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_118])).
% 2.81/1.39  tff(c_155, plain, (k10_lattice3('#skF_2', '#skF_3', '#skF_4')=k10_lattice3('#skF_2', '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_146])).
% 2.81/1.39  tff(c_171, plain, (![A_86, B_87, C_88]: (k13_lattice3(A_86, B_87, C_88)=k10_lattice3(A_86, B_87, C_88) | ~m1_subset_1(C_88, u1_struct_0(A_86)) | ~m1_subset_1(B_87, u1_struct_0(A_86)) | ~l1_orders_2(A_86) | ~v1_lattice3(A_86) | ~v5_orders_2(A_86))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.81/1.39  tff(c_175, plain, (![B_87]: (k13_lattice3('#skF_2', B_87, '#skF_4')=k10_lattice3('#skF_2', B_87, '#skF_4') | ~m1_subset_1(B_87, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_171])).
% 2.81/1.39  tff(c_205, plain, (![B_93]: (k13_lattice3('#skF_2', B_93, '#skF_4')=k10_lattice3('#skF_2', B_93, '#skF_4') | ~m1_subset_1(B_93, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_175])).
% 2.81/1.39  tff(c_208, plain, (k13_lattice3('#skF_2', '#skF_3', '#skF_4')=k10_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_205])).
% 2.81/1.39  tff(c_213, plain, (k13_lattice3('#skF_2', '#skF_3', '#skF_4')=k10_lattice3('#skF_2', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_208])).
% 2.81/1.39  tff(c_46, plain, (k13_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_3' | r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.81/1.39  tff(c_48, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 2.81/1.39  tff(c_40, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_3') | k13_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.81/1.39  tff(c_50, plain, (k13_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40])).
% 2.81/1.39  tff(c_215, plain, (k10_lattice3('#skF_2', '#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_213, c_50])).
% 2.81/1.39  tff(c_51, plain, (![A_69, B_70, C_71]: (r3_orders_2(A_69, B_70, B_70) | ~m1_subset_1(C_71, u1_struct_0(A_69)) | ~m1_subset_1(B_70, u1_struct_0(A_69)) | ~l1_orders_2(A_69) | ~v3_orders_2(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.81/1.39  tff(c_53, plain, (![B_70]: (r3_orders_2('#skF_2', B_70, B_70) | ~m1_subset_1(B_70, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_51])).
% 2.81/1.39  tff(c_58, plain, (![B_70]: (r3_orders_2('#skF_2', B_70, B_70) | ~m1_subset_1(B_70, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_53])).
% 2.81/1.39  tff(c_62, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_58])).
% 2.81/1.39  tff(c_65, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_62, c_8])).
% 2.81/1.39  tff(c_69, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_65])).
% 2.81/1.39  tff(c_71, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 2.81/1.39  tff(c_72, plain, (![B_72]: (r3_orders_2('#skF_2', B_72, B_72) | ~m1_subset_1(B_72, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_58])).
% 2.81/1.39  tff(c_77, plain, (r3_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_72])).
% 2.81/1.39  tff(c_127, plain, (![A_81, B_82, C_83]: (r1_orders_2(A_81, B_82, C_83) | ~r3_orders_2(A_81, B_82, C_83) | ~m1_subset_1(C_83, u1_struct_0(A_81)) | ~m1_subset_1(B_82, u1_struct_0(A_81)) | ~l1_orders_2(A_81) | ~v3_orders_2(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.81/1.39  tff(c_133, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_77, c_127])).
% 2.81/1.39  tff(c_144, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_30, c_133])).
% 2.81/1.39  tff(c_145, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_71, c_144])).
% 2.81/1.39  tff(c_300, plain, (![A_105, C_106, B_107, D_108]: (r1_orders_2(A_105, C_106, '#skF_1'(A_105, B_107, C_106, D_108)) | k10_lattice3(A_105, B_107, C_106)=D_108 | ~r1_orders_2(A_105, C_106, D_108) | ~r1_orders_2(A_105, B_107, D_108) | ~m1_subset_1(D_108, u1_struct_0(A_105)) | ~m1_subset_1(C_106, u1_struct_0(A_105)) | ~m1_subset_1(B_107, u1_struct_0(A_105)) | ~l1_orders_2(A_105) | ~v1_lattice3(A_105) | ~v5_orders_2(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.81/1.39  tff(c_10, plain, (![A_8, D_50, B_32, C_44]: (~r1_orders_2(A_8, D_50, '#skF_1'(A_8, B_32, C_44, D_50)) | k10_lattice3(A_8, B_32, C_44)=D_50 | ~r1_orders_2(A_8, C_44, D_50) | ~r1_orders_2(A_8, B_32, D_50) | ~m1_subset_1(D_50, u1_struct_0(A_8)) | ~m1_subset_1(C_44, u1_struct_0(A_8)) | ~m1_subset_1(B_32, u1_struct_0(A_8)) | ~l1_orders_2(A_8) | ~v1_lattice3(A_8) | ~v5_orders_2(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.81/1.39  tff(c_306, plain, (![A_109, B_110, D_111]: (k10_lattice3(A_109, B_110, D_111)=D_111 | ~r1_orders_2(A_109, D_111, D_111) | ~r1_orders_2(A_109, B_110, D_111) | ~m1_subset_1(D_111, u1_struct_0(A_109)) | ~m1_subset_1(B_110, u1_struct_0(A_109)) | ~l1_orders_2(A_109) | ~v1_lattice3(A_109) | ~v5_orders_2(A_109) | v2_struct_0(A_109))), inference(resolution, [status(thm)], [c_300, c_10])).
% 2.81/1.39  tff(c_308, plain, (![B_110]: (k10_lattice3('#skF_2', B_110, '#skF_3')='#skF_3' | ~r1_orders_2('#skF_2', B_110, '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_110, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_145, c_306])).
% 2.81/1.39  tff(c_313, plain, (![B_110]: (k10_lattice3('#skF_2', B_110, '#skF_3')='#skF_3' | ~r1_orders_2('#skF_2', B_110, '#skF_3') | ~m1_subset_1(B_110, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_308])).
% 2.81/1.39  tff(c_319, plain, (![B_112]: (k10_lattice3('#skF_2', B_112, '#skF_3')='#skF_3' | ~r1_orders_2('#skF_2', B_112, '#skF_3') | ~m1_subset_1(B_112, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_71, c_313])).
% 2.81/1.39  tff(c_329, plain, (k10_lattice3('#skF_2', '#skF_4', '#skF_3')='#skF_3' | ~r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_319])).
% 2.81/1.39  tff(c_339, plain, (k10_lattice3('#skF_2', '#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_329])).
% 2.81/1.39  tff(c_341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_215, c_339])).
% 2.81/1.39  tff(c_343, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 2.81/1.39  tff(c_411, plain, (![A_122, C_123, B_124]: (k10_lattice3(A_122, C_123, B_124)=k10_lattice3(A_122, B_124, C_123) | ~m1_subset_1(C_123, u1_struct_0(A_122)) | ~m1_subset_1(B_124, u1_struct_0(A_122)) | ~l1_orders_2(A_122) | ~v1_lattice3(A_122) | ~v5_orders_2(A_122))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.81/1.39  tff(c_413, plain, (![B_124]: (k10_lattice3('#skF_2', B_124, '#skF_3')=k10_lattice3('#skF_2', '#skF_3', B_124) | ~m1_subset_1(B_124, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_411])).
% 2.81/1.39  tff(c_433, plain, (![B_128]: (k10_lattice3('#skF_2', B_128, '#skF_3')=k10_lattice3('#skF_2', '#skF_3', B_128) | ~m1_subset_1(B_128, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_413])).
% 2.81/1.39  tff(c_442, plain, (k10_lattice3('#skF_2', '#skF_3', '#skF_4')=k10_lattice3('#skF_2', '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_433])).
% 2.81/1.39  tff(c_342, plain, (k13_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_46])).
% 2.81/1.39  tff(c_422, plain, (![A_125, B_126, C_127]: (k13_lattice3(A_125, B_126, C_127)=k10_lattice3(A_125, B_126, C_127) | ~m1_subset_1(C_127, u1_struct_0(A_125)) | ~m1_subset_1(B_126, u1_struct_0(A_125)) | ~l1_orders_2(A_125) | ~v1_lattice3(A_125) | ~v5_orders_2(A_125))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.81/1.39  tff(c_426, plain, (![B_126]: (k13_lattice3('#skF_2', B_126, '#skF_4')=k10_lattice3('#skF_2', B_126, '#skF_4') | ~m1_subset_1(B_126, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_422])).
% 2.81/1.39  tff(c_464, plain, (![B_130]: (k13_lattice3('#skF_2', B_130, '#skF_4')=k10_lattice3('#skF_2', B_130, '#skF_4') | ~m1_subset_1(B_130, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_426])).
% 2.81/1.39  tff(c_467, plain, (k13_lattice3('#skF_2', '#skF_3', '#skF_4')=k10_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_464])).
% 2.81/1.39  tff(c_472, plain, (k10_lattice3('#skF_2', '#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_442, c_342, c_467])).
% 2.81/1.39  tff(c_516, plain, (![A_135, B_136, C_137]: (r1_orders_2(A_135, B_136, k10_lattice3(A_135, B_136, C_137)) | ~m1_subset_1(k10_lattice3(A_135, B_136, C_137), u1_struct_0(A_135)) | ~m1_subset_1(C_137, u1_struct_0(A_135)) | ~m1_subset_1(B_136, u1_struct_0(A_135)) | ~l1_orders_2(A_135) | ~v1_lattice3(A_135) | ~v5_orders_2(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.81/1.39  tff(c_520, plain, (r1_orders_2('#skF_2', '#skF_4', k10_lattice3('#skF_2', '#skF_4', '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_472, c_516])).
% 2.81/1.39  tff(c_525, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_28, c_30, c_30, c_472, c_520])).
% 2.81/1.39  tff(c_527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_368, c_343, c_525])).
% 2.81/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.39  
% 2.81/1.39  Inference rules
% 2.81/1.39  ----------------------
% 2.81/1.39  #Ref     : 0
% 2.81/1.39  #Sup     : 98
% 2.81/1.39  #Fact    : 0
% 2.81/1.39  #Define  : 0
% 2.81/1.39  #Split   : 6
% 2.81/1.39  #Chain   : 0
% 2.81/1.39  #Close   : 0
% 2.81/1.39  
% 2.81/1.39  Ordering : KBO
% 2.81/1.39  
% 2.81/1.39  Simplification rules
% 2.81/1.39  ----------------------
% 2.81/1.39  #Subsume      : 5
% 2.81/1.39  #Demod        : 137
% 2.81/1.39  #Tautology    : 40
% 2.81/1.39  #SimpNegUnit  : 26
% 2.81/1.39  #BackRed      : 3
% 2.81/1.39  
% 2.81/1.39  #Partial instantiations: 0
% 2.81/1.39  #Strategies tried      : 1
% 2.81/1.39  
% 2.81/1.39  Timing (in seconds)
% 2.81/1.39  ----------------------
% 2.81/1.39  Preprocessing        : 0.33
% 2.81/1.39  Parsing              : 0.17
% 2.81/1.39  CNF conversion       : 0.03
% 2.81/1.39  Main loop            : 0.29
% 2.81/1.39  Inferencing          : 0.10
% 2.81/1.39  Reduction            : 0.09
% 2.81/1.39  Demodulation         : 0.06
% 2.81/1.40  BG Simplification    : 0.02
% 2.81/1.40  Subsumption          : 0.06
% 2.81/1.40  Abstraction          : 0.02
% 2.81/1.40  MUC search           : 0.00
% 2.81/1.40  Cooper               : 0.00
% 2.81/1.40  Total                : 0.66
% 2.81/1.40  Index Insertion      : 0.00
% 2.81/1.40  Index Deletion       : 0.00
% 2.81/1.40  Index Matching       : 0.00
% 2.81/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
