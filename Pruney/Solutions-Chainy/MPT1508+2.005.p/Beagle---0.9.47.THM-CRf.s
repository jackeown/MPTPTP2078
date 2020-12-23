%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:47 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 199 expanded)
%              Number of leaves         :   35 (  86 expanded)
%              Depth                    :   12
%              Number of atoms          :  301 ( 916 expanded)
%              Number of equality atoms :   10 (  48 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

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

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_161,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( ( r2_hidden(B,C)
                  & r3_lattice3(A,B,C) )
               => k16_lattice3(A,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).

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

tff(f_72,axiom,(
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

tff(f_53,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k16_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

tff(f_122,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( B = k16_lattice3(A,C)
            <=> ( r3_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r3_lattice3(A,D,C)
                     => r3_lattices(A,D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

tff(f_141,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r2_hidden(B,C)
             => ( r3_lattices(A,B,k15_lattice3(A,C))
                & r3_lattices(A,k16_lattice3(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).

tff(f_91,axiom,(
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

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_50,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_54,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_42,plain,(
    k16_lattice3('#skF_2','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_52,plain,(
    v4_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_89,plain,(
    ! [A_74,B_75,C_76] :
      ( r3_lattices(A_74,B_75,C_76)
      | ~ r1_lattices(A_74,B_75,C_76)
      | ~ m1_subset_1(C_76,u1_struct_0(A_74))
      | ~ m1_subset_1(B_75,u1_struct_0(A_74))
      | ~ l3_lattices(A_74)
      | ~ v9_lattices(A_74)
      | ~ v8_lattices(A_74)
      | ~ v6_lattices(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_93,plain,(
    ! [B_75] :
      ( r3_lattices('#skF_2',B_75,'#skF_3')
      | ~ r1_lattices('#skF_2',B_75,'#skF_3')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_2'))
      | ~ l3_lattices('#skF_2')
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_89])).

tff(c_97,plain,(
    ! [B_75] :
      ( r3_lattices('#skF_2',B_75,'#skF_3')
      | ~ r1_lattices('#skF_2',B_75,'#skF_3')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_93])).

tff(c_98,plain,(
    ! [B_75] :
      ( r3_lattices('#skF_2',B_75,'#skF_3')
      | ~ r1_lattices('#skF_2',B_75,'#skF_3')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_97])).

tff(c_99,plain,(
    ~ v6_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_102,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_99])).

tff(c_105,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_102])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_105])).

tff(c_109,plain,(
    v6_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_98])).

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

tff(c_108,plain,(
    ! [B_75] :
      ( ~ v8_lattices('#skF_2')
      | ~ v9_lattices('#skF_2')
      | r3_lattices('#skF_2',B_75,'#skF_3')
      | ~ r1_lattices('#skF_2',B_75,'#skF_3')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_110,plain,(
    ~ v9_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_113,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_110])).

tff(c_116,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_113])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_116])).

tff(c_119,plain,(
    ! [B_75] :
      ( ~ v8_lattices('#skF_2')
      | r3_lattices('#skF_2',B_75,'#skF_3')
      | ~ r1_lattices('#skF_2',B_75,'#skF_3')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_121,plain,(
    ~ v8_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_124,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_121])).

tff(c_127,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_124])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_127])).

tff(c_131,plain,(
    v8_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_120,plain,(
    v9_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_46,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_57,plain,(
    ! [A_48] :
      ( l2_lattices(A_48)
      | ~ l3_lattices(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_61,plain,(
    l2_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_57])).

tff(c_44,plain,(
    r3_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k16_lattice3(A_13,B_14),u1_struct_0(A_13))
      | ~ l3_lattices(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_197,plain,(
    ! [A_94,D_95,C_96] :
      ( r3_lattices(A_94,D_95,k16_lattice3(A_94,C_96))
      | ~ r3_lattice3(A_94,D_95,C_96)
      | ~ m1_subset_1(D_95,u1_struct_0(A_94))
      | ~ m1_subset_1(k16_lattice3(A_94,C_96),u1_struct_0(A_94))
      | ~ l3_lattices(A_94)
      | ~ v4_lattice3(A_94)
      | ~ v10_lattices(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_201,plain,(
    ! [A_97,D_98,B_99] :
      ( r3_lattices(A_97,D_98,k16_lattice3(A_97,B_99))
      | ~ r3_lattice3(A_97,D_98,B_99)
      | ~ m1_subset_1(D_98,u1_struct_0(A_97))
      | ~ v4_lattice3(A_97)
      | ~ v10_lattices(A_97)
      | ~ l3_lattices(A_97)
      | v2_struct_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_26,c_197])).

tff(c_22,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_lattices(A_3,B_4,C_5)
      | ~ r3_lattices(A_3,B_4,C_5)
      | ~ m1_subset_1(C_5,u1_struct_0(A_3))
      | ~ m1_subset_1(B_4,u1_struct_0(A_3))
      | ~ l3_lattices(A_3)
      | ~ v9_lattices(A_3)
      | ~ v8_lattices(A_3)
      | ~ v6_lattices(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_219,plain,(
    ! [A_109,D_110,B_111] :
      ( r1_lattices(A_109,D_110,k16_lattice3(A_109,B_111))
      | ~ m1_subset_1(k16_lattice3(A_109,B_111),u1_struct_0(A_109))
      | ~ v9_lattices(A_109)
      | ~ v8_lattices(A_109)
      | ~ v6_lattices(A_109)
      | ~ r3_lattice3(A_109,D_110,B_111)
      | ~ m1_subset_1(D_110,u1_struct_0(A_109))
      | ~ v4_lattice3(A_109)
      | ~ v10_lattices(A_109)
      | ~ l3_lattices(A_109)
      | v2_struct_0(A_109) ) ),
    inference(resolution,[status(thm)],[c_201,c_22])).

tff(c_222,plain,(
    ! [A_13,D_110,B_14] :
      ( r1_lattices(A_13,D_110,k16_lattice3(A_13,B_14))
      | ~ v9_lattices(A_13)
      | ~ v8_lattices(A_13)
      | ~ v6_lattices(A_13)
      | ~ r3_lattice3(A_13,D_110,B_14)
      | ~ m1_subset_1(D_110,u1_struct_0(A_13))
      | ~ v4_lattice3(A_13)
      | ~ v10_lattices(A_13)
      | ~ l3_lattices(A_13)
      | v2_struct_0(A_13) ) ),
    inference(resolution,[status(thm)],[c_26,c_219])).

tff(c_38,plain,(
    ! [A_37,C_43,B_41] :
      ( r3_lattices(A_37,k16_lattice3(A_37,C_43),B_41)
      | ~ r2_hidden(B_41,C_43)
      | ~ m1_subset_1(B_41,u1_struct_0(A_37))
      | ~ l3_lattices(A_37)
      | ~ v4_lattice3(A_37)
      | ~ v10_lattices(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_82,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_211,plain,(
    ! [A_103,C_104,B_105] :
      ( r1_lattices(A_103,k16_lattice3(A_103,C_104),B_105)
      | ~ m1_subset_1(k16_lattice3(A_103,C_104),u1_struct_0(A_103))
      | ~ v9_lattices(A_103)
      | ~ v8_lattices(A_103)
      | ~ v6_lattices(A_103)
      | ~ r2_hidden(B_105,C_104)
      | ~ m1_subset_1(B_105,u1_struct_0(A_103))
      | ~ l3_lattices(A_103)
      | ~ v4_lattice3(A_103)
      | ~ v10_lattices(A_103)
      | v2_struct_0(A_103) ) ),
    inference(resolution,[status(thm)],[c_38,c_82])).

tff(c_215,plain,(
    ! [A_106,B_107,B_108] :
      ( r1_lattices(A_106,k16_lattice3(A_106,B_107),B_108)
      | ~ v9_lattices(A_106)
      | ~ v8_lattices(A_106)
      | ~ v6_lattices(A_106)
      | ~ r2_hidden(B_108,B_107)
      | ~ m1_subset_1(B_108,u1_struct_0(A_106))
      | ~ v4_lattice3(A_106)
      | ~ v10_lattices(A_106)
      | ~ l3_lattices(A_106)
      | v2_struct_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_26,c_211])).

tff(c_24,plain,(
    ! [C_12,B_10,A_6] :
      ( C_12 = B_10
      | ~ r1_lattices(A_6,C_12,B_10)
      | ~ r1_lattices(A_6,B_10,C_12)
      | ~ m1_subset_1(C_12,u1_struct_0(A_6))
      | ~ m1_subset_1(B_10,u1_struct_0(A_6))
      | ~ l2_lattices(A_6)
      | ~ v4_lattices(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_227,plain,(
    ! [A_115,B_116,B_117] :
      ( k16_lattice3(A_115,B_116) = B_117
      | ~ r1_lattices(A_115,B_117,k16_lattice3(A_115,B_116))
      | ~ m1_subset_1(k16_lattice3(A_115,B_116),u1_struct_0(A_115))
      | ~ l2_lattices(A_115)
      | ~ v4_lattices(A_115)
      | ~ v9_lattices(A_115)
      | ~ v8_lattices(A_115)
      | ~ v6_lattices(A_115)
      | ~ r2_hidden(B_117,B_116)
      | ~ m1_subset_1(B_117,u1_struct_0(A_115))
      | ~ v4_lattice3(A_115)
      | ~ v10_lattices(A_115)
      | ~ l3_lattices(A_115)
      | v2_struct_0(A_115) ) ),
    inference(resolution,[status(thm)],[c_215,c_24])).

tff(c_235,plain,(
    ! [A_118,B_119,D_120] :
      ( k16_lattice3(A_118,B_119) = D_120
      | ~ m1_subset_1(k16_lattice3(A_118,B_119),u1_struct_0(A_118))
      | ~ l2_lattices(A_118)
      | ~ v4_lattices(A_118)
      | ~ r2_hidden(D_120,B_119)
      | ~ v9_lattices(A_118)
      | ~ v8_lattices(A_118)
      | ~ v6_lattices(A_118)
      | ~ r3_lattice3(A_118,D_120,B_119)
      | ~ m1_subset_1(D_120,u1_struct_0(A_118))
      | ~ v4_lattice3(A_118)
      | ~ v10_lattices(A_118)
      | ~ l3_lattices(A_118)
      | v2_struct_0(A_118) ) ),
    inference(resolution,[status(thm)],[c_222,c_227])).

tff(c_239,plain,(
    ! [A_121,B_122,D_123] :
      ( k16_lattice3(A_121,B_122) = D_123
      | ~ l2_lattices(A_121)
      | ~ v4_lattices(A_121)
      | ~ r2_hidden(D_123,B_122)
      | ~ v9_lattices(A_121)
      | ~ v8_lattices(A_121)
      | ~ v6_lattices(A_121)
      | ~ r3_lattice3(A_121,D_123,B_122)
      | ~ m1_subset_1(D_123,u1_struct_0(A_121))
      | ~ v4_lattice3(A_121)
      | ~ v10_lattices(A_121)
      | ~ l3_lattices(A_121)
      | v2_struct_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_26,c_235])).

tff(c_245,plain,
    ( k16_lattice3('#skF_2','#skF_4') = '#skF_3'
    | ~ l2_lattices('#skF_2')
    | ~ v4_lattices('#skF_2')
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v9_lattices('#skF_2')
    | ~ v8_lattices('#skF_2')
    | ~ v6_lattices('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v4_lattice3('#skF_2')
    | ~ v10_lattices('#skF_2')
    | ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_239])).

tff(c_251,plain,
    ( k16_lattice3('#skF_2','#skF_4') = '#skF_3'
    | ~ v4_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_52,c_48,c_109,c_131,c_120,c_46,c_61,c_245])).

tff(c_252,plain,(
    ~ v4_lattices('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_42,c_251])).

tff(c_256,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_252])).

tff(c_259,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_256])).

tff(c_261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_259])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:02:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.36  
% 2.43/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.36  %$ r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.72/1.36  
% 2.72/1.36  %Foreground sorts:
% 2.72/1.36  
% 2.72/1.36  
% 2.72/1.36  %Background operators:
% 2.72/1.36  
% 2.72/1.36  
% 2.72/1.36  %Foreground operators:
% 2.72/1.36  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.72/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.72/1.36  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.72/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.72/1.36  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 2.72/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.36  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 2.72/1.36  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 2.72/1.36  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.72/1.36  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.72/1.36  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.72/1.36  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.72/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.36  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.72/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.36  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 2.72/1.36  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.72/1.36  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.72/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.72/1.36  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.72/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.72/1.36  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 2.72/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.72/1.36  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.72/1.36  
% 2.72/1.38  tff(f_161, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r3_lattice3(A, B, C)) => (k16_lattice3(A, C) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_lattice3)).
% 2.72/1.38  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 2.72/1.38  tff(f_72, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 2.72/1.38  tff(f_53, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.72/1.38  tff(f_98, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k16_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 2.72/1.38  tff(f_122, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 2.72/1.38  tff(f_141, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_lattice3)).
% 2.72/1.38  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_lattices(A, B, C) & r1_lattices(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_lattices)).
% 2.72/1.38  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.72/1.38  tff(c_50, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.72/1.38  tff(c_54, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.72/1.38  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.72/1.38  tff(c_42, plain, (k16_lattice3('#skF_2', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.72/1.38  tff(c_52, plain, (v4_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.72/1.38  tff(c_48, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.72/1.38  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.72/1.38  tff(c_89, plain, (![A_74, B_75, C_76]: (r3_lattices(A_74, B_75, C_76) | ~r1_lattices(A_74, B_75, C_76) | ~m1_subset_1(C_76, u1_struct_0(A_74)) | ~m1_subset_1(B_75, u1_struct_0(A_74)) | ~l3_lattices(A_74) | ~v9_lattices(A_74) | ~v8_lattices(A_74) | ~v6_lattices(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.72/1.38  tff(c_93, plain, (![B_75]: (r3_lattices('#skF_2', B_75, '#skF_3') | ~r1_lattices('#skF_2', B_75, '#skF_3') | ~m1_subset_1(B_75, u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_89])).
% 2.72/1.38  tff(c_97, plain, (![B_75]: (r3_lattices('#skF_2', B_75, '#skF_3') | ~r1_lattices('#skF_2', B_75, '#skF_3') | ~m1_subset_1(B_75, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_93])).
% 2.72/1.38  tff(c_98, plain, (![B_75]: (r3_lattices('#skF_2', B_75, '#skF_3') | ~r1_lattices('#skF_2', B_75, '#skF_3') | ~m1_subset_1(B_75, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_97])).
% 2.72/1.38  tff(c_99, plain, (~v6_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_98])).
% 2.72/1.38  tff(c_102, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_8, c_99])).
% 2.72/1.38  tff(c_105, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_102])).
% 2.72/1.38  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_105])).
% 2.72/1.38  tff(c_109, plain, (v6_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_98])).
% 2.72/1.38  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.72/1.38  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.72/1.38  tff(c_108, plain, (![B_75]: (~v8_lattices('#skF_2') | ~v9_lattices('#skF_2') | r3_lattices('#skF_2', B_75, '#skF_3') | ~r1_lattices('#skF_2', B_75, '#skF_3') | ~m1_subset_1(B_75, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_98])).
% 2.72/1.38  tff(c_110, plain, (~v9_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_108])).
% 2.72/1.38  tff(c_113, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_2, c_110])).
% 2.72/1.38  tff(c_116, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_113])).
% 2.72/1.38  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_116])).
% 2.72/1.38  tff(c_119, plain, (![B_75]: (~v8_lattices('#skF_2') | r3_lattices('#skF_2', B_75, '#skF_3') | ~r1_lattices('#skF_2', B_75, '#skF_3') | ~m1_subset_1(B_75, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_108])).
% 2.72/1.38  tff(c_121, plain, (~v8_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_119])).
% 2.72/1.38  tff(c_124, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_4, c_121])).
% 2.72/1.38  tff(c_127, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_124])).
% 2.72/1.38  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_127])).
% 2.72/1.38  tff(c_131, plain, (v8_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_119])).
% 2.72/1.38  tff(c_120, plain, (v9_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_108])).
% 2.72/1.38  tff(c_46, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.72/1.38  tff(c_57, plain, (![A_48]: (l2_lattices(A_48) | ~l3_lattices(A_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.72/1.38  tff(c_61, plain, (l2_lattices('#skF_2')), inference(resolution, [status(thm)], [c_50, c_57])).
% 2.72/1.38  tff(c_44, plain, (r3_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.72/1.38  tff(c_26, plain, (![A_13, B_14]: (m1_subset_1(k16_lattice3(A_13, B_14), u1_struct_0(A_13)) | ~l3_lattices(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.72/1.38  tff(c_197, plain, (![A_94, D_95, C_96]: (r3_lattices(A_94, D_95, k16_lattice3(A_94, C_96)) | ~r3_lattice3(A_94, D_95, C_96) | ~m1_subset_1(D_95, u1_struct_0(A_94)) | ~m1_subset_1(k16_lattice3(A_94, C_96), u1_struct_0(A_94)) | ~l3_lattices(A_94) | ~v4_lattice3(A_94) | ~v10_lattices(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.72/1.38  tff(c_201, plain, (![A_97, D_98, B_99]: (r3_lattices(A_97, D_98, k16_lattice3(A_97, B_99)) | ~r3_lattice3(A_97, D_98, B_99) | ~m1_subset_1(D_98, u1_struct_0(A_97)) | ~v4_lattice3(A_97) | ~v10_lattices(A_97) | ~l3_lattices(A_97) | v2_struct_0(A_97))), inference(resolution, [status(thm)], [c_26, c_197])).
% 2.72/1.38  tff(c_22, plain, (![A_3, B_4, C_5]: (r1_lattices(A_3, B_4, C_5) | ~r3_lattices(A_3, B_4, C_5) | ~m1_subset_1(C_5, u1_struct_0(A_3)) | ~m1_subset_1(B_4, u1_struct_0(A_3)) | ~l3_lattices(A_3) | ~v9_lattices(A_3) | ~v8_lattices(A_3) | ~v6_lattices(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.72/1.38  tff(c_219, plain, (![A_109, D_110, B_111]: (r1_lattices(A_109, D_110, k16_lattice3(A_109, B_111)) | ~m1_subset_1(k16_lattice3(A_109, B_111), u1_struct_0(A_109)) | ~v9_lattices(A_109) | ~v8_lattices(A_109) | ~v6_lattices(A_109) | ~r3_lattice3(A_109, D_110, B_111) | ~m1_subset_1(D_110, u1_struct_0(A_109)) | ~v4_lattice3(A_109) | ~v10_lattices(A_109) | ~l3_lattices(A_109) | v2_struct_0(A_109))), inference(resolution, [status(thm)], [c_201, c_22])).
% 2.72/1.38  tff(c_222, plain, (![A_13, D_110, B_14]: (r1_lattices(A_13, D_110, k16_lattice3(A_13, B_14)) | ~v9_lattices(A_13) | ~v8_lattices(A_13) | ~v6_lattices(A_13) | ~r3_lattice3(A_13, D_110, B_14) | ~m1_subset_1(D_110, u1_struct_0(A_13)) | ~v4_lattice3(A_13) | ~v10_lattices(A_13) | ~l3_lattices(A_13) | v2_struct_0(A_13))), inference(resolution, [status(thm)], [c_26, c_219])).
% 2.72/1.38  tff(c_38, plain, (![A_37, C_43, B_41]: (r3_lattices(A_37, k16_lattice3(A_37, C_43), B_41) | ~r2_hidden(B_41, C_43) | ~m1_subset_1(B_41, u1_struct_0(A_37)) | ~l3_lattices(A_37) | ~v4_lattice3(A_37) | ~v10_lattices(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.72/1.38  tff(c_82, plain, (![A_71, B_72, C_73]: (r1_lattices(A_71, B_72, C_73) | ~r3_lattices(A_71, B_72, C_73) | ~m1_subset_1(C_73, u1_struct_0(A_71)) | ~m1_subset_1(B_72, u1_struct_0(A_71)) | ~l3_lattices(A_71) | ~v9_lattices(A_71) | ~v8_lattices(A_71) | ~v6_lattices(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.72/1.38  tff(c_211, plain, (![A_103, C_104, B_105]: (r1_lattices(A_103, k16_lattice3(A_103, C_104), B_105) | ~m1_subset_1(k16_lattice3(A_103, C_104), u1_struct_0(A_103)) | ~v9_lattices(A_103) | ~v8_lattices(A_103) | ~v6_lattices(A_103) | ~r2_hidden(B_105, C_104) | ~m1_subset_1(B_105, u1_struct_0(A_103)) | ~l3_lattices(A_103) | ~v4_lattice3(A_103) | ~v10_lattices(A_103) | v2_struct_0(A_103))), inference(resolution, [status(thm)], [c_38, c_82])).
% 2.72/1.38  tff(c_215, plain, (![A_106, B_107, B_108]: (r1_lattices(A_106, k16_lattice3(A_106, B_107), B_108) | ~v9_lattices(A_106) | ~v8_lattices(A_106) | ~v6_lattices(A_106) | ~r2_hidden(B_108, B_107) | ~m1_subset_1(B_108, u1_struct_0(A_106)) | ~v4_lattice3(A_106) | ~v10_lattices(A_106) | ~l3_lattices(A_106) | v2_struct_0(A_106))), inference(resolution, [status(thm)], [c_26, c_211])).
% 2.72/1.38  tff(c_24, plain, (![C_12, B_10, A_6]: (C_12=B_10 | ~r1_lattices(A_6, C_12, B_10) | ~r1_lattices(A_6, B_10, C_12) | ~m1_subset_1(C_12, u1_struct_0(A_6)) | ~m1_subset_1(B_10, u1_struct_0(A_6)) | ~l2_lattices(A_6) | ~v4_lattices(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.72/1.38  tff(c_227, plain, (![A_115, B_116, B_117]: (k16_lattice3(A_115, B_116)=B_117 | ~r1_lattices(A_115, B_117, k16_lattice3(A_115, B_116)) | ~m1_subset_1(k16_lattice3(A_115, B_116), u1_struct_0(A_115)) | ~l2_lattices(A_115) | ~v4_lattices(A_115) | ~v9_lattices(A_115) | ~v8_lattices(A_115) | ~v6_lattices(A_115) | ~r2_hidden(B_117, B_116) | ~m1_subset_1(B_117, u1_struct_0(A_115)) | ~v4_lattice3(A_115) | ~v10_lattices(A_115) | ~l3_lattices(A_115) | v2_struct_0(A_115))), inference(resolution, [status(thm)], [c_215, c_24])).
% 2.72/1.38  tff(c_235, plain, (![A_118, B_119, D_120]: (k16_lattice3(A_118, B_119)=D_120 | ~m1_subset_1(k16_lattice3(A_118, B_119), u1_struct_0(A_118)) | ~l2_lattices(A_118) | ~v4_lattices(A_118) | ~r2_hidden(D_120, B_119) | ~v9_lattices(A_118) | ~v8_lattices(A_118) | ~v6_lattices(A_118) | ~r3_lattice3(A_118, D_120, B_119) | ~m1_subset_1(D_120, u1_struct_0(A_118)) | ~v4_lattice3(A_118) | ~v10_lattices(A_118) | ~l3_lattices(A_118) | v2_struct_0(A_118))), inference(resolution, [status(thm)], [c_222, c_227])).
% 2.72/1.38  tff(c_239, plain, (![A_121, B_122, D_123]: (k16_lattice3(A_121, B_122)=D_123 | ~l2_lattices(A_121) | ~v4_lattices(A_121) | ~r2_hidden(D_123, B_122) | ~v9_lattices(A_121) | ~v8_lattices(A_121) | ~v6_lattices(A_121) | ~r3_lattice3(A_121, D_123, B_122) | ~m1_subset_1(D_123, u1_struct_0(A_121)) | ~v4_lattice3(A_121) | ~v10_lattices(A_121) | ~l3_lattices(A_121) | v2_struct_0(A_121))), inference(resolution, [status(thm)], [c_26, c_235])).
% 2.72/1.38  tff(c_245, plain, (k16_lattice3('#skF_2', '#skF_4')='#skF_3' | ~l2_lattices('#skF_2') | ~v4_lattices('#skF_2') | ~r2_hidden('#skF_3', '#skF_4') | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v4_lattice3('#skF_2') | ~v10_lattices('#skF_2') | ~l3_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_239])).
% 2.72/1.38  tff(c_251, plain, (k16_lattice3('#skF_2', '#skF_4')='#skF_3' | ~v4_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_52, c_48, c_109, c_131, c_120, c_46, c_61, c_245])).
% 2.72/1.38  tff(c_252, plain, (~v4_lattices('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_42, c_251])).
% 2.72/1.38  tff(c_256, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_12, c_252])).
% 2.72/1.38  tff(c_259, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_256])).
% 2.72/1.38  tff(c_261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_259])).
% 2.72/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.38  
% 2.72/1.38  Inference rules
% 2.72/1.38  ----------------------
% 2.72/1.38  #Ref     : 0
% 2.72/1.38  #Sup     : 34
% 2.72/1.38  #Fact    : 0
% 2.72/1.38  #Define  : 0
% 2.72/1.38  #Split   : 4
% 2.72/1.38  #Chain   : 0
% 2.72/1.38  #Close   : 0
% 2.72/1.38  
% 2.72/1.38  Ordering : KBO
% 2.72/1.38  
% 2.72/1.38  Simplification rules
% 2.72/1.38  ----------------------
% 2.72/1.38  #Subsume      : 5
% 2.72/1.38  #Demod        : 36
% 2.72/1.38  #Tautology    : 5
% 2.72/1.38  #SimpNegUnit  : 11
% 2.72/1.38  #BackRed      : 0
% 2.72/1.38  
% 2.72/1.38  #Partial instantiations: 0
% 2.72/1.38  #Strategies tried      : 1
% 2.72/1.38  
% 2.72/1.38  Timing (in seconds)
% 2.72/1.38  ----------------------
% 2.72/1.39  Preprocessing        : 0.31
% 2.72/1.39  Parsing              : 0.17
% 2.72/1.39  CNF conversion       : 0.03
% 2.72/1.39  Main loop            : 0.27
% 2.72/1.39  Inferencing          : 0.11
% 2.72/1.39  Reduction            : 0.07
% 2.72/1.39  Demodulation         : 0.05
% 2.72/1.39  BG Simplification    : 0.02
% 2.72/1.39  Subsumption          : 0.06
% 2.72/1.39  Abstraction          : 0.01
% 2.72/1.39  MUC search           : 0.00
% 2.72/1.39  Cooper               : 0.00
% 2.72/1.39  Total                : 0.62
% 2.72/1.39  Index Insertion      : 0.00
% 2.72/1.39  Index Deletion       : 0.00
% 2.72/1.39  Index Matching       : 0.00
% 2.72/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
