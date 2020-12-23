%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:44 EST 2020

% Result     : Theorem 9.17s
% Output     : CNFRefutation 9.39s
% Verified   : 
% Statistics : Number of formulae       :  158 (1229 expanded)
%              Number of leaves         :   40 ( 419 expanded)
%              Depth                    :   26
%              Number of atoms          :  703 (6020 expanded)
%              Number of equality atoms :    6 (  23 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k3_lattices > a_3_4_lattice3 > k16_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3

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

tff(a_3_4_lattice3,type,(
    a_3_4_lattice3: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_198,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] : r3_lattices(A,k3_lattices(A,B,k16_lattice3(A,C)),k16_lattice3(A,a_3_4_lattice3(A,B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_lattice3)).

tff(f_138,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k16_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

tff(f_182,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

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

tff(f_66,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_lattices(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_lattices)).

tff(f_85,axiom,(
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

tff(f_158,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v2_struct_0(B)
        & v10_lattices(B)
        & v4_lattice3(B)
        & l3_lattices(B)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( r2_hidden(A,a_3_4_lattice3(B,C,D))
      <=> ? [E] :
            ( m1_subset_1(E,u1_struct_0(B))
            & A = k3_lattices(B,C,E)
            & r2_hidden(E,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_3_4_lattice3)).

tff(f_131,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r3_lattice3(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_hidden(D,C)
                   => r1_lattices(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

tff(f_113,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & v5_lattices(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r3_lattices(A,B,C)
                   => r3_lattices(A,k3_lattices(A,D,B),k3_lattices(A,D,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_filter_0)).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_60,plain,(
    l3_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_64,plain,(
    v10_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_62,plain,(
    v4_lattice3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_36,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k16_lattice3(A_46,B_47),u1_struct_0(A_46))
      | ~ l3_lattices(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_87,plain,(
    ! [A_100,C_101] :
      ( r3_lattice3(A_100,k16_lattice3(A_100,C_101),C_101)
      | ~ m1_subset_1(k16_lattice3(A_100,C_101),u1_struct_0(A_100))
      | ~ l3_lattices(A_100)
      | ~ v4_lattice3(A_100)
      | ~ v10_lattices(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_90,plain,(
    ! [A_46,B_47] :
      ( r3_lattice3(A_46,k16_lattice3(A_46,B_47),B_47)
      | ~ v4_lattice3(A_46)
      | ~ v10_lattices(A_46)
      | ~ l3_lattices(A_46)
      | v2_struct_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_36,c_87])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_72,plain,(
    ! [A_82] :
      ( l2_lattices(A_82)
      | ~ l3_lattices(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_76,plain,(
    l2_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_72])).

tff(c_16,plain,(
    ! [A_2,B_3,C_4] :
      ( m1_subset_1(k3_lattices(A_2,B_3,C_4),u1_struct_0(A_2))
      | ~ m1_subset_1(C_4,u1_struct_0(A_2))
      | ~ m1_subset_1(B_3,u1_struct_0(A_2))
      | ~ l2_lattices(A_2)
      | ~ v4_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

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

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_102,plain,(
    ! [A_118,B_119,C_120] :
      ( r3_lattices(A_118,B_119,C_120)
      | ~ r1_lattices(A_118,B_119,C_120)
      | ~ m1_subset_1(C_120,u1_struct_0(A_118))
      | ~ m1_subset_1(B_119,u1_struct_0(A_118))
      | ~ l3_lattices(A_118)
      | ~ v9_lattices(A_118)
      | ~ v8_lattices(A_118)
      | ~ v6_lattices(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_110,plain,(
    ! [B_119] :
      ( r3_lattices('#skF_4',B_119,'#skF_5')
      | ~ r1_lattices('#skF_4',B_119,'#skF_5')
      | ~ m1_subset_1(B_119,u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_102])).

tff(c_116,plain,(
    ! [B_119] :
      ( r3_lattices('#skF_4',B_119,'#skF_5')
      | ~ r1_lattices('#skF_4',B_119,'#skF_5')
      | ~ m1_subset_1(B_119,u1_struct_0('#skF_4'))
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_110])).

tff(c_117,plain,(
    ! [B_119] :
      ( r3_lattices('#skF_4',B_119,'#skF_5')
      | ~ r1_lattices('#skF_4',B_119,'#skF_5')
      | ~ m1_subset_1(B_119,u1_struct_0('#skF_4'))
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | ~ v6_lattices('#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_116])).

tff(c_118,plain,(
    ~ v6_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_121,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_118])).

tff(c_124,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64,c_121])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_124])).

tff(c_127,plain,(
    ! [B_119] :
      ( ~ v8_lattices('#skF_4')
      | ~ v9_lattices('#skF_4')
      | r3_lattices('#skF_4',B_119,'#skF_5')
      | ~ r1_lattices('#skF_4',B_119,'#skF_5')
      | ~ m1_subset_1(B_119,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_129,plain,(
    ~ v9_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_132,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_129])).

tff(c_135,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64,c_132])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_135])).

tff(c_138,plain,(
    ! [B_119] :
      ( ~ v8_lattices('#skF_4')
      | r3_lattices('#skF_4',B_119,'#skF_5')
      | ~ r1_lattices('#skF_4',B_119,'#skF_5')
      | ~ m1_subset_1(B_119,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_140,plain,(
    ~ v8_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_143,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_140])).

tff(c_146,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64,c_143])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_146])).

tff(c_155,plain,(
    ! [B_125] :
      ( r3_lattices('#skF_4',B_125,'#skF_5')
      | ~ r1_lattices('#skF_4',B_125,'#skF_5')
      | ~ m1_subset_1(B_125,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_163,plain,(
    ! [B_3,C_4] :
      ( r3_lattices('#skF_4',k3_lattices('#skF_4',B_3,C_4),'#skF_5')
      | ~ r1_lattices('#skF_4',k3_lattices('#skF_4',B_3,C_4),'#skF_5')
      | ~ m1_subset_1(C_4,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_3,u1_struct_0('#skF_4'))
      | ~ l2_lattices('#skF_4')
      | ~ v4_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_155])).

tff(c_181,plain,(
    ! [B_3,C_4] :
      ( r3_lattices('#skF_4',k3_lattices('#skF_4',B_3,C_4),'#skF_5')
      | ~ r1_lattices('#skF_4',k3_lattices('#skF_4',B_3,C_4),'#skF_5')
      | ~ m1_subset_1(C_4,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_3,u1_struct_0('#skF_4'))
      | ~ v4_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_163])).

tff(c_182,plain,(
    ! [B_3,C_4] :
      ( r3_lattices('#skF_4',k3_lattices('#skF_4',B_3,C_4),'#skF_5')
      | ~ r1_lattices('#skF_4',k3_lattices('#skF_4',B_3,C_4),'#skF_5')
      | ~ m1_subset_1(C_4,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_3,u1_struct_0('#skF_4'))
      | ~ v4_lattices('#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_181])).

tff(c_207,plain,(
    ~ v4_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_210,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_207])).

tff(c_213,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64,c_210])).

tff(c_215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_213])).

tff(c_217,plain,(
    v4_lattices('#skF_4') ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_128,plain,(
    v6_lattices('#skF_4') ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_150,plain,(
    v8_lattices('#skF_4') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_139,plain,(
    v9_lattices('#skF_4') ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_226,plain,(
    ! [A_134,B_135,B_136] :
      ( r3_lattices(A_134,B_135,k16_lattice3(A_134,B_136))
      | ~ r1_lattices(A_134,B_135,k16_lattice3(A_134,B_136))
      | ~ m1_subset_1(B_135,u1_struct_0(A_134))
      | ~ v9_lattices(A_134)
      | ~ v8_lattices(A_134)
      | ~ v6_lattices(A_134)
      | ~ l3_lattices(A_134)
      | v2_struct_0(A_134) ) ),
    inference(resolution,[status(thm)],[c_36,c_102])).

tff(c_56,plain,(
    ~ r3_lattices('#skF_4',k3_lattices('#skF_4','#skF_5',k16_lattice3('#skF_4','#skF_6')),k16_lattice3('#skF_4',a_3_4_lattice3('#skF_4','#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_235,plain,
    ( ~ r1_lattices('#skF_4',k3_lattices('#skF_4','#skF_5',k16_lattice3('#skF_4','#skF_6')),k16_lattice3('#skF_4',a_3_4_lattice3('#skF_4','#skF_5','#skF_6')))
    | ~ m1_subset_1(k3_lattices('#skF_4','#skF_5',k16_lattice3('#skF_4','#skF_6')),u1_struct_0('#skF_4'))
    | ~ v9_lattices('#skF_4')
    | ~ v8_lattices('#skF_4')
    | ~ v6_lattices('#skF_4')
    | ~ l3_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_226,c_56])).

tff(c_240,plain,
    ( ~ r1_lattices('#skF_4',k3_lattices('#skF_4','#skF_5',k16_lattice3('#skF_4','#skF_6')),k16_lattice3('#skF_4',a_3_4_lattice3('#skF_4','#skF_5','#skF_6')))
    | ~ m1_subset_1(k3_lattices('#skF_4','#skF_5',k16_lattice3('#skF_4','#skF_6')),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_128,c_150,c_139,c_235])).

tff(c_241,plain,
    ( ~ r1_lattices('#skF_4',k3_lattices('#skF_4','#skF_5',k16_lattice3('#skF_4','#skF_6')),k16_lattice3('#skF_4',a_3_4_lattice3('#skF_4','#skF_5','#skF_6')))
    | ~ m1_subset_1(k3_lattices('#skF_4','#skF_5',k16_lattice3('#skF_4','#skF_6')),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_240])).

tff(c_242,plain,(
    ~ m1_subset_1(k3_lattices('#skF_4','#skF_5',k16_lattice3('#skF_4','#skF_6')),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_241])).

tff(c_252,plain,
    ( ~ m1_subset_1(k16_lattice3('#skF_4','#skF_6'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l2_lattices('#skF_4')
    | ~ v4_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_242])).

tff(c_255,plain,
    ( ~ m1_subset_1(k16_lattice3('#skF_4','#skF_6'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_76,c_58,c_252])).

tff(c_256,plain,(
    ~ m1_subset_1(k16_lattice3('#skF_4','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_255])).

tff(c_259,plain,
    ( ~ l3_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_256])).

tff(c_262,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_259])).

tff(c_264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_262])).

tff(c_266,plain,(
    m1_subset_1(k3_lattices('#skF_4','#skF_5',k16_lattice3('#skF_4','#skF_6')),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_343,plain,(
    ! [B_161,C_162,E_163,D_164] :
      ( r2_hidden(k3_lattices(B_161,C_162,E_163),a_3_4_lattice3(B_161,C_162,D_164))
      | ~ r2_hidden(E_163,D_164)
      | ~ m1_subset_1(E_163,u1_struct_0(B_161))
      | ~ m1_subset_1(C_162,u1_struct_0(B_161))
      | ~ l3_lattices(B_161)
      | ~ v4_lattice3(B_161)
      | ~ v10_lattices(B_161)
      | v2_struct_0(B_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_28,plain,(
    ! [A_24,B_36,D_45,C_42] :
      ( r1_lattices(A_24,B_36,D_45)
      | ~ r2_hidden(D_45,C_42)
      | ~ m1_subset_1(D_45,u1_struct_0(A_24))
      | ~ r3_lattice3(A_24,B_36,C_42)
      | ~ m1_subset_1(B_36,u1_struct_0(A_24))
      | ~ l3_lattices(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_514,plain,(
    ! [B_234,C_230,E_233,A_232,B_231,D_229] :
      ( r1_lattices(A_232,B_234,k3_lattices(B_231,C_230,E_233))
      | ~ m1_subset_1(k3_lattices(B_231,C_230,E_233),u1_struct_0(A_232))
      | ~ r3_lattice3(A_232,B_234,a_3_4_lattice3(B_231,C_230,D_229))
      | ~ m1_subset_1(B_234,u1_struct_0(A_232))
      | ~ l3_lattices(A_232)
      | v2_struct_0(A_232)
      | ~ r2_hidden(E_233,D_229)
      | ~ m1_subset_1(E_233,u1_struct_0(B_231))
      | ~ m1_subset_1(C_230,u1_struct_0(B_231))
      | ~ l3_lattices(B_231)
      | ~ v4_lattice3(B_231)
      | ~ v10_lattices(B_231)
      | v2_struct_0(B_231) ) ),
    inference(resolution,[status(thm)],[c_343,c_28])).

tff(c_518,plain,(
    ! [B_234,D_229] :
      ( r1_lattices('#skF_4',B_234,k3_lattices('#skF_4','#skF_5',k16_lattice3('#skF_4','#skF_6')))
      | ~ r3_lattice3('#skF_4',B_234,a_3_4_lattice3('#skF_4','#skF_5',D_229))
      | ~ m1_subset_1(B_234,u1_struct_0('#skF_4'))
      | ~ r2_hidden(k16_lattice3('#skF_4','#skF_6'),D_229)
      | ~ m1_subset_1(k16_lattice3('#skF_4','#skF_6'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v4_lattice3('#skF_4')
      | ~ v10_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_266,c_514])).

tff(c_523,plain,(
    ! [B_234,D_229] :
      ( r1_lattices('#skF_4',B_234,k3_lattices('#skF_4','#skF_5',k16_lattice3('#skF_4','#skF_6')))
      | ~ r3_lattice3('#skF_4',B_234,a_3_4_lattice3('#skF_4','#skF_5',D_229))
      | ~ m1_subset_1(B_234,u1_struct_0('#skF_4'))
      | ~ r2_hidden(k16_lattice3('#skF_4','#skF_6'),D_229)
      | ~ m1_subset_1(k16_lattice3('#skF_4','#skF_6'),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_518])).

tff(c_524,plain,(
    ! [B_234,D_229] :
      ( r1_lattices('#skF_4',B_234,k3_lattices('#skF_4','#skF_5',k16_lattice3('#skF_4','#skF_6')))
      | ~ r3_lattice3('#skF_4',B_234,a_3_4_lattice3('#skF_4','#skF_5',D_229))
      | ~ m1_subset_1(B_234,u1_struct_0('#skF_4'))
      | ~ r2_hidden(k16_lattice3('#skF_4','#skF_6'),D_229)
      | ~ m1_subset_1(k16_lattice3('#skF_4','#skF_6'),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_523])).

tff(c_526,plain,(
    ~ m1_subset_1(k16_lattice3('#skF_4','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_524])).

tff(c_579,plain,
    ( ~ l3_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_526])).

tff(c_582,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_579])).

tff(c_584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_582])).

tff(c_586,plain,(
    m1_subset_1(k16_lattice3('#skF_4','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_524])).

tff(c_10,plain,(
    ! [A_1] :
      ( v5_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( r3_lattices(A_6,B_7,C_8)
      | ~ r1_lattices(A_6,B_7,C_8)
      | ~ m1_subset_1(C_8,u1_struct_0(A_6))
      | ~ m1_subset_1(B_7,u1_struct_0(A_6))
      | ~ l3_lattices(A_6)
      | ~ v9_lattices(A_6)
      | ~ v8_lattices(A_6)
      | ~ v6_lattices(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_591,plain,(
    ! [B_7] :
      ( r3_lattices('#skF_4',B_7,k16_lattice3('#skF_4','#skF_6'))
      | ~ r1_lattices('#skF_4',B_7,k16_lattice3('#skF_4','#skF_6'))
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_586,c_22])).

tff(c_595,plain,(
    ! [B_7] :
      ( r3_lattices('#skF_4',B_7,k16_lattice3('#skF_4','#skF_6'))
      | ~ r1_lattices('#skF_4',B_7,k16_lattice3('#skF_4','#skF_6'))
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_150,c_139,c_60,c_591])).

tff(c_596,plain,(
    ! [B_7] :
      ( r3_lattices('#skF_4',B_7,k16_lattice3('#skF_4','#skF_6'))
      | ~ r1_lattices('#skF_4',B_7,k16_lattice3('#skF_4','#skF_6'))
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_595])).

tff(c_42,plain,(
    ! [B_49,C_50,A_48,D_51] :
      ( k3_lattices(B_49,C_50,'#skF_2'(A_48,B_49,C_50,D_51)) = A_48
      | ~ r2_hidden(A_48,a_3_4_lattice3(B_49,C_50,D_51))
      | ~ m1_subset_1(C_50,u1_struct_0(B_49))
      | ~ l3_lattices(B_49)
      | ~ v4_lattice3(B_49)
      | ~ v10_lattices(B_49)
      | v2_struct_0(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_348,plain,(
    ! [B_161,C_162,E_163,D_164] :
      ( k3_lattices(B_161,C_162,'#skF_2'(k3_lattices(B_161,C_162,E_163),B_161,C_162,D_164)) = k3_lattices(B_161,C_162,E_163)
      | ~ r2_hidden(E_163,D_164)
      | ~ m1_subset_1(E_163,u1_struct_0(B_161))
      | ~ m1_subset_1(C_162,u1_struct_0(B_161))
      | ~ l3_lattices(B_161)
      | ~ v4_lattice3(B_161)
      | ~ v10_lattices(B_161)
      | v2_struct_0(B_161) ) ),
    inference(resolution,[status(thm)],[c_343,c_42])).

tff(c_440,plain,(
    ! [A_194,D_195,B_196,C_197] :
      ( r3_lattices(A_194,k3_lattices(A_194,D_195,B_196),k3_lattices(A_194,D_195,C_197))
      | ~ r3_lattices(A_194,B_196,C_197)
      | ~ m1_subset_1(D_195,u1_struct_0(A_194))
      | ~ m1_subset_1(C_197,u1_struct_0(A_194))
      | ~ m1_subset_1(B_196,u1_struct_0(A_194))
      | ~ l3_lattices(A_194)
      | ~ v9_lattices(A_194)
      | ~ v8_lattices(A_194)
      | ~ v6_lattices(A_194)
      | ~ v5_lattices(A_194)
      | ~ v4_lattices(A_194)
      | v2_struct_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1371,plain,(
    ! [C_454,B_453,C_452,D_451,E_455] :
      ( r3_lattices(B_453,k3_lattices(B_453,C_452,E_455),k3_lattices(B_453,C_452,C_454))
      | ~ r3_lattices(B_453,'#skF_2'(k3_lattices(B_453,C_452,E_455),B_453,C_452,D_451),C_454)
      | ~ m1_subset_1(C_452,u1_struct_0(B_453))
      | ~ m1_subset_1(C_454,u1_struct_0(B_453))
      | ~ m1_subset_1('#skF_2'(k3_lattices(B_453,C_452,E_455),B_453,C_452,D_451),u1_struct_0(B_453))
      | ~ l3_lattices(B_453)
      | ~ v9_lattices(B_453)
      | ~ v8_lattices(B_453)
      | ~ v6_lattices(B_453)
      | ~ v5_lattices(B_453)
      | ~ v4_lattices(B_453)
      | v2_struct_0(B_453)
      | ~ r2_hidden(E_455,D_451)
      | ~ m1_subset_1(E_455,u1_struct_0(B_453))
      | ~ m1_subset_1(C_452,u1_struct_0(B_453))
      | ~ l3_lattices(B_453)
      | ~ v4_lattice3(B_453)
      | ~ v10_lattices(B_453)
      | v2_struct_0(B_453) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_440])).

tff(c_1387,plain,(
    ! [C_452,E_455,D_451] :
      ( r3_lattices('#skF_4',k3_lattices('#skF_4',C_452,E_455),k3_lattices('#skF_4',C_452,k16_lattice3('#skF_4','#skF_6')))
      | ~ m1_subset_1(k16_lattice3('#skF_4','#skF_6'),u1_struct_0('#skF_4'))
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | ~ v6_lattices('#skF_4')
      | ~ v5_lattices('#skF_4')
      | ~ v4_lattices('#skF_4')
      | ~ r2_hidden(E_455,D_451)
      | ~ m1_subset_1(E_455,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_452,u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v4_lattice3('#skF_4')
      | ~ v10_lattices('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_lattices('#skF_4','#skF_2'(k3_lattices('#skF_4',C_452,E_455),'#skF_4',C_452,D_451),k16_lattice3('#skF_4','#skF_6'))
      | ~ m1_subset_1('#skF_2'(k3_lattices('#skF_4',C_452,E_455),'#skF_4',C_452,D_451),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_596,c_1371])).

tff(c_1422,plain,(
    ! [C_452,E_455,D_451] :
      ( r3_lattices('#skF_4',k3_lattices('#skF_4',C_452,E_455),k3_lattices('#skF_4',C_452,k16_lattice3('#skF_4','#skF_6')))
      | ~ v5_lattices('#skF_4')
      | ~ r2_hidden(E_455,D_451)
      | ~ m1_subset_1(E_455,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_452,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ r1_lattices('#skF_4','#skF_2'(k3_lattices('#skF_4',C_452,E_455),'#skF_4',C_452,D_451),k16_lattice3('#skF_4','#skF_6'))
      | ~ m1_subset_1('#skF_2'(k3_lattices('#skF_4',C_452,E_455),'#skF_4',C_452,D_451),u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_217,c_128,c_150,c_139,c_586,c_1387])).

tff(c_1423,plain,(
    ! [C_452,E_455,D_451] :
      ( r3_lattices('#skF_4',k3_lattices('#skF_4',C_452,E_455),k3_lattices('#skF_4',C_452,k16_lattice3('#skF_4','#skF_6')))
      | ~ v5_lattices('#skF_4')
      | ~ r2_hidden(E_455,D_451)
      | ~ m1_subset_1(E_455,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_452,u1_struct_0('#skF_4'))
      | ~ r1_lattices('#skF_4','#skF_2'(k3_lattices('#skF_4',C_452,E_455),'#skF_4',C_452,D_451),k16_lattice3('#skF_4','#skF_6'))
      | ~ m1_subset_1('#skF_2'(k3_lattices('#skF_4',C_452,E_455),'#skF_4',C_452,D_451),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1422])).

tff(c_1438,plain,(
    ~ v5_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1423])).

tff(c_1469,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_1438])).

tff(c_1472,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64,c_1469])).

tff(c_1474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1472])).

tff(c_1476,plain,(
    v5_lattices('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1423])).

tff(c_34,plain,(
    ! [A_24,B_36,C_42] :
      ( m1_subset_1('#skF_1'(A_24,B_36,C_42),u1_struct_0(A_24))
      | r3_lattice3(A_24,B_36,C_42)
      | ~ m1_subset_1(B_36,u1_struct_0(A_24))
      | ~ l3_lattices(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_32,plain,(
    ! [A_24,B_36,C_42] :
      ( r2_hidden('#skF_1'(A_24,B_36,C_42),C_42)
      | r3_lattice3(A_24,B_36,C_42)
      | ~ m1_subset_1(B_36,u1_struct_0(A_24))
      | ~ l3_lattices(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_44,plain,(
    ! [A_48,B_49,C_50,D_51] :
      ( m1_subset_1('#skF_2'(A_48,B_49,C_50,D_51),u1_struct_0(B_49))
      | ~ r2_hidden(A_48,a_3_4_lattice3(B_49,C_50,D_51))
      | ~ m1_subset_1(C_50,u1_struct_0(B_49))
      | ~ l3_lattices(B_49)
      | ~ v4_lattice3(B_49)
      | ~ v10_lattices(B_49)
      | v2_struct_0(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_97,plain,(
    ! [A_111,B_112,C_113,D_114] :
      ( r2_hidden('#skF_2'(A_111,B_112,C_113,D_114),D_114)
      | ~ r2_hidden(A_111,a_3_4_lattice3(B_112,C_113,D_114))
      | ~ m1_subset_1(C_113,u1_struct_0(B_112))
      | ~ l3_lattices(B_112)
      | ~ v4_lattice3(B_112)
      | ~ v10_lattices(B_112)
      | v2_struct_0(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_509,plain,(
    ! [B_222,D_219,A_221,A_220,C_218,B_223] :
      ( r1_lattices(A_220,B_223,'#skF_2'(A_221,B_222,C_218,D_219))
      | ~ m1_subset_1('#skF_2'(A_221,B_222,C_218,D_219),u1_struct_0(A_220))
      | ~ r3_lattice3(A_220,B_223,D_219)
      | ~ m1_subset_1(B_223,u1_struct_0(A_220))
      | ~ l3_lattices(A_220)
      | v2_struct_0(A_220)
      | ~ r2_hidden(A_221,a_3_4_lattice3(B_222,C_218,D_219))
      | ~ m1_subset_1(C_218,u1_struct_0(B_222))
      | ~ l3_lattices(B_222)
      | ~ v4_lattice3(B_222)
      | ~ v10_lattices(B_222)
      | v2_struct_0(B_222) ) ),
    inference(resolution,[status(thm)],[c_97,c_28])).

tff(c_512,plain,(
    ! [B_49,A_48,D_51,C_50,B_223] :
      ( r1_lattices(B_49,B_223,'#skF_2'(A_48,B_49,C_50,D_51))
      | ~ r3_lattice3(B_49,B_223,D_51)
      | ~ m1_subset_1(B_223,u1_struct_0(B_49))
      | ~ r2_hidden(A_48,a_3_4_lattice3(B_49,C_50,D_51))
      | ~ m1_subset_1(C_50,u1_struct_0(B_49))
      | ~ l3_lattices(B_49)
      | ~ v4_lattice3(B_49)
      | ~ v10_lattices(B_49)
      | v2_struct_0(B_49) ) ),
    inference(resolution,[status(thm)],[c_44,c_509])).

tff(c_151,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( m1_subset_1('#skF_2'(A_121,B_122,C_123,D_124),u1_struct_0(B_122))
      | ~ r2_hidden(A_121,a_3_4_lattice3(B_122,C_123,D_124))
      | ~ m1_subset_1(C_123,u1_struct_0(B_122))
      | ~ l3_lattices(B_122)
      | ~ v4_lattice3(B_122)
      | ~ v10_lattices(B_122)
      | v2_struct_0(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_154,plain,(
    ! [B_7,B_122,A_121,D_124,C_123] :
      ( r3_lattices(B_122,B_7,'#skF_2'(A_121,B_122,C_123,D_124))
      | ~ r1_lattices(B_122,B_7,'#skF_2'(A_121,B_122,C_123,D_124))
      | ~ m1_subset_1(B_7,u1_struct_0(B_122))
      | ~ v9_lattices(B_122)
      | ~ v8_lattices(B_122)
      | ~ v6_lattices(B_122)
      | ~ r2_hidden(A_121,a_3_4_lattice3(B_122,C_123,D_124))
      | ~ m1_subset_1(C_123,u1_struct_0(B_122))
      | ~ l3_lattices(B_122)
      | ~ v4_lattice3(B_122)
      | ~ v10_lattices(B_122)
      | v2_struct_0(B_122) ) ),
    inference(resolution,[status(thm)],[c_151,c_22])).

tff(c_278,plain,(
    ! [B_140,C_141,A_142,D_143] :
      ( k3_lattices(B_140,C_141,'#skF_2'(A_142,B_140,C_141,D_143)) = A_142
      | ~ r2_hidden(A_142,a_3_4_lattice3(B_140,C_141,D_143))
      | ~ m1_subset_1(C_141,u1_struct_0(B_140))
      | ~ l3_lattices(B_140)
      | ~ v4_lattice3(B_140)
      | ~ v10_lattices(B_140)
      | v2_struct_0(B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_664,plain,(
    ! [C_255,B_256,A_254,B_253,D_252] :
      ( k3_lattices(B_253,C_255,'#skF_2'('#skF_1'(A_254,B_256,a_3_4_lattice3(B_253,C_255,D_252)),B_253,C_255,D_252)) = '#skF_1'(A_254,B_256,a_3_4_lattice3(B_253,C_255,D_252))
      | ~ m1_subset_1(C_255,u1_struct_0(B_253))
      | ~ l3_lattices(B_253)
      | ~ v4_lattice3(B_253)
      | ~ v10_lattices(B_253)
      | v2_struct_0(B_253)
      | r3_lattice3(A_254,B_256,a_3_4_lattice3(B_253,C_255,D_252))
      | ~ m1_subset_1(B_256,u1_struct_0(A_254))
      | ~ l3_lattices(A_254)
      | v2_struct_0(A_254) ) ),
    inference(resolution,[status(thm)],[c_32,c_278])).

tff(c_26,plain,(
    ! [A_9,D_23,B_17,C_21] :
      ( r3_lattices(A_9,k3_lattices(A_9,D_23,B_17),k3_lattices(A_9,D_23,C_21))
      | ~ r3_lattices(A_9,B_17,C_21)
      | ~ m1_subset_1(D_23,u1_struct_0(A_9))
      | ~ m1_subset_1(C_21,u1_struct_0(A_9))
      | ~ m1_subset_1(B_17,u1_struct_0(A_9))
      | ~ l3_lattices(A_9)
      | ~ v9_lattices(A_9)
      | ~ v8_lattices(A_9)
      | ~ v6_lattices(A_9)
      | ~ v5_lattices(A_9)
      | ~ v4_lattices(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2578,plain,(
    ! [B_754,A_753,B_749,D_751,B_752,C_750] :
      ( r3_lattices(B_754,k3_lattices(B_754,C_750,B_752),'#skF_1'(A_753,B_749,a_3_4_lattice3(B_754,C_750,D_751)))
      | ~ r3_lattices(B_754,B_752,'#skF_2'('#skF_1'(A_753,B_749,a_3_4_lattice3(B_754,C_750,D_751)),B_754,C_750,D_751))
      | ~ m1_subset_1(C_750,u1_struct_0(B_754))
      | ~ m1_subset_1('#skF_2'('#skF_1'(A_753,B_749,a_3_4_lattice3(B_754,C_750,D_751)),B_754,C_750,D_751),u1_struct_0(B_754))
      | ~ m1_subset_1(B_752,u1_struct_0(B_754))
      | ~ l3_lattices(B_754)
      | ~ v9_lattices(B_754)
      | ~ v8_lattices(B_754)
      | ~ v6_lattices(B_754)
      | ~ v5_lattices(B_754)
      | ~ v4_lattices(B_754)
      | v2_struct_0(B_754)
      | ~ m1_subset_1(C_750,u1_struct_0(B_754))
      | ~ l3_lattices(B_754)
      | ~ v4_lattice3(B_754)
      | ~ v10_lattices(B_754)
      | v2_struct_0(B_754)
      | r3_lattice3(A_753,B_749,a_3_4_lattice3(B_754,C_750,D_751))
      | ~ m1_subset_1(B_749,u1_struct_0(A_753))
      | ~ l3_lattices(A_753)
      | v2_struct_0(A_753) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_664,c_26])).

tff(c_3487,plain,(
    ! [B_943,C_945,B_946,B_947,A_942,D_944] :
      ( r3_lattices(B_943,k3_lattices(B_943,C_945,B_946),'#skF_1'(A_942,B_947,a_3_4_lattice3(B_943,C_945,D_944)))
      | ~ m1_subset_1('#skF_2'('#skF_1'(A_942,B_947,a_3_4_lattice3(B_943,C_945,D_944)),B_943,C_945,D_944),u1_struct_0(B_943))
      | ~ v5_lattices(B_943)
      | ~ v4_lattices(B_943)
      | r3_lattice3(A_942,B_947,a_3_4_lattice3(B_943,C_945,D_944))
      | ~ m1_subset_1(B_947,u1_struct_0(A_942))
      | ~ l3_lattices(A_942)
      | v2_struct_0(A_942)
      | ~ r1_lattices(B_943,B_946,'#skF_2'('#skF_1'(A_942,B_947,a_3_4_lattice3(B_943,C_945,D_944)),B_943,C_945,D_944))
      | ~ m1_subset_1(B_946,u1_struct_0(B_943))
      | ~ v9_lattices(B_943)
      | ~ v8_lattices(B_943)
      | ~ v6_lattices(B_943)
      | ~ r2_hidden('#skF_1'(A_942,B_947,a_3_4_lattice3(B_943,C_945,D_944)),a_3_4_lattice3(B_943,C_945,D_944))
      | ~ m1_subset_1(C_945,u1_struct_0(B_943))
      | ~ l3_lattices(B_943)
      | ~ v4_lattice3(B_943)
      | ~ v10_lattices(B_943)
      | v2_struct_0(B_943) ) ),
    inference(resolution,[status(thm)],[c_154,c_2578])).

tff(c_3496,plain,(
    ! [C_951,B_953,D_949,B_950,A_952,B_948] :
      ( r3_lattices(B_950,k3_lattices(B_950,C_951,B_953),'#skF_1'(A_952,B_948,a_3_4_lattice3(B_950,C_951,D_949)))
      | ~ v5_lattices(B_950)
      | ~ v4_lattices(B_950)
      | r3_lattice3(A_952,B_948,a_3_4_lattice3(B_950,C_951,D_949))
      | ~ m1_subset_1(B_948,u1_struct_0(A_952))
      | ~ l3_lattices(A_952)
      | v2_struct_0(A_952)
      | ~ r1_lattices(B_950,B_953,'#skF_2'('#skF_1'(A_952,B_948,a_3_4_lattice3(B_950,C_951,D_949)),B_950,C_951,D_949))
      | ~ m1_subset_1(B_953,u1_struct_0(B_950))
      | ~ v9_lattices(B_950)
      | ~ v8_lattices(B_950)
      | ~ v6_lattices(B_950)
      | ~ r2_hidden('#skF_1'(A_952,B_948,a_3_4_lattice3(B_950,C_951,D_949)),a_3_4_lattice3(B_950,C_951,D_949))
      | ~ m1_subset_1(C_951,u1_struct_0(B_950))
      | ~ l3_lattices(B_950)
      | ~ v4_lattice3(B_950)
      | ~ v10_lattices(B_950)
      | v2_struct_0(B_950) ) ),
    inference(resolution,[status(thm)],[c_44,c_3487])).

tff(c_3505,plain,(
    ! [D_954,C_956,A_958,B_959,B_955,B_957] :
      ( r3_lattices(B_955,k3_lattices(B_955,C_956,B_959),'#skF_1'(A_958,B_957,a_3_4_lattice3(B_955,C_956,D_954)))
      | ~ v5_lattices(B_955)
      | ~ v4_lattices(B_955)
      | r3_lattice3(A_958,B_957,a_3_4_lattice3(B_955,C_956,D_954))
      | ~ m1_subset_1(B_957,u1_struct_0(A_958))
      | ~ l3_lattices(A_958)
      | v2_struct_0(A_958)
      | ~ v9_lattices(B_955)
      | ~ v8_lattices(B_955)
      | ~ v6_lattices(B_955)
      | ~ r3_lattice3(B_955,B_959,D_954)
      | ~ m1_subset_1(B_959,u1_struct_0(B_955))
      | ~ r2_hidden('#skF_1'(A_958,B_957,a_3_4_lattice3(B_955,C_956,D_954)),a_3_4_lattice3(B_955,C_956,D_954))
      | ~ m1_subset_1(C_956,u1_struct_0(B_955))
      | ~ l3_lattices(B_955)
      | ~ v4_lattice3(B_955)
      | ~ v10_lattices(B_955)
      | v2_struct_0(B_955) ) ),
    inference(resolution,[status(thm)],[c_512,c_3496])).

tff(c_3510,plain,(
    ! [A_962,C_963,B_964,B_960,D_961,B_965] :
      ( r3_lattices(B_964,k3_lattices(B_964,C_963,B_960),'#skF_1'(A_962,B_965,a_3_4_lattice3(B_964,C_963,D_961)))
      | ~ v5_lattices(B_964)
      | ~ v4_lattices(B_964)
      | ~ v9_lattices(B_964)
      | ~ v8_lattices(B_964)
      | ~ v6_lattices(B_964)
      | ~ r3_lattice3(B_964,B_960,D_961)
      | ~ m1_subset_1(B_960,u1_struct_0(B_964))
      | ~ m1_subset_1(C_963,u1_struct_0(B_964))
      | ~ l3_lattices(B_964)
      | ~ v4_lattice3(B_964)
      | ~ v10_lattices(B_964)
      | v2_struct_0(B_964)
      | r3_lattice3(A_962,B_965,a_3_4_lattice3(B_964,C_963,D_961))
      | ~ m1_subset_1(B_965,u1_struct_0(A_962))
      | ~ l3_lattices(A_962)
      | v2_struct_0(A_962) ) ),
    inference(resolution,[status(thm)],[c_32,c_3505])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_lattices(A_6,B_7,C_8)
      | ~ r3_lattices(A_6,B_7,C_8)
      | ~ m1_subset_1(C_8,u1_struct_0(A_6))
      | ~ m1_subset_1(B_7,u1_struct_0(A_6))
      | ~ l3_lattices(A_6)
      | ~ v9_lattices(A_6)
      | ~ v8_lattices(A_6)
      | ~ v6_lattices(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3523,plain,(
    ! [B_971,B_970,B_967,C_969,D_968,A_966] :
      ( r1_lattices(B_967,k3_lattices(B_967,C_969,B_971),'#skF_1'(A_966,B_970,a_3_4_lattice3(B_967,C_969,D_968)))
      | ~ m1_subset_1('#skF_1'(A_966,B_970,a_3_4_lattice3(B_967,C_969,D_968)),u1_struct_0(B_967))
      | ~ m1_subset_1(k3_lattices(B_967,C_969,B_971),u1_struct_0(B_967))
      | ~ v5_lattices(B_967)
      | ~ v4_lattices(B_967)
      | ~ v9_lattices(B_967)
      | ~ v8_lattices(B_967)
      | ~ v6_lattices(B_967)
      | ~ r3_lattice3(B_967,B_971,D_968)
      | ~ m1_subset_1(B_971,u1_struct_0(B_967))
      | ~ m1_subset_1(C_969,u1_struct_0(B_967))
      | ~ l3_lattices(B_967)
      | ~ v4_lattice3(B_967)
      | ~ v10_lattices(B_967)
      | v2_struct_0(B_967)
      | r3_lattice3(A_966,B_970,a_3_4_lattice3(B_967,C_969,D_968))
      | ~ m1_subset_1(B_970,u1_struct_0(A_966))
      | ~ l3_lattices(A_966)
      | v2_struct_0(A_966) ) ),
    inference(resolution,[status(thm)],[c_3510,c_24])).

tff(c_30,plain,(
    ! [A_24,B_36,C_42] :
      ( ~ r1_lattices(A_24,B_36,'#skF_1'(A_24,B_36,C_42))
      | r3_lattice3(A_24,B_36,C_42)
      | ~ m1_subset_1(B_36,u1_struct_0(A_24))
      | ~ l3_lattices(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3544,plain,(
    ! [A_979,C_980,B_981,D_982] :
      ( ~ m1_subset_1('#skF_1'(A_979,k3_lattices(A_979,C_980,B_981),a_3_4_lattice3(A_979,C_980,D_982)),u1_struct_0(A_979))
      | ~ v5_lattices(A_979)
      | ~ v4_lattices(A_979)
      | ~ v9_lattices(A_979)
      | ~ v8_lattices(A_979)
      | ~ v6_lattices(A_979)
      | ~ r3_lattice3(A_979,B_981,D_982)
      | ~ m1_subset_1(B_981,u1_struct_0(A_979))
      | ~ m1_subset_1(C_980,u1_struct_0(A_979))
      | ~ v4_lattice3(A_979)
      | ~ v10_lattices(A_979)
      | r3_lattice3(A_979,k3_lattices(A_979,C_980,B_981),a_3_4_lattice3(A_979,C_980,D_982))
      | ~ m1_subset_1(k3_lattices(A_979,C_980,B_981),u1_struct_0(A_979))
      | ~ l3_lattices(A_979)
      | v2_struct_0(A_979) ) ),
    inference(resolution,[status(thm)],[c_3523,c_30])).

tff(c_3564,plain,(
    ! [A_983,B_984,D_985,C_986] :
      ( ~ v5_lattices(A_983)
      | ~ v4_lattices(A_983)
      | ~ v9_lattices(A_983)
      | ~ v8_lattices(A_983)
      | ~ v6_lattices(A_983)
      | ~ r3_lattice3(A_983,B_984,D_985)
      | ~ m1_subset_1(B_984,u1_struct_0(A_983))
      | ~ m1_subset_1(C_986,u1_struct_0(A_983))
      | ~ v4_lattice3(A_983)
      | ~ v10_lattices(A_983)
      | r3_lattice3(A_983,k3_lattices(A_983,C_986,B_984),a_3_4_lattice3(A_983,C_986,D_985))
      | ~ m1_subset_1(k3_lattices(A_983,C_986,B_984),u1_struct_0(A_983))
      | ~ l3_lattices(A_983)
      | v2_struct_0(A_983) ) ),
    inference(resolution,[status(thm)],[c_34,c_3544])).

tff(c_339,plain,(
    ! [A_158,D_159,C_160] :
      ( r3_lattices(A_158,D_159,k16_lattice3(A_158,C_160))
      | ~ r3_lattice3(A_158,D_159,C_160)
      | ~ m1_subset_1(D_159,u1_struct_0(A_158))
      | ~ m1_subset_1(k16_lattice3(A_158,C_160),u1_struct_0(A_158))
      | ~ l3_lattices(A_158)
      | ~ v4_lattice3(A_158)
      | ~ v10_lattices(A_158)
      | v2_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_350,plain,(
    ! [A_165,D_166,B_167] :
      ( r3_lattices(A_165,D_166,k16_lattice3(A_165,B_167))
      | ~ r3_lattice3(A_165,D_166,B_167)
      | ~ m1_subset_1(D_166,u1_struct_0(A_165))
      | ~ v4_lattice3(A_165)
      | ~ v10_lattices(A_165)
      | ~ l3_lattices(A_165)
      | v2_struct_0(A_165) ) ),
    inference(resolution,[status(thm)],[c_36,c_339])).

tff(c_359,plain,
    ( ~ r3_lattice3('#skF_4',k3_lattices('#skF_4','#skF_5',k16_lattice3('#skF_4','#skF_6')),a_3_4_lattice3('#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1(k3_lattices('#skF_4','#skF_5',k16_lattice3('#skF_4','#skF_6')),u1_struct_0('#skF_4'))
    | ~ v4_lattice3('#skF_4')
    | ~ v10_lattices('#skF_4')
    | ~ l3_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_350,c_56])).

tff(c_364,plain,
    ( ~ r3_lattice3('#skF_4',k3_lattices('#skF_4','#skF_5',k16_lattice3('#skF_4','#skF_6')),a_3_4_lattice3('#skF_4','#skF_5','#skF_6'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64,c_62,c_266,c_359])).

tff(c_365,plain,(
    ~ r3_lattice3('#skF_4',k3_lattices('#skF_4','#skF_5',k16_lattice3('#skF_4','#skF_6')),a_3_4_lattice3('#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_364])).

tff(c_3585,plain,
    ( ~ v5_lattices('#skF_4')
    | ~ v4_lattices('#skF_4')
    | ~ v9_lattices('#skF_4')
    | ~ v8_lattices('#skF_4')
    | ~ v6_lattices('#skF_4')
    | ~ r3_lattice3('#skF_4',k16_lattice3('#skF_4','#skF_6'),'#skF_6')
    | ~ m1_subset_1(k16_lattice3('#skF_4','#skF_6'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v4_lattice3('#skF_4')
    | ~ v10_lattices('#skF_4')
    | ~ m1_subset_1(k3_lattices('#skF_4','#skF_5',k16_lattice3('#skF_4','#skF_6')),u1_struct_0('#skF_4'))
    | ~ l3_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3564,c_365])).

tff(c_3610,plain,
    ( ~ r3_lattice3('#skF_4',k16_lattice3('#skF_4','#skF_6'),'#skF_6')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_266,c_64,c_62,c_58,c_586,c_128,c_150,c_139,c_217,c_1476,c_3585])).

tff(c_3611,plain,(
    ~ r3_lattice3('#skF_4',k16_lattice3('#skF_4','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3610])).

tff(c_3614,plain,
    ( ~ v4_lattice3('#skF_4')
    | ~ v10_lattices('#skF_4')
    | ~ l3_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_3611])).

tff(c_3617,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64,c_62,c_3614])).

tff(c_3619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3617])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n011.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 10:16:57 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.17/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.17/3.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.31/3.49  
% 9.31/3.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.31/3.49  %$ r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k3_lattices > a_3_4_lattice3 > k16_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3
% 9.31/3.49  
% 9.31/3.49  %Foreground sorts:
% 9.31/3.49  
% 9.31/3.49  
% 9.31/3.49  %Background operators:
% 9.31/3.49  
% 9.31/3.49  
% 9.31/3.49  %Foreground operators:
% 9.31/3.49  tff(l3_lattices, type, l3_lattices: $i > $o).
% 9.31/3.49  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 9.31/3.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.31/3.49  tff(l2_lattices, type, l2_lattices: $i > $o).
% 9.31/3.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.31/3.49  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 9.31/3.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.31/3.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.31/3.49  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 9.31/3.49  tff(a_3_4_lattice3, type, a_3_4_lattice3: ($i * $i * $i) > $i).
% 9.31/3.49  tff(l1_lattices, type, l1_lattices: $i > $o).
% 9.31/3.49  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 9.31/3.49  tff('#skF_5', type, '#skF_5': $i).
% 9.31/3.49  tff(v4_lattices, type, v4_lattices: $i > $o).
% 9.31/3.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.31/3.49  tff('#skF_6', type, '#skF_6': $i).
% 9.31/3.49  tff(v6_lattices, type, v6_lattices: $i > $o).
% 9.31/3.49  tff(v9_lattices, type, v9_lattices: $i > $o).
% 9.31/3.49  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 9.31/3.49  tff(v5_lattices, type, v5_lattices: $i > $o).
% 9.31/3.49  tff(v10_lattices, type, v10_lattices: $i > $o).
% 9.31/3.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.31/3.49  tff('#skF_4', type, '#skF_4': $i).
% 9.31/3.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.31/3.49  tff(v8_lattices, type, v8_lattices: $i > $o).
% 9.31/3.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.31/3.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.31/3.49  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 9.31/3.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.31/3.49  tff(v7_lattices, type, v7_lattices: $i > $o).
% 9.31/3.49  
% 9.39/3.51  tff(f_198, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: r3_lattices(A, k3_lattices(A, B, k16_lattice3(A, C)), k16_lattice3(A, a_3_4_lattice3(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_lattice3)).
% 9.39/3.51  tff(f_138, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k16_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 9.39/3.51  tff(f_182, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 9.39/3.51  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 9.39/3.51  tff(f_66, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 9.39/3.51  tff(f_60, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_lattices(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_lattices)).
% 9.39/3.51  tff(f_85, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 9.39/3.51  tff(f_158, axiom, (![A, B, C, D]: (((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) & m1_subset_1(C, u1_struct_0(B))) => (r2_hidden(A, a_3_4_lattice3(B, C, D)) <=> (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & (A = k3_lattices(B, C, E))) & r2_hidden(E, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_3_4_lattice3)).
% 9.39/3.51  tff(f_131, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 9.39/3.51  tff(f_113, axiom, (![A]: (((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattices(A, B, C) => r3_lattices(A, k3_lattices(A, D, B), k3_lattices(A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_filter_0)).
% 9.39/3.51  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.39/3.51  tff(c_60, plain, (l3_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.39/3.51  tff(c_64, plain, (v10_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.39/3.51  tff(c_62, plain, (v4_lattice3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.39/3.51  tff(c_36, plain, (![A_46, B_47]: (m1_subset_1(k16_lattice3(A_46, B_47), u1_struct_0(A_46)) | ~l3_lattices(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.39/3.51  tff(c_87, plain, (![A_100, C_101]: (r3_lattice3(A_100, k16_lattice3(A_100, C_101), C_101) | ~m1_subset_1(k16_lattice3(A_100, C_101), u1_struct_0(A_100)) | ~l3_lattices(A_100) | ~v4_lattice3(A_100) | ~v10_lattices(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_182])).
% 9.39/3.51  tff(c_90, plain, (![A_46, B_47]: (r3_lattice3(A_46, k16_lattice3(A_46, B_47), B_47) | ~v4_lattice3(A_46) | ~v10_lattices(A_46) | ~l3_lattices(A_46) | v2_struct_0(A_46))), inference(resolution, [status(thm)], [c_36, c_87])).
% 9.39/3.51  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.39/3.51  tff(c_72, plain, (![A_82]: (l2_lattices(A_82) | ~l3_lattices(A_82))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.39/3.51  tff(c_76, plain, (l2_lattices('#skF_4')), inference(resolution, [status(thm)], [c_60, c_72])).
% 9.39/3.51  tff(c_16, plain, (![A_2, B_3, C_4]: (m1_subset_1(k3_lattices(A_2, B_3, C_4), u1_struct_0(A_2)) | ~m1_subset_1(C_4, u1_struct_0(A_2)) | ~m1_subset_1(B_3, u1_struct_0(A_2)) | ~l2_lattices(A_2) | ~v4_lattices(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.39/3.51  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.39/3.51  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.39/3.51  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.39/3.51  tff(c_58, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.39/3.51  tff(c_102, plain, (![A_118, B_119, C_120]: (r3_lattices(A_118, B_119, C_120) | ~r1_lattices(A_118, B_119, C_120) | ~m1_subset_1(C_120, u1_struct_0(A_118)) | ~m1_subset_1(B_119, u1_struct_0(A_118)) | ~l3_lattices(A_118) | ~v9_lattices(A_118) | ~v8_lattices(A_118) | ~v6_lattices(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.39/3.51  tff(c_110, plain, (![B_119]: (r3_lattices('#skF_4', B_119, '#skF_5') | ~r1_lattices('#skF_4', B_119, '#skF_5') | ~m1_subset_1(B_119, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_102])).
% 9.39/3.51  tff(c_116, plain, (![B_119]: (r3_lattices('#skF_4', B_119, '#skF_5') | ~r1_lattices('#skF_4', B_119, '#skF_5') | ~m1_subset_1(B_119, u1_struct_0('#skF_4')) | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_110])).
% 9.39/3.51  tff(c_117, plain, (![B_119]: (r3_lattices('#skF_4', B_119, '#skF_5') | ~r1_lattices('#skF_4', B_119, '#skF_5') | ~m1_subset_1(B_119, u1_struct_0('#skF_4')) | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_116])).
% 9.39/3.51  tff(c_118, plain, (~v6_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_117])).
% 9.39/3.51  tff(c_121, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_8, c_118])).
% 9.39/3.51  tff(c_124, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_64, c_121])).
% 9.39/3.51  tff(c_126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_124])).
% 9.39/3.51  tff(c_127, plain, (![B_119]: (~v8_lattices('#skF_4') | ~v9_lattices('#skF_4') | r3_lattices('#skF_4', B_119, '#skF_5') | ~r1_lattices('#skF_4', B_119, '#skF_5') | ~m1_subset_1(B_119, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_117])).
% 9.39/3.51  tff(c_129, plain, (~v9_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_127])).
% 9.39/3.51  tff(c_132, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_2, c_129])).
% 9.39/3.51  tff(c_135, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_64, c_132])).
% 9.39/3.51  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_135])).
% 9.39/3.51  tff(c_138, plain, (![B_119]: (~v8_lattices('#skF_4') | r3_lattices('#skF_4', B_119, '#skF_5') | ~r1_lattices('#skF_4', B_119, '#skF_5') | ~m1_subset_1(B_119, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_127])).
% 9.39/3.51  tff(c_140, plain, (~v8_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_138])).
% 9.39/3.51  tff(c_143, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_4, c_140])).
% 9.39/3.51  tff(c_146, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_64, c_143])).
% 9.39/3.51  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_146])).
% 9.39/3.51  tff(c_155, plain, (![B_125]: (r3_lattices('#skF_4', B_125, '#skF_5') | ~r1_lattices('#skF_4', B_125, '#skF_5') | ~m1_subset_1(B_125, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_138])).
% 9.39/3.51  tff(c_163, plain, (![B_3, C_4]: (r3_lattices('#skF_4', k3_lattices('#skF_4', B_3, C_4), '#skF_5') | ~r1_lattices('#skF_4', k3_lattices('#skF_4', B_3, C_4), '#skF_5') | ~m1_subset_1(C_4, u1_struct_0('#skF_4')) | ~m1_subset_1(B_3, u1_struct_0('#skF_4')) | ~l2_lattices('#skF_4') | ~v4_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_155])).
% 9.39/3.51  tff(c_181, plain, (![B_3, C_4]: (r3_lattices('#skF_4', k3_lattices('#skF_4', B_3, C_4), '#skF_5') | ~r1_lattices('#skF_4', k3_lattices('#skF_4', B_3, C_4), '#skF_5') | ~m1_subset_1(C_4, u1_struct_0('#skF_4')) | ~m1_subset_1(B_3, u1_struct_0('#skF_4')) | ~v4_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_163])).
% 9.39/3.51  tff(c_182, plain, (![B_3, C_4]: (r3_lattices('#skF_4', k3_lattices('#skF_4', B_3, C_4), '#skF_5') | ~r1_lattices('#skF_4', k3_lattices('#skF_4', B_3, C_4), '#skF_5') | ~m1_subset_1(C_4, u1_struct_0('#skF_4')) | ~m1_subset_1(B_3, u1_struct_0('#skF_4')) | ~v4_lattices('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_181])).
% 9.39/3.51  tff(c_207, plain, (~v4_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_182])).
% 9.39/3.51  tff(c_210, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_12, c_207])).
% 9.39/3.51  tff(c_213, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_64, c_210])).
% 9.39/3.51  tff(c_215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_213])).
% 9.39/3.51  tff(c_217, plain, (v4_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_182])).
% 9.39/3.51  tff(c_128, plain, (v6_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_117])).
% 9.39/3.51  tff(c_150, plain, (v8_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_138])).
% 9.39/3.51  tff(c_139, plain, (v9_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_127])).
% 9.39/3.51  tff(c_226, plain, (![A_134, B_135, B_136]: (r3_lattices(A_134, B_135, k16_lattice3(A_134, B_136)) | ~r1_lattices(A_134, B_135, k16_lattice3(A_134, B_136)) | ~m1_subset_1(B_135, u1_struct_0(A_134)) | ~v9_lattices(A_134) | ~v8_lattices(A_134) | ~v6_lattices(A_134) | ~l3_lattices(A_134) | v2_struct_0(A_134))), inference(resolution, [status(thm)], [c_36, c_102])).
% 9.39/3.51  tff(c_56, plain, (~r3_lattices('#skF_4', k3_lattices('#skF_4', '#skF_5', k16_lattice3('#skF_4', '#skF_6')), k16_lattice3('#skF_4', a_3_4_lattice3('#skF_4', '#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.39/3.51  tff(c_235, plain, (~r1_lattices('#skF_4', k3_lattices('#skF_4', '#skF_5', k16_lattice3('#skF_4', '#skF_6')), k16_lattice3('#skF_4', a_3_4_lattice3('#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k3_lattices('#skF_4', '#skF_5', k16_lattice3('#skF_4', '#skF_6')), u1_struct_0('#skF_4')) | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_226, c_56])).
% 9.39/3.51  tff(c_240, plain, (~r1_lattices('#skF_4', k3_lattices('#skF_4', '#skF_5', k16_lattice3('#skF_4', '#skF_6')), k16_lattice3('#skF_4', a_3_4_lattice3('#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k3_lattices('#skF_4', '#skF_5', k16_lattice3('#skF_4', '#skF_6')), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_128, c_150, c_139, c_235])).
% 9.39/3.51  tff(c_241, plain, (~r1_lattices('#skF_4', k3_lattices('#skF_4', '#skF_5', k16_lattice3('#skF_4', '#skF_6')), k16_lattice3('#skF_4', a_3_4_lattice3('#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k3_lattices('#skF_4', '#skF_5', k16_lattice3('#skF_4', '#skF_6')), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_240])).
% 9.39/3.51  tff(c_242, plain, (~m1_subset_1(k3_lattices('#skF_4', '#skF_5', k16_lattice3('#skF_4', '#skF_6')), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_241])).
% 9.39/3.51  tff(c_252, plain, (~m1_subset_1(k16_lattice3('#skF_4', '#skF_6'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l2_lattices('#skF_4') | ~v4_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_16, c_242])).
% 9.39/3.51  tff(c_255, plain, (~m1_subset_1(k16_lattice3('#skF_4', '#skF_6'), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_217, c_76, c_58, c_252])).
% 9.39/3.51  tff(c_256, plain, (~m1_subset_1(k16_lattice3('#skF_4', '#skF_6'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_255])).
% 9.39/3.52  tff(c_259, plain, (~l3_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_256])).
% 9.39/3.52  tff(c_262, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_259])).
% 9.39/3.52  tff(c_264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_262])).
% 9.39/3.52  tff(c_266, plain, (m1_subset_1(k3_lattices('#skF_4', '#skF_5', k16_lattice3('#skF_4', '#skF_6')), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_241])).
% 9.39/3.52  tff(c_343, plain, (![B_161, C_162, E_163, D_164]: (r2_hidden(k3_lattices(B_161, C_162, E_163), a_3_4_lattice3(B_161, C_162, D_164)) | ~r2_hidden(E_163, D_164) | ~m1_subset_1(E_163, u1_struct_0(B_161)) | ~m1_subset_1(C_162, u1_struct_0(B_161)) | ~l3_lattices(B_161) | ~v4_lattice3(B_161) | ~v10_lattices(B_161) | v2_struct_0(B_161))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.39/3.52  tff(c_28, plain, (![A_24, B_36, D_45, C_42]: (r1_lattices(A_24, B_36, D_45) | ~r2_hidden(D_45, C_42) | ~m1_subset_1(D_45, u1_struct_0(A_24)) | ~r3_lattice3(A_24, B_36, C_42) | ~m1_subset_1(B_36, u1_struct_0(A_24)) | ~l3_lattices(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.39/3.52  tff(c_514, plain, (![B_234, C_230, E_233, A_232, B_231, D_229]: (r1_lattices(A_232, B_234, k3_lattices(B_231, C_230, E_233)) | ~m1_subset_1(k3_lattices(B_231, C_230, E_233), u1_struct_0(A_232)) | ~r3_lattice3(A_232, B_234, a_3_4_lattice3(B_231, C_230, D_229)) | ~m1_subset_1(B_234, u1_struct_0(A_232)) | ~l3_lattices(A_232) | v2_struct_0(A_232) | ~r2_hidden(E_233, D_229) | ~m1_subset_1(E_233, u1_struct_0(B_231)) | ~m1_subset_1(C_230, u1_struct_0(B_231)) | ~l3_lattices(B_231) | ~v4_lattice3(B_231) | ~v10_lattices(B_231) | v2_struct_0(B_231))), inference(resolution, [status(thm)], [c_343, c_28])).
% 9.39/3.52  tff(c_518, plain, (![B_234, D_229]: (r1_lattices('#skF_4', B_234, k3_lattices('#skF_4', '#skF_5', k16_lattice3('#skF_4', '#skF_6'))) | ~r3_lattice3('#skF_4', B_234, a_3_4_lattice3('#skF_4', '#skF_5', D_229)) | ~m1_subset_1(B_234, u1_struct_0('#skF_4')) | ~r2_hidden(k16_lattice3('#skF_4', '#skF_6'), D_229) | ~m1_subset_1(k16_lattice3('#skF_4', '#skF_6'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v4_lattice3('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_266, c_514])).
% 9.39/3.52  tff(c_523, plain, (![B_234, D_229]: (r1_lattices('#skF_4', B_234, k3_lattices('#skF_4', '#skF_5', k16_lattice3('#skF_4', '#skF_6'))) | ~r3_lattice3('#skF_4', B_234, a_3_4_lattice3('#skF_4', '#skF_5', D_229)) | ~m1_subset_1(B_234, u1_struct_0('#skF_4')) | ~r2_hidden(k16_lattice3('#skF_4', '#skF_6'), D_229) | ~m1_subset_1(k16_lattice3('#skF_4', '#skF_6'), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_518])).
% 9.39/3.52  tff(c_524, plain, (![B_234, D_229]: (r1_lattices('#skF_4', B_234, k3_lattices('#skF_4', '#skF_5', k16_lattice3('#skF_4', '#skF_6'))) | ~r3_lattice3('#skF_4', B_234, a_3_4_lattice3('#skF_4', '#skF_5', D_229)) | ~m1_subset_1(B_234, u1_struct_0('#skF_4')) | ~r2_hidden(k16_lattice3('#skF_4', '#skF_6'), D_229) | ~m1_subset_1(k16_lattice3('#skF_4', '#skF_6'), u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_523])).
% 9.39/3.52  tff(c_526, plain, (~m1_subset_1(k16_lattice3('#skF_4', '#skF_6'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_524])).
% 9.39/3.52  tff(c_579, plain, (~l3_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_526])).
% 9.39/3.52  tff(c_582, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_579])).
% 9.39/3.52  tff(c_584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_582])).
% 9.39/3.52  tff(c_586, plain, (m1_subset_1(k16_lattice3('#skF_4', '#skF_6'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_524])).
% 9.39/3.52  tff(c_10, plain, (![A_1]: (v5_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.39/3.52  tff(c_22, plain, (![A_6, B_7, C_8]: (r3_lattices(A_6, B_7, C_8) | ~r1_lattices(A_6, B_7, C_8) | ~m1_subset_1(C_8, u1_struct_0(A_6)) | ~m1_subset_1(B_7, u1_struct_0(A_6)) | ~l3_lattices(A_6) | ~v9_lattices(A_6) | ~v8_lattices(A_6) | ~v6_lattices(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.39/3.52  tff(c_591, plain, (![B_7]: (r3_lattices('#skF_4', B_7, k16_lattice3('#skF_4', '#skF_6')) | ~r1_lattices('#skF_4', B_7, k16_lattice3('#skF_4', '#skF_6')) | ~m1_subset_1(B_7, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_586, c_22])).
% 9.39/3.52  tff(c_595, plain, (![B_7]: (r3_lattices('#skF_4', B_7, k16_lattice3('#skF_4', '#skF_6')) | ~r1_lattices('#skF_4', B_7, k16_lattice3('#skF_4', '#skF_6')) | ~m1_subset_1(B_7, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_150, c_139, c_60, c_591])).
% 9.39/3.52  tff(c_596, plain, (![B_7]: (r3_lattices('#skF_4', B_7, k16_lattice3('#skF_4', '#skF_6')) | ~r1_lattices('#skF_4', B_7, k16_lattice3('#skF_4', '#skF_6')) | ~m1_subset_1(B_7, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_595])).
% 9.39/3.52  tff(c_42, plain, (![B_49, C_50, A_48, D_51]: (k3_lattices(B_49, C_50, '#skF_2'(A_48, B_49, C_50, D_51))=A_48 | ~r2_hidden(A_48, a_3_4_lattice3(B_49, C_50, D_51)) | ~m1_subset_1(C_50, u1_struct_0(B_49)) | ~l3_lattices(B_49) | ~v4_lattice3(B_49) | ~v10_lattices(B_49) | v2_struct_0(B_49))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.39/3.52  tff(c_348, plain, (![B_161, C_162, E_163, D_164]: (k3_lattices(B_161, C_162, '#skF_2'(k3_lattices(B_161, C_162, E_163), B_161, C_162, D_164))=k3_lattices(B_161, C_162, E_163) | ~r2_hidden(E_163, D_164) | ~m1_subset_1(E_163, u1_struct_0(B_161)) | ~m1_subset_1(C_162, u1_struct_0(B_161)) | ~l3_lattices(B_161) | ~v4_lattice3(B_161) | ~v10_lattices(B_161) | v2_struct_0(B_161))), inference(resolution, [status(thm)], [c_343, c_42])).
% 9.39/3.52  tff(c_440, plain, (![A_194, D_195, B_196, C_197]: (r3_lattices(A_194, k3_lattices(A_194, D_195, B_196), k3_lattices(A_194, D_195, C_197)) | ~r3_lattices(A_194, B_196, C_197) | ~m1_subset_1(D_195, u1_struct_0(A_194)) | ~m1_subset_1(C_197, u1_struct_0(A_194)) | ~m1_subset_1(B_196, u1_struct_0(A_194)) | ~l3_lattices(A_194) | ~v9_lattices(A_194) | ~v8_lattices(A_194) | ~v6_lattices(A_194) | ~v5_lattices(A_194) | ~v4_lattices(A_194) | v2_struct_0(A_194))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.39/3.52  tff(c_1371, plain, (![C_454, B_453, C_452, D_451, E_455]: (r3_lattices(B_453, k3_lattices(B_453, C_452, E_455), k3_lattices(B_453, C_452, C_454)) | ~r3_lattices(B_453, '#skF_2'(k3_lattices(B_453, C_452, E_455), B_453, C_452, D_451), C_454) | ~m1_subset_1(C_452, u1_struct_0(B_453)) | ~m1_subset_1(C_454, u1_struct_0(B_453)) | ~m1_subset_1('#skF_2'(k3_lattices(B_453, C_452, E_455), B_453, C_452, D_451), u1_struct_0(B_453)) | ~l3_lattices(B_453) | ~v9_lattices(B_453) | ~v8_lattices(B_453) | ~v6_lattices(B_453) | ~v5_lattices(B_453) | ~v4_lattices(B_453) | v2_struct_0(B_453) | ~r2_hidden(E_455, D_451) | ~m1_subset_1(E_455, u1_struct_0(B_453)) | ~m1_subset_1(C_452, u1_struct_0(B_453)) | ~l3_lattices(B_453) | ~v4_lattice3(B_453) | ~v10_lattices(B_453) | v2_struct_0(B_453))), inference(superposition, [status(thm), theory('equality')], [c_348, c_440])).
% 9.39/3.52  tff(c_1387, plain, (![C_452, E_455, D_451]: (r3_lattices('#skF_4', k3_lattices('#skF_4', C_452, E_455), k3_lattices('#skF_4', C_452, k16_lattice3('#skF_4', '#skF_6'))) | ~m1_subset_1(k16_lattice3('#skF_4', '#skF_6'), u1_struct_0('#skF_4')) | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | ~v5_lattices('#skF_4') | ~v4_lattices('#skF_4') | ~r2_hidden(E_455, D_451) | ~m1_subset_1(E_455, u1_struct_0('#skF_4')) | ~m1_subset_1(C_452, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v4_lattice3('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~r1_lattices('#skF_4', '#skF_2'(k3_lattices('#skF_4', C_452, E_455), '#skF_4', C_452, D_451), k16_lattice3('#skF_4', '#skF_6')) | ~m1_subset_1('#skF_2'(k3_lattices('#skF_4', C_452, E_455), '#skF_4', C_452, D_451), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_596, c_1371])).
% 9.39/3.52  tff(c_1422, plain, (![C_452, E_455, D_451]: (r3_lattices('#skF_4', k3_lattices('#skF_4', C_452, E_455), k3_lattices('#skF_4', C_452, k16_lattice3('#skF_4', '#skF_6'))) | ~v5_lattices('#skF_4') | ~r2_hidden(E_455, D_451) | ~m1_subset_1(E_455, u1_struct_0('#skF_4')) | ~m1_subset_1(C_452, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~r1_lattices('#skF_4', '#skF_2'(k3_lattices('#skF_4', C_452, E_455), '#skF_4', C_452, D_451), k16_lattice3('#skF_4', '#skF_6')) | ~m1_subset_1('#skF_2'(k3_lattices('#skF_4', C_452, E_455), '#skF_4', C_452, D_451), u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_217, c_128, c_150, c_139, c_586, c_1387])).
% 9.39/3.52  tff(c_1423, plain, (![C_452, E_455, D_451]: (r3_lattices('#skF_4', k3_lattices('#skF_4', C_452, E_455), k3_lattices('#skF_4', C_452, k16_lattice3('#skF_4', '#skF_6'))) | ~v5_lattices('#skF_4') | ~r2_hidden(E_455, D_451) | ~m1_subset_1(E_455, u1_struct_0('#skF_4')) | ~m1_subset_1(C_452, u1_struct_0('#skF_4')) | ~r1_lattices('#skF_4', '#skF_2'(k3_lattices('#skF_4', C_452, E_455), '#skF_4', C_452, D_451), k16_lattice3('#skF_4', '#skF_6')) | ~m1_subset_1('#skF_2'(k3_lattices('#skF_4', C_452, E_455), '#skF_4', C_452, D_451), u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_1422])).
% 9.39/3.52  tff(c_1438, plain, (~v5_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_1423])).
% 9.39/3.52  tff(c_1469, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_10, c_1438])).
% 9.39/3.52  tff(c_1472, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_64, c_1469])).
% 9.39/3.52  tff(c_1474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1472])).
% 9.39/3.52  tff(c_1476, plain, (v5_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_1423])).
% 9.39/3.52  tff(c_34, plain, (![A_24, B_36, C_42]: (m1_subset_1('#skF_1'(A_24, B_36, C_42), u1_struct_0(A_24)) | r3_lattice3(A_24, B_36, C_42) | ~m1_subset_1(B_36, u1_struct_0(A_24)) | ~l3_lattices(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.39/3.52  tff(c_32, plain, (![A_24, B_36, C_42]: (r2_hidden('#skF_1'(A_24, B_36, C_42), C_42) | r3_lattice3(A_24, B_36, C_42) | ~m1_subset_1(B_36, u1_struct_0(A_24)) | ~l3_lattices(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.39/3.52  tff(c_44, plain, (![A_48, B_49, C_50, D_51]: (m1_subset_1('#skF_2'(A_48, B_49, C_50, D_51), u1_struct_0(B_49)) | ~r2_hidden(A_48, a_3_4_lattice3(B_49, C_50, D_51)) | ~m1_subset_1(C_50, u1_struct_0(B_49)) | ~l3_lattices(B_49) | ~v4_lattice3(B_49) | ~v10_lattices(B_49) | v2_struct_0(B_49))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.39/3.52  tff(c_97, plain, (![A_111, B_112, C_113, D_114]: (r2_hidden('#skF_2'(A_111, B_112, C_113, D_114), D_114) | ~r2_hidden(A_111, a_3_4_lattice3(B_112, C_113, D_114)) | ~m1_subset_1(C_113, u1_struct_0(B_112)) | ~l3_lattices(B_112) | ~v4_lattice3(B_112) | ~v10_lattices(B_112) | v2_struct_0(B_112))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.39/3.52  tff(c_509, plain, (![B_222, D_219, A_221, A_220, C_218, B_223]: (r1_lattices(A_220, B_223, '#skF_2'(A_221, B_222, C_218, D_219)) | ~m1_subset_1('#skF_2'(A_221, B_222, C_218, D_219), u1_struct_0(A_220)) | ~r3_lattice3(A_220, B_223, D_219) | ~m1_subset_1(B_223, u1_struct_0(A_220)) | ~l3_lattices(A_220) | v2_struct_0(A_220) | ~r2_hidden(A_221, a_3_4_lattice3(B_222, C_218, D_219)) | ~m1_subset_1(C_218, u1_struct_0(B_222)) | ~l3_lattices(B_222) | ~v4_lattice3(B_222) | ~v10_lattices(B_222) | v2_struct_0(B_222))), inference(resolution, [status(thm)], [c_97, c_28])).
% 9.39/3.52  tff(c_512, plain, (![B_49, A_48, D_51, C_50, B_223]: (r1_lattices(B_49, B_223, '#skF_2'(A_48, B_49, C_50, D_51)) | ~r3_lattice3(B_49, B_223, D_51) | ~m1_subset_1(B_223, u1_struct_0(B_49)) | ~r2_hidden(A_48, a_3_4_lattice3(B_49, C_50, D_51)) | ~m1_subset_1(C_50, u1_struct_0(B_49)) | ~l3_lattices(B_49) | ~v4_lattice3(B_49) | ~v10_lattices(B_49) | v2_struct_0(B_49))), inference(resolution, [status(thm)], [c_44, c_509])).
% 9.39/3.52  tff(c_151, plain, (![A_121, B_122, C_123, D_124]: (m1_subset_1('#skF_2'(A_121, B_122, C_123, D_124), u1_struct_0(B_122)) | ~r2_hidden(A_121, a_3_4_lattice3(B_122, C_123, D_124)) | ~m1_subset_1(C_123, u1_struct_0(B_122)) | ~l3_lattices(B_122) | ~v4_lattice3(B_122) | ~v10_lattices(B_122) | v2_struct_0(B_122))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.39/3.52  tff(c_154, plain, (![B_7, B_122, A_121, D_124, C_123]: (r3_lattices(B_122, B_7, '#skF_2'(A_121, B_122, C_123, D_124)) | ~r1_lattices(B_122, B_7, '#skF_2'(A_121, B_122, C_123, D_124)) | ~m1_subset_1(B_7, u1_struct_0(B_122)) | ~v9_lattices(B_122) | ~v8_lattices(B_122) | ~v6_lattices(B_122) | ~r2_hidden(A_121, a_3_4_lattice3(B_122, C_123, D_124)) | ~m1_subset_1(C_123, u1_struct_0(B_122)) | ~l3_lattices(B_122) | ~v4_lattice3(B_122) | ~v10_lattices(B_122) | v2_struct_0(B_122))), inference(resolution, [status(thm)], [c_151, c_22])).
% 9.39/3.52  tff(c_278, plain, (![B_140, C_141, A_142, D_143]: (k3_lattices(B_140, C_141, '#skF_2'(A_142, B_140, C_141, D_143))=A_142 | ~r2_hidden(A_142, a_3_4_lattice3(B_140, C_141, D_143)) | ~m1_subset_1(C_141, u1_struct_0(B_140)) | ~l3_lattices(B_140) | ~v4_lattice3(B_140) | ~v10_lattices(B_140) | v2_struct_0(B_140))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.39/3.52  tff(c_664, plain, (![C_255, B_256, A_254, B_253, D_252]: (k3_lattices(B_253, C_255, '#skF_2'('#skF_1'(A_254, B_256, a_3_4_lattice3(B_253, C_255, D_252)), B_253, C_255, D_252))='#skF_1'(A_254, B_256, a_3_4_lattice3(B_253, C_255, D_252)) | ~m1_subset_1(C_255, u1_struct_0(B_253)) | ~l3_lattices(B_253) | ~v4_lattice3(B_253) | ~v10_lattices(B_253) | v2_struct_0(B_253) | r3_lattice3(A_254, B_256, a_3_4_lattice3(B_253, C_255, D_252)) | ~m1_subset_1(B_256, u1_struct_0(A_254)) | ~l3_lattices(A_254) | v2_struct_0(A_254))), inference(resolution, [status(thm)], [c_32, c_278])).
% 9.39/3.52  tff(c_26, plain, (![A_9, D_23, B_17, C_21]: (r3_lattices(A_9, k3_lattices(A_9, D_23, B_17), k3_lattices(A_9, D_23, C_21)) | ~r3_lattices(A_9, B_17, C_21) | ~m1_subset_1(D_23, u1_struct_0(A_9)) | ~m1_subset_1(C_21, u1_struct_0(A_9)) | ~m1_subset_1(B_17, u1_struct_0(A_9)) | ~l3_lattices(A_9) | ~v9_lattices(A_9) | ~v8_lattices(A_9) | ~v6_lattices(A_9) | ~v5_lattices(A_9) | ~v4_lattices(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.39/3.52  tff(c_2578, plain, (![B_754, A_753, B_749, D_751, B_752, C_750]: (r3_lattices(B_754, k3_lattices(B_754, C_750, B_752), '#skF_1'(A_753, B_749, a_3_4_lattice3(B_754, C_750, D_751))) | ~r3_lattices(B_754, B_752, '#skF_2'('#skF_1'(A_753, B_749, a_3_4_lattice3(B_754, C_750, D_751)), B_754, C_750, D_751)) | ~m1_subset_1(C_750, u1_struct_0(B_754)) | ~m1_subset_1('#skF_2'('#skF_1'(A_753, B_749, a_3_4_lattice3(B_754, C_750, D_751)), B_754, C_750, D_751), u1_struct_0(B_754)) | ~m1_subset_1(B_752, u1_struct_0(B_754)) | ~l3_lattices(B_754) | ~v9_lattices(B_754) | ~v8_lattices(B_754) | ~v6_lattices(B_754) | ~v5_lattices(B_754) | ~v4_lattices(B_754) | v2_struct_0(B_754) | ~m1_subset_1(C_750, u1_struct_0(B_754)) | ~l3_lattices(B_754) | ~v4_lattice3(B_754) | ~v10_lattices(B_754) | v2_struct_0(B_754) | r3_lattice3(A_753, B_749, a_3_4_lattice3(B_754, C_750, D_751)) | ~m1_subset_1(B_749, u1_struct_0(A_753)) | ~l3_lattices(A_753) | v2_struct_0(A_753))), inference(superposition, [status(thm), theory('equality')], [c_664, c_26])).
% 9.39/3.52  tff(c_3487, plain, (![B_943, C_945, B_946, B_947, A_942, D_944]: (r3_lattices(B_943, k3_lattices(B_943, C_945, B_946), '#skF_1'(A_942, B_947, a_3_4_lattice3(B_943, C_945, D_944))) | ~m1_subset_1('#skF_2'('#skF_1'(A_942, B_947, a_3_4_lattice3(B_943, C_945, D_944)), B_943, C_945, D_944), u1_struct_0(B_943)) | ~v5_lattices(B_943) | ~v4_lattices(B_943) | r3_lattice3(A_942, B_947, a_3_4_lattice3(B_943, C_945, D_944)) | ~m1_subset_1(B_947, u1_struct_0(A_942)) | ~l3_lattices(A_942) | v2_struct_0(A_942) | ~r1_lattices(B_943, B_946, '#skF_2'('#skF_1'(A_942, B_947, a_3_4_lattice3(B_943, C_945, D_944)), B_943, C_945, D_944)) | ~m1_subset_1(B_946, u1_struct_0(B_943)) | ~v9_lattices(B_943) | ~v8_lattices(B_943) | ~v6_lattices(B_943) | ~r2_hidden('#skF_1'(A_942, B_947, a_3_4_lattice3(B_943, C_945, D_944)), a_3_4_lattice3(B_943, C_945, D_944)) | ~m1_subset_1(C_945, u1_struct_0(B_943)) | ~l3_lattices(B_943) | ~v4_lattice3(B_943) | ~v10_lattices(B_943) | v2_struct_0(B_943))), inference(resolution, [status(thm)], [c_154, c_2578])).
% 9.39/3.52  tff(c_3496, plain, (![C_951, B_953, D_949, B_950, A_952, B_948]: (r3_lattices(B_950, k3_lattices(B_950, C_951, B_953), '#skF_1'(A_952, B_948, a_3_4_lattice3(B_950, C_951, D_949))) | ~v5_lattices(B_950) | ~v4_lattices(B_950) | r3_lattice3(A_952, B_948, a_3_4_lattice3(B_950, C_951, D_949)) | ~m1_subset_1(B_948, u1_struct_0(A_952)) | ~l3_lattices(A_952) | v2_struct_0(A_952) | ~r1_lattices(B_950, B_953, '#skF_2'('#skF_1'(A_952, B_948, a_3_4_lattice3(B_950, C_951, D_949)), B_950, C_951, D_949)) | ~m1_subset_1(B_953, u1_struct_0(B_950)) | ~v9_lattices(B_950) | ~v8_lattices(B_950) | ~v6_lattices(B_950) | ~r2_hidden('#skF_1'(A_952, B_948, a_3_4_lattice3(B_950, C_951, D_949)), a_3_4_lattice3(B_950, C_951, D_949)) | ~m1_subset_1(C_951, u1_struct_0(B_950)) | ~l3_lattices(B_950) | ~v4_lattice3(B_950) | ~v10_lattices(B_950) | v2_struct_0(B_950))), inference(resolution, [status(thm)], [c_44, c_3487])).
% 9.39/3.52  tff(c_3505, plain, (![D_954, C_956, A_958, B_959, B_955, B_957]: (r3_lattices(B_955, k3_lattices(B_955, C_956, B_959), '#skF_1'(A_958, B_957, a_3_4_lattice3(B_955, C_956, D_954))) | ~v5_lattices(B_955) | ~v4_lattices(B_955) | r3_lattice3(A_958, B_957, a_3_4_lattice3(B_955, C_956, D_954)) | ~m1_subset_1(B_957, u1_struct_0(A_958)) | ~l3_lattices(A_958) | v2_struct_0(A_958) | ~v9_lattices(B_955) | ~v8_lattices(B_955) | ~v6_lattices(B_955) | ~r3_lattice3(B_955, B_959, D_954) | ~m1_subset_1(B_959, u1_struct_0(B_955)) | ~r2_hidden('#skF_1'(A_958, B_957, a_3_4_lattice3(B_955, C_956, D_954)), a_3_4_lattice3(B_955, C_956, D_954)) | ~m1_subset_1(C_956, u1_struct_0(B_955)) | ~l3_lattices(B_955) | ~v4_lattice3(B_955) | ~v10_lattices(B_955) | v2_struct_0(B_955))), inference(resolution, [status(thm)], [c_512, c_3496])).
% 9.39/3.52  tff(c_3510, plain, (![A_962, C_963, B_964, B_960, D_961, B_965]: (r3_lattices(B_964, k3_lattices(B_964, C_963, B_960), '#skF_1'(A_962, B_965, a_3_4_lattice3(B_964, C_963, D_961))) | ~v5_lattices(B_964) | ~v4_lattices(B_964) | ~v9_lattices(B_964) | ~v8_lattices(B_964) | ~v6_lattices(B_964) | ~r3_lattice3(B_964, B_960, D_961) | ~m1_subset_1(B_960, u1_struct_0(B_964)) | ~m1_subset_1(C_963, u1_struct_0(B_964)) | ~l3_lattices(B_964) | ~v4_lattice3(B_964) | ~v10_lattices(B_964) | v2_struct_0(B_964) | r3_lattice3(A_962, B_965, a_3_4_lattice3(B_964, C_963, D_961)) | ~m1_subset_1(B_965, u1_struct_0(A_962)) | ~l3_lattices(A_962) | v2_struct_0(A_962))), inference(resolution, [status(thm)], [c_32, c_3505])).
% 9.39/3.52  tff(c_24, plain, (![A_6, B_7, C_8]: (r1_lattices(A_6, B_7, C_8) | ~r3_lattices(A_6, B_7, C_8) | ~m1_subset_1(C_8, u1_struct_0(A_6)) | ~m1_subset_1(B_7, u1_struct_0(A_6)) | ~l3_lattices(A_6) | ~v9_lattices(A_6) | ~v8_lattices(A_6) | ~v6_lattices(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.39/3.52  tff(c_3523, plain, (![B_971, B_970, B_967, C_969, D_968, A_966]: (r1_lattices(B_967, k3_lattices(B_967, C_969, B_971), '#skF_1'(A_966, B_970, a_3_4_lattice3(B_967, C_969, D_968))) | ~m1_subset_1('#skF_1'(A_966, B_970, a_3_4_lattice3(B_967, C_969, D_968)), u1_struct_0(B_967)) | ~m1_subset_1(k3_lattices(B_967, C_969, B_971), u1_struct_0(B_967)) | ~v5_lattices(B_967) | ~v4_lattices(B_967) | ~v9_lattices(B_967) | ~v8_lattices(B_967) | ~v6_lattices(B_967) | ~r3_lattice3(B_967, B_971, D_968) | ~m1_subset_1(B_971, u1_struct_0(B_967)) | ~m1_subset_1(C_969, u1_struct_0(B_967)) | ~l3_lattices(B_967) | ~v4_lattice3(B_967) | ~v10_lattices(B_967) | v2_struct_0(B_967) | r3_lattice3(A_966, B_970, a_3_4_lattice3(B_967, C_969, D_968)) | ~m1_subset_1(B_970, u1_struct_0(A_966)) | ~l3_lattices(A_966) | v2_struct_0(A_966))), inference(resolution, [status(thm)], [c_3510, c_24])).
% 9.39/3.52  tff(c_30, plain, (![A_24, B_36, C_42]: (~r1_lattices(A_24, B_36, '#skF_1'(A_24, B_36, C_42)) | r3_lattice3(A_24, B_36, C_42) | ~m1_subset_1(B_36, u1_struct_0(A_24)) | ~l3_lattices(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.39/3.52  tff(c_3544, plain, (![A_979, C_980, B_981, D_982]: (~m1_subset_1('#skF_1'(A_979, k3_lattices(A_979, C_980, B_981), a_3_4_lattice3(A_979, C_980, D_982)), u1_struct_0(A_979)) | ~v5_lattices(A_979) | ~v4_lattices(A_979) | ~v9_lattices(A_979) | ~v8_lattices(A_979) | ~v6_lattices(A_979) | ~r3_lattice3(A_979, B_981, D_982) | ~m1_subset_1(B_981, u1_struct_0(A_979)) | ~m1_subset_1(C_980, u1_struct_0(A_979)) | ~v4_lattice3(A_979) | ~v10_lattices(A_979) | r3_lattice3(A_979, k3_lattices(A_979, C_980, B_981), a_3_4_lattice3(A_979, C_980, D_982)) | ~m1_subset_1(k3_lattices(A_979, C_980, B_981), u1_struct_0(A_979)) | ~l3_lattices(A_979) | v2_struct_0(A_979))), inference(resolution, [status(thm)], [c_3523, c_30])).
% 9.39/3.52  tff(c_3564, plain, (![A_983, B_984, D_985, C_986]: (~v5_lattices(A_983) | ~v4_lattices(A_983) | ~v9_lattices(A_983) | ~v8_lattices(A_983) | ~v6_lattices(A_983) | ~r3_lattice3(A_983, B_984, D_985) | ~m1_subset_1(B_984, u1_struct_0(A_983)) | ~m1_subset_1(C_986, u1_struct_0(A_983)) | ~v4_lattice3(A_983) | ~v10_lattices(A_983) | r3_lattice3(A_983, k3_lattices(A_983, C_986, B_984), a_3_4_lattice3(A_983, C_986, D_985)) | ~m1_subset_1(k3_lattices(A_983, C_986, B_984), u1_struct_0(A_983)) | ~l3_lattices(A_983) | v2_struct_0(A_983))), inference(resolution, [status(thm)], [c_34, c_3544])).
% 9.39/3.52  tff(c_339, plain, (![A_158, D_159, C_160]: (r3_lattices(A_158, D_159, k16_lattice3(A_158, C_160)) | ~r3_lattice3(A_158, D_159, C_160) | ~m1_subset_1(D_159, u1_struct_0(A_158)) | ~m1_subset_1(k16_lattice3(A_158, C_160), u1_struct_0(A_158)) | ~l3_lattices(A_158) | ~v4_lattice3(A_158) | ~v10_lattices(A_158) | v2_struct_0(A_158))), inference(cnfTransformation, [status(thm)], [f_182])).
% 9.39/3.52  tff(c_350, plain, (![A_165, D_166, B_167]: (r3_lattices(A_165, D_166, k16_lattice3(A_165, B_167)) | ~r3_lattice3(A_165, D_166, B_167) | ~m1_subset_1(D_166, u1_struct_0(A_165)) | ~v4_lattice3(A_165) | ~v10_lattices(A_165) | ~l3_lattices(A_165) | v2_struct_0(A_165))), inference(resolution, [status(thm)], [c_36, c_339])).
% 9.39/3.52  tff(c_359, plain, (~r3_lattice3('#skF_4', k3_lattices('#skF_4', '#skF_5', k16_lattice3('#skF_4', '#skF_6')), a_3_4_lattice3('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(k3_lattices('#skF_4', '#skF_5', k16_lattice3('#skF_4', '#skF_6')), u1_struct_0('#skF_4')) | ~v4_lattice3('#skF_4') | ~v10_lattices('#skF_4') | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_350, c_56])).
% 9.39/3.52  tff(c_364, plain, (~r3_lattice3('#skF_4', k3_lattices('#skF_4', '#skF_5', k16_lattice3('#skF_4', '#skF_6')), a_3_4_lattice3('#skF_4', '#skF_5', '#skF_6')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_64, c_62, c_266, c_359])).
% 9.39/3.52  tff(c_365, plain, (~r3_lattice3('#skF_4', k3_lattices('#skF_4', '#skF_5', k16_lattice3('#skF_4', '#skF_6')), a_3_4_lattice3('#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_66, c_364])).
% 9.39/3.52  tff(c_3585, plain, (~v5_lattices('#skF_4') | ~v4_lattices('#skF_4') | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | ~r3_lattice3('#skF_4', k16_lattice3('#skF_4', '#skF_6'), '#skF_6') | ~m1_subset_1(k16_lattice3('#skF_4', '#skF_6'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v4_lattice3('#skF_4') | ~v10_lattices('#skF_4') | ~m1_subset_1(k3_lattices('#skF_4', '#skF_5', k16_lattice3('#skF_4', '#skF_6')), u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_3564, c_365])).
% 9.39/3.52  tff(c_3610, plain, (~r3_lattice3('#skF_4', k16_lattice3('#skF_4', '#skF_6'), '#skF_6') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_266, c_64, c_62, c_58, c_586, c_128, c_150, c_139, c_217, c_1476, c_3585])).
% 9.39/3.52  tff(c_3611, plain, (~r3_lattice3('#skF_4', k16_lattice3('#skF_4', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_66, c_3610])).
% 9.39/3.52  tff(c_3614, plain, (~v4_lattice3('#skF_4') | ~v10_lattices('#skF_4') | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_90, c_3611])).
% 9.39/3.52  tff(c_3617, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_64, c_62, c_3614])).
% 9.39/3.52  tff(c_3619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_3617])).
% 9.39/3.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.39/3.52  
% 9.39/3.52  Inference rules
% 9.39/3.52  ----------------------
% 9.39/3.52  #Ref     : 0
% 9.39/3.52  #Sup     : 684
% 9.39/3.52  #Fact    : 0
% 9.39/3.52  #Define  : 0
% 9.39/3.52  #Split   : 9
% 9.39/3.52  #Chain   : 0
% 9.39/3.52  #Close   : 0
% 9.39/3.52  
% 9.39/3.52  Ordering : KBO
% 9.39/3.52  
% 9.39/3.52  Simplification rules
% 9.39/3.52  ----------------------
% 9.39/3.52  #Subsume      : 118
% 9.39/3.52  #Demod        : 1117
% 9.39/3.52  #Tautology    : 34
% 9.39/3.52  #SimpNegUnit  : 302
% 9.39/3.52  #BackRed      : 0
% 9.39/3.52  
% 9.39/3.52  #Partial instantiations: 0
% 9.39/3.52  #Strategies tried      : 1
% 9.39/3.52  
% 9.39/3.52  Timing (in seconds)
% 9.39/3.52  ----------------------
% 9.39/3.52  Preprocessing        : 0.37
% 9.39/3.52  Parsing              : 0.20
% 9.39/3.52  CNF conversion       : 0.03
% 9.39/3.52  Main loop            : 2.38
% 9.39/3.52  Inferencing          : 0.79
% 9.39/3.52  Reduction            : 0.51
% 9.39/3.52  Demodulation         : 0.35
% 9.39/3.52  BG Simplification    : 0.08
% 9.39/3.52  Subsumption          : 0.89
% 9.39/3.52  Abstraction          : 0.09
% 9.39/3.52  MUC search           : 0.00
% 9.39/3.52  Cooper               : 0.00
% 9.39/3.52  Total                : 2.80
% 9.39/3.52  Index Insertion      : 0.00
% 9.39/3.52  Index Deletion       : 0.00
% 9.39/3.52  Index Matching       : 0.00
% 9.39/3.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
