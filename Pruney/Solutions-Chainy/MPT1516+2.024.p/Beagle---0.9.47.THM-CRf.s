%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:54 EST 2020

% Result     : Theorem 15.11s
% Output     : CNFRefutation 15.27s
% Verified   : 
% Statistics : Number of formulae       :  222 (3436 expanded)
%              Number of leaves         :   57 (1245 expanded)
%              Depth                    :   32
%              Number of atoms          :  709 (15137 expanded)
%              Number of equality atoms :  106 (1759 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k6_domain_1 > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > a_2_5_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_5 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(a_2_5_lattice3,type,(
    a_2_5_lattice3: ( $i * $i ) > $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v13_lattices,type,(
    v13_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_lattices,type,(
    k5_lattices: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(a_2_6_lattice3,type,(
    a_2_6_lattice3: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_264,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v13_lattices(A)
          & l3_lattices(A)
          & k5_lattices(A) = k15_lattice3(A,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).

tff(f_97,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_174,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_152,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => ( v13_lattices(A)
      <=> ? [B] :
            ( m1_subset_1(B,u1_struct_0(A))
            & ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( k2_lattices(A,B,C) = B
                  & k2_lattices(A,C,B) = B ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).

tff(f_213,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( k15_lattice3(A,k6_domain_1(u1_struct_0(A),B)) = B
            & k16_lattice3(A,k6_domain_1(u1_struct_0(A),B)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattice3)).

tff(f_65,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_197,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v10_lattices(B)
        & v4_lattice3(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_5_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ? [E] :
                ( m1_subset_1(E,u1_struct_0(B))
                & r3_lattices(B,D,E)
                & r2_hidden(E,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_38,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_243,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( k15_lattice3(A,B) = k15_lattice3(A,a_2_5_lattice3(A,B))
          & k16_lattice3(A,B) = k16_lattice3(A,a_2_6_lattice3(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattice3)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

tff(f_167,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => ( v6_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k2_lattices(A,B,C) = k2_lattices(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).

tff(f_229,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B,C] :
          ( r1_tarski(B,C)
         => ( r3_lattices(A,k15_lattice3(A,B),k15_lattice3(A,C))
            & r3_lattices(A,k16_lattice3(A,C),k16_lattice3(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_lattice3)).

tff(f_116,axiom,(
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

tff(f_135,axiom,(
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

tff(f_84,axiom,(
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

tff(c_102,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_96,plain,(
    l3_lattices('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_107,plain,(
    ! [A_82] :
      ( l1_lattices(A_82)
      | ~ l3_lattices(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_111,plain,(
    l1_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_96,c_107])).

tff(c_68,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(k15_lattice3(A_55,B_56),u1_struct_0(A_55))
      | ~ l3_lattices(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_100,plain,(
    v10_lattices('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_94,plain,
    ( k15_lattice3('#skF_9',k1_xboole_0) != k5_lattices('#skF_9')
    | ~ l3_lattices('#skF_9')
    | ~ v13_lattices('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_104,plain,
    ( k15_lattice3('#skF_9',k1_xboole_0) != k5_lattices('#skF_9')
    | ~ v13_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_96,c_94])).

tff(c_105,plain,
    ( k15_lattice3('#skF_9',k1_xboole_0) != k5_lattices('#skF_9')
    | ~ v13_lattices('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_104])).

tff(c_117,plain,(
    ~ v13_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_52,plain,(
    ! [A_33,B_42] :
      ( m1_subset_1('#skF_4'(A_33,B_42),u1_struct_0(A_33))
      | v13_lattices(A_33)
      | ~ m1_subset_1(B_42,u1_struct_0(A_33))
      | ~ l1_lattices(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_98,plain,(
    v4_lattice3('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_84,plain,(
    ! [A_70,B_72] :
      ( k15_lattice3(A_70,k6_domain_1(u1_struct_0(A_70),B_72)) = B_72
      | ~ m1_subset_1(B_72,u1_struct_0(A_70))
      | ~ l3_lattices(A_70)
      | ~ v4_lattice3(A_70)
      | ~ v10_lattices(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_20,plain,(
    ! [A_10] :
      ( v6_lattices(A_10)
      | ~ v10_lattices(A_10)
      | v2_struct_0(A_10)
      | ~ l3_lattices(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_394,plain,(
    ! [A_150,B_151,C_152] :
      ( r2_hidden('#skF_8'(A_150,B_151,C_152),C_152)
      | ~ r2_hidden(A_150,a_2_5_lattice3(B_151,C_152))
      | ~ l3_lattices(B_151)
      | ~ v4_lattice3(B_151)
      | ~ v10_lattices(B_151)
      | v2_struct_0(B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( ~ r1_tarski(B_9,A_8)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_447,plain,(
    ! [C_164,A_165,B_166] :
      ( ~ r1_tarski(C_164,'#skF_8'(A_165,B_166,C_164))
      | ~ r2_hidden(A_165,a_2_5_lattice3(B_166,C_164))
      | ~ l3_lattices(B_166)
      | ~ v4_lattice3(B_166)
      | ~ v10_lattices(B_166)
      | v2_struct_0(B_166) ) ),
    inference(resolution,[status(thm)],[c_394,c_12])).

tff(c_452,plain,(
    ! [A_167,B_168] :
      ( ~ r2_hidden(A_167,a_2_5_lattice3(B_168,k1_xboole_0))
      | ~ l3_lattices(B_168)
      | ~ v4_lattice3(B_168)
      | ~ v10_lattices(B_168)
      | v2_struct_0(B_168) ) ),
    inference(resolution,[status(thm)],[c_8,c_447])).

tff(c_468,plain,(
    ! [B_169,B_170] :
      ( ~ l3_lattices(B_169)
      | ~ v4_lattice3(B_169)
      | ~ v10_lattices(B_169)
      | v2_struct_0(B_169)
      | r1_tarski(a_2_5_lattice3(B_169,k1_xboole_0),B_170) ) ),
    inference(resolution,[status(thm)],[c_6,c_452])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_502,plain,(
    ! [B_174] :
      ( a_2_5_lattice3(B_174,k1_xboole_0) = k1_xboole_0
      | ~ l3_lattices(B_174)
      | ~ v4_lattice3(B_174)
      | ~ v10_lattices(B_174)
      | v2_struct_0(B_174) ) ),
    inference(resolution,[status(thm)],[c_468,c_10])).

tff(c_505,plain,
    ( a_2_5_lattice3('#skF_9',k1_xboole_0) = k1_xboole_0
    | ~ l3_lattices('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_98,c_502])).

tff(c_508,plain,
    ( a_2_5_lattice3('#skF_9',k1_xboole_0) = k1_xboole_0
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_96,c_505])).

tff(c_509,plain,(
    a_2_5_lattice3('#skF_9',k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_508])).

tff(c_90,plain,(
    ! [A_78,B_80] :
      ( k15_lattice3(A_78,a_2_5_lattice3(A_78,B_80)) = k15_lattice3(A_78,B_80)
      | ~ l3_lattices(A_78)
      | ~ v4_lattice3(A_78)
      | ~ v10_lattices(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_36,plain,(
    ! [A_21] :
      ( m1_subset_1(k5_lattices(A_21),u1_struct_0(A_21))
      | ~ l1_lattices(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_575,plain,(
    ! [A_179,C_180,B_181] :
      ( k2_lattices(A_179,C_180,B_181) = k2_lattices(A_179,B_181,C_180)
      | ~ m1_subset_1(C_180,u1_struct_0(A_179))
      | ~ m1_subset_1(B_181,u1_struct_0(A_179))
      | ~ v6_lattices(A_179)
      | ~ l1_lattices(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_603,plain,(
    ! [A_182,B_183] :
      ( k2_lattices(A_182,k5_lattices(A_182),B_183) = k2_lattices(A_182,B_183,k5_lattices(A_182))
      | ~ m1_subset_1(B_183,u1_struct_0(A_182))
      | ~ v6_lattices(A_182)
      | ~ l1_lattices(A_182)
      | v2_struct_0(A_182) ) ),
    inference(resolution,[status(thm)],[c_36,c_575])).

tff(c_1159,plain,(
    ! [A_260,B_261] :
      ( k2_lattices(A_260,k15_lattice3(A_260,B_261),k5_lattices(A_260)) = k2_lattices(A_260,k5_lattices(A_260),k15_lattice3(A_260,B_261))
      | ~ v6_lattices(A_260)
      | ~ l1_lattices(A_260)
      | ~ l3_lattices(A_260)
      | v2_struct_0(A_260) ) ),
    inference(resolution,[status(thm)],[c_68,c_603])).

tff(c_3079,plain,(
    ! [A_520,B_521] :
      ( k2_lattices(A_520,k5_lattices(A_520),k15_lattice3(A_520,a_2_5_lattice3(A_520,B_521))) = k2_lattices(A_520,k15_lattice3(A_520,B_521),k5_lattices(A_520))
      | ~ v6_lattices(A_520)
      | ~ l1_lattices(A_520)
      | ~ l3_lattices(A_520)
      | v2_struct_0(A_520)
      | ~ l3_lattices(A_520)
      | ~ v4_lattice3(A_520)
      | ~ v10_lattices(A_520)
      | v2_struct_0(A_520) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_1159])).

tff(c_3101,plain,
    ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),k5_lattices('#skF_9')) = k2_lattices('#skF_9',k5_lattices('#skF_9'),k15_lattice3('#skF_9',k1_xboole_0))
    | ~ v6_lattices('#skF_9')
    | ~ l1_lattices('#skF_9')
    | ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9')
    | ~ v4_lattice3('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_509,c_3079])).

tff(c_3108,plain,
    ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),k5_lattices('#skF_9')) = k2_lattices('#skF_9',k5_lattices('#skF_9'),k15_lattice3('#skF_9',k1_xboole_0))
    | ~ v6_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_96,c_96,c_111,c_3101])).

tff(c_3109,plain,
    ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),k5_lattices('#skF_9')) = k2_lattices('#skF_9',k5_lattices('#skF_9'),k15_lattice3('#skF_9',k1_xboole_0))
    | ~ v6_lattices('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_3108])).

tff(c_3110,plain,(
    ~ v6_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_3109])).

tff(c_3117,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_20,c_3110])).

tff(c_3120,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_100,c_3117])).

tff(c_3122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_3120])).

tff(c_3124,plain,(
    v6_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_3109])).

tff(c_16,plain,(
    ! [A_10] :
      ( v8_lattices(A_10)
      | ~ v10_lattices(A_10)
      | v2_struct_0(A_10)
      | ~ l3_lattices(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_427,plain,(
    ! [A_158,B_159,C_160] :
      ( r3_lattices(A_158,k15_lattice3(A_158,B_159),k15_lattice3(A_158,C_160))
      | ~ r1_tarski(B_159,C_160)
      | ~ l3_lattices(A_158)
      | ~ v4_lattice3(A_158)
      | ~ v10_lattices(A_158)
      | v2_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_2933,plain,(
    ! [A_493,B_494,B_495] :
      ( r3_lattices(A_493,k15_lattice3(A_493,B_494),B_495)
      | ~ r1_tarski(B_494,k6_domain_1(u1_struct_0(A_493),B_495))
      | ~ l3_lattices(A_493)
      | ~ v4_lattice3(A_493)
      | ~ v10_lattices(A_493)
      | v2_struct_0(A_493)
      | ~ m1_subset_1(B_495,u1_struct_0(A_493))
      | ~ l3_lattices(A_493)
      | ~ v4_lattice3(A_493)
      | ~ v10_lattices(A_493)
      | v2_struct_0(A_493) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_427])).

tff(c_2966,plain,(
    ! [A_496,B_497] :
      ( r3_lattices(A_496,k15_lattice3(A_496,k1_xboole_0),B_497)
      | ~ m1_subset_1(B_497,u1_struct_0(A_496))
      | ~ l3_lattices(A_496)
      | ~ v4_lattice3(A_496)
      | ~ v10_lattices(A_496)
      | v2_struct_0(A_496) ) ),
    inference(resolution,[status(thm)],[c_8,c_2933])).

tff(c_44,plain,(
    ! [A_23,B_24,C_25] :
      ( r1_lattices(A_23,B_24,C_25)
      | ~ r3_lattices(A_23,B_24,C_25)
      | ~ m1_subset_1(C_25,u1_struct_0(A_23))
      | ~ m1_subset_1(B_24,u1_struct_0(A_23))
      | ~ l3_lattices(A_23)
      | ~ v9_lattices(A_23)
      | ~ v8_lattices(A_23)
      | ~ v6_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3007,plain,(
    ! [A_506,B_507] :
      ( r1_lattices(A_506,k15_lattice3(A_506,k1_xboole_0),B_507)
      | ~ m1_subset_1(k15_lattice3(A_506,k1_xboole_0),u1_struct_0(A_506))
      | ~ v9_lattices(A_506)
      | ~ v8_lattices(A_506)
      | ~ v6_lattices(A_506)
      | ~ m1_subset_1(B_507,u1_struct_0(A_506))
      | ~ l3_lattices(A_506)
      | ~ v4_lattice3(A_506)
      | ~ v10_lattices(A_506)
      | v2_struct_0(A_506) ) ),
    inference(resolution,[status(thm)],[c_2966,c_44])).

tff(c_3035,plain,(
    ! [A_512,B_513] :
      ( r1_lattices(A_512,k15_lattice3(A_512,k1_xboole_0),B_513)
      | ~ v9_lattices(A_512)
      | ~ v8_lattices(A_512)
      | ~ v6_lattices(A_512)
      | ~ m1_subset_1(B_513,u1_struct_0(A_512))
      | ~ v4_lattice3(A_512)
      | ~ v10_lattices(A_512)
      | ~ l3_lattices(A_512)
      | v2_struct_0(A_512) ) ),
    inference(resolution,[status(thm)],[c_68,c_3007])).

tff(c_48,plain,(
    ! [A_26,B_30,C_32] :
      ( k2_lattices(A_26,B_30,C_32) = B_30
      | ~ r1_lattices(A_26,B_30,C_32)
      | ~ m1_subset_1(C_32,u1_struct_0(A_26))
      | ~ m1_subset_1(B_30,u1_struct_0(A_26))
      | ~ l3_lattices(A_26)
      | ~ v9_lattices(A_26)
      | ~ v8_lattices(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3676,plain,(
    ! [A_563,B_564] :
      ( k2_lattices(A_563,k15_lattice3(A_563,k1_xboole_0),B_564) = k15_lattice3(A_563,k1_xboole_0)
      | ~ m1_subset_1(k15_lattice3(A_563,k1_xboole_0),u1_struct_0(A_563))
      | ~ v9_lattices(A_563)
      | ~ v8_lattices(A_563)
      | ~ v6_lattices(A_563)
      | ~ m1_subset_1(B_564,u1_struct_0(A_563))
      | ~ v4_lattice3(A_563)
      | ~ v10_lattices(A_563)
      | ~ l3_lattices(A_563)
      | v2_struct_0(A_563) ) ),
    inference(resolution,[status(thm)],[c_3035,c_48])).

tff(c_3681,plain,(
    ! [A_565,B_566] :
      ( k2_lattices(A_565,k15_lattice3(A_565,k1_xboole_0),B_566) = k15_lattice3(A_565,k1_xboole_0)
      | ~ v9_lattices(A_565)
      | ~ v8_lattices(A_565)
      | ~ v6_lattices(A_565)
      | ~ m1_subset_1(B_566,u1_struct_0(A_565))
      | ~ v4_lattice3(A_565)
      | ~ v10_lattices(A_565)
      | ~ l3_lattices(A_565)
      | v2_struct_0(A_565) ) ),
    inference(resolution,[status(thm)],[c_68,c_3676])).

tff(c_3751,plain,(
    ! [A_569] :
      ( k2_lattices(A_569,k15_lattice3(A_569,k1_xboole_0),k5_lattices(A_569)) = k15_lattice3(A_569,k1_xboole_0)
      | ~ v9_lattices(A_569)
      | ~ v8_lattices(A_569)
      | ~ v6_lattices(A_569)
      | ~ v4_lattice3(A_569)
      | ~ v10_lattices(A_569)
      | ~ l3_lattices(A_569)
      | ~ l1_lattices(A_569)
      | v2_struct_0(A_569) ) ),
    inference(resolution,[status(thm)],[c_36,c_3681])).

tff(c_3123,plain,(
    k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),k5_lattices('#skF_9')) = k2_lattices('#skF_9',k5_lattices('#skF_9'),k15_lattice3('#skF_9',k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_3109])).

tff(c_3757,plain,
    ( k2_lattices('#skF_9',k5_lattices('#skF_9'),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
    | ~ v9_lattices('#skF_9')
    | ~ v8_lattices('#skF_9')
    | ~ v6_lattices('#skF_9')
    | ~ v4_lattice3('#skF_9')
    | ~ v10_lattices('#skF_9')
    | ~ l3_lattices('#skF_9')
    | ~ l1_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_3751,c_3123])).

tff(c_3780,plain,
    ( k2_lattices('#skF_9',k5_lattices('#skF_9'),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
    | ~ v9_lattices('#skF_9')
    | ~ v8_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_96,c_100,c_98,c_3124,c_3757])).

tff(c_3781,plain,
    ( k2_lattices('#skF_9',k5_lattices('#skF_9'),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
    | ~ v9_lattices('#skF_9')
    | ~ v8_lattices('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_3780])).

tff(c_3786,plain,(
    ~ v8_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_3781])).

tff(c_3789,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_16,c_3786])).

tff(c_3792,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_100,c_3789])).

tff(c_3794,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_3792])).

tff(c_3796,plain,(
    v8_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_3781])).

tff(c_14,plain,(
    ! [A_10] :
      ( v9_lattices(A_10)
      | ~ v10_lattices(A_10)
      | v2_struct_0(A_10)
      | ~ l3_lattices(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3795,plain,
    ( ~ v9_lattices('#skF_9')
    | k2_lattices('#skF_9',k5_lattices('#skF_9'),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3781])).

tff(c_3797,plain,(
    ~ v9_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_3795])).

tff(c_3828,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_14,c_3797])).

tff(c_3831,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_100,c_3828])).

tff(c_3833,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_3831])).

tff(c_3835,plain,(
    v9_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_3795])).

tff(c_1421,plain,(
    ! [A_283,B_284,B_285] :
      ( k2_lattices(A_283,k15_lattice3(A_283,B_284),B_285) = k2_lattices(A_283,B_285,k15_lattice3(A_283,B_284))
      | ~ m1_subset_1(B_285,u1_struct_0(A_283))
      | ~ v6_lattices(A_283)
      | ~ l1_lattices(A_283)
      | ~ l3_lattices(A_283)
      | v2_struct_0(A_283) ) ),
    inference(resolution,[status(thm)],[c_68,c_575])).

tff(c_1470,plain,(
    ! [A_288,B_290,B_289] :
      ( k2_lattices(A_288,k15_lattice3(A_288,B_290),k15_lattice3(A_288,B_289)) = k2_lattices(A_288,k15_lattice3(A_288,B_289),k15_lattice3(A_288,B_290))
      | ~ v6_lattices(A_288)
      | ~ l1_lattices(A_288)
      | ~ l3_lattices(A_288)
      | v2_struct_0(A_288) ) ),
    inference(resolution,[status(thm)],[c_68,c_1421])).

tff(c_4406,plain,(
    ! [A_615,B_616,B_617] :
      ( k2_lattices(A_615,k15_lattice3(A_615,B_616),k15_lattice3(A_615,a_2_5_lattice3(A_615,B_617))) = k2_lattices(A_615,k15_lattice3(A_615,B_617),k15_lattice3(A_615,B_616))
      | ~ v6_lattices(A_615)
      | ~ l1_lattices(A_615)
      | ~ l3_lattices(A_615)
      | v2_struct_0(A_615)
      | ~ l3_lattices(A_615)
      | ~ v4_lattice3(A_615)
      | ~ v10_lattices(A_615)
      | v2_struct_0(A_615) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_1470])).

tff(c_4461,plain,(
    ! [B_616] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),k15_lattice3('#skF_9',B_616)) = k2_lattices('#skF_9',k15_lattice3('#skF_9',B_616),k15_lattice3('#skF_9',k1_xboole_0))
      | ~ v6_lattices('#skF_9')
      | ~ l1_lattices('#skF_9')
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l3_lattices('#skF_9')
      | ~ v4_lattice3('#skF_9')
      | ~ v10_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_509,c_4406])).

tff(c_4474,plain,(
    ! [B_616] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),k15_lattice3('#skF_9',B_616)) = k2_lattices('#skF_9',k15_lattice3('#skF_9',B_616),k15_lattice3('#skF_9',k1_xboole_0))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_96,c_96,c_111,c_3124,c_4461])).

tff(c_4476,plain,(
    ! [B_618] : k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),k15_lattice3('#skF_9',B_618)) = k2_lattices('#skF_9',k15_lattice3('#skF_9',B_618),k15_lattice3('#skF_9',k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_4474])).

tff(c_3707,plain,(
    ! [A_55,B_56] :
      ( k2_lattices(A_55,k15_lattice3(A_55,k1_xboole_0),k15_lattice3(A_55,B_56)) = k15_lattice3(A_55,k1_xboole_0)
      | ~ v9_lattices(A_55)
      | ~ v8_lattices(A_55)
      | ~ v6_lattices(A_55)
      | ~ v4_lattice3(A_55)
      | ~ v10_lattices(A_55)
      | ~ l3_lattices(A_55)
      | v2_struct_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_68,c_3681])).

tff(c_4488,plain,(
    ! [B_618] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',B_618),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
      | ~ v9_lattices('#skF_9')
      | ~ v8_lattices('#skF_9')
      | ~ v6_lattices('#skF_9')
      | ~ v4_lattice3('#skF_9')
      | ~ v10_lattices('#skF_9')
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4476,c_3707])).

tff(c_4549,plain,(
    ! [B_618] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',B_618),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_100,c_98,c_3124,c_3796,c_3835,c_4488])).

tff(c_4601,plain,(
    ! [B_619] : k2_lattices('#skF_9',k15_lattice3('#skF_9',B_619),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_4549])).

tff(c_4650,plain,(
    ! [B_72] :
      ( k2_lattices('#skF_9',B_72,k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
      | ~ m1_subset_1(B_72,u1_struct_0('#skF_9'))
      | ~ l3_lattices('#skF_9')
      | ~ v4_lattice3('#skF_9')
      | ~ v10_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_4601])).

tff(c_4697,plain,(
    ! [B_72] :
      ( k2_lattices('#skF_9',B_72,k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
      | ~ m1_subset_1(B_72,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_96,c_4650])).

tff(c_4909,plain,(
    ! [B_625] :
      ( k2_lattices('#skF_9',B_625,k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
      | ~ m1_subset_1(B_625,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_4697])).

tff(c_4925,plain,(
    ! [B_42] :
      ( k2_lattices('#skF_9','#skF_4'('#skF_9',B_42),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
      | v13_lattices('#skF_9')
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_9'))
      | ~ l1_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_52,c_4909])).

tff(c_4960,plain,(
    ! [B_42] :
      ( k2_lattices('#skF_9','#skF_4'('#skF_9',B_42),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
      | v13_lattices('#skF_9')
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_4925])).

tff(c_5023,plain,(
    ! [B_630] :
      ( k2_lattices('#skF_9','#skF_4'('#skF_9',B_630),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
      | ~ m1_subset_1(B_630,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_117,c_4960])).

tff(c_50,plain,(
    ! [A_33,B_42] :
      ( k2_lattices(A_33,'#skF_4'(A_33,B_42),B_42) != B_42
      | k2_lattices(A_33,B_42,'#skF_4'(A_33,B_42)) != B_42
      | v13_lattices(A_33)
      | ~ m1_subset_1(B_42,u1_struct_0(A_33))
      | ~ l1_lattices(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_5032,plain,
    ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),'#skF_4'('#skF_9',k15_lattice3('#skF_9',k1_xboole_0))) != k15_lattice3('#skF_9',k1_xboole_0)
    | v13_lattices('#skF_9')
    | ~ l1_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ m1_subset_1(k15_lattice3('#skF_9',k1_xboole_0),u1_struct_0('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5023,c_50])).

tff(c_5046,plain,
    ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),'#skF_4'('#skF_9',k15_lattice3('#skF_9',k1_xboole_0))) != k15_lattice3('#skF_9',k1_xboole_0)
    | v13_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ m1_subset_1(k15_lattice3('#skF_9',k1_xboole_0),u1_struct_0('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_5032])).

tff(c_5047,plain,
    ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),'#skF_4'('#skF_9',k15_lattice3('#skF_9',k1_xboole_0))) != k15_lattice3('#skF_9',k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3('#skF_9',k1_xboole_0),u1_struct_0('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_117,c_5046])).

tff(c_5133,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_9',k1_xboole_0),u1_struct_0('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_5047])).

tff(c_5152,plain,
    ( ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_68,c_5133])).

tff(c_5155,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_5152])).

tff(c_5157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_5155])).

tff(c_5159,plain,(
    m1_subset_1(k15_lattice3('#skF_9',k1_xboole_0),u1_struct_0('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_5047])).

tff(c_4550,plain,(
    ! [B_618] : k2_lattices('#skF_9',k15_lattice3('#skF_9',B_618),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_4549])).

tff(c_4475,plain,(
    ! [B_616] : k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),k15_lattice3('#skF_9',B_616)) = k2_lattices('#skF_9',k15_lattice3('#skF_9',B_616),k15_lattice3('#skF_9',k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_4474])).

tff(c_4703,plain,(
    ! [B_620] : k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),k15_lattice3('#skF_9',B_620)) = k15_lattice3('#skF_9',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4550,c_4475])).

tff(c_4766,plain,(
    ! [B_72] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),B_72) = k15_lattice3('#skF_9',k1_xboole_0)
      | ~ m1_subset_1(B_72,u1_struct_0('#skF_9'))
      | ~ l3_lattices('#skF_9')
      | ~ v4_lattice3('#skF_9')
      | ~ v10_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_4703])).

tff(c_4821,plain,(
    ! [B_72] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),B_72) = k15_lattice3('#skF_9',k1_xboole_0)
      | ~ m1_subset_1(B_72,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_96,c_4766])).

tff(c_4836,plain,(
    ! [B_624] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),B_624) = k15_lattice3('#skF_9',k1_xboole_0)
      | ~ m1_subset_1(B_624,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_4821])).

tff(c_4852,plain,(
    ! [B_42] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),'#skF_4'('#skF_9',B_42)) = k15_lattice3('#skF_9',k1_xboole_0)
      | v13_lattices('#skF_9')
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_9'))
      | ~ l1_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_52,c_4836])).

tff(c_4887,plain,(
    ! [B_42] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),'#skF_4'('#skF_9',B_42)) = k15_lattice3('#skF_9',k1_xboole_0)
      | v13_lattices('#skF_9')
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_4852])).

tff(c_4888,plain,(
    ! [B_42] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),'#skF_4'('#skF_9',B_42)) = k15_lattice3('#skF_9',k1_xboole_0)
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_117,c_4887])).

tff(c_5158,plain,(
    k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),'#skF_4'('#skF_9',k15_lattice3('#skF_9',k1_xboole_0))) != k15_lattice3('#skF_9',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5047])).

tff(c_5292,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_9',k1_xboole_0),u1_struct_0('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4888,c_5158])).

tff(c_5299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5159,c_5292])).

tff(c_5301,plain,(
    v13_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_54,plain,(
    ! [A_33] :
      ( m1_subset_1('#skF_3'(A_33),u1_struct_0(A_33))
      | ~ v13_lattices(A_33)
      | ~ l1_lattices(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_5831,plain,(
    ! [A_743,C_744] :
      ( k2_lattices(A_743,k5_lattices(A_743),C_744) = k5_lattices(A_743)
      | ~ m1_subset_1(C_744,u1_struct_0(A_743))
      | ~ m1_subset_1(k5_lattices(A_743),u1_struct_0(A_743))
      | ~ v13_lattices(A_743)
      | ~ l1_lattices(A_743)
      | v2_struct_0(A_743) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5859,plain,(
    ! [A_745] :
      ( k2_lattices(A_745,k5_lattices(A_745),'#skF_3'(A_745)) = k5_lattices(A_745)
      | ~ m1_subset_1(k5_lattices(A_745),u1_struct_0(A_745))
      | ~ v13_lattices(A_745)
      | ~ l1_lattices(A_745)
      | v2_struct_0(A_745) ) ),
    inference(resolution,[status(thm)],[c_54,c_5831])).

tff(c_5891,plain,(
    ! [A_748] :
      ( k2_lattices(A_748,k5_lattices(A_748),'#skF_3'(A_748)) = k5_lattices(A_748)
      | ~ v13_lattices(A_748)
      | ~ l1_lattices(A_748)
      | v2_struct_0(A_748) ) ),
    inference(resolution,[status(thm)],[c_36,c_5859])).

tff(c_5414,plain,(
    ! [A_685,C_686] :
      ( k2_lattices(A_685,C_686,'#skF_3'(A_685)) = '#skF_3'(A_685)
      | ~ m1_subset_1(C_686,u1_struct_0(A_685))
      | ~ v13_lattices(A_685)
      | ~ l1_lattices(A_685)
      | v2_struct_0(A_685) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_5432,plain,(
    ! [A_21] :
      ( k2_lattices(A_21,k5_lattices(A_21),'#skF_3'(A_21)) = '#skF_3'(A_21)
      | ~ v13_lattices(A_21)
      | ~ l1_lattices(A_21)
      | v2_struct_0(A_21) ) ),
    inference(resolution,[status(thm)],[c_36,c_5414])).

tff(c_5900,plain,(
    ! [A_748] :
      ( k5_lattices(A_748) = '#skF_3'(A_748)
      | ~ v13_lattices(A_748)
      | ~ l1_lattices(A_748)
      | v2_struct_0(A_748)
      | ~ v13_lattices(A_748)
      | ~ l1_lattices(A_748)
      | v2_struct_0(A_748) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5891,c_5432])).

tff(c_5925,plain,(
    ! [A_750] :
      ( k5_lattices(A_750) = '#skF_3'(A_750)
      | ~ v13_lattices(A_750)
      | ~ l1_lattices(A_750)
      | v2_struct_0(A_750) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_5900])).

tff(c_5928,plain,
    ( k5_lattices('#skF_9') = '#skF_3'('#skF_9')
    | ~ v13_lattices('#skF_9')
    | ~ l1_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_5925,c_102])).

tff(c_5931,plain,(
    k5_lattices('#skF_9') = '#skF_3'('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_5301,c_5928])).

tff(c_5300,plain,(
    k15_lattice3('#skF_9',k1_xboole_0) != k5_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_5932,plain,(
    k15_lattice3('#skF_9',k1_xboole_0) != '#skF_3'('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5931,c_5300])).

tff(c_5948,plain,
    ( m1_subset_1('#skF_3'('#skF_9'),u1_struct_0('#skF_9'))
    | ~ l1_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_5931,c_36])).

tff(c_5964,plain,
    ( m1_subset_1('#skF_3'('#skF_9'),u1_struct_0('#skF_9'))
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_5948])).

tff(c_5965,plain,(
    m1_subset_1('#skF_3'('#skF_9'),u1_struct_0('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_5964])).

tff(c_60,plain,(
    ! [A_44,C_53,B_51] :
      ( k2_lattices(A_44,C_53,B_51) = k2_lattices(A_44,B_51,C_53)
      | ~ m1_subset_1(C_53,u1_struct_0(A_44))
      | ~ m1_subset_1(B_51,u1_struct_0(A_44))
      | ~ v6_lattices(A_44)
      | ~ l1_lattices(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_5974,plain,(
    ! [B_51] :
      ( k2_lattices('#skF_9',B_51,'#skF_3'('#skF_9')) = k2_lattices('#skF_9','#skF_3'('#skF_9'),B_51)
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_9'))
      | ~ v6_lattices('#skF_9')
      | ~ l1_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_5965,c_60])).

tff(c_5993,plain,(
    ! [B_51] :
      ( k2_lattices('#skF_9',B_51,'#skF_3'('#skF_9')) = k2_lattices('#skF_9','#skF_3'('#skF_9'),B_51)
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_9'))
      | ~ v6_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_5974])).

tff(c_5994,plain,(
    ! [B_51] :
      ( k2_lattices('#skF_9',B_51,'#skF_3'('#skF_9')) = k2_lattices('#skF_9','#skF_3'('#skF_9'),B_51)
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_9'))
      | ~ v6_lattices('#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_5993])).

tff(c_6028,plain,(
    ~ v6_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_5994])).

tff(c_6031,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_20,c_6028])).

tff(c_6034,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_100,c_6031])).

tff(c_6036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_6034])).

tff(c_6038,plain,(
    v6_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_5994])).

tff(c_6502,plain,(
    ! [A_779,B_780,C_781] :
      ( r1_lattices(A_779,B_780,C_781)
      | k2_lattices(A_779,B_780,C_781) != B_780
      | ~ m1_subset_1(C_781,u1_struct_0(A_779))
      | ~ m1_subset_1(B_780,u1_struct_0(A_779))
      | ~ l3_lattices(A_779)
      | ~ v9_lattices(A_779)
      | ~ v8_lattices(A_779)
      | v2_struct_0(A_779) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_6504,plain,(
    ! [B_780] :
      ( r1_lattices('#skF_9',B_780,'#skF_3'('#skF_9'))
      | k2_lattices('#skF_9',B_780,'#skF_3'('#skF_9')) != B_780
      | ~ m1_subset_1(B_780,u1_struct_0('#skF_9'))
      | ~ l3_lattices('#skF_9')
      | ~ v9_lattices('#skF_9')
      | ~ v8_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_5965,c_6502])).

tff(c_6525,plain,(
    ! [B_780] :
      ( r1_lattices('#skF_9',B_780,'#skF_3'('#skF_9'))
      | k2_lattices('#skF_9',B_780,'#skF_3'('#skF_9')) != B_780
      | ~ m1_subset_1(B_780,u1_struct_0('#skF_9'))
      | ~ v9_lattices('#skF_9')
      | ~ v8_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_6504])).

tff(c_6526,plain,(
    ! [B_780] :
      ( r1_lattices('#skF_9',B_780,'#skF_3'('#skF_9'))
      | k2_lattices('#skF_9',B_780,'#skF_3'('#skF_9')) != B_780
      | ~ m1_subset_1(B_780,u1_struct_0('#skF_9'))
      | ~ v9_lattices('#skF_9')
      | ~ v8_lattices('#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_6525])).

tff(c_6536,plain,(
    ~ v8_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_6526])).

tff(c_6539,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_16,c_6536])).

tff(c_6542,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_100,c_6539])).

tff(c_6544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_6542])).

tff(c_6546,plain,(
    v8_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_6526])).

tff(c_6545,plain,(
    ! [B_780] :
      ( ~ v9_lattices('#skF_9')
      | r1_lattices('#skF_9',B_780,'#skF_3'('#skF_9'))
      | k2_lattices('#skF_9',B_780,'#skF_3'('#skF_9')) != B_780
      | ~ m1_subset_1(B_780,u1_struct_0('#skF_9')) ) ),
    inference(splitRight,[status(thm)],[c_6526])).

tff(c_6548,plain,(
    ~ v9_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_6545])).

tff(c_6551,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_14,c_6548])).

tff(c_6554,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_100,c_6551])).

tff(c_6556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_6554])).

tff(c_6558,plain,(
    v9_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_6545])).

tff(c_6040,plain,(
    ! [B_756] :
      ( k2_lattices('#skF_9',B_756,'#skF_3'('#skF_9')) = k2_lattices('#skF_9','#skF_3'('#skF_9'),B_756)
      | ~ m1_subset_1(B_756,u1_struct_0('#skF_9')) ) ),
    inference(splitRight,[status(thm)],[c_5994])).

tff(c_6075,plain,(
    ! [B_56] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',B_56),'#skF_3'('#skF_9')) = k2_lattices('#skF_9','#skF_3'('#skF_9'),k15_lattice3('#skF_9',B_56))
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_68,c_6040])).

tff(c_6112,plain,(
    ! [B_56] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',B_56),'#skF_3'('#skF_9')) = k2_lattices('#skF_9','#skF_3'('#skF_9'),k15_lattice3('#skF_9',B_56))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_6075])).

tff(c_6118,plain,(
    ! [B_757] : k2_lattices('#skF_9',k15_lattice3('#skF_9',B_757),'#skF_3'('#skF_9')) = k2_lattices('#skF_9','#skF_3'('#skF_9'),k15_lattice3('#skF_9',B_757)) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_6112])).

tff(c_5431,plain,(
    ! [A_55,B_56] :
      ( k2_lattices(A_55,k15_lattice3(A_55,B_56),'#skF_3'(A_55)) = '#skF_3'(A_55)
      | ~ v13_lattices(A_55)
      | ~ l1_lattices(A_55)
      | ~ l3_lattices(A_55)
      | v2_struct_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_68,c_5414])).

tff(c_6124,plain,(
    ! [B_757] :
      ( k2_lattices('#skF_9','#skF_3'('#skF_9'),k15_lattice3('#skF_9',B_757)) = '#skF_3'('#skF_9')
      | ~ v13_lattices('#skF_9')
      | ~ l1_lattices('#skF_9')
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6118,c_5431])).

tff(c_6142,plain,(
    ! [B_757] :
      ( k2_lattices('#skF_9','#skF_3'('#skF_9'),k15_lattice3('#skF_9',B_757)) = '#skF_3'('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_111,c_5301,c_6124])).

tff(c_6143,plain,(
    ! [B_757] : k2_lattices('#skF_9','#skF_3'('#skF_9'),k15_lattice3('#skF_9',B_757)) = '#skF_3'('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_6142])).

tff(c_6113,plain,(
    ! [B_56] : k2_lattices('#skF_9',k15_lattice3('#skF_9',B_56),'#skF_3'('#skF_9')) = k2_lattices('#skF_9','#skF_3'('#skF_9'),k15_lattice3('#skF_9',B_56)) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_6112])).

tff(c_6154,plain,(
    ! [B_56] : k2_lattices('#skF_9',k15_lattice3('#skF_9',B_56),'#skF_3'('#skF_9')) = '#skF_3'('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6143,c_6113])).

tff(c_5580,plain,(
    ! [A_712,B_713] :
      ( k15_lattice3(A_712,k6_domain_1(u1_struct_0(A_712),B_713)) = B_713
      | ~ m1_subset_1(B_713,u1_struct_0(A_712))
      | ~ l3_lattices(A_712)
      | ~ v4_lattice3(A_712)
      | ~ v10_lattices(A_712)
      | v2_struct_0(A_712) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_88,plain,(
    ! [A_73,B_76,C_77] :
      ( r3_lattices(A_73,k15_lattice3(A_73,B_76),k15_lattice3(A_73,C_77))
      | ~ r1_tarski(B_76,C_77)
      | ~ l3_lattices(A_73)
      | ~ v4_lattice3(A_73)
      | ~ v10_lattices(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_10603,plain,(
    ! [A_1093,B_1094,B_1095] :
      ( r3_lattices(A_1093,k15_lattice3(A_1093,B_1094),B_1095)
      | ~ r1_tarski(B_1094,k6_domain_1(u1_struct_0(A_1093),B_1095))
      | ~ l3_lattices(A_1093)
      | ~ v4_lattice3(A_1093)
      | ~ v10_lattices(A_1093)
      | v2_struct_0(A_1093)
      | ~ m1_subset_1(B_1095,u1_struct_0(A_1093))
      | ~ l3_lattices(A_1093)
      | ~ v4_lattice3(A_1093)
      | ~ v10_lattices(A_1093)
      | v2_struct_0(A_1093) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5580,c_88])).

tff(c_10668,plain,(
    ! [A_1096,B_1097] :
      ( r3_lattices(A_1096,k15_lattice3(A_1096,k1_xboole_0),B_1097)
      | ~ m1_subset_1(B_1097,u1_struct_0(A_1096))
      | ~ l3_lattices(A_1096)
      | ~ v4_lattice3(A_1096)
      | ~ v10_lattices(A_1096)
      | v2_struct_0(A_1096) ) ),
    inference(resolution,[status(thm)],[c_8,c_10603])).

tff(c_10693,plain,(
    ! [A_1103,B_1104] :
      ( r1_lattices(A_1103,k15_lattice3(A_1103,k1_xboole_0),B_1104)
      | ~ m1_subset_1(k15_lattice3(A_1103,k1_xboole_0),u1_struct_0(A_1103))
      | ~ v9_lattices(A_1103)
      | ~ v8_lattices(A_1103)
      | ~ v6_lattices(A_1103)
      | ~ m1_subset_1(B_1104,u1_struct_0(A_1103))
      | ~ l3_lattices(A_1103)
      | ~ v4_lattice3(A_1103)
      | ~ v10_lattices(A_1103)
      | v2_struct_0(A_1103) ) ),
    inference(resolution,[status(thm)],[c_10668,c_44])).

tff(c_10698,plain,(
    ! [A_1105,B_1106] :
      ( r1_lattices(A_1105,k15_lattice3(A_1105,k1_xboole_0),B_1106)
      | ~ v9_lattices(A_1105)
      | ~ v8_lattices(A_1105)
      | ~ v6_lattices(A_1105)
      | ~ m1_subset_1(B_1106,u1_struct_0(A_1105))
      | ~ v4_lattice3(A_1105)
      | ~ v10_lattices(A_1105)
      | ~ l3_lattices(A_1105)
      | v2_struct_0(A_1105) ) ),
    inference(resolution,[status(thm)],[c_68,c_10693])).

tff(c_12908,plain,(
    ! [A_1221,B_1222] :
      ( k2_lattices(A_1221,k15_lattice3(A_1221,k1_xboole_0),B_1222) = k15_lattice3(A_1221,k1_xboole_0)
      | ~ m1_subset_1(k15_lattice3(A_1221,k1_xboole_0),u1_struct_0(A_1221))
      | ~ v9_lattices(A_1221)
      | ~ v8_lattices(A_1221)
      | ~ v6_lattices(A_1221)
      | ~ m1_subset_1(B_1222,u1_struct_0(A_1221))
      | ~ v4_lattice3(A_1221)
      | ~ v10_lattices(A_1221)
      | ~ l3_lattices(A_1221)
      | v2_struct_0(A_1221) ) ),
    inference(resolution,[status(thm)],[c_10698,c_48])).

tff(c_12913,plain,(
    ! [A_1223,B_1224] :
      ( k2_lattices(A_1223,k15_lattice3(A_1223,k1_xboole_0),B_1224) = k15_lattice3(A_1223,k1_xboole_0)
      | ~ v9_lattices(A_1223)
      | ~ v8_lattices(A_1223)
      | ~ v6_lattices(A_1223)
      | ~ m1_subset_1(B_1224,u1_struct_0(A_1223))
      | ~ v4_lattice3(A_1223)
      | ~ v10_lattices(A_1223)
      | ~ l3_lattices(A_1223)
      | v2_struct_0(A_1223) ) ),
    inference(resolution,[status(thm)],[c_68,c_12908])).

tff(c_12915,plain,
    ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),'#skF_3'('#skF_9')) = k15_lattice3('#skF_9',k1_xboole_0)
    | ~ v9_lattices('#skF_9')
    | ~ v8_lattices('#skF_9')
    | ~ v6_lattices('#skF_9')
    | ~ v4_lattice3('#skF_9')
    | ~ v10_lattices('#skF_9')
    | ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_5965,c_12913])).

tff(c_12936,plain,
    ( k15_lattice3('#skF_9',k1_xboole_0) = '#skF_3'('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_100,c_98,c_6038,c_6546,c_6558,c_6154,c_12915])).

tff(c_12938,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_5932,c_12936])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:17:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.11/6.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.18/6.76  
% 15.18/6.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.18/6.76  %$ r3_lattices > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k6_domain_1 > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > a_2_5_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_5 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1 > #skF_6 > #skF_4
% 15.18/6.76  
% 15.18/6.76  %Foreground sorts:
% 15.18/6.76  
% 15.18/6.76  
% 15.18/6.76  %Background operators:
% 15.18/6.76  
% 15.18/6.76  
% 15.18/6.76  %Foreground operators:
% 15.18/6.76  tff(l3_lattices, type, l3_lattices: $i > $o).
% 15.18/6.76  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 15.18/6.76  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 15.18/6.76  tff('#skF_5', type, '#skF_5': $i > $i).
% 15.18/6.76  tff(l2_lattices, type, l2_lattices: $i > $o).
% 15.18/6.76  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 15.18/6.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.18/6.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.18/6.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.18/6.76  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 15.18/6.76  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 15.18/6.76  tff(l1_lattices, type, l1_lattices: $i > $o).
% 15.18/6.76  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 15.18/6.76  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 15.18/6.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.18/6.76  tff(v4_lattices, type, v4_lattices: $i > $o).
% 15.18/6.76  tff(v6_lattices, type, v6_lattices: $i > $o).
% 15.18/6.76  tff(v9_lattices, type, v9_lattices: $i > $o).
% 15.18/6.76  tff(a_2_5_lattice3, type, a_2_5_lattice3: ($i * $i) > $i).
% 15.18/6.76  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 15.18/6.76  tff(v5_lattices, type, v5_lattices: $i > $o).
% 15.18/6.76  tff(v10_lattices, type, v10_lattices: $i > $o).
% 15.18/6.76  tff('#skF_9', type, '#skF_9': $i).
% 15.18/6.76  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 15.18/6.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.18/6.76  tff(v13_lattices, type, v13_lattices: $i > $o).
% 15.18/6.76  tff('#skF_3', type, '#skF_3': $i > $i).
% 15.18/6.76  tff(v8_lattices, type, v8_lattices: $i > $o).
% 15.18/6.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.18/6.76  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 15.18/6.76  tff(k5_lattices, type, k5_lattices: $i > $i).
% 15.18/6.76  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 15.18/6.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.18/6.76  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.18/6.76  tff(a_2_6_lattice3, type, a_2_6_lattice3: ($i * $i) > $i).
% 15.18/6.76  tff('#skF_6', type, '#skF_6': $i > $i).
% 15.18/6.76  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 15.18/6.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.18/6.76  tff(v7_lattices, type, v7_lattices: $i > $o).
% 15.18/6.76  
% 15.27/6.79  tff(f_264, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) & (k5_lattices(A) = k15_lattice3(A, k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_lattice3)).
% 15.27/6.79  tff(f_97, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 15.27/6.79  tff(f_174, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 15.27/6.79  tff(f_152, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_lattices)).
% 15.27/6.79  tff(f_213, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((k15_lattice3(A, k6_domain_1(u1_struct_0(A), B)) = B) & (k16_lattice3(A, k6_domain_1(u1_struct_0(A), B)) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_lattice3)).
% 15.27/6.79  tff(f_65, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 15.27/6.79  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 15.27/6.79  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 15.27/6.79  tff(f_197, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_5_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r3_lattices(B, D, E)) & r2_hidden(E, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_5_lattice3)).
% 15.27/6.79  tff(f_43, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 15.27/6.79  tff(f_38, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 15.27/6.79  tff(f_243, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: ((k15_lattice3(A, B) = k15_lattice3(A, a_2_5_lattice3(A, B))) & (k16_lattice3(A, B) = k16_lattice3(A, a_2_6_lattice3(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_lattice3)).
% 15.27/6.79  tff(f_91, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 15.27/6.79  tff(f_167, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v6_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, C) = k2_lattices(A, C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_lattices)).
% 15.27/6.79  tff(f_229, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (r1_tarski(B, C) => (r3_lattices(A, k15_lattice3(A, B), k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), k16_lattice3(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_lattice3)).
% 15.27/6.79  tff(f_116, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 15.27/6.79  tff(f_135, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 15.27/6.79  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 15.27/6.79  tff(c_102, plain, (~v2_struct_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_264])).
% 15.27/6.79  tff(c_96, plain, (l3_lattices('#skF_9')), inference(cnfTransformation, [status(thm)], [f_264])).
% 15.27/6.79  tff(c_107, plain, (![A_82]: (l1_lattices(A_82) | ~l3_lattices(A_82))), inference(cnfTransformation, [status(thm)], [f_97])).
% 15.27/6.79  tff(c_111, plain, (l1_lattices('#skF_9')), inference(resolution, [status(thm)], [c_96, c_107])).
% 15.27/6.79  tff(c_68, plain, (![A_55, B_56]: (m1_subset_1(k15_lattice3(A_55, B_56), u1_struct_0(A_55)) | ~l3_lattices(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_174])).
% 15.27/6.79  tff(c_100, plain, (v10_lattices('#skF_9')), inference(cnfTransformation, [status(thm)], [f_264])).
% 15.27/6.79  tff(c_94, plain, (k15_lattice3('#skF_9', k1_xboole_0)!=k5_lattices('#skF_9') | ~l3_lattices('#skF_9') | ~v13_lattices('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_264])).
% 15.27/6.79  tff(c_104, plain, (k15_lattice3('#skF_9', k1_xboole_0)!=k5_lattices('#skF_9') | ~v13_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_96, c_94])).
% 15.27/6.79  tff(c_105, plain, (k15_lattice3('#skF_9', k1_xboole_0)!=k5_lattices('#skF_9') | ~v13_lattices('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_102, c_104])).
% 15.27/6.79  tff(c_117, plain, (~v13_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_105])).
% 15.27/6.79  tff(c_52, plain, (![A_33, B_42]: (m1_subset_1('#skF_4'(A_33, B_42), u1_struct_0(A_33)) | v13_lattices(A_33) | ~m1_subset_1(B_42, u1_struct_0(A_33)) | ~l1_lattices(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_152])).
% 15.27/6.79  tff(c_98, plain, (v4_lattice3('#skF_9')), inference(cnfTransformation, [status(thm)], [f_264])).
% 15.27/6.79  tff(c_84, plain, (![A_70, B_72]: (k15_lattice3(A_70, k6_domain_1(u1_struct_0(A_70), B_72))=B_72 | ~m1_subset_1(B_72, u1_struct_0(A_70)) | ~l3_lattices(A_70) | ~v4_lattice3(A_70) | ~v10_lattices(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_213])).
% 15.27/6.79  tff(c_20, plain, (![A_10]: (v6_lattices(A_10) | ~v10_lattices(A_10) | v2_struct_0(A_10) | ~l3_lattices(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.27/6.79  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.27/6.79  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 15.27/6.79  tff(c_394, plain, (![A_150, B_151, C_152]: (r2_hidden('#skF_8'(A_150, B_151, C_152), C_152) | ~r2_hidden(A_150, a_2_5_lattice3(B_151, C_152)) | ~l3_lattices(B_151) | ~v4_lattice3(B_151) | ~v10_lattices(B_151) | v2_struct_0(B_151))), inference(cnfTransformation, [status(thm)], [f_197])).
% 15.27/6.79  tff(c_12, plain, (![B_9, A_8]: (~r1_tarski(B_9, A_8) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.27/6.79  tff(c_447, plain, (![C_164, A_165, B_166]: (~r1_tarski(C_164, '#skF_8'(A_165, B_166, C_164)) | ~r2_hidden(A_165, a_2_5_lattice3(B_166, C_164)) | ~l3_lattices(B_166) | ~v4_lattice3(B_166) | ~v10_lattices(B_166) | v2_struct_0(B_166))), inference(resolution, [status(thm)], [c_394, c_12])).
% 15.27/6.79  tff(c_452, plain, (![A_167, B_168]: (~r2_hidden(A_167, a_2_5_lattice3(B_168, k1_xboole_0)) | ~l3_lattices(B_168) | ~v4_lattice3(B_168) | ~v10_lattices(B_168) | v2_struct_0(B_168))), inference(resolution, [status(thm)], [c_8, c_447])).
% 15.27/6.79  tff(c_468, plain, (![B_169, B_170]: (~l3_lattices(B_169) | ~v4_lattice3(B_169) | ~v10_lattices(B_169) | v2_struct_0(B_169) | r1_tarski(a_2_5_lattice3(B_169, k1_xboole_0), B_170))), inference(resolution, [status(thm)], [c_6, c_452])).
% 15.27/6.79  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.27/6.79  tff(c_502, plain, (![B_174]: (a_2_5_lattice3(B_174, k1_xboole_0)=k1_xboole_0 | ~l3_lattices(B_174) | ~v4_lattice3(B_174) | ~v10_lattices(B_174) | v2_struct_0(B_174))), inference(resolution, [status(thm)], [c_468, c_10])).
% 15.27/6.79  tff(c_505, plain, (a_2_5_lattice3('#skF_9', k1_xboole_0)=k1_xboole_0 | ~l3_lattices('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_98, c_502])).
% 15.27/6.79  tff(c_508, plain, (a_2_5_lattice3('#skF_9', k1_xboole_0)=k1_xboole_0 | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_96, c_505])).
% 15.27/6.79  tff(c_509, plain, (a_2_5_lattice3('#skF_9', k1_xboole_0)=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_102, c_508])).
% 15.27/6.79  tff(c_90, plain, (![A_78, B_80]: (k15_lattice3(A_78, a_2_5_lattice3(A_78, B_80))=k15_lattice3(A_78, B_80) | ~l3_lattices(A_78) | ~v4_lattice3(A_78) | ~v10_lattices(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_243])).
% 15.27/6.79  tff(c_36, plain, (![A_21]: (m1_subset_1(k5_lattices(A_21), u1_struct_0(A_21)) | ~l1_lattices(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_91])).
% 15.27/6.79  tff(c_575, plain, (![A_179, C_180, B_181]: (k2_lattices(A_179, C_180, B_181)=k2_lattices(A_179, B_181, C_180) | ~m1_subset_1(C_180, u1_struct_0(A_179)) | ~m1_subset_1(B_181, u1_struct_0(A_179)) | ~v6_lattices(A_179) | ~l1_lattices(A_179) | v2_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_167])).
% 15.27/6.79  tff(c_603, plain, (![A_182, B_183]: (k2_lattices(A_182, k5_lattices(A_182), B_183)=k2_lattices(A_182, B_183, k5_lattices(A_182)) | ~m1_subset_1(B_183, u1_struct_0(A_182)) | ~v6_lattices(A_182) | ~l1_lattices(A_182) | v2_struct_0(A_182))), inference(resolution, [status(thm)], [c_36, c_575])).
% 15.27/6.79  tff(c_1159, plain, (![A_260, B_261]: (k2_lattices(A_260, k15_lattice3(A_260, B_261), k5_lattices(A_260))=k2_lattices(A_260, k5_lattices(A_260), k15_lattice3(A_260, B_261)) | ~v6_lattices(A_260) | ~l1_lattices(A_260) | ~l3_lattices(A_260) | v2_struct_0(A_260))), inference(resolution, [status(thm)], [c_68, c_603])).
% 15.27/6.79  tff(c_3079, plain, (![A_520, B_521]: (k2_lattices(A_520, k5_lattices(A_520), k15_lattice3(A_520, a_2_5_lattice3(A_520, B_521)))=k2_lattices(A_520, k15_lattice3(A_520, B_521), k5_lattices(A_520)) | ~v6_lattices(A_520) | ~l1_lattices(A_520) | ~l3_lattices(A_520) | v2_struct_0(A_520) | ~l3_lattices(A_520) | ~v4_lattice3(A_520) | ~v10_lattices(A_520) | v2_struct_0(A_520))), inference(superposition, [status(thm), theory('equality')], [c_90, c_1159])).
% 15.27/6.79  tff(c_3101, plain, (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), k5_lattices('#skF_9'))=k2_lattices('#skF_9', k5_lattices('#skF_9'), k15_lattice3('#skF_9', k1_xboole_0)) | ~v6_lattices('#skF_9') | ~l1_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_509, c_3079])).
% 15.27/6.79  tff(c_3108, plain, (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), k5_lattices('#skF_9'))=k2_lattices('#skF_9', k5_lattices('#skF_9'), k15_lattice3('#skF_9', k1_xboole_0)) | ~v6_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_96, c_96, c_111, c_3101])).
% 15.27/6.79  tff(c_3109, plain, (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), k5_lattices('#skF_9'))=k2_lattices('#skF_9', k5_lattices('#skF_9'), k15_lattice3('#skF_9', k1_xboole_0)) | ~v6_lattices('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_102, c_3108])).
% 15.27/6.79  tff(c_3110, plain, (~v6_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_3109])).
% 15.27/6.79  tff(c_3117, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_20, c_3110])).
% 15.27/6.79  tff(c_3120, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_100, c_3117])).
% 15.27/6.79  tff(c_3122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_3120])).
% 15.27/6.79  tff(c_3124, plain, (v6_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_3109])).
% 15.27/6.79  tff(c_16, plain, (![A_10]: (v8_lattices(A_10) | ~v10_lattices(A_10) | v2_struct_0(A_10) | ~l3_lattices(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.27/6.79  tff(c_427, plain, (![A_158, B_159, C_160]: (r3_lattices(A_158, k15_lattice3(A_158, B_159), k15_lattice3(A_158, C_160)) | ~r1_tarski(B_159, C_160) | ~l3_lattices(A_158) | ~v4_lattice3(A_158) | ~v10_lattices(A_158) | v2_struct_0(A_158))), inference(cnfTransformation, [status(thm)], [f_229])).
% 15.27/6.79  tff(c_2933, plain, (![A_493, B_494, B_495]: (r3_lattices(A_493, k15_lattice3(A_493, B_494), B_495) | ~r1_tarski(B_494, k6_domain_1(u1_struct_0(A_493), B_495)) | ~l3_lattices(A_493) | ~v4_lattice3(A_493) | ~v10_lattices(A_493) | v2_struct_0(A_493) | ~m1_subset_1(B_495, u1_struct_0(A_493)) | ~l3_lattices(A_493) | ~v4_lattice3(A_493) | ~v10_lattices(A_493) | v2_struct_0(A_493))), inference(superposition, [status(thm), theory('equality')], [c_84, c_427])).
% 15.27/6.79  tff(c_2966, plain, (![A_496, B_497]: (r3_lattices(A_496, k15_lattice3(A_496, k1_xboole_0), B_497) | ~m1_subset_1(B_497, u1_struct_0(A_496)) | ~l3_lattices(A_496) | ~v4_lattice3(A_496) | ~v10_lattices(A_496) | v2_struct_0(A_496))), inference(resolution, [status(thm)], [c_8, c_2933])).
% 15.27/6.79  tff(c_44, plain, (![A_23, B_24, C_25]: (r1_lattices(A_23, B_24, C_25) | ~r3_lattices(A_23, B_24, C_25) | ~m1_subset_1(C_25, u1_struct_0(A_23)) | ~m1_subset_1(B_24, u1_struct_0(A_23)) | ~l3_lattices(A_23) | ~v9_lattices(A_23) | ~v8_lattices(A_23) | ~v6_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_116])).
% 15.27/6.79  tff(c_3007, plain, (![A_506, B_507]: (r1_lattices(A_506, k15_lattice3(A_506, k1_xboole_0), B_507) | ~m1_subset_1(k15_lattice3(A_506, k1_xboole_0), u1_struct_0(A_506)) | ~v9_lattices(A_506) | ~v8_lattices(A_506) | ~v6_lattices(A_506) | ~m1_subset_1(B_507, u1_struct_0(A_506)) | ~l3_lattices(A_506) | ~v4_lattice3(A_506) | ~v10_lattices(A_506) | v2_struct_0(A_506))), inference(resolution, [status(thm)], [c_2966, c_44])).
% 15.27/6.79  tff(c_3035, plain, (![A_512, B_513]: (r1_lattices(A_512, k15_lattice3(A_512, k1_xboole_0), B_513) | ~v9_lattices(A_512) | ~v8_lattices(A_512) | ~v6_lattices(A_512) | ~m1_subset_1(B_513, u1_struct_0(A_512)) | ~v4_lattice3(A_512) | ~v10_lattices(A_512) | ~l3_lattices(A_512) | v2_struct_0(A_512))), inference(resolution, [status(thm)], [c_68, c_3007])).
% 15.27/6.79  tff(c_48, plain, (![A_26, B_30, C_32]: (k2_lattices(A_26, B_30, C_32)=B_30 | ~r1_lattices(A_26, B_30, C_32) | ~m1_subset_1(C_32, u1_struct_0(A_26)) | ~m1_subset_1(B_30, u1_struct_0(A_26)) | ~l3_lattices(A_26) | ~v9_lattices(A_26) | ~v8_lattices(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.27/6.79  tff(c_3676, plain, (![A_563, B_564]: (k2_lattices(A_563, k15_lattice3(A_563, k1_xboole_0), B_564)=k15_lattice3(A_563, k1_xboole_0) | ~m1_subset_1(k15_lattice3(A_563, k1_xboole_0), u1_struct_0(A_563)) | ~v9_lattices(A_563) | ~v8_lattices(A_563) | ~v6_lattices(A_563) | ~m1_subset_1(B_564, u1_struct_0(A_563)) | ~v4_lattice3(A_563) | ~v10_lattices(A_563) | ~l3_lattices(A_563) | v2_struct_0(A_563))), inference(resolution, [status(thm)], [c_3035, c_48])).
% 15.27/6.79  tff(c_3681, plain, (![A_565, B_566]: (k2_lattices(A_565, k15_lattice3(A_565, k1_xboole_0), B_566)=k15_lattice3(A_565, k1_xboole_0) | ~v9_lattices(A_565) | ~v8_lattices(A_565) | ~v6_lattices(A_565) | ~m1_subset_1(B_566, u1_struct_0(A_565)) | ~v4_lattice3(A_565) | ~v10_lattices(A_565) | ~l3_lattices(A_565) | v2_struct_0(A_565))), inference(resolution, [status(thm)], [c_68, c_3676])).
% 15.27/6.79  tff(c_3751, plain, (![A_569]: (k2_lattices(A_569, k15_lattice3(A_569, k1_xboole_0), k5_lattices(A_569))=k15_lattice3(A_569, k1_xboole_0) | ~v9_lattices(A_569) | ~v8_lattices(A_569) | ~v6_lattices(A_569) | ~v4_lattice3(A_569) | ~v10_lattices(A_569) | ~l3_lattices(A_569) | ~l1_lattices(A_569) | v2_struct_0(A_569))), inference(resolution, [status(thm)], [c_36, c_3681])).
% 15.27/6.79  tff(c_3123, plain, (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), k5_lattices('#skF_9'))=k2_lattices('#skF_9', k5_lattices('#skF_9'), k15_lattice3('#skF_9', k1_xboole_0))), inference(splitRight, [status(thm)], [c_3109])).
% 15.27/6.79  tff(c_3757, plain, (k2_lattices('#skF_9', k5_lattices('#skF_9'), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | ~l3_lattices('#skF_9') | ~l1_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_3751, c_3123])).
% 15.27/6.79  tff(c_3780, plain, (k2_lattices('#skF_9', k5_lattices('#skF_9'), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_96, c_100, c_98, c_3124, c_3757])).
% 15.27/6.79  tff(c_3781, plain, (k2_lattices('#skF_9', k5_lattices('#skF_9'), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_102, c_3780])).
% 15.27/6.79  tff(c_3786, plain, (~v8_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_3781])).
% 15.27/6.79  tff(c_3789, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_16, c_3786])).
% 15.27/6.79  tff(c_3792, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_100, c_3789])).
% 15.27/6.79  tff(c_3794, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_3792])).
% 15.27/6.79  tff(c_3796, plain, (v8_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_3781])).
% 15.27/6.79  tff(c_14, plain, (![A_10]: (v9_lattices(A_10) | ~v10_lattices(A_10) | v2_struct_0(A_10) | ~l3_lattices(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.27/6.79  tff(c_3795, plain, (~v9_lattices('#skF_9') | k2_lattices('#skF_9', k5_lattices('#skF_9'), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0)), inference(splitRight, [status(thm)], [c_3781])).
% 15.27/6.79  tff(c_3797, plain, (~v9_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_3795])).
% 15.27/6.79  tff(c_3828, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_14, c_3797])).
% 15.27/6.79  tff(c_3831, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_100, c_3828])).
% 15.27/6.79  tff(c_3833, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_3831])).
% 15.27/6.79  tff(c_3835, plain, (v9_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_3795])).
% 15.27/6.79  tff(c_1421, plain, (![A_283, B_284, B_285]: (k2_lattices(A_283, k15_lattice3(A_283, B_284), B_285)=k2_lattices(A_283, B_285, k15_lattice3(A_283, B_284)) | ~m1_subset_1(B_285, u1_struct_0(A_283)) | ~v6_lattices(A_283) | ~l1_lattices(A_283) | ~l3_lattices(A_283) | v2_struct_0(A_283))), inference(resolution, [status(thm)], [c_68, c_575])).
% 15.27/6.79  tff(c_1470, plain, (![A_288, B_290, B_289]: (k2_lattices(A_288, k15_lattice3(A_288, B_290), k15_lattice3(A_288, B_289))=k2_lattices(A_288, k15_lattice3(A_288, B_289), k15_lattice3(A_288, B_290)) | ~v6_lattices(A_288) | ~l1_lattices(A_288) | ~l3_lattices(A_288) | v2_struct_0(A_288))), inference(resolution, [status(thm)], [c_68, c_1421])).
% 15.27/6.79  tff(c_4406, plain, (![A_615, B_616, B_617]: (k2_lattices(A_615, k15_lattice3(A_615, B_616), k15_lattice3(A_615, a_2_5_lattice3(A_615, B_617)))=k2_lattices(A_615, k15_lattice3(A_615, B_617), k15_lattice3(A_615, B_616)) | ~v6_lattices(A_615) | ~l1_lattices(A_615) | ~l3_lattices(A_615) | v2_struct_0(A_615) | ~l3_lattices(A_615) | ~v4_lattice3(A_615) | ~v10_lattices(A_615) | v2_struct_0(A_615))), inference(superposition, [status(thm), theory('equality')], [c_90, c_1470])).
% 15.27/6.79  tff(c_4461, plain, (![B_616]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), k15_lattice3('#skF_9', B_616))=k2_lattices('#skF_9', k15_lattice3('#skF_9', B_616), k15_lattice3('#skF_9', k1_xboole_0)) | ~v6_lattices('#skF_9') | ~l1_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_509, c_4406])).
% 15.27/6.79  tff(c_4474, plain, (![B_616]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), k15_lattice3('#skF_9', B_616))=k2_lattices('#skF_9', k15_lattice3('#skF_9', B_616), k15_lattice3('#skF_9', k1_xboole_0)) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_96, c_96, c_111, c_3124, c_4461])).
% 15.27/6.79  tff(c_4476, plain, (![B_618]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), k15_lattice3('#skF_9', B_618))=k2_lattices('#skF_9', k15_lattice3('#skF_9', B_618), k15_lattice3('#skF_9', k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_102, c_4474])).
% 15.27/6.79  tff(c_3707, plain, (![A_55, B_56]: (k2_lattices(A_55, k15_lattice3(A_55, k1_xboole_0), k15_lattice3(A_55, B_56))=k15_lattice3(A_55, k1_xboole_0) | ~v9_lattices(A_55) | ~v8_lattices(A_55) | ~v6_lattices(A_55) | ~v4_lattice3(A_55) | ~v10_lattices(A_55) | ~l3_lattices(A_55) | v2_struct_0(A_55))), inference(resolution, [status(thm)], [c_68, c_3681])).
% 15.27/6.79  tff(c_4488, plain, (![B_618]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_618), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_4476, c_3707])).
% 15.27/6.79  tff(c_4549, plain, (![B_618]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_618), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_100, c_98, c_3124, c_3796, c_3835, c_4488])).
% 15.27/6.79  tff(c_4601, plain, (![B_619]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_619), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_102, c_4549])).
% 15.27/6.79  tff(c_4650, plain, (![B_72]: (k2_lattices('#skF_9', B_72, k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | ~m1_subset_1(B_72, u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_4601])).
% 15.27/6.79  tff(c_4697, plain, (![B_72]: (k2_lattices('#skF_9', B_72, k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | ~m1_subset_1(B_72, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_96, c_4650])).
% 15.27/6.79  tff(c_4909, plain, (![B_625]: (k2_lattices('#skF_9', B_625, k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | ~m1_subset_1(B_625, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_102, c_4697])).
% 15.27/6.79  tff(c_4925, plain, (![B_42]: (k2_lattices('#skF_9', '#skF_4'('#skF_9', B_42), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | v13_lattices('#skF_9') | ~m1_subset_1(B_42, u1_struct_0('#skF_9')) | ~l1_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_52, c_4909])).
% 15.27/6.79  tff(c_4960, plain, (![B_42]: (k2_lattices('#skF_9', '#skF_4'('#skF_9', B_42), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | v13_lattices('#skF_9') | ~m1_subset_1(B_42, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_4925])).
% 15.27/6.79  tff(c_5023, plain, (![B_630]: (k2_lattices('#skF_9', '#skF_4'('#skF_9', B_630), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | ~m1_subset_1(B_630, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_102, c_117, c_4960])).
% 15.27/6.79  tff(c_50, plain, (![A_33, B_42]: (k2_lattices(A_33, '#skF_4'(A_33, B_42), B_42)!=B_42 | k2_lattices(A_33, B_42, '#skF_4'(A_33, B_42))!=B_42 | v13_lattices(A_33) | ~m1_subset_1(B_42, u1_struct_0(A_33)) | ~l1_lattices(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_152])).
% 15.27/6.79  tff(c_5032, plain, (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), '#skF_4'('#skF_9', k15_lattice3('#skF_9', k1_xboole_0)))!=k15_lattice3('#skF_9', k1_xboole_0) | v13_lattices('#skF_9') | ~l1_lattices('#skF_9') | v2_struct_0('#skF_9') | ~m1_subset_1(k15_lattice3('#skF_9', k1_xboole_0), u1_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_5023, c_50])).
% 15.27/6.79  tff(c_5046, plain, (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), '#skF_4'('#skF_9', k15_lattice3('#skF_9', k1_xboole_0)))!=k15_lattice3('#skF_9', k1_xboole_0) | v13_lattices('#skF_9') | v2_struct_0('#skF_9') | ~m1_subset_1(k15_lattice3('#skF_9', k1_xboole_0), u1_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_5032])).
% 15.27/6.79  tff(c_5047, plain, (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), '#skF_4'('#skF_9', k15_lattice3('#skF_9', k1_xboole_0)))!=k15_lattice3('#skF_9', k1_xboole_0) | ~m1_subset_1(k15_lattice3('#skF_9', k1_xboole_0), u1_struct_0('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_102, c_117, c_5046])).
% 15.27/6.79  tff(c_5133, plain, (~m1_subset_1(k15_lattice3('#skF_9', k1_xboole_0), u1_struct_0('#skF_9'))), inference(splitLeft, [status(thm)], [c_5047])).
% 15.27/6.79  tff(c_5152, plain, (~l3_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_68, c_5133])).
% 15.27/6.79  tff(c_5155, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_5152])).
% 15.27/6.79  tff(c_5157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_5155])).
% 15.27/6.79  tff(c_5159, plain, (m1_subset_1(k15_lattice3('#skF_9', k1_xboole_0), u1_struct_0('#skF_9'))), inference(splitRight, [status(thm)], [c_5047])).
% 15.27/6.79  tff(c_4550, plain, (![B_618]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_618), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_102, c_4549])).
% 15.27/6.79  tff(c_4475, plain, (![B_616]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), k15_lattice3('#skF_9', B_616))=k2_lattices('#skF_9', k15_lattice3('#skF_9', B_616), k15_lattice3('#skF_9', k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_102, c_4474])).
% 15.27/6.79  tff(c_4703, plain, (![B_620]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), k15_lattice3('#skF_9', B_620))=k15_lattice3('#skF_9', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_4550, c_4475])).
% 15.27/6.79  tff(c_4766, plain, (![B_72]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), B_72)=k15_lattice3('#skF_9', k1_xboole_0) | ~m1_subset_1(B_72, u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_4703])).
% 15.27/6.79  tff(c_4821, plain, (![B_72]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), B_72)=k15_lattice3('#skF_9', k1_xboole_0) | ~m1_subset_1(B_72, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_96, c_4766])).
% 15.27/6.79  tff(c_4836, plain, (![B_624]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), B_624)=k15_lattice3('#skF_9', k1_xboole_0) | ~m1_subset_1(B_624, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_102, c_4821])).
% 15.27/6.79  tff(c_4852, plain, (![B_42]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), '#skF_4'('#skF_9', B_42))=k15_lattice3('#skF_9', k1_xboole_0) | v13_lattices('#skF_9') | ~m1_subset_1(B_42, u1_struct_0('#skF_9')) | ~l1_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_52, c_4836])).
% 15.27/6.79  tff(c_4887, plain, (![B_42]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), '#skF_4'('#skF_9', B_42))=k15_lattice3('#skF_9', k1_xboole_0) | v13_lattices('#skF_9') | ~m1_subset_1(B_42, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_4852])).
% 15.27/6.79  tff(c_4888, plain, (![B_42]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), '#skF_4'('#skF_9', B_42))=k15_lattice3('#skF_9', k1_xboole_0) | ~m1_subset_1(B_42, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_102, c_117, c_4887])).
% 15.27/6.79  tff(c_5158, plain, (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), '#skF_4'('#skF_9', k15_lattice3('#skF_9', k1_xboole_0)))!=k15_lattice3('#skF_9', k1_xboole_0)), inference(splitRight, [status(thm)], [c_5047])).
% 15.27/6.79  tff(c_5292, plain, (~m1_subset_1(k15_lattice3('#skF_9', k1_xboole_0), u1_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_4888, c_5158])).
% 15.27/6.79  tff(c_5299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5159, c_5292])).
% 15.27/6.79  tff(c_5301, plain, (v13_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_105])).
% 15.27/6.79  tff(c_54, plain, (![A_33]: (m1_subset_1('#skF_3'(A_33), u1_struct_0(A_33)) | ~v13_lattices(A_33) | ~l1_lattices(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_152])).
% 15.27/6.79  tff(c_5831, plain, (![A_743, C_744]: (k2_lattices(A_743, k5_lattices(A_743), C_744)=k5_lattices(A_743) | ~m1_subset_1(C_744, u1_struct_0(A_743)) | ~m1_subset_1(k5_lattices(A_743), u1_struct_0(A_743)) | ~v13_lattices(A_743) | ~l1_lattices(A_743) | v2_struct_0(A_743))), inference(cnfTransformation, [status(thm)], [f_84])).
% 15.27/6.79  tff(c_5859, plain, (![A_745]: (k2_lattices(A_745, k5_lattices(A_745), '#skF_3'(A_745))=k5_lattices(A_745) | ~m1_subset_1(k5_lattices(A_745), u1_struct_0(A_745)) | ~v13_lattices(A_745) | ~l1_lattices(A_745) | v2_struct_0(A_745))), inference(resolution, [status(thm)], [c_54, c_5831])).
% 15.27/6.79  tff(c_5891, plain, (![A_748]: (k2_lattices(A_748, k5_lattices(A_748), '#skF_3'(A_748))=k5_lattices(A_748) | ~v13_lattices(A_748) | ~l1_lattices(A_748) | v2_struct_0(A_748))), inference(resolution, [status(thm)], [c_36, c_5859])).
% 15.27/6.79  tff(c_5414, plain, (![A_685, C_686]: (k2_lattices(A_685, C_686, '#skF_3'(A_685))='#skF_3'(A_685) | ~m1_subset_1(C_686, u1_struct_0(A_685)) | ~v13_lattices(A_685) | ~l1_lattices(A_685) | v2_struct_0(A_685))), inference(cnfTransformation, [status(thm)], [f_152])).
% 15.27/6.79  tff(c_5432, plain, (![A_21]: (k2_lattices(A_21, k5_lattices(A_21), '#skF_3'(A_21))='#skF_3'(A_21) | ~v13_lattices(A_21) | ~l1_lattices(A_21) | v2_struct_0(A_21))), inference(resolution, [status(thm)], [c_36, c_5414])).
% 15.27/6.79  tff(c_5900, plain, (![A_748]: (k5_lattices(A_748)='#skF_3'(A_748) | ~v13_lattices(A_748) | ~l1_lattices(A_748) | v2_struct_0(A_748) | ~v13_lattices(A_748) | ~l1_lattices(A_748) | v2_struct_0(A_748))), inference(superposition, [status(thm), theory('equality')], [c_5891, c_5432])).
% 15.27/6.79  tff(c_5925, plain, (![A_750]: (k5_lattices(A_750)='#skF_3'(A_750) | ~v13_lattices(A_750) | ~l1_lattices(A_750) | v2_struct_0(A_750))), inference(factorization, [status(thm), theory('equality')], [c_5900])).
% 15.27/6.79  tff(c_5928, plain, (k5_lattices('#skF_9')='#skF_3'('#skF_9') | ~v13_lattices('#skF_9') | ~l1_lattices('#skF_9')), inference(resolution, [status(thm)], [c_5925, c_102])).
% 15.27/6.79  tff(c_5931, plain, (k5_lattices('#skF_9')='#skF_3'('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_5301, c_5928])).
% 15.27/6.79  tff(c_5300, plain, (k15_lattice3('#skF_9', k1_xboole_0)!=k5_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_105])).
% 15.27/6.79  tff(c_5932, plain, (k15_lattice3('#skF_9', k1_xboole_0)!='#skF_3'('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_5931, c_5300])).
% 15.27/6.79  tff(c_5948, plain, (m1_subset_1('#skF_3'('#skF_9'), u1_struct_0('#skF_9')) | ~l1_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_5931, c_36])).
% 15.27/6.79  tff(c_5964, plain, (m1_subset_1('#skF_3'('#skF_9'), u1_struct_0('#skF_9')) | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_5948])).
% 15.27/6.79  tff(c_5965, plain, (m1_subset_1('#skF_3'('#skF_9'), u1_struct_0('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_102, c_5964])).
% 15.27/6.79  tff(c_60, plain, (![A_44, C_53, B_51]: (k2_lattices(A_44, C_53, B_51)=k2_lattices(A_44, B_51, C_53) | ~m1_subset_1(C_53, u1_struct_0(A_44)) | ~m1_subset_1(B_51, u1_struct_0(A_44)) | ~v6_lattices(A_44) | ~l1_lattices(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_167])).
% 15.27/6.79  tff(c_5974, plain, (![B_51]: (k2_lattices('#skF_9', B_51, '#skF_3'('#skF_9'))=k2_lattices('#skF_9', '#skF_3'('#skF_9'), B_51) | ~m1_subset_1(B_51, u1_struct_0('#skF_9')) | ~v6_lattices('#skF_9') | ~l1_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_5965, c_60])).
% 15.27/6.79  tff(c_5993, plain, (![B_51]: (k2_lattices('#skF_9', B_51, '#skF_3'('#skF_9'))=k2_lattices('#skF_9', '#skF_3'('#skF_9'), B_51) | ~m1_subset_1(B_51, u1_struct_0('#skF_9')) | ~v6_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_5974])).
% 15.27/6.79  tff(c_5994, plain, (![B_51]: (k2_lattices('#skF_9', B_51, '#skF_3'('#skF_9'))=k2_lattices('#skF_9', '#skF_3'('#skF_9'), B_51) | ~m1_subset_1(B_51, u1_struct_0('#skF_9')) | ~v6_lattices('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_102, c_5993])).
% 15.27/6.79  tff(c_6028, plain, (~v6_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_5994])).
% 15.27/6.79  tff(c_6031, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_20, c_6028])).
% 15.27/6.79  tff(c_6034, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_100, c_6031])).
% 15.27/6.79  tff(c_6036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_6034])).
% 15.27/6.79  tff(c_6038, plain, (v6_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_5994])).
% 15.27/6.79  tff(c_6502, plain, (![A_779, B_780, C_781]: (r1_lattices(A_779, B_780, C_781) | k2_lattices(A_779, B_780, C_781)!=B_780 | ~m1_subset_1(C_781, u1_struct_0(A_779)) | ~m1_subset_1(B_780, u1_struct_0(A_779)) | ~l3_lattices(A_779) | ~v9_lattices(A_779) | ~v8_lattices(A_779) | v2_struct_0(A_779))), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.27/6.79  tff(c_6504, plain, (![B_780]: (r1_lattices('#skF_9', B_780, '#skF_3'('#skF_9')) | k2_lattices('#skF_9', B_780, '#skF_3'('#skF_9'))!=B_780 | ~m1_subset_1(B_780, u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_5965, c_6502])).
% 15.27/6.79  tff(c_6525, plain, (![B_780]: (r1_lattices('#skF_9', B_780, '#skF_3'('#skF_9')) | k2_lattices('#skF_9', B_780, '#skF_3'('#skF_9'))!=B_780 | ~m1_subset_1(B_780, u1_struct_0('#skF_9')) | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_6504])).
% 15.27/6.79  tff(c_6526, plain, (![B_780]: (r1_lattices('#skF_9', B_780, '#skF_3'('#skF_9')) | k2_lattices('#skF_9', B_780, '#skF_3'('#skF_9'))!=B_780 | ~m1_subset_1(B_780, u1_struct_0('#skF_9')) | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_102, c_6525])).
% 15.27/6.79  tff(c_6536, plain, (~v8_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_6526])).
% 15.27/6.79  tff(c_6539, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_16, c_6536])).
% 15.27/6.79  tff(c_6542, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_100, c_6539])).
% 15.27/6.79  tff(c_6544, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_6542])).
% 15.27/6.79  tff(c_6546, plain, (v8_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_6526])).
% 15.27/6.79  tff(c_6545, plain, (![B_780]: (~v9_lattices('#skF_9') | r1_lattices('#skF_9', B_780, '#skF_3'('#skF_9')) | k2_lattices('#skF_9', B_780, '#skF_3'('#skF_9'))!=B_780 | ~m1_subset_1(B_780, u1_struct_0('#skF_9')))), inference(splitRight, [status(thm)], [c_6526])).
% 15.27/6.79  tff(c_6548, plain, (~v9_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_6545])).
% 15.27/6.79  tff(c_6551, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_14, c_6548])).
% 15.27/6.79  tff(c_6554, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_100, c_6551])).
% 15.27/6.79  tff(c_6556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_6554])).
% 15.27/6.79  tff(c_6558, plain, (v9_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_6545])).
% 15.27/6.79  tff(c_6040, plain, (![B_756]: (k2_lattices('#skF_9', B_756, '#skF_3'('#skF_9'))=k2_lattices('#skF_9', '#skF_3'('#skF_9'), B_756) | ~m1_subset_1(B_756, u1_struct_0('#skF_9')))), inference(splitRight, [status(thm)], [c_5994])).
% 15.27/6.79  tff(c_6075, plain, (![B_56]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_56), '#skF_3'('#skF_9'))=k2_lattices('#skF_9', '#skF_3'('#skF_9'), k15_lattice3('#skF_9', B_56)) | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_68, c_6040])).
% 15.27/6.79  tff(c_6112, plain, (![B_56]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_56), '#skF_3'('#skF_9'))=k2_lattices('#skF_9', '#skF_3'('#skF_9'), k15_lattice3('#skF_9', B_56)) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_6075])).
% 15.27/6.79  tff(c_6118, plain, (![B_757]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_757), '#skF_3'('#skF_9'))=k2_lattices('#skF_9', '#skF_3'('#skF_9'), k15_lattice3('#skF_9', B_757)))), inference(negUnitSimplification, [status(thm)], [c_102, c_6112])).
% 15.27/6.79  tff(c_5431, plain, (![A_55, B_56]: (k2_lattices(A_55, k15_lattice3(A_55, B_56), '#skF_3'(A_55))='#skF_3'(A_55) | ~v13_lattices(A_55) | ~l1_lattices(A_55) | ~l3_lattices(A_55) | v2_struct_0(A_55))), inference(resolution, [status(thm)], [c_68, c_5414])).
% 15.27/6.79  tff(c_6124, plain, (![B_757]: (k2_lattices('#skF_9', '#skF_3'('#skF_9'), k15_lattice3('#skF_9', B_757))='#skF_3'('#skF_9') | ~v13_lattices('#skF_9') | ~l1_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_6118, c_5431])).
% 15.27/6.79  tff(c_6142, plain, (![B_757]: (k2_lattices('#skF_9', '#skF_3'('#skF_9'), k15_lattice3('#skF_9', B_757))='#skF_3'('#skF_9') | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_111, c_5301, c_6124])).
% 15.27/6.79  tff(c_6143, plain, (![B_757]: (k2_lattices('#skF_9', '#skF_3'('#skF_9'), k15_lattice3('#skF_9', B_757))='#skF_3'('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_102, c_6142])).
% 15.27/6.79  tff(c_6113, plain, (![B_56]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_56), '#skF_3'('#skF_9'))=k2_lattices('#skF_9', '#skF_3'('#skF_9'), k15_lattice3('#skF_9', B_56)))), inference(negUnitSimplification, [status(thm)], [c_102, c_6112])).
% 15.27/6.79  tff(c_6154, plain, (![B_56]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_56), '#skF_3'('#skF_9'))='#skF_3'('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_6143, c_6113])).
% 15.27/6.79  tff(c_5580, plain, (![A_712, B_713]: (k15_lattice3(A_712, k6_domain_1(u1_struct_0(A_712), B_713))=B_713 | ~m1_subset_1(B_713, u1_struct_0(A_712)) | ~l3_lattices(A_712) | ~v4_lattice3(A_712) | ~v10_lattices(A_712) | v2_struct_0(A_712))), inference(cnfTransformation, [status(thm)], [f_213])).
% 15.27/6.79  tff(c_88, plain, (![A_73, B_76, C_77]: (r3_lattices(A_73, k15_lattice3(A_73, B_76), k15_lattice3(A_73, C_77)) | ~r1_tarski(B_76, C_77) | ~l3_lattices(A_73) | ~v4_lattice3(A_73) | ~v10_lattices(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_229])).
% 15.27/6.79  tff(c_10603, plain, (![A_1093, B_1094, B_1095]: (r3_lattices(A_1093, k15_lattice3(A_1093, B_1094), B_1095) | ~r1_tarski(B_1094, k6_domain_1(u1_struct_0(A_1093), B_1095)) | ~l3_lattices(A_1093) | ~v4_lattice3(A_1093) | ~v10_lattices(A_1093) | v2_struct_0(A_1093) | ~m1_subset_1(B_1095, u1_struct_0(A_1093)) | ~l3_lattices(A_1093) | ~v4_lattice3(A_1093) | ~v10_lattices(A_1093) | v2_struct_0(A_1093))), inference(superposition, [status(thm), theory('equality')], [c_5580, c_88])).
% 15.27/6.79  tff(c_10668, plain, (![A_1096, B_1097]: (r3_lattices(A_1096, k15_lattice3(A_1096, k1_xboole_0), B_1097) | ~m1_subset_1(B_1097, u1_struct_0(A_1096)) | ~l3_lattices(A_1096) | ~v4_lattice3(A_1096) | ~v10_lattices(A_1096) | v2_struct_0(A_1096))), inference(resolution, [status(thm)], [c_8, c_10603])).
% 15.27/6.79  tff(c_10693, plain, (![A_1103, B_1104]: (r1_lattices(A_1103, k15_lattice3(A_1103, k1_xboole_0), B_1104) | ~m1_subset_1(k15_lattice3(A_1103, k1_xboole_0), u1_struct_0(A_1103)) | ~v9_lattices(A_1103) | ~v8_lattices(A_1103) | ~v6_lattices(A_1103) | ~m1_subset_1(B_1104, u1_struct_0(A_1103)) | ~l3_lattices(A_1103) | ~v4_lattice3(A_1103) | ~v10_lattices(A_1103) | v2_struct_0(A_1103))), inference(resolution, [status(thm)], [c_10668, c_44])).
% 15.27/6.79  tff(c_10698, plain, (![A_1105, B_1106]: (r1_lattices(A_1105, k15_lattice3(A_1105, k1_xboole_0), B_1106) | ~v9_lattices(A_1105) | ~v8_lattices(A_1105) | ~v6_lattices(A_1105) | ~m1_subset_1(B_1106, u1_struct_0(A_1105)) | ~v4_lattice3(A_1105) | ~v10_lattices(A_1105) | ~l3_lattices(A_1105) | v2_struct_0(A_1105))), inference(resolution, [status(thm)], [c_68, c_10693])).
% 15.27/6.79  tff(c_12908, plain, (![A_1221, B_1222]: (k2_lattices(A_1221, k15_lattice3(A_1221, k1_xboole_0), B_1222)=k15_lattice3(A_1221, k1_xboole_0) | ~m1_subset_1(k15_lattice3(A_1221, k1_xboole_0), u1_struct_0(A_1221)) | ~v9_lattices(A_1221) | ~v8_lattices(A_1221) | ~v6_lattices(A_1221) | ~m1_subset_1(B_1222, u1_struct_0(A_1221)) | ~v4_lattice3(A_1221) | ~v10_lattices(A_1221) | ~l3_lattices(A_1221) | v2_struct_0(A_1221))), inference(resolution, [status(thm)], [c_10698, c_48])).
% 15.27/6.79  tff(c_12913, plain, (![A_1223, B_1224]: (k2_lattices(A_1223, k15_lattice3(A_1223, k1_xboole_0), B_1224)=k15_lattice3(A_1223, k1_xboole_0) | ~v9_lattices(A_1223) | ~v8_lattices(A_1223) | ~v6_lattices(A_1223) | ~m1_subset_1(B_1224, u1_struct_0(A_1223)) | ~v4_lattice3(A_1223) | ~v10_lattices(A_1223) | ~l3_lattices(A_1223) | v2_struct_0(A_1223))), inference(resolution, [status(thm)], [c_68, c_12908])).
% 15.27/6.79  tff(c_12915, plain, (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), '#skF_3'('#skF_9'))=k15_lattice3('#skF_9', k1_xboole_0) | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_5965, c_12913])).
% 15.27/6.79  tff(c_12936, plain, (k15_lattice3('#skF_9', k1_xboole_0)='#skF_3'('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_100, c_98, c_6038, c_6546, c_6558, c_6154, c_12915])).
% 15.27/6.79  tff(c_12938, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_5932, c_12936])).
% 15.27/6.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.27/6.79  
% 15.27/6.79  Inference rules
% 15.27/6.79  ----------------------
% 15.27/6.79  #Ref     : 0
% 15.27/6.79  #Sup     : 2963
% 15.27/6.79  #Fact    : 4
% 15.27/6.79  #Define  : 0
% 15.27/6.79  #Split   : 17
% 15.27/6.79  #Chain   : 0
% 15.27/6.79  #Close   : 0
% 15.27/6.79  
% 15.27/6.79  Ordering : KBO
% 15.27/6.79  
% 15.27/6.79  Simplification rules
% 15.27/6.79  ----------------------
% 15.27/6.79  #Subsume      : 1008
% 15.27/6.79  #Demod        : 2116
% 15.27/6.79  #Tautology    : 834
% 15.27/6.79  #SimpNegUnit  : 464
% 15.27/6.79  #BackRed      : 4
% 15.27/6.79  
% 15.27/6.79  #Partial instantiations: 0
% 15.27/6.79  #Strategies tried      : 1
% 15.27/6.79  
% 15.27/6.79  Timing (in seconds)
% 15.27/6.79  ----------------------
% 15.27/6.80  Preprocessing        : 0.41
% 15.27/6.80  Parsing              : 0.21
% 15.27/6.80  CNF conversion       : 0.03
% 15.27/6.80  Main loop            : 5.58
% 15.27/6.80  Inferencing          : 1.10
% 15.27/6.80  Reduction            : 0.74
% 15.27/6.80  Demodulation         : 0.51
% 15.27/6.80  BG Simplification    : 0.11
% 15.27/6.80  Subsumption          : 3.46
% 15.27/6.80  Abstraction          : 0.13
% 15.27/6.80  MUC search           : 0.00
% 15.27/6.80  Cooper               : 0.00
% 15.27/6.80  Total                : 6.06
% 15.27/6.80  Index Insertion      : 0.00
% 15.27/6.80  Index Deletion       : 0.00
% 15.27/6.80  Index Matching       : 0.00
% 15.27/6.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
