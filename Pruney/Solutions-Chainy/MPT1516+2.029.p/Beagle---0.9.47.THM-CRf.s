%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:55 EST 2020

% Result     : Theorem 17.39s
% Output     : CNFRefutation 17.82s
% Verified   : 
% Statistics : Number of formulae       :  181 (4499 expanded)
%              Number of leaves         :   49 (1583 expanded)
%              Depth                    :   25
%              Number of atoms          :  675 (21749 expanded)
%              Number of equality atoms :   79 (4301 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k16_lattice3 > k15_lattice3 > a_2_4_lattice3 > a_2_3_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_6 > #skF_7 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(a_2_4_lattice3,type,(
    a_2_4_lattice3: ( $i * $i ) > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(a_2_3_lattice3,type,(
    a_2_3_lattice3: ( $i * $i ) > $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

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

tff(f_219,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).

tff(f_79,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_54,axiom,(
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

tff(f_156,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_134,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).

tff(f_172,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( B = k15_lattice3(A,a_2_3_lattice3(A,B))
            & B = k16_lattice3(A,a_2_4_lattice3(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattice3)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_198,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B,C] :
          ( ! [D] :
              ( m1_subset_1(D,u1_struct_0(A))
             => ~ ( r2_hidden(D,B)
                  & ! [E] :
                      ( m1_subset_1(E,u1_struct_0(A))
                     => ~ ( r3_lattices(A,D,E)
                          & r2_hidden(E,C) ) ) ) )
         => r3_lattices(A,k15_lattice3(A,B),k15_lattice3(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).

tff(f_32,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_98,axiom,(
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

tff(f_117,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

tff(f_149,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => ( v6_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k2_lattices(A,B,C) = k2_lattices(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).

tff(f_73,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_72,plain,(
    l3_lattices('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_83,plain,(
    ! [A_70] :
      ( l1_lattices(A_70)
      | ~ l3_lattices(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_87,plain,(
    l1_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_83])).

tff(c_76,plain,(
    v10_lattices('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_70,plain,
    ( k15_lattice3('#skF_7',k1_xboole_0) != k5_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | ~ v13_lattices('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_80,plain,
    ( k15_lattice3('#skF_7',k1_xboole_0) != k5_lattices('#skF_7')
    | ~ v13_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70])).

tff(c_81,plain,
    ( k15_lattice3('#skF_7',k1_xboole_0) != k5_lattices('#skF_7')
    | ~ v13_lattices('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_80])).

tff(c_93,plain,(
    ~ v13_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_74,plain,(
    v4_lattice3('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_12,plain,(
    ! [A_4] :
      ( v6_lattices(A_4)
      | ~ v10_lattices(A_4)
      | v2_struct_0(A_4)
      | ~ l3_lattices(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_4] :
      ( v8_lattices(A_4)
      | ~ v10_lattices(A_4)
      | v2_struct_0(A_4)
      | ~ l3_lattices(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_4] :
      ( v9_lattices(A_4)
      | ~ v10_lattices(A_4)
      | v2_struct_0(A_4)
      | ~ l3_lattices(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_58,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(k15_lattice3(A_48,B_49),u1_struct_0(A_48))
      | ~ l3_lattices(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_42,plain,(
    ! [A_26,B_35] :
      ( m1_subset_1('#skF_3'(A_26,B_35),u1_struct_0(A_26))
      | v13_lattices(A_26)
      | ~ m1_subset_1(B_35,u1_struct_0(A_26))
      | ~ l1_lattices(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_217,plain,(
    ! [A_102,B_103] :
      ( k15_lattice3(A_102,a_2_3_lattice3(A_102,B_103)) = B_103
      | ~ m1_subset_1(B_103,u1_struct_0(A_102))
      | ~ l3_lattices(A_102)
      | ~ v4_lattice3(A_102)
      | ~ v10_lattices(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_228,plain,(
    ! [A_26,B_35] :
      ( k15_lattice3(A_26,a_2_3_lattice3(A_26,'#skF_3'(A_26,B_35))) = '#skF_3'(A_26,B_35)
      | ~ l3_lattices(A_26)
      | ~ v4_lattice3(A_26)
      | ~ v10_lattices(A_26)
      | v13_lattices(A_26)
      | ~ m1_subset_1(B_35,u1_struct_0(A_26))
      | ~ l1_lattices(A_26)
      | v2_struct_0(A_26) ) ),
    inference(resolution,[status(thm)],[c_42,c_217])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_360,plain,(
    ! [A_120,B_121,C_122] :
      ( r2_hidden('#skF_6'(A_120,B_121,C_122),B_121)
      | r3_lattices(A_120,k15_lattice3(A_120,B_121),k15_lattice3(A_120,C_122))
      | ~ l3_lattices(A_120)
      | ~ v4_lattice3(A_120)
      | ~ v10_lattices(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( ~ r1_tarski(B_3,A_2)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_395,plain,(
    ! [B_129,A_130,C_131] :
      ( ~ r1_tarski(B_129,'#skF_6'(A_130,B_129,C_131))
      | r3_lattices(A_130,k15_lattice3(A_130,B_129),k15_lattice3(A_130,C_131))
      | ~ l3_lattices(A_130)
      | ~ v4_lattice3(A_130)
      | ~ v10_lattices(A_130)
      | v2_struct_0(A_130) ) ),
    inference(resolution,[status(thm)],[c_360,c_4])).

tff(c_399,plain,(
    ! [A_130,C_131] :
      ( r3_lattices(A_130,k15_lattice3(A_130,k1_xboole_0),k15_lattice3(A_130,C_131))
      | ~ l3_lattices(A_130)
      | ~ v4_lattice3(A_130)
      | ~ v10_lattices(A_130)
      | v2_struct_0(A_130) ) ),
    inference(resolution,[status(thm)],[c_2,c_395])).

tff(c_609,plain,(
    ! [A_169,B_170,C_171] :
      ( r1_lattices(A_169,B_170,C_171)
      | ~ r3_lattices(A_169,B_170,C_171)
      | ~ m1_subset_1(C_171,u1_struct_0(A_169))
      | ~ m1_subset_1(B_170,u1_struct_0(A_169))
      | ~ l3_lattices(A_169)
      | ~ v9_lattices(A_169)
      | ~ v8_lattices(A_169)
      | ~ v6_lattices(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1109,plain,(
    ! [A_239,C_240] :
      ( r1_lattices(A_239,k15_lattice3(A_239,k1_xboole_0),k15_lattice3(A_239,C_240))
      | ~ m1_subset_1(k15_lattice3(A_239,C_240),u1_struct_0(A_239))
      | ~ m1_subset_1(k15_lattice3(A_239,k1_xboole_0),u1_struct_0(A_239))
      | ~ v9_lattices(A_239)
      | ~ v8_lattices(A_239)
      | ~ v6_lattices(A_239)
      | ~ l3_lattices(A_239)
      | ~ v4_lattice3(A_239)
      | ~ v10_lattices(A_239)
      | v2_struct_0(A_239) ) ),
    inference(resolution,[status(thm)],[c_399,c_609])).

tff(c_38,plain,(
    ! [A_19,B_23,C_25] :
      ( k2_lattices(A_19,B_23,C_25) = B_23
      | ~ r1_lattices(A_19,B_23,C_25)
      | ~ m1_subset_1(C_25,u1_struct_0(A_19))
      | ~ m1_subset_1(B_23,u1_struct_0(A_19))
      | ~ l3_lattices(A_19)
      | ~ v9_lattices(A_19)
      | ~ v8_lattices(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2836,plain,(
    ! [A_347,C_348] :
      ( k2_lattices(A_347,k15_lattice3(A_347,k1_xboole_0),k15_lattice3(A_347,C_348)) = k15_lattice3(A_347,k1_xboole_0)
      | ~ m1_subset_1(k15_lattice3(A_347,C_348),u1_struct_0(A_347))
      | ~ m1_subset_1(k15_lattice3(A_347,k1_xboole_0),u1_struct_0(A_347))
      | ~ v9_lattices(A_347)
      | ~ v8_lattices(A_347)
      | ~ v6_lattices(A_347)
      | ~ l3_lattices(A_347)
      | ~ v4_lattice3(A_347)
      | ~ v10_lattices(A_347)
      | v2_struct_0(A_347) ) ),
    inference(resolution,[status(thm)],[c_1109,c_38])).

tff(c_2856,plain,(
    ! [A_349,B_350] :
      ( k2_lattices(A_349,k15_lattice3(A_349,k1_xboole_0),k15_lattice3(A_349,B_350)) = k15_lattice3(A_349,k1_xboole_0)
      | ~ m1_subset_1(k15_lattice3(A_349,k1_xboole_0),u1_struct_0(A_349))
      | ~ v9_lattices(A_349)
      | ~ v8_lattices(A_349)
      | ~ v6_lattices(A_349)
      | ~ v4_lattice3(A_349)
      | ~ v10_lattices(A_349)
      | ~ l3_lattices(A_349)
      | v2_struct_0(A_349) ) ),
    inference(resolution,[status(thm)],[c_58,c_2836])).

tff(c_2861,plain,(
    ! [A_351,B_352] :
      ( k2_lattices(A_351,k15_lattice3(A_351,k1_xboole_0),k15_lattice3(A_351,B_352)) = k15_lattice3(A_351,k1_xboole_0)
      | ~ v9_lattices(A_351)
      | ~ v8_lattices(A_351)
      | ~ v6_lattices(A_351)
      | ~ v4_lattice3(A_351)
      | ~ v10_lattices(A_351)
      | ~ l3_lattices(A_351)
      | v2_struct_0(A_351) ) ),
    inference(resolution,[status(thm)],[c_58,c_2856])).

tff(c_2903,plain,(
    ! [A_26,B_35] :
      ( k2_lattices(A_26,k15_lattice3(A_26,k1_xboole_0),'#skF_3'(A_26,B_35)) = k15_lattice3(A_26,k1_xboole_0)
      | ~ v9_lattices(A_26)
      | ~ v8_lattices(A_26)
      | ~ v6_lattices(A_26)
      | ~ v4_lattice3(A_26)
      | ~ v10_lattices(A_26)
      | ~ l3_lattices(A_26)
      | v2_struct_0(A_26)
      | ~ l3_lattices(A_26)
      | ~ v4_lattice3(A_26)
      | ~ v10_lattices(A_26)
      | v13_lattices(A_26)
      | ~ m1_subset_1(B_35,u1_struct_0(A_26))
      | ~ l1_lattices(A_26)
      | v2_struct_0(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_2861])).

tff(c_66,plain,(
    ! [A_53,B_62,C_63] :
      ( r2_hidden('#skF_6'(A_53,B_62,C_63),B_62)
      | r3_lattices(A_53,k15_lattice3(A_53,B_62),k15_lattice3(A_53,C_63))
      | ~ l3_lattices(A_53)
      | ~ v4_lattice3(A_53)
      | ~ v10_lattices(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1968,plain,(
    ! [A_299,B_300,C_301] :
      ( r1_lattices(A_299,k15_lattice3(A_299,B_300),k15_lattice3(A_299,C_301))
      | ~ m1_subset_1(k15_lattice3(A_299,C_301),u1_struct_0(A_299))
      | ~ m1_subset_1(k15_lattice3(A_299,B_300),u1_struct_0(A_299))
      | ~ v9_lattices(A_299)
      | ~ v8_lattices(A_299)
      | ~ v6_lattices(A_299)
      | r2_hidden('#skF_6'(A_299,B_300,C_301),B_300)
      | ~ l3_lattices(A_299)
      | ~ v4_lattice3(A_299)
      | ~ v10_lattices(A_299)
      | v2_struct_0(A_299) ) ),
    inference(resolution,[status(thm)],[c_66,c_609])).

tff(c_5492,plain,(
    ! [A_470,B_471,C_472] :
      ( k2_lattices(A_470,k15_lattice3(A_470,B_471),k15_lattice3(A_470,C_472)) = k15_lattice3(A_470,B_471)
      | ~ m1_subset_1(k15_lattice3(A_470,C_472),u1_struct_0(A_470))
      | ~ m1_subset_1(k15_lattice3(A_470,B_471),u1_struct_0(A_470))
      | ~ v9_lattices(A_470)
      | ~ v8_lattices(A_470)
      | ~ v6_lattices(A_470)
      | r2_hidden('#skF_6'(A_470,B_471,C_472),B_471)
      | ~ l3_lattices(A_470)
      | ~ v4_lattice3(A_470)
      | ~ v10_lattices(A_470)
      | v2_struct_0(A_470) ) ),
    inference(resolution,[status(thm)],[c_1968,c_38])).

tff(c_6924,plain,(
    ! [A_521,B_522,B_523] :
      ( k2_lattices(A_521,k15_lattice3(A_521,B_522),k15_lattice3(A_521,B_523)) = k15_lattice3(A_521,B_522)
      | ~ m1_subset_1(k15_lattice3(A_521,B_522),u1_struct_0(A_521))
      | ~ v9_lattices(A_521)
      | ~ v8_lattices(A_521)
      | ~ v6_lattices(A_521)
      | r2_hidden('#skF_6'(A_521,B_522,B_523),B_522)
      | ~ v4_lattice3(A_521)
      | ~ v10_lattices(A_521)
      | ~ l3_lattices(A_521)
      | v2_struct_0(A_521) ) ),
    inference(resolution,[status(thm)],[c_58,c_5492])).

tff(c_6952,plain,(
    ! [A_524,B_525,B_526] :
      ( k2_lattices(A_524,k15_lattice3(A_524,B_525),k15_lattice3(A_524,B_526)) = k15_lattice3(A_524,B_525)
      | ~ v9_lattices(A_524)
      | ~ v8_lattices(A_524)
      | ~ v6_lattices(A_524)
      | r2_hidden('#skF_6'(A_524,B_525,B_526),B_525)
      | ~ v4_lattice3(A_524)
      | ~ v10_lattices(A_524)
      | ~ l3_lattices(A_524)
      | v2_struct_0(A_524) ) ),
    inference(resolution,[status(thm)],[c_58,c_6924])).

tff(c_376,plain,(
    ! [A_126,C_127,B_128] :
      ( k2_lattices(A_126,C_127,B_128) = k2_lattices(A_126,B_128,C_127)
      | ~ m1_subset_1(C_127,u1_struct_0(A_126))
      | ~ m1_subset_1(B_128,u1_struct_0(A_126))
      | ~ v6_lattices(A_126)
      | ~ l1_lattices(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_482,plain,(
    ! [A_152,B_153,B_154] :
      ( k2_lattices(A_152,k15_lattice3(A_152,B_153),B_154) = k2_lattices(A_152,B_154,k15_lattice3(A_152,B_153))
      | ~ m1_subset_1(B_154,u1_struct_0(A_152))
      | ~ v6_lattices(A_152)
      | ~ l1_lattices(A_152)
      | ~ l3_lattices(A_152)
      | v2_struct_0(A_152) ) ),
    inference(resolution,[status(thm)],[c_58,c_376])).

tff(c_500,plain,(
    ! [A_48,B_49,B_153] :
      ( k2_lattices(A_48,k15_lattice3(A_48,B_49),k15_lattice3(A_48,B_153)) = k2_lattices(A_48,k15_lattice3(A_48,B_153),k15_lattice3(A_48,B_49))
      | ~ v6_lattices(A_48)
      | ~ l1_lattices(A_48)
      | ~ l3_lattices(A_48)
      | v2_struct_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_58,c_482])).

tff(c_10012,plain,(
    ! [A_612,B_613,B_614] :
      ( k2_lattices(A_612,k15_lattice3(A_612,B_613),k15_lattice3(A_612,B_614)) = k15_lattice3(A_612,B_614)
      | ~ v6_lattices(A_612)
      | ~ l1_lattices(A_612)
      | ~ l3_lattices(A_612)
      | v2_struct_0(A_612)
      | ~ v9_lattices(A_612)
      | ~ v8_lattices(A_612)
      | ~ v6_lattices(A_612)
      | r2_hidden('#skF_6'(A_612,B_614,B_613),B_614)
      | ~ v4_lattice3(A_612)
      | ~ v10_lattices(A_612)
      | ~ l3_lattices(A_612)
      | v2_struct_0(A_612) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6952,c_500])).

tff(c_10171,plain,(
    ! [B_615,A_616,B_617] :
      ( ~ r1_tarski(B_615,'#skF_6'(A_616,B_615,B_617))
      | k2_lattices(A_616,k15_lattice3(A_616,B_617),k15_lattice3(A_616,B_615)) = k15_lattice3(A_616,B_615)
      | ~ l1_lattices(A_616)
      | ~ v9_lattices(A_616)
      | ~ v8_lattices(A_616)
      | ~ v6_lattices(A_616)
      | ~ v4_lattice3(A_616)
      | ~ v10_lattices(A_616)
      | ~ l3_lattices(A_616)
      | v2_struct_0(A_616) ) ),
    inference(resolution,[status(thm)],[c_10012,c_4])).

tff(c_10205,plain,(
    ! [A_621,B_622] :
      ( k2_lattices(A_621,k15_lattice3(A_621,B_622),k15_lattice3(A_621,k1_xboole_0)) = k15_lattice3(A_621,k1_xboole_0)
      | ~ l1_lattices(A_621)
      | ~ v9_lattices(A_621)
      | ~ v8_lattices(A_621)
      | ~ v6_lattices(A_621)
      | ~ v4_lattice3(A_621)
      | ~ v10_lattices(A_621)
      | ~ l3_lattices(A_621)
      | v2_struct_0(A_621) ) ),
    inference(resolution,[status(thm)],[c_2,c_10171])).

tff(c_21718,plain,(
    ! [A_919,B_920] :
      ( k2_lattices(A_919,'#skF_3'(A_919,B_920),k15_lattice3(A_919,k1_xboole_0)) = k15_lattice3(A_919,k1_xboole_0)
      | ~ l1_lattices(A_919)
      | ~ v9_lattices(A_919)
      | ~ v8_lattices(A_919)
      | ~ v6_lattices(A_919)
      | ~ v4_lattice3(A_919)
      | ~ v10_lattices(A_919)
      | ~ l3_lattices(A_919)
      | v2_struct_0(A_919)
      | ~ l3_lattices(A_919)
      | ~ v4_lattice3(A_919)
      | ~ v10_lattices(A_919)
      | v13_lattices(A_919)
      | ~ m1_subset_1(B_920,u1_struct_0(A_919))
      | ~ l1_lattices(A_919)
      | v2_struct_0(A_919) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_10205])).

tff(c_40,plain,(
    ! [A_26,B_35] :
      ( k2_lattices(A_26,'#skF_3'(A_26,B_35),B_35) != B_35
      | k2_lattices(A_26,B_35,'#skF_3'(A_26,B_35)) != B_35
      | v13_lattices(A_26)
      | ~ m1_subset_1(B_35,u1_struct_0(A_26))
      | ~ l1_lattices(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_21738,plain,(
    ! [A_921] :
      ( k2_lattices(A_921,k15_lattice3(A_921,k1_xboole_0),'#skF_3'(A_921,k15_lattice3(A_921,k1_xboole_0))) != k15_lattice3(A_921,k1_xboole_0)
      | ~ v9_lattices(A_921)
      | ~ v8_lattices(A_921)
      | ~ v6_lattices(A_921)
      | ~ l3_lattices(A_921)
      | ~ v4_lattice3(A_921)
      | ~ v10_lattices(A_921)
      | v13_lattices(A_921)
      | ~ m1_subset_1(k15_lattice3(A_921,k1_xboole_0),u1_struct_0(A_921))
      | ~ l1_lattices(A_921)
      | v2_struct_0(A_921) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21718,c_40])).

tff(c_21744,plain,(
    ! [A_922] :
      ( ~ v9_lattices(A_922)
      | ~ v8_lattices(A_922)
      | ~ v6_lattices(A_922)
      | ~ l3_lattices(A_922)
      | ~ v4_lattice3(A_922)
      | ~ v10_lattices(A_922)
      | v13_lattices(A_922)
      | ~ m1_subset_1(k15_lattice3(A_922,k1_xboole_0),u1_struct_0(A_922))
      | ~ l1_lattices(A_922)
      | v2_struct_0(A_922) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2903,c_21738])).

tff(c_21750,plain,(
    ! [A_923] :
      ( ~ v9_lattices(A_923)
      | ~ v8_lattices(A_923)
      | ~ v6_lattices(A_923)
      | ~ v4_lattice3(A_923)
      | ~ v10_lattices(A_923)
      | v13_lattices(A_923)
      | ~ l1_lattices(A_923)
      | ~ l3_lattices(A_923)
      | v2_struct_0(A_923) ) ),
    inference(resolution,[status(thm)],[c_58,c_21744])).

tff(c_21755,plain,(
    ! [A_924] :
      ( ~ v8_lattices(A_924)
      | ~ v6_lattices(A_924)
      | ~ v4_lattice3(A_924)
      | v13_lattices(A_924)
      | ~ l1_lattices(A_924)
      | ~ v10_lattices(A_924)
      | v2_struct_0(A_924)
      | ~ l3_lattices(A_924) ) ),
    inference(resolution,[status(thm)],[c_6,c_21750])).

tff(c_21760,plain,(
    ! [A_925] :
      ( ~ v6_lattices(A_925)
      | ~ v4_lattice3(A_925)
      | v13_lattices(A_925)
      | ~ l1_lattices(A_925)
      | ~ v10_lattices(A_925)
      | v2_struct_0(A_925)
      | ~ l3_lattices(A_925) ) ),
    inference(resolution,[status(thm)],[c_8,c_21755])).

tff(c_21765,plain,(
    ! [A_926] :
      ( ~ v4_lattice3(A_926)
      | v13_lattices(A_926)
      | ~ l1_lattices(A_926)
      | ~ v10_lattices(A_926)
      | v2_struct_0(A_926)
      | ~ l3_lattices(A_926) ) ),
    inference(resolution,[status(thm)],[c_12,c_21760])).

tff(c_21768,plain,
    ( v13_lattices('#skF_7')
    | ~ l1_lattices('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l3_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_21765])).

tff(c_21771,plain,
    ( v13_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_87,c_21768])).

tff(c_21773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_93,c_21771])).

tff(c_21775,plain,(
    v13_lattices('#skF_7') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_44,plain,(
    ! [A_26] :
      ( m1_subset_1('#skF_2'(A_26),u1_struct_0(A_26))
      | ~ v13_lattices(A_26)
      | ~ l1_lattices(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_21954,plain,(
    ! [A_964,B_965] :
      ( m1_subset_1('#skF_1'(A_964,B_965),u1_struct_0(A_964))
      | k5_lattices(A_964) = B_965
      | ~ m1_subset_1(B_965,u1_struct_0(A_964))
      | ~ v13_lattices(A_964)
      | ~ l1_lattices(A_964)
      | v2_struct_0(A_964) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_48,plain,(
    ! [A_26,C_34] :
      ( k2_lattices(A_26,'#skF_2'(A_26),C_34) = '#skF_2'(A_26)
      | ~ m1_subset_1(C_34,u1_struct_0(A_26))
      | ~ v13_lattices(A_26)
      | ~ l1_lattices(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_21965,plain,(
    ! [A_964,B_965] :
      ( k2_lattices(A_964,'#skF_2'(A_964),'#skF_1'(A_964,B_965)) = '#skF_2'(A_964)
      | k5_lattices(A_964) = B_965
      | ~ m1_subset_1(B_965,u1_struct_0(A_964))
      | ~ v13_lattices(A_964)
      | ~ l1_lattices(A_964)
      | v2_struct_0(A_964) ) ),
    inference(resolution,[status(thm)],[c_21954,c_48])).

tff(c_46,plain,(
    ! [A_26,C_34] :
      ( k2_lattices(A_26,C_34,'#skF_2'(A_26)) = '#skF_2'(A_26)
      | ~ m1_subset_1(C_34,u1_struct_0(A_26))
      | ~ v13_lattices(A_26)
      | ~ l1_lattices(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_21966,plain,(
    ! [A_964,B_965] :
      ( k2_lattices(A_964,'#skF_1'(A_964,B_965),'#skF_2'(A_964)) = '#skF_2'(A_964)
      | k5_lattices(A_964) = B_965
      | ~ m1_subset_1(B_965,u1_struct_0(A_964))
      | ~ v13_lattices(A_964)
      | ~ l1_lattices(A_964)
      | v2_struct_0(A_964) ) ),
    inference(resolution,[status(thm)],[c_21954,c_46])).

tff(c_22311,plain,(
    ! [A_1030,B_1031] :
      ( k2_lattices(A_1030,'#skF_1'(A_1030,B_1031),B_1031) != B_1031
      | k2_lattices(A_1030,B_1031,'#skF_1'(A_1030,B_1031)) != B_1031
      | k5_lattices(A_1030) = B_1031
      | ~ m1_subset_1(B_1031,u1_struct_0(A_1030))
      | ~ v13_lattices(A_1030)
      | ~ l1_lattices(A_1030)
      | v2_struct_0(A_1030) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22316,plain,(
    ! [A_1032] :
      ( k2_lattices(A_1032,'#skF_2'(A_1032),'#skF_1'(A_1032,'#skF_2'(A_1032))) != '#skF_2'(A_1032)
      | k5_lattices(A_1032) = '#skF_2'(A_1032)
      | ~ m1_subset_1('#skF_2'(A_1032),u1_struct_0(A_1032))
      | ~ v13_lattices(A_1032)
      | ~ l1_lattices(A_1032)
      | v2_struct_0(A_1032) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21966,c_22311])).

tff(c_22322,plain,(
    ! [A_1033] :
      ( k5_lattices(A_1033) = '#skF_2'(A_1033)
      | ~ m1_subset_1('#skF_2'(A_1033),u1_struct_0(A_1033))
      | ~ v13_lattices(A_1033)
      | ~ l1_lattices(A_1033)
      | v2_struct_0(A_1033) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21965,c_22316])).

tff(c_22327,plain,(
    ! [A_1034] :
      ( k5_lattices(A_1034) = '#skF_2'(A_1034)
      | ~ v13_lattices(A_1034)
      | ~ l1_lattices(A_1034)
      | v2_struct_0(A_1034) ) ),
    inference(resolution,[status(thm)],[c_44,c_22322])).

tff(c_22330,plain,
    ( k5_lattices('#skF_7') = '#skF_2'('#skF_7')
    | ~ v13_lattices('#skF_7')
    | ~ l1_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_22327,c_78])).

tff(c_22333,plain,(
    k5_lattices('#skF_7') = '#skF_2'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_21775,c_22330])).

tff(c_21774,plain,(
    k15_lattice3('#skF_7',k1_xboole_0) != k5_lattices('#skF_7') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_22334,plain,(
    k15_lattice3('#skF_7',k1_xboole_0) != '#skF_2'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22333,c_21774])).

tff(c_22052,plain,(
    ! [A_976,C_977] :
      ( k2_lattices(A_976,C_977,k5_lattices(A_976)) = k5_lattices(A_976)
      | ~ m1_subset_1(C_977,u1_struct_0(A_976))
      | ~ m1_subset_1(k5_lattices(A_976),u1_struct_0(A_976))
      | ~ v13_lattices(A_976)
      | ~ l1_lattices(A_976)
      | v2_struct_0(A_976) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22069,plain,(
    ! [A_26] :
      ( k2_lattices(A_26,'#skF_2'(A_26),k5_lattices(A_26)) = k5_lattices(A_26)
      | ~ m1_subset_1(k5_lattices(A_26),u1_struct_0(A_26))
      | ~ v13_lattices(A_26)
      | ~ l1_lattices(A_26)
      | v2_struct_0(A_26) ) ),
    inference(resolution,[status(thm)],[c_44,c_22052])).

tff(c_22349,plain,
    ( k2_lattices('#skF_7','#skF_2'('#skF_7'),k5_lattices('#skF_7')) = k5_lattices('#skF_7')
    | ~ m1_subset_1('#skF_2'('#skF_7'),u1_struct_0('#skF_7'))
    | ~ v13_lattices('#skF_7')
    | ~ l1_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_22333,c_22069])).

tff(c_22373,plain,
    ( k2_lattices('#skF_7','#skF_2'('#skF_7'),'#skF_2'('#skF_7')) = '#skF_2'('#skF_7')
    | ~ m1_subset_1('#skF_2'('#skF_7'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_21775,c_22333,c_22333,c_22349])).

tff(c_22374,plain,
    ( k2_lattices('#skF_7','#skF_2'('#skF_7'),'#skF_2'('#skF_7')) = '#skF_2'('#skF_7')
    | ~ m1_subset_1('#skF_2'('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_22373])).

tff(c_22379,plain,(
    ~ m1_subset_1('#skF_2'('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_22374])).

tff(c_22382,plain,
    ( ~ v13_lattices('#skF_7')
    | ~ l1_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_22379])).

tff(c_22385,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_21775,c_22382])).

tff(c_22387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_22385])).

tff(c_22389,plain,(
    m1_subset_1('#skF_2'('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_22374])).

tff(c_36,plain,(
    ! [A_19,B_23,C_25] :
      ( r1_lattices(A_19,B_23,C_25)
      | k2_lattices(A_19,B_23,C_25) != B_23
      | ~ m1_subset_1(C_25,u1_struct_0(A_19))
      | ~ m1_subset_1(B_23,u1_struct_0(A_19))
      | ~ l3_lattices(A_19)
      | ~ v9_lattices(A_19)
      | ~ v8_lattices(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_22393,plain,(
    ! [B_23] :
      ( r1_lattices('#skF_7',B_23,'#skF_2'('#skF_7'))
      | k2_lattices('#skF_7',B_23,'#skF_2'('#skF_7')) != B_23
      | ~ m1_subset_1(B_23,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v9_lattices('#skF_7')
      | ~ v8_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_22389,c_36])).

tff(c_22418,plain,(
    ! [B_23] :
      ( r1_lattices('#skF_7',B_23,'#skF_2'('#skF_7'))
      | k2_lattices('#skF_7',B_23,'#skF_2'('#skF_7')) != B_23
      | ~ m1_subset_1(B_23,u1_struct_0('#skF_7'))
      | ~ v9_lattices('#skF_7')
      | ~ v8_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_22393])).

tff(c_22419,plain,(
    ! [B_23] :
      ( r1_lattices('#skF_7',B_23,'#skF_2'('#skF_7'))
      | k2_lattices('#skF_7',B_23,'#skF_2'('#skF_7')) != B_23
      | ~ m1_subset_1(B_23,u1_struct_0('#skF_7'))
      | ~ v9_lattices('#skF_7')
      | ~ v8_lattices('#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_22418])).

tff(c_23088,plain,(
    ~ v8_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_22419])).

tff(c_23095,plain,
    ( ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l3_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_8,c_23088])).

tff(c_23098,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_23095])).

tff(c_23100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_23098])).

tff(c_23102,plain,(
    v8_lattices('#skF_7') ),
    inference(splitRight,[status(thm)],[c_22419])).

tff(c_23101,plain,(
    ! [B_23] :
      ( ~ v9_lattices('#skF_7')
      | r1_lattices('#skF_7',B_23,'#skF_2'('#skF_7'))
      | k2_lattices('#skF_7',B_23,'#skF_2'('#skF_7')) != B_23
      | ~ m1_subset_1(B_23,u1_struct_0('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_22419])).

tff(c_23103,plain,(
    ~ v9_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_23101])).

tff(c_23109,plain,
    ( ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l3_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_23103])).

tff(c_23112,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_23109])).

tff(c_23114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_23112])).

tff(c_23116,plain,(
    v9_lattices('#skF_7') ),
    inference(splitRight,[status(thm)],[c_23101])).

tff(c_22070,plain,(
    ! [A_48,B_49] :
      ( k2_lattices(A_48,k15_lattice3(A_48,B_49),k5_lattices(A_48)) = k5_lattices(A_48)
      | ~ m1_subset_1(k5_lattices(A_48),u1_struct_0(A_48))
      | ~ v13_lattices(A_48)
      | ~ l1_lattices(A_48)
      | ~ l3_lattices(A_48)
      | v2_struct_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_58,c_22052])).

tff(c_22339,plain,(
    ! [B_49] :
      ( k2_lattices('#skF_7',k15_lattice3('#skF_7',B_49),k5_lattices('#skF_7')) = k5_lattices('#skF_7')
      | ~ m1_subset_1('#skF_2'('#skF_7'),u1_struct_0('#skF_7'))
      | ~ v13_lattices('#skF_7')
      | ~ l1_lattices('#skF_7')
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22333,c_22070])).

tff(c_22358,plain,(
    ! [B_49] :
      ( k2_lattices('#skF_7',k15_lattice3('#skF_7',B_49),'#skF_2'('#skF_7')) = '#skF_2'('#skF_7')
      | ~ m1_subset_1('#skF_2'('#skF_7'),u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_87,c_21775,c_22333,c_22333,c_22339])).

tff(c_22359,plain,(
    ! [B_49] :
      ( k2_lattices('#skF_7',k15_lattice3('#skF_7',B_49),'#skF_2'('#skF_7')) = '#skF_2'('#skF_7')
      | ~ m1_subset_1('#skF_2'('#skF_7'),u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_22358])).

tff(c_22687,plain,(
    ! [B_1041] : k2_lattices('#skF_7',k15_lattice3('#skF_7',B_1041),'#skF_2'('#skF_7')) = '#skF_2'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22389,c_22359])).

tff(c_22014,plain,(
    ! [A_971,C_972,B_973] :
      ( k2_lattices(A_971,C_972,B_973) = k2_lattices(A_971,B_973,C_972)
      | ~ m1_subset_1(C_972,u1_struct_0(A_971))
      | ~ m1_subset_1(B_973,u1_struct_0(A_971))
      | ~ v6_lattices(A_971)
      | ~ l1_lattices(A_971)
      | v2_struct_0(A_971) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_22123,plain,(
    ! [A_998,B_999] :
      ( k2_lattices(A_998,B_999,'#skF_2'(A_998)) = k2_lattices(A_998,'#skF_2'(A_998),B_999)
      | ~ m1_subset_1(B_999,u1_struct_0(A_998))
      | ~ v6_lattices(A_998)
      | ~ v13_lattices(A_998)
      | ~ l1_lattices(A_998)
      | v2_struct_0(A_998) ) ),
    inference(resolution,[status(thm)],[c_44,c_22014])).

tff(c_22142,plain,(
    ! [A_48,B_49] :
      ( k2_lattices(A_48,k15_lattice3(A_48,B_49),'#skF_2'(A_48)) = k2_lattices(A_48,'#skF_2'(A_48),k15_lattice3(A_48,B_49))
      | ~ v6_lattices(A_48)
      | ~ v13_lattices(A_48)
      | ~ l1_lattices(A_48)
      | ~ l3_lattices(A_48)
      | v2_struct_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_58,c_22123])).

tff(c_22692,plain,(
    ! [B_1041] :
      ( k2_lattices('#skF_7','#skF_2'('#skF_7'),k15_lattice3('#skF_7',B_1041)) = '#skF_2'('#skF_7')
      | ~ v6_lattices('#skF_7')
      | ~ v13_lattices('#skF_7')
      | ~ l1_lattices('#skF_7')
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22687,c_22142])).

tff(c_22722,plain,(
    ! [B_1041] :
      ( k2_lattices('#skF_7','#skF_2'('#skF_7'),k15_lattice3('#skF_7',B_1041)) = '#skF_2'('#skF_7')
      | ~ v6_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_87,c_21775,c_22692])).

tff(c_22723,plain,(
    ! [B_1041] :
      ( k2_lattices('#skF_7','#skF_2'('#skF_7'),k15_lattice3('#skF_7',B_1041)) = '#skF_2'('#skF_7')
      | ~ v6_lattices('#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_22722])).

tff(c_22746,plain,(
    ~ v6_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_22723])).

tff(c_22749,plain,
    ( ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l3_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_22746])).

tff(c_22752,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_22749])).

tff(c_22754,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_22752])).

tff(c_22756,plain,(
    v6_lattices('#skF_7') ),
    inference(splitRight,[status(thm)],[c_22723])).

tff(c_62,plain,(
    ! [A_50,B_52] :
      ( k15_lattice3(A_50,a_2_3_lattice3(A_50,B_52)) = B_52
      | ~ m1_subset_1(B_52,u1_struct_0(A_50))
      | ~ l3_lattices(A_50)
      | ~ v4_lattice3(A_50)
      | ~ v10_lattices(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_22407,plain,
    ( k15_lattice3('#skF_7',a_2_3_lattice3('#skF_7','#skF_2'('#skF_7'))) = '#skF_2'('#skF_7')
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_22389,c_62])).

tff(c_22447,plain,
    ( k15_lattice3('#skF_7',a_2_3_lattice3('#skF_7','#skF_2'('#skF_7'))) = '#skF_2'('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_22407])).

tff(c_22448,plain,(
    k15_lattice3('#skF_7',a_2_3_lattice3('#skF_7','#skF_2'('#skF_7'))) = '#skF_2'('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_22447])).

tff(c_21976,plain,(
    ! [A_967,B_968,C_969] :
      ( r2_hidden('#skF_6'(A_967,B_968,C_969),B_968)
      | r3_lattices(A_967,k15_lattice3(A_967,B_968),k15_lattice3(A_967,C_969))
      | ~ l3_lattices(A_967)
      | ~ v4_lattice3(A_967)
      | ~ v10_lattices(A_967)
      | v2_struct_0(A_967) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_22100,plain,(
    ! [B_989,A_990,C_991] :
      ( ~ r1_tarski(B_989,'#skF_6'(A_990,B_989,C_991))
      | r3_lattices(A_990,k15_lattice3(A_990,B_989),k15_lattice3(A_990,C_991))
      | ~ l3_lattices(A_990)
      | ~ v4_lattice3(A_990)
      | ~ v10_lattices(A_990)
      | v2_struct_0(A_990) ) ),
    inference(resolution,[status(thm)],[c_21976,c_4])).

tff(c_22104,plain,(
    ! [A_990,C_991] :
      ( r3_lattices(A_990,k15_lattice3(A_990,k1_xboole_0),k15_lattice3(A_990,C_991))
      | ~ l3_lattices(A_990)
      | ~ v4_lattice3(A_990)
      | ~ v10_lattices(A_990)
      | v2_struct_0(A_990) ) ),
    inference(resolution,[status(thm)],[c_2,c_22100])).

tff(c_22505,plain,
    ( r3_lattices('#skF_7',k15_lattice3('#skF_7',k1_xboole_0),'#skF_2'('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_22448,c_22104])).

tff(c_22561,plain,
    ( r3_lattices('#skF_7',k15_lattice3('#skF_7',k1_xboole_0),'#skF_2'('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_22505])).

tff(c_22562,plain,(
    r3_lattices('#skF_7',k15_lattice3('#skF_7',k1_xboole_0),'#skF_2'('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_22561])).

tff(c_34,plain,(
    ! [A_16,B_17,C_18] :
      ( r1_lattices(A_16,B_17,C_18)
      | ~ r3_lattices(A_16,B_17,C_18)
      | ~ m1_subset_1(C_18,u1_struct_0(A_16))
      | ~ m1_subset_1(B_17,u1_struct_0(A_16))
      | ~ l3_lattices(A_16)
      | ~ v9_lattices(A_16)
      | ~ v8_lattices(A_16)
      | ~ v6_lattices(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22597,plain,
    ( r1_lattices('#skF_7',k15_lattice3('#skF_7',k1_xboole_0),'#skF_2'('#skF_7'))
    | ~ m1_subset_1('#skF_2'('#skF_7'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1(k15_lattice3('#skF_7',k1_xboole_0),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v9_lattices('#skF_7')
    | ~ v8_lattices('#skF_7')
    | ~ v6_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_22562,c_34])).

tff(c_22600,plain,
    ( r1_lattices('#skF_7',k15_lattice3('#skF_7',k1_xboole_0),'#skF_2'('#skF_7'))
    | ~ m1_subset_1(k15_lattice3('#skF_7',k1_xboole_0),u1_struct_0('#skF_7'))
    | ~ v9_lattices('#skF_7')
    | ~ v8_lattices('#skF_7')
    | ~ v6_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_22389,c_22597])).

tff(c_22601,plain,
    ( r1_lattices('#skF_7',k15_lattice3('#skF_7',k1_xboole_0),'#skF_2'('#skF_7'))
    | ~ m1_subset_1(k15_lattice3('#skF_7',k1_xboole_0),u1_struct_0('#skF_7'))
    | ~ v9_lattices('#skF_7')
    | ~ v8_lattices('#skF_7')
    | ~ v6_lattices('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_22600])).

tff(c_23127,plain,
    ( r1_lattices('#skF_7',k15_lattice3('#skF_7',k1_xboole_0),'#skF_2'('#skF_7'))
    | ~ m1_subset_1(k15_lattice3('#skF_7',k1_xboole_0),u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22756,c_23102,c_23116,c_22601])).

tff(c_23128,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_7',k1_xboole_0),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_23127])).

tff(c_23135,plain,
    ( ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_23128])).

tff(c_23138,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_23135])).

tff(c_23140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_23138])).

tff(c_23142,plain,(
    m1_subset_1(k15_lattice3('#skF_7',k1_xboole_0),u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_23127])).

tff(c_22686,plain,(
    ! [B_49] : k2_lattices('#skF_7',k15_lattice3('#skF_7',B_49),'#skF_2'('#skF_7')) = '#skF_2'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22389,c_22359])).

tff(c_23141,plain,(
    r1_lattices('#skF_7',k15_lattice3('#skF_7',k1_xboole_0),'#skF_2'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_23127])).

tff(c_23215,plain,
    ( k2_lattices('#skF_7',k15_lattice3('#skF_7',k1_xboole_0),'#skF_2'('#skF_7')) = k15_lattice3('#skF_7',k1_xboole_0)
    | ~ m1_subset_1('#skF_2'('#skF_7'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1(k15_lattice3('#skF_7',k1_xboole_0),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v9_lattices('#skF_7')
    | ~ v8_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_23141,c_38])).

tff(c_23218,plain,
    ( k15_lattice3('#skF_7',k1_xboole_0) = '#skF_2'('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23102,c_23116,c_72,c_23142,c_22389,c_22686,c_23215])).

tff(c_23220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_22334,c_23218])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.39/8.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.39/8.26  
% 17.39/8.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.39/8.26  %$ r3_lattices > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k16_lattice3 > k15_lattice3 > a_2_4_lattice3 > a_2_3_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_6 > #skF_7 > #skF_3 > #skF_1
% 17.39/8.26  
% 17.39/8.26  %Foreground sorts:
% 17.39/8.26  
% 17.39/8.26  
% 17.39/8.26  %Background operators:
% 17.39/8.26  
% 17.39/8.26  
% 17.39/8.26  %Foreground operators:
% 17.39/8.26  tff(l3_lattices, type, l3_lattices: $i > $o).
% 17.39/8.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 17.39/8.26  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 17.39/8.26  tff('#skF_5', type, '#skF_5': $i > $i).
% 17.39/8.26  tff(l2_lattices, type, l2_lattices: $i > $o).
% 17.39/8.26  tff('#skF_2', type, '#skF_2': $i > $i).
% 17.39/8.26  tff('#skF_4', type, '#skF_4': $i > $i).
% 17.39/8.26  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 17.39/8.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.39/8.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.39/8.26  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 17.39/8.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.39/8.26  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 17.39/8.26  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 17.39/8.26  tff(l1_lattices, type, l1_lattices: $i > $o).
% 17.39/8.26  tff('#skF_7', type, '#skF_7': $i).
% 17.39/8.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 17.39/8.26  tff(a_2_4_lattice3, type, a_2_4_lattice3: ($i * $i) > $i).
% 17.39/8.26  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 17.39/8.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.39/8.26  tff(v4_lattices, type, v4_lattices: $i > $o).
% 17.39/8.26  tff(v6_lattices, type, v6_lattices: $i > $o).
% 17.39/8.26  tff(v9_lattices, type, v9_lattices: $i > $o).
% 17.39/8.26  tff(a_2_3_lattice3, type, a_2_3_lattice3: ($i * $i) > $i).
% 17.39/8.26  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 17.39/8.26  tff(v5_lattices, type, v5_lattices: $i > $o).
% 17.39/8.26  tff(v10_lattices, type, v10_lattices: $i > $o).
% 17.39/8.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.39/8.26  tff(v13_lattices, type, v13_lattices: $i > $o).
% 17.39/8.26  tff(v8_lattices, type, v8_lattices: $i > $o).
% 17.39/8.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.39/8.26  tff(k5_lattices, type, k5_lattices: $i > $i).
% 17.39/8.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 17.39/8.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.39/8.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.39/8.26  tff(v7_lattices, type, v7_lattices: $i > $o).
% 17.39/8.26  
% 17.82/8.29  tff(f_219, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) & (k5_lattices(A) = k15_lattice3(A, k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattice3)).
% 17.82/8.29  tff(f_79, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 17.82/8.29  tff(f_54, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 17.82/8.29  tff(f_156, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 17.82/8.29  tff(f_134, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_lattices)).
% 17.82/8.29  tff(f_172, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k15_lattice3(A, a_2_3_lattice3(A, B))) & (B = k16_lattice3(A, a_2_4_lattice3(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_lattice3)).
% 17.82/8.29  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 17.82/8.29  tff(f_198, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: ((![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, B) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ~(r3_lattices(A, D, E) & r2_hidden(E, C))))))) => r3_lattices(A, k15_lattice3(A, B), k15_lattice3(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_lattice3)).
% 17.82/8.29  tff(f_32, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 17.82/8.29  tff(f_98, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 17.82/8.29  tff(f_117, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 17.82/8.29  tff(f_149, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v6_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, C) = k2_lattices(A, C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_lattices)).
% 17.82/8.29  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 17.82/8.29  tff(c_78, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_219])).
% 17.82/8.29  tff(c_72, plain, (l3_lattices('#skF_7')), inference(cnfTransformation, [status(thm)], [f_219])).
% 17.82/8.29  tff(c_83, plain, (![A_70]: (l1_lattices(A_70) | ~l3_lattices(A_70))), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.82/8.29  tff(c_87, plain, (l1_lattices('#skF_7')), inference(resolution, [status(thm)], [c_72, c_83])).
% 17.82/8.29  tff(c_76, plain, (v10_lattices('#skF_7')), inference(cnfTransformation, [status(thm)], [f_219])).
% 17.82/8.29  tff(c_70, plain, (k15_lattice3('#skF_7', k1_xboole_0)!=k5_lattices('#skF_7') | ~l3_lattices('#skF_7') | ~v13_lattices('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_219])).
% 17.82/8.29  tff(c_80, plain, (k15_lattice3('#skF_7', k1_xboole_0)!=k5_lattices('#skF_7') | ~v13_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70])).
% 17.82/8.29  tff(c_81, plain, (k15_lattice3('#skF_7', k1_xboole_0)!=k5_lattices('#skF_7') | ~v13_lattices('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_78, c_80])).
% 17.82/8.29  tff(c_93, plain, (~v13_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_81])).
% 17.82/8.29  tff(c_74, plain, (v4_lattice3('#skF_7')), inference(cnfTransformation, [status(thm)], [f_219])).
% 17.82/8.29  tff(c_12, plain, (![A_4]: (v6_lattices(A_4) | ~v10_lattices(A_4) | v2_struct_0(A_4) | ~l3_lattices(A_4))), inference(cnfTransformation, [status(thm)], [f_54])).
% 17.82/8.29  tff(c_8, plain, (![A_4]: (v8_lattices(A_4) | ~v10_lattices(A_4) | v2_struct_0(A_4) | ~l3_lattices(A_4))), inference(cnfTransformation, [status(thm)], [f_54])).
% 17.82/8.29  tff(c_6, plain, (![A_4]: (v9_lattices(A_4) | ~v10_lattices(A_4) | v2_struct_0(A_4) | ~l3_lattices(A_4))), inference(cnfTransformation, [status(thm)], [f_54])).
% 17.82/8.29  tff(c_58, plain, (![A_48, B_49]: (m1_subset_1(k15_lattice3(A_48, B_49), u1_struct_0(A_48)) | ~l3_lattices(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_156])).
% 17.82/8.29  tff(c_42, plain, (![A_26, B_35]: (m1_subset_1('#skF_3'(A_26, B_35), u1_struct_0(A_26)) | v13_lattices(A_26) | ~m1_subset_1(B_35, u1_struct_0(A_26)) | ~l1_lattices(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.82/8.29  tff(c_217, plain, (![A_102, B_103]: (k15_lattice3(A_102, a_2_3_lattice3(A_102, B_103))=B_103 | ~m1_subset_1(B_103, u1_struct_0(A_102)) | ~l3_lattices(A_102) | ~v4_lattice3(A_102) | ~v10_lattices(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_172])).
% 17.82/8.29  tff(c_228, plain, (![A_26, B_35]: (k15_lattice3(A_26, a_2_3_lattice3(A_26, '#skF_3'(A_26, B_35)))='#skF_3'(A_26, B_35) | ~l3_lattices(A_26) | ~v4_lattice3(A_26) | ~v10_lattices(A_26) | v13_lattices(A_26) | ~m1_subset_1(B_35, u1_struct_0(A_26)) | ~l1_lattices(A_26) | v2_struct_0(A_26))), inference(resolution, [status(thm)], [c_42, c_217])).
% 17.82/8.29  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 17.82/8.29  tff(c_360, plain, (![A_120, B_121, C_122]: (r2_hidden('#skF_6'(A_120, B_121, C_122), B_121) | r3_lattices(A_120, k15_lattice3(A_120, B_121), k15_lattice3(A_120, C_122)) | ~l3_lattices(A_120) | ~v4_lattice3(A_120) | ~v10_lattices(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_198])).
% 17.82/8.29  tff(c_4, plain, (![B_3, A_2]: (~r1_tarski(B_3, A_2) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.82/8.29  tff(c_395, plain, (![B_129, A_130, C_131]: (~r1_tarski(B_129, '#skF_6'(A_130, B_129, C_131)) | r3_lattices(A_130, k15_lattice3(A_130, B_129), k15_lattice3(A_130, C_131)) | ~l3_lattices(A_130) | ~v4_lattice3(A_130) | ~v10_lattices(A_130) | v2_struct_0(A_130))), inference(resolution, [status(thm)], [c_360, c_4])).
% 17.82/8.29  tff(c_399, plain, (![A_130, C_131]: (r3_lattices(A_130, k15_lattice3(A_130, k1_xboole_0), k15_lattice3(A_130, C_131)) | ~l3_lattices(A_130) | ~v4_lattice3(A_130) | ~v10_lattices(A_130) | v2_struct_0(A_130))), inference(resolution, [status(thm)], [c_2, c_395])).
% 17.82/8.29  tff(c_609, plain, (![A_169, B_170, C_171]: (r1_lattices(A_169, B_170, C_171) | ~r3_lattices(A_169, B_170, C_171) | ~m1_subset_1(C_171, u1_struct_0(A_169)) | ~m1_subset_1(B_170, u1_struct_0(A_169)) | ~l3_lattices(A_169) | ~v9_lattices(A_169) | ~v8_lattices(A_169) | ~v6_lattices(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_98])).
% 17.82/8.29  tff(c_1109, plain, (![A_239, C_240]: (r1_lattices(A_239, k15_lattice3(A_239, k1_xboole_0), k15_lattice3(A_239, C_240)) | ~m1_subset_1(k15_lattice3(A_239, C_240), u1_struct_0(A_239)) | ~m1_subset_1(k15_lattice3(A_239, k1_xboole_0), u1_struct_0(A_239)) | ~v9_lattices(A_239) | ~v8_lattices(A_239) | ~v6_lattices(A_239) | ~l3_lattices(A_239) | ~v4_lattice3(A_239) | ~v10_lattices(A_239) | v2_struct_0(A_239))), inference(resolution, [status(thm)], [c_399, c_609])).
% 17.82/8.29  tff(c_38, plain, (![A_19, B_23, C_25]: (k2_lattices(A_19, B_23, C_25)=B_23 | ~r1_lattices(A_19, B_23, C_25) | ~m1_subset_1(C_25, u1_struct_0(A_19)) | ~m1_subset_1(B_23, u1_struct_0(A_19)) | ~l3_lattices(A_19) | ~v9_lattices(A_19) | ~v8_lattices(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_117])).
% 17.82/8.29  tff(c_2836, plain, (![A_347, C_348]: (k2_lattices(A_347, k15_lattice3(A_347, k1_xboole_0), k15_lattice3(A_347, C_348))=k15_lattice3(A_347, k1_xboole_0) | ~m1_subset_1(k15_lattice3(A_347, C_348), u1_struct_0(A_347)) | ~m1_subset_1(k15_lattice3(A_347, k1_xboole_0), u1_struct_0(A_347)) | ~v9_lattices(A_347) | ~v8_lattices(A_347) | ~v6_lattices(A_347) | ~l3_lattices(A_347) | ~v4_lattice3(A_347) | ~v10_lattices(A_347) | v2_struct_0(A_347))), inference(resolution, [status(thm)], [c_1109, c_38])).
% 17.82/8.29  tff(c_2856, plain, (![A_349, B_350]: (k2_lattices(A_349, k15_lattice3(A_349, k1_xboole_0), k15_lattice3(A_349, B_350))=k15_lattice3(A_349, k1_xboole_0) | ~m1_subset_1(k15_lattice3(A_349, k1_xboole_0), u1_struct_0(A_349)) | ~v9_lattices(A_349) | ~v8_lattices(A_349) | ~v6_lattices(A_349) | ~v4_lattice3(A_349) | ~v10_lattices(A_349) | ~l3_lattices(A_349) | v2_struct_0(A_349))), inference(resolution, [status(thm)], [c_58, c_2836])).
% 17.82/8.29  tff(c_2861, plain, (![A_351, B_352]: (k2_lattices(A_351, k15_lattice3(A_351, k1_xboole_0), k15_lattice3(A_351, B_352))=k15_lattice3(A_351, k1_xboole_0) | ~v9_lattices(A_351) | ~v8_lattices(A_351) | ~v6_lattices(A_351) | ~v4_lattice3(A_351) | ~v10_lattices(A_351) | ~l3_lattices(A_351) | v2_struct_0(A_351))), inference(resolution, [status(thm)], [c_58, c_2856])).
% 17.82/8.29  tff(c_2903, plain, (![A_26, B_35]: (k2_lattices(A_26, k15_lattice3(A_26, k1_xboole_0), '#skF_3'(A_26, B_35))=k15_lattice3(A_26, k1_xboole_0) | ~v9_lattices(A_26) | ~v8_lattices(A_26) | ~v6_lattices(A_26) | ~v4_lattice3(A_26) | ~v10_lattices(A_26) | ~l3_lattices(A_26) | v2_struct_0(A_26) | ~l3_lattices(A_26) | ~v4_lattice3(A_26) | ~v10_lattices(A_26) | v13_lattices(A_26) | ~m1_subset_1(B_35, u1_struct_0(A_26)) | ~l1_lattices(A_26) | v2_struct_0(A_26))), inference(superposition, [status(thm), theory('equality')], [c_228, c_2861])).
% 17.82/8.29  tff(c_66, plain, (![A_53, B_62, C_63]: (r2_hidden('#skF_6'(A_53, B_62, C_63), B_62) | r3_lattices(A_53, k15_lattice3(A_53, B_62), k15_lattice3(A_53, C_63)) | ~l3_lattices(A_53) | ~v4_lattice3(A_53) | ~v10_lattices(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_198])).
% 17.82/8.29  tff(c_1968, plain, (![A_299, B_300, C_301]: (r1_lattices(A_299, k15_lattice3(A_299, B_300), k15_lattice3(A_299, C_301)) | ~m1_subset_1(k15_lattice3(A_299, C_301), u1_struct_0(A_299)) | ~m1_subset_1(k15_lattice3(A_299, B_300), u1_struct_0(A_299)) | ~v9_lattices(A_299) | ~v8_lattices(A_299) | ~v6_lattices(A_299) | r2_hidden('#skF_6'(A_299, B_300, C_301), B_300) | ~l3_lattices(A_299) | ~v4_lattice3(A_299) | ~v10_lattices(A_299) | v2_struct_0(A_299))), inference(resolution, [status(thm)], [c_66, c_609])).
% 17.82/8.29  tff(c_5492, plain, (![A_470, B_471, C_472]: (k2_lattices(A_470, k15_lattice3(A_470, B_471), k15_lattice3(A_470, C_472))=k15_lattice3(A_470, B_471) | ~m1_subset_1(k15_lattice3(A_470, C_472), u1_struct_0(A_470)) | ~m1_subset_1(k15_lattice3(A_470, B_471), u1_struct_0(A_470)) | ~v9_lattices(A_470) | ~v8_lattices(A_470) | ~v6_lattices(A_470) | r2_hidden('#skF_6'(A_470, B_471, C_472), B_471) | ~l3_lattices(A_470) | ~v4_lattice3(A_470) | ~v10_lattices(A_470) | v2_struct_0(A_470))), inference(resolution, [status(thm)], [c_1968, c_38])).
% 17.82/8.29  tff(c_6924, plain, (![A_521, B_522, B_523]: (k2_lattices(A_521, k15_lattice3(A_521, B_522), k15_lattice3(A_521, B_523))=k15_lattice3(A_521, B_522) | ~m1_subset_1(k15_lattice3(A_521, B_522), u1_struct_0(A_521)) | ~v9_lattices(A_521) | ~v8_lattices(A_521) | ~v6_lattices(A_521) | r2_hidden('#skF_6'(A_521, B_522, B_523), B_522) | ~v4_lattice3(A_521) | ~v10_lattices(A_521) | ~l3_lattices(A_521) | v2_struct_0(A_521))), inference(resolution, [status(thm)], [c_58, c_5492])).
% 17.82/8.29  tff(c_6952, plain, (![A_524, B_525, B_526]: (k2_lattices(A_524, k15_lattice3(A_524, B_525), k15_lattice3(A_524, B_526))=k15_lattice3(A_524, B_525) | ~v9_lattices(A_524) | ~v8_lattices(A_524) | ~v6_lattices(A_524) | r2_hidden('#skF_6'(A_524, B_525, B_526), B_525) | ~v4_lattice3(A_524) | ~v10_lattices(A_524) | ~l3_lattices(A_524) | v2_struct_0(A_524))), inference(resolution, [status(thm)], [c_58, c_6924])).
% 17.82/8.29  tff(c_376, plain, (![A_126, C_127, B_128]: (k2_lattices(A_126, C_127, B_128)=k2_lattices(A_126, B_128, C_127) | ~m1_subset_1(C_127, u1_struct_0(A_126)) | ~m1_subset_1(B_128, u1_struct_0(A_126)) | ~v6_lattices(A_126) | ~l1_lattices(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_149])).
% 17.82/8.29  tff(c_482, plain, (![A_152, B_153, B_154]: (k2_lattices(A_152, k15_lattice3(A_152, B_153), B_154)=k2_lattices(A_152, B_154, k15_lattice3(A_152, B_153)) | ~m1_subset_1(B_154, u1_struct_0(A_152)) | ~v6_lattices(A_152) | ~l1_lattices(A_152) | ~l3_lattices(A_152) | v2_struct_0(A_152))), inference(resolution, [status(thm)], [c_58, c_376])).
% 17.82/8.29  tff(c_500, plain, (![A_48, B_49, B_153]: (k2_lattices(A_48, k15_lattice3(A_48, B_49), k15_lattice3(A_48, B_153))=k2_lattices(A_48, k15_lattice3(A_48, B_153), k15_lattice3(A_48, B_49)) | ~v6_lattices(A_48) | ~l1_lattices(A_48) | ~l3_lattices(A_48) | v2_struct_0(A_48))), inference(resolution, [status(thm)], [c_58, c_482])).
% 17.82/8.29  tff(c_10012, plain, (![A_612, B_613, B_614]: (k2_lattices(A_612, k15_lattice3(A_612, B_613), k15_lattice3(A_612, B_614))=k15_lattice3(A_612, B_614) | ~v6_lattices(A_612) | ~l1_lattices(A_612) | ~l3_lattices(A_612) | v2_struct_0(A_612) | ~v9_lattices(A_612) | ~v8_lattices(A_612) | ~v6_lattices(A_612) | r2_hidden('#skF_6'(A_612, B_614, B_613), B_614) | ~v4_lattice3(A_612) | ~v10_lattices(A_612) | ~l3_lattices(A_612) | v2_struct_0(A_612))), inference(superposition, [status(thm), theory('equality')], [c_6952, c_500])).
% 17.82/8.29  tff(c_10171, plain, (![B_615, A_616, B_617]: (~r1_tarski(B_615, '#skF_6'(A_616, B_615, B_617)) | k2_lattices(A_616, k15_lattice3(A_616, B_617), k15_lattice3(A_616, B_615))=k15_lattice3(A_616, B_615) | ~l1_lattices(A_616) | ~v9_lattices(A_616) | ~v8_lattices(A_616) | ~v6_lattices(A_616) | ~v4_lattice3(A_616) | ~v10_lattices(A_616) | ~l3_lattices(A_616) | v2_struct_0(A_616))), inference(resolution, [status(thm)], [c_10012, c_4])).
% 17.82/8.29  tff(c_10205, plain, (![A_621, B_622]: (k2_lattices(A_621, k15_lattice3(A_621, B_622), k15_lattice3(A_621, k1_xboole_0))=k15_lattice3(A_621, k1_xboole_0) | ~l1_lattices(A_621) | ~v9_lattices(A_621) | ~v8_lattices(A_621) | ~v6_lattices(A_621) | ~v4_lattice3(A_621) | ~v10_lattices(A_621) | ~l3_lattices(A_621) | v2_struct_0(A_621))), inference(resolution, [status(thm)], [c_2, c_10171])).
% 17.82/8.29  tff(c_21718, plain, (![A_919, B_920]: (k2_lattices(A_919, '#skF_3'(A_919, B_920), k15_lattice3(A_919, k1_xboole_0))=k15_lattice3(A_919, k1_xboole_0) | ~l1_lattices(A_919) | ~v9_lattices(A_919) | ~v8_lattices(A_919) | ~v6_lattices(A_919) | ~v4_lattice3(A_919) | ~v10_lattices(A_919) | ~l3_lattices(A_919) | v2_struct_0(A_919) | ~l3_lattices(A_919) | ~v4_lattice3(A_919) | ~v10_lattices(A_919) | v13_lattices(A_919) | ~m1_subset_1(B_920, u1_struct_0(A_919)) | ~l1_lattices(A_919) | v2_struct_0(A_919))), inference(superposition, [status(thm), theory('equality')], [c_228, c_10205])).
% 17.82/8.29  tff(c_40, plain, (![A_26, B_35]: (k2_lattices(A_26, '#skF_3'(A_26, B_35), B_35)!=B_35 | k2_lattices(A_26, B_35, '#skF_3'(A_26, B_35))!=B_35 | v13_lattices(A_26) | ~m1_subset_1(B_35, u1_struct_0(A_26)) | ~l1_lattices(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.82/8.29  tff(c_21738, plain, (![A_921]: (k2_lattices(A_921, k15_lattice3(A_921, k1_xboole_0), '#skF_3'(A_921, k15_lattice3(A_921, k1_xboole_0)))!=k15_lattice3(A_921, k1_xboole_0) | ~v9_lattices(A_921) | ~v8_lattices(A_921) | ~v6_lattices(A_921) | ~l3_lattices(A_921) | ~v4_lattice3(A_921) | ~v10_lattices(A_921) | v13_lattices(A_921) | ~m1_subset_1(k15_lattice3(A_921, k1_xboole_0), u1_struct_0(A_921)) | ~l1_lattices(A_921) | v2_struct_0(A_921))), inference(superposition, [status(thm), theory('equality')], [c_21718, c_40])).
% 17.82/8.29  tff(c_21744, plain, (![A_922]: (~v9_lattices(A_922) | ~v8_lattices(A_922) | ~v6_lattices(A_922) | ~l3_lattices(A_922) | ~v4_lattice3(A_922) | ~v10_lattices(A_922) | v13_lattices(A_922) | ~m1_subset_1(k15_lattice3(A_922, k1_xboole_0), u1_struct_0(A_922)) | ~l1_lattices(A_922) | v2_struct_0(A_922))), inference(superposition, [status(thm), theory('equality')], [c_2903, c_21738])).
% 17.82/8.29  tff(c_21750, plain, (![A_923]: (~v9_lattices(A_923) | ~v8_lattices(A_923) | ~v6_lattices(A_923) | ~v4_lattice3(A_923) | ~v10_lattices(A_923) | v13_lattices(A_923) | ~l1_lattices(A_923) | ~l3_lattices(A_923) | v2_struct_0(A_923))), inference(resolution, [status(thm)], [c_58, c_21744])).
% 17.82/8.29  tff(c_21755, plain, (![A_924]: (~v8_lattices(A_924) | ~v6_lattices(A_924) | ~v4_lattice3(A_924) | v13_lattices(A_924) | ~l1_lattices(A_924) | ~v10_lattices(A_924) | v2_struct_0(A_924) | ~l3_lattices(A_924))), inference(resolution, [status(thm)], [c_6, c_21750])).
% 17.82/8.29  tff(c_21760, plain, (![A_925]: (~v6_lattices(A_925) | ~v4_lattice3(A_925) | v13_lattices(A_925) | ~l1_lattices(A_925) | ~v10_lattices(A_925) | v2_struct_0(A_925) | ~l3_lattices(A_925))), inference(resolution, [status(thm)], [c_8, c_21755])).
% 17.82/8.29  tff(c_21765, plain, (![A_926]: (~v4_lattice3(A_926) | v13_lattices(A_926) | ~l1_lattices(A_926) | ~v10_lattices(A_926) | v2_struct_0(A_926) | ~l3_lattices(A_926))), inference(resolution, [status(thm)], [c_12, c_21760])).
% 17.82/8.29  tff(c_21768, plain, (v13_lattices('#skF_7') | ~l1_lattices('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7')), inference(resolution, [status(thm)], [c_74, c_21765])).
% 17.82/8.29  tff(c_21771, plain, (v13_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_87, c_21768])).
% 17.82/8.29  tff(c_21773, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_93, c_21771])).
% 17.82/8.29  tff(c_21775, plain, (v13_lattices('#skF_7')), inference(splitRight, [status(thm)], [c_81])).
% 17.82/8.29  tff(c_44, plain, (![A_26]: (m1_subset_1('#skF_2'(A_26), u1_struct_0(A_26)) | ~v13_lattices(A_26) | ~l1_lattices(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.82/8.29  tff(c_21954, plain, (![A_964, B_965]: (m1_subset_1('#skF_1'(A_964, B_965), u1_struct_0(A_964)) | k5_lattices(A_964)=B_965 | ~m1_subset_1(B_965, u1_struct_0(A_964)) | ~v13_lattices(A_964) | ~l1_lattices(A_964) | v2_struct_0(A_964))), inference(cnfTransformation, [status(thm)], [f_73])).
% 17.82/8.29  tff(c_48, plain, (![A_26, C_34]: (k2_lattices(A_26, '#skF_2'(A_26), C_34)='#skF_2'(A_26) | ~m1_subset_1(C_34, u1_struct_0(A_26)) | ~v13_lattices(A_26) | ~l1_lattices(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.82/8.29  tff(c_21965, plain, (![A_964, B_965]: (k2_lattices(A_964, '#skF_2'(A_964), '#skF_1'(A_964, B_965))='#skF_2'(A_964) | k5_lattices(A_964)=B_965 | ~m1_subset_1(B_965, u1_struct_0(A_964)) | ~v13_lattices(A_964) | ~l1_lattices(A_964) | v2_struct_0(A_964))), inference(resolution, [status(thm)], [c_21954, c_48])).
% 17.82/8.29  tff(c_46, plain, (![A_26, C_34]: (k2_lattices(A_26, C_34, '#skF_2'(A_26))='#skF_2'(A_26) | ~m1_subset_1(C_34, u1_struct_0(A_26)) | ~v13_lattices(A_26) | ~l1_lattices(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_134])).
% 17.82/8.29  tff(c_21966, plain, (![A_964, B_965]: (k2_lattices(A_964, '#skF_1'(A_964, B_965), '#skF_2'(A_964))='#skF_2'(A_964) | k5_lattices(A_964)=B_965 | ~m1_subset_1(B_965, u1_struct_0(A_964)) | ~v13_lattices(A_964) | ~l1_lattices(A_964) | v2_struct_0(A_964))), inference(resolution, [status(thm)], [c_21954, c_46])).
% 17.82/8.29  tff(c_22311, plain, (![A_1030, B_1031]: (k2_lattices(A_1030, '#skF_1'(A_1030, B_1031), B_1031)!=B_1031 | k2_lattices(A_1030, B_1031, '#skF_1'(A_1030, B_1031))!=B_1031 | k5_lattices(A_1030)=B_1031 | ~m1_subset_1(B_1031, u1_struct_0(A_1030)) | ~v13_lattices(A_1030) | ~l1_lattices(A_1030) | v2_struct_0(A_1030))), inference(cnfTransformation, [status(thm)], [f_73])).
% 17.82/8.29  tff(c_22316, plain, (![A_1032]: (k2_lattices(A_1032, '#skF_2'(A_1032), '#skF_1'(A_1032, '#skF_2'(A_1032)))!='#skF_2'(A_1032) | k5_lattices(A_1032)='#skF_2'(A_1032) | ~m1_subset_1('#skF_2'(A_1032), u1_struct_0(A_1032)) | ~v13_lattices(A_1032) | ~l1_lattices(A_1032) | v2_struct_0(A_1032))), inference(superposition, [status(thm), theory('equality')], [c_21966, c_22311])).
% 17.82/8.29  tff(c_22322, plain, (![A_1033]: (k5_lattices(A_1033)='#skF_2'(A_1033) | ~m1_subset_1('#skF_2'(A_1033), u1_struct_0(A_1033)) | ~v13_lattices(A_1033) | ~l1_lattices(A_1033) | v2_struct_0(A_1033))), inference(superposition, [status(thm), theory('equality')], [c_21965, c_22316])).
% 17.82/8.29  tff(c_22327, plain, (![A_1034]: (k5_lattices(A_1034)='#skF_2'(A_1034) | ~v13_lattices(A_1034) | ~l1_lattices(A_1034) | v2_struct_0(A_1034))), inference(resolution, [status(thm)], [c_44, c_22322])).
% 17.82/8.29  tff(c_22330, plain, (k5_lattices('#skF_7')='#skF_2'('#skF_7') | ~v13_lattices('#skF_7') | ~l1_lattices('#skF_7')), inference(resolution, [status(thm)], [c_22327, c_78])).
% 17.82/8.29  tff(c_22333, plain, (k5_lattices('#skF_7')='#skF_2'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_21775, c_22330])).
% 17.82/8.29  tff(c_21774, plain, (k15_lattice3('#skF_7', k1_xboole_0)!=k5_lattices('#skF_7')), inference(splitRight, [status(thm)], [c_81])).
% 17.82/8.29  tff(c_22334, plain, (k15_lattice3('#skF_7', k1_xboole_0)!='#skF_2'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_22333, c_21774])).
% 17.82/8.29  tff(c_22052, plain, (![A_976, C_977]: (k2_lattices(A_976, C_977, k5_lattices(A_976))=k5_lattices(A_976) | ~m1_subset_1(C_977, u1_struct_0(A_976)) | ~m1_subset_1(k5_lattices(A_976), u1_struct_0(A_976)) | ~v13_lattices(A_976) | ~l1_lattices(A_976) | v2_struct_0(A_976))), inference(cnfTransformation, [status(thm)], [f_73])).
% 17.82/8.29  tff(c_22069, plain, (![A_26]: (k2_lattices(A_26, '#skF_2'(A_26), k5_lattices(A_26))=k5_lattices(A_26) | ~m1_subset_1(k5_lattices(A_26), u1_struct_0(A_26)) | ~v13_lattices(A_26) | ~l1_lattices(A_26) | v2_struct_0(A_26))), inference(resolution, [status(thm)], [c_44, c_22052])).
% 17.82/8.29  tff(c_22349, plain, (k2_lattices('#skF_7', '#skF_2'('#skF_7'), k5_lattices('#skF_7'))=k5_lattices('#skF_7') | ~m1_subset_1('#skF_2'('#skF_7'), u1_struct_0('#skF_7')) | ~v13_lattices('#skF_7') | ~l1_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_22333, c_22069])).
% 17.82/8.29  tff(c_22373, plain, (k2_lattices('#skF_7', '#skF_2'('#skF_7'), '#skF_2'('#skF_7'))='#skF_2'('#skF_7') | ~m1_subset_1('#skF_2'('#skF_7'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_21775, c_22333, c_22333, c_22349])).
% 17.82/8.29  tff(c_22374, plain, (k2_lattices('#skF_7', '#skF_2'('#skF_7'), '#skF_2'('#skF_7'))='#skF_2'('#skF_7') | ~m1_subset_1('#skF_2'('#skF_7'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_78, c_22373])).
% 17.82/8.29  tff(c_22379, plain, (~m1_subset_1('#skF_2'('#skF_7'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_22374])).
% 17.82/8.29  tff(c_22382, plain, (~v13_lattices('#skF_7') | ~l1_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_44, c_22379])).
% 17.82/8.29  tff(c_22385, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_21775, c_22382])).
% 17.82/8.29  tff(c_22387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_22385])).
% 17.82/8.29  tff(c_22389, plain, (m1_subset_1('#skF_2'('#skF_7'), u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_22374])).
% 17.82/8.29  tff(c_36, plain, (![A_19, B_23, C_25]: (r1_lattices(A_19, B_23, C_25) | k2_lattices(A_19, B_23, C_25)!=B_23 | ~m1_subset_1(C_25, u1_struct_0(A_19)) | ~m1_subset_1(B_23, u1_struct_0(A_19)) | ~l3_lattices(A_19) | ~v9_lattices(A_19) | ~v8_lattices(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_117])).
% 17.82/8.29  tff(c_22393, plain, (![B_23]: (r1_lattices('#skF_7', B_23, '#skF_2'('#skF_7')) | k2_lattices('#skF_7', B_23, '#skF_2'('#skF_7'))!=B_23 | ~m1_subset_1(B_23, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_22389, c_36])).
% 17.82/8.29  tff(c_22418, plain, (![B_23]: (r1_lattices('#skF_7', B_23, '#skF_2'('#skF_7')) | k2_lattices('#skF_7', B_23, '#skF_2'('#skF_7'))!=B_23 | ~m1_subset_1(B_23, u1_struct_0('#skF_7')) | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_22393])).
% 17.82/8.29  tff(c_22419, plain, (![B_23]: (r1_lattices('#skF_7', B_23, '#skF_2'('#skF_7')) | k2_lattices('#skF_7', B_23, '#skF_2'('#skF_7'))!=B_23 | ~m1_subset_1(B_23, u1_struct_0('#skF_7')) | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_78, c_22418])).
% 17.82/8.29  tff(c_23088, plain, (~v8_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_22419])).
% 17.82/8.29  tff(c_23095, plain, (~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7')), inference(resolution, [status(thm)], [c_8, c_23088])).
% 17.82/8.29  tff(c_23098, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_23095])).
% 17.82/8.29  tff(c_23100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_23098])).
% 17.82/8.29  tff(c_23102, plain, (v8_lattices('#skF_7')), inference(splitRight, [status(thm)], [c_22419])).
% 17.82/8.29  tff(c_23101, plain, (![B_23]: (~v9_lattices('#skF_7') | r1_lattices('#skF_7', B_23, '#skF_2'('#skF_7')) | k2_lattices('#skF_7', B_23, '#skF_2'('#skF_7'))!=B_23 | ~m1_subset_1(B_23, u1_struct_0('#skF_7')))), inference(splitRight, [status(thm)], [c_22419])).
% 17.82/8.29  tff(c_23103, plain, (~v9_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_23101])).
% 17.82/8.29  tff(c_23109, plain, (~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7')), inference(resolution, [status(thm)], [c_6, c_23103])).
% 17.82/8.29  tff(c_23112, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_23109])).
% 17.82/8.29  tff(c_23114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_23112])).
% 17.82/8.29  tff(c_23116, plain, (v9_lattices('#skF_7')), inference(splitRight, [status(thm)], [c_23101])).
% 17.82/8.29  tff(c_22070, plain, (![A_48, B_49]: (k2_lattices(A_48, k15_lattice3(A_48, B_49), k5_lattices(A_48))=k5_lattices(A_48) | ~m1_subset_1(k5_lattices(A_48), u1_struct_0(A_48)) | ~v13_lattices(A_48) | ~l1_lattices(A_48) | ~l3_lattices(A_48) | v2_struct_0(A_48))), inference(resolution, [status(thm)], [c_58, c_22052])).
% 17.82/8.29  tff(c_22339, plain, (![B_49]: (k2_lattices('#skF_7', k15_lattice3('#skF_7', B_49), k5_lattices('#skF_7'))=k5_lattices('#skF_7') | ~m1_subset_1('#skF_2'('#skF_7'), u1_struct_0('#skF_7')) | ~v13_lattices('#skF_7') | ~l1_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_22333, c_22070])).
% 17.82/8.29  tff(c_22358, plain, (![B_49]: (k2_lattices('#skF_7', k15_lattice3('#skF_7', B_49), '#skF_2'('#skF_7'))='#skF_2'('#skF_7') | ~m1_subset_1('#skF_2'('#skF_7'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_87, c_21775, c_22333, c_22333, c_22339])).
% 17.82/8.29  tff(c_22359, plain, (![B_49]: (k2_lattices('#skF_7', k15_lattice3('#skF_7', B_49), '#skF_2'('#skF_7'))='#skF_2'('#skF_7') | ~m1_subset_1('#skF_2'('#skF_7'), u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_78, c_22358])).
% 17.82/8.29  tff(c_22687, plain, (![B_1041]: (k2_lattices('#skF_7', k15_lattice3('#skF_7', B_1041), '#skF_2'('#skF_7'))='#skF_2'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_22389, c_22359])).
% 17.82/8.29  tff(c_22014, plain, (![A_971, C_972, B_973]: (k2_lattices(A_971, C_972, B_973)=k2_lattices(A_971, B_973, C_972) | ~m1_subset_1(C_972, u1_struct_0(A_971)) | ~m1_subset_1(B_973, u1_struct_0(A_971)) | ~v6_lattices(A_971) | ~l1_lattices(A_971) | v2_struct_0(A_971))), inference(cnfTransformation, [status(thm)], [f_149])).
% 17.82/8.29  tff(c_22123, plain, (![A_998, B_999]: (k2_lattices(A_998, B_999, '#skF_2'(A_998))=k2_lattices(A_998, '#skF_2'(A_998), B_999) | ~m1_subset_1(B_999, u1_struct_0(A_998)) | ~v6_lattices(A_998) | ~v13_lattices(A_998) | ~l1_lattices(A_998) | v2_struct_0(A_998))), inference(resolution, [status(thm)], [c_44, c_22014])).
% 17.82/8.29  tff(c_22142, plain, (![A_48, B_49]: (k2_lattices(A_48, k15_lattice3(A_48, B_49), '#skF_2'(A_48))=k2_lattices(A_48, '#skF_2'(A_48), k15_lattice3(A_48, B_49)) | ~v6_lattices(A_48) | ~v13_lattices(A_48) | ~l1_lattices(A_48) | ~l3_lattices(A_48) | v2_struct_0(A_48))), inference(resolution, [status(thm)], [c_58, c_22123])).
% 17.82/8.29  tff(c_22692, plain, (![B_1041]: (k2_lattices('#skF_7', '#skF_2'('#skF_7'), k15_lattice3('#skF_7', B_1041))='#skF_2'('#skF_7') | ~v6_lattices('#skF_7') | ~v13_lattices('#skF_7') | ~l1_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_22687, c_22142])).
% 17.82/8.29  tff(c_22722, plain, (![B_1041]: (k2_lattices('#skF_7', '#skF_2'('#skF_7'), k15_lattice3('#skF_7', B_1041))='#skF_2'('#skF_7') | ~v6_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_87, c_21775, c_22692])).
% 17.82/8.29  tff(c_22723, plain, (![B_1041]: (k2_lattices('#skF_7', '#skF_2'('#skF_7'), k15_lattice3('#skF_7', B_1041))='#skF_2'('#skF_7') | ~v6_lattices('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_78, c_22722])).
% 17.82/8.29  tff(c_22746, plain, (~v6_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_22723])).
% 17.82/8.29  tff(c_22749, plain, (~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7')), inference(resolution, [status(thm)], [c_12, c_22746])).
% 17.82/8.29  tff(c_22752, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_22749])).
% 17.82/8.29  tff(c_22754, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_22752])).
% 17.82/8.29  tff(c_22756, plain, (v6_lattices('#skF_7')), inference(splitRight, [status(thm)], [c_22723])).
% 17.82/8.29  tff(c_62, plain, (![A_50, B_52]: (k15_lattice3(A_50, a_2_3_lattice3(A_50, B_52))=B_52 | ~m1_subset_1(B_52, u1_struct_0(A_50)) | ~l3_lattices(A_50) | ~v4_lattice3(A_50) | ~v10_lattices(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_172])).
% 17.82/8.29  tff(c_22407, plain, (k15_lattice3('#skF_7', a_2_3_lattice3('#skF_7', '#skF_2'('#skF_7')))='#skF_2'('#skF_7') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_22389, c_62])).
% 17.82/8.29  tff(c_22447, plain, (k15_lattice3('#skF_7', a_2_3_lattice3('#skF_7', '#skF_2'('#skF_7')))='#skF_2'('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_22407])).
% 17.82/8.29  tff(c_22448, plain, (k15_lattice3('#skF_7', a_2_3_lattice3('#skF_7', '#skF_2'('#skF_7')))='#skF_2'('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_78, c_22447])).
% 17.82/8.29  tff(c_21976, plain, (![A_967, B_968, C_969]: (r2_hidden('#skF_6'(A_967, B_968, C_969), B_968) | r3_lattices(A_967, k15_lattice3(A_967, B_968), k15_lattice3(A_967, C_969)) | ~l3_lattices(A_967) | ~v4_lattice3(A_967) | ~v10_lattices(A_967) | v2_struct_0(A_967))), inference(cnfTransformation, [status(thm)], [f_198])).
% 17.82/8.29  tff(c_22100, plain, (![B_989, A_990, C_991]: (~r1_tarski(B_989, '#skF_6'(A_990, B_989, C_991)) | r3_lattices(A_990, k15_lattice3(A_990, B_989), k15_lattice3(A_990, C_991)) | ~l3_lattices(A_990) | ~v4_lattice3(A_990) | ~v10_lattices(A_990) | v2_struct_0(A_990))), inference(resolution, [status(thm)], [c_21976, c_4])).
% 17.82/8.29  tff(c_22104, plain, (![A_990, C_991]: (r3_lattices(A_990, k15_lattice3(A_990, k1_xboole_0), k15_lattice3(A_990, C_991)) | ~l3_lattices(A_990) | ~v4_lattice3(A_990) | ~v10_lattices(A_990) | v2_struct_0(A_990))), inference(resolution, [status(thm)], [c_2, c_22100])).
% 17.82/8.29  tff(c_22505, plain, (r3_lattices('#skF_7', k15_lattice3('#skF_7', k1_xboole_0), '#skF_2'('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_22448, c_22104])).
% 17.82/8.29  tff(c_22561, plain, (r3_lattices('#skF_7', k15_lattice3('#skF_7', k1_xboole_0), '#skF_2'('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_22505])).
% 17.82/8.29  tff(c_22562, plain, (r3_lattices('#skF_7', k15_lattice3('#skF_7', k1_xboole_0), '#skF_2'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_78, c_22561])).
% 17.82/8.29  tff(c_34, plain, (![A_16, B_17, C_18]: (r1_lattices(A_16, B_17, C_18) | ~r3_lattices(A_16, B_17, C_18) | ~m1_subset_1(C_18, u1_struct_0(A_16)) | ~m1_subset_1(B_17, u1_struct_0(A_16)) | ~l3_lattices(A_16) | ~v9_lattices(A_16) | ~v8_lattices(A_16) | ~v6_lattices(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_98])).
% 17.82/8.29  tff(c_22597, plain, (r1_lattices('#skF_7', k15_lattice3('#skF_7', k1_xboole_0), '#skF_2'('#skF_7')) | ~m1_subset_1('#skF_2'('#skF_7'), u1_struct_0('#skF_7')) | ~m1_subset_1(k15_lattice3('#skF_7', k1_xboole_0), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | ~v6_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_22562, c_34])).
% 17.82/8.29  tff(c_22600, plain, (r1_lattices('#skF_7', k15_lattice3('#skF_7', k1_xboole_0), '#skF_2'('#skF_7')) | ~m1_subset_1(k15_lattice3('#skF_7', k1_xboole_0), u1_struct_0('#skF_7')) | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | ~v6_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_22389, c_22597])).
% 17.82/8.29  tff(c_22601, plain, (r1_lattices('#skF_7', k15_lattice3('#skF_7', k1_xboole_0), '#skF_2'('#skF_7')) | ~m1_subset_1(k15_lattice3('#skF_7', k1_xboole_0), u1_struct_0('#skF_7')) | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | ~v6_lattices('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_78, c_22600])).
% 17.82/8.29  tff(c_23127, plain, (r1_lattices('#skF_7', k15_lattice3('#skF_7', k1_xboole_0), '#skF_2'('#skF_7')) | ~m1_subset_1(k15_lattice3('#skF_7', k1_xboole_0), u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_22756, c_23102, c_23116, c_22601])).
% 17.82/8.29  tff(c_23128, plain, (~m1_subset_1(k15_lattice3('#skF_7', k1_xboole_0), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_23127])).
% 17.82/8.29  tff(c_23135, plain, (~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_58, c_23128])).
% 17.82/8.29  tff(c_23138, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_23135])).
% 17.82/8.29  tff(c_23140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_23138])).
% 17.82/8.29  tff(c_23142, plain, (m1_subset_1(k15_lattice3('#skF_7', k1_xboole_0), u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_23127])).
% 17.82/8.29  tff(c_22686, plain, (![B_49]: (k2_lattices('#skF_7', k15_lattice3('#skF_7', B_49), '#skF_2'('#skF_7'))='#skF_2'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_22389, c_22359])).
% 17.82/8.29  tff(c_23141, plain, (r1_lattices('#skF_7', k15_lattice3('#skF_7', k1_xboole_0), '#skF_2'('#skF_7'))), inference(splitRight, [status(thm)], [c_23127])).
% 17.82/8.29  tff(c_23215, plain, (k2_lattices('#skF_7', k15_lattice3('#skF_7', k1_xboole_0), '#skF_2'('#skF_7'))=k15_lattice3('#skF_7', k1_xboole_0) | ~m1_subset_1('#skF_2'('#skF_7'), u1_struct_0('#skF_7')) | ~m1_subset_1(k15_lattice3('#skF_7', k1_xboole_0), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_23141, c_38])).
% 17.82/8.29  tff(c_23218, plain, (k15_lattice3('#skF_7', k1_xboole_0)='#skF_2'('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_23102, c_23116, c_72, c_23142, c_22389, c_22686, c_23215])).
% 17.82/8.29  tff(c_23220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_22334, c_23218])).
% 17.82/8.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.82/8.29  
% 17.82/8.29  Inference rules
% 17.82/8.29  ----------------------
% 17.82/8.29  #Ref     : 0
% 17.82/8.29  #Sup     : 6862
% 17.82/8.29  #Fact    : 0
% 17.82/8.29  #Define  : 0
% 17.82/8.29  #Split   : 8
% 17.82/8.29  #Chain   : 0
% 17.82/8.29  #Close   : 0
% 17.82/8.29  
% 17.82/8.29  Ordering : KBO
% 17.82/8.29  
% 17.82/8.29  Simplification rules
% 17.82/8.29  ----------------------
% 17.82/8.29  #Subsume      : 1344
% 17.82/8.29  #Demod        : 412
% 17.82/8.29  #Tautology    : 1254
% 17.82/8.29  #SimpNegUnit  : 107
% 17.82/8.29  #BackRed      : 1
% 17.82/8.29  
% 17.82/8.29  #Partial instantiations: 0
% 17.82/8.29  #Strategies tried      : 1
% 17.82/8.29  
% 17.82/8.29  Timing (in seconds)
% 17.82/8.29  ----------------------
% 17.82/8.29  Preprocessing        : 0.37
% 17.82/8.29  Parsing              : 0.19
% 17.82/8.29  CNF conversion       : 0.03
% 17.82/8.29  Main loop            : 7.12
% 17.82/8.29  Inferencing          : 2.34
% 17.82/8.29  Reduction            : 1.30
% 17.82/8.29  Demodulation         : 0.88
% 17.82/8.29  BG Simplification    : 0.33
% 17.82/8.29  Subsumption          : 2.81
% 17.82/8.29  Abstraction          : 0.36
% 17.82/8.29  MUC search           : 0.00
% 17.82/8.29  Cooper               : 0.00
% 17.82/8.29  Total                : 7.54
% 17.82/8.29  Index Insertion      : 0.00
% 17.82/8.29  Index Deletion       : 0.00
% 17.82/8.29  Index Matching       : 0.00
% 17.82/8.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
