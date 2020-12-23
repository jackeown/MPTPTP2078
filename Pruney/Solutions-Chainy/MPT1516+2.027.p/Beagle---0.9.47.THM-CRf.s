%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:54 EST 2020

% Result     : Theorem 7.79s
% Output     : CNFRefutation 8.02s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 817 expanded)
%              Number of leaves         :   49 ( 299 expanded)
%              Depth                    :   23
%              Number of atoms          :  644 (3492 expanded)
%              Number of equality atoms :   66 ( 433 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k6_domain_1 > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_6 > #skF_7 > #skF_3 > #skF_1

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

tff(f_226,negated_conjecture,(
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

tff(f_86,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_163,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_141,axiom,(
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

tff(f_179,axiom,(
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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_205,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattice3)).

tff(f_32,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_105,axiom,(
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

tff(f_124,axiom,(
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

tff(f_156,axiom,(
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

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_74,plain,(
    l3_lattices('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_85,plain,(
    ! [A_71] :
      ( l1_lattices(A_71)
      | ~ l3_lattices(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_89,plain,(
    l1_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_85])).

tff(c_78,plain,(
    v10_lattices('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_72,plain,
    ( k15_lattice3('#skF_7',k1_xboole_0) != k5_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | ~ v13_lattices('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_82,plain,
    ( k15_lattice3('#skF_7',k1_xboole_0) != k5_lattices('#skF_7')
    | ~ v13_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72])).

tff(c_83,plain,
    ( k15_lattice3('#skF_7',k1_xboole_0) != k5_lattices('#skF_7')
    | ~ v13_lattices('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_82])).

tff(c_95,plain,(
    ~ v13_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_76,plain,(
    v4_lattice3('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

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

tff(c_60,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k15_lattice3(A_49,B_50),u1_struct_0(A_49))
      | ~ l3_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_44,plain,(
    ! [A_27,B_36] :
      ( m1_subset_1('#skF_3'(A_27,B_36),u1_struct_0(A_27))
      | v13_lattices(A_27)
      | ~ m1_subset_1(B_36,u1_struct_0(A_27))
      | ~ l1_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_64,plain,(
    ! [A_51,B_53] :
      ( k15_lattice3(A_51,k6_domain_1(u1_struct_0(A_51),B_53)) = B_53
      | ~ m1_subset_1(B_53,u1_struct_0(A_51))
      | ~ l3_lattices(A_51)
      | ~ v4_lattice3(A_51)
      | ~ v10_lattices(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_263,plain,(
    ! [A_111,B_112,C_113] :
      ( r2_hidden('#skF_6'(A_111,B_112,C_113),B_112)
      | r3_lattices(A_111,k15_lattice3(A_111,B_112),k15_lattice3(A_111,C_113))
      | ~ l3_lattices(A_111)
      | ~ v4_lattice3(A_111)
      | ~ v10_lattices(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( ~ r1_tarski(B_3,A_2)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_561,plain,(
    ! [B_153,A_154,C_155] :
      ( ~ r1_tarski(B_153,'#skF_6'(A_154,B_153,C_155))
      | r3_lattices(A_154,k15_lattice3(A_154,B_153),k15_lattice3(A_154,C_155))
      | ~ l3_lattices(A_154)
      | ~ v4_lattice3(A_154)
      | ~ v10_lattices(A_154)
      | v2_struct_0(A_154) ) ),
    inference(resolution,[status(thm)],[c_263,c_4])).

tff(c_566,plain,(
    ! [A_156,C_157] :
      ( r3_lattices(A_156,k15_lattice3(A_156,k1_xboole_0),k15_lattice3(A_156,C_157))
      | ~ l3_lattices(A_156)
      | ~ v4_lattice3(A_156)
      | ~ v10_lattices(A_156)
      | v2_struct_0(A_156) ) ),
    inference(resolution,[status(thm)],[c_2,c_561])).

tff(c_813,plain,(
    ! [A_204,B_205] :
      ( r3_lattices(A_204,k15_lattice3(A_204,k1_xboole_0),B_205)
      | ~ l3_lattices(A_204)
      | ~ v4_lattice3(A_204)
      | ~ v10_lattices(A_204)
      | v2_struct_0(A_204)
      | ~ m1_subset_1(B_205,u1_struct_0(A_204))
      | ~ l3_lattices(A_204)
      | ~ v4_lattice3(A_204)
      | ~ v10_lattices(A_204)
      | v2_struct_0(A_204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_566])).

tff(c_36,plain,(
    ! [A_17,B_18,C_19] :
      ( r1_lattices(A_17,B_18,C_19)
      | ~ r3_lattices(A_17,B_18,C_19)
      | ~ m1_subset_1(C_19,u1_struct_0(A_17))
      | ~ m1_subset_1(B_18,u1_struct_0(A_17))
      | ~ l3_lattices(A_17)
      | ~ v9_lattices(A_17)
      | ~ v8_lattices(A_17)
      | ~ v6_lattices(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1049,plain,(
    ! [A_239,B_240] :
      ( r1_lattices(A_239,k15_lattice3(A_239,k1_xboole_0),B_240)
      | ~ m1_subset_1(k15_lattice3(A_239,k1_xboole_0),u1_struct_0(A_239))
      | ~ v9_lattices(A_239)
      | ~ v8_lattices(A_239)
      | ~ v6_lattices(A_239)
      | ~ m1_subset_1(B_240,u1_struct_0(A_239))
      | ~ l3_lattices(A_239)
      | ~ v4_lattice3(A_239)
      | ~ v10_lattices(A_239)
      | v2_struct_0(A_239) ) ),
    inference(resolution,[status(thm)],[c_813,c_36])).

tff(c_1054,plain,(
    ! [A_241,B_242] :
      ( r1_lattices(A_241,k15_lattice3(A_241,k1_xboole_0),B_242)
      | ~ v9_lattices(A_241)
      | ~ v8_lattices(A_241)
      | ~ v6_lattices(A_241)
      | ~ m1_subset_1(B_242,u1_struct_0(A_241))
      | ~ v4_lattice3(A_241)
      | ~ v10_lattices(A_241)
      | ~ l3_lattices(A_241)
      | v2_struct_0(A_241) ) ),
    inference(resolution,[status(thm)],[c_60,c_1049])).

tff(c_40,plain,(
    ! [A_20,B_24,C_26] :
      ( k2_lattices(A_20,B_24,C_26) = B_24
      | ~ r1_lattices(A_20,B_24,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_20))
      | ~ m1_subset_1(B_24,u1_struct_0(A_20))
      | ~ l3_lattices(A_20)
      | ~ v9_lattices(A_20)
      | ~ v8_lattices(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1135,plain,(
    ! [A_255,B_256] :
      ( k2_lattices(A_255,k15_lattice3(A_255,k1_xboole_0),B_256) = k15_lattice3(A_255,k1_xboole_0)
      | ~ m1_subset_1(k15_lattice3(A_255,k1_xboole_0),u1_struct_0(A_255))
      | ~ v9_lattices(A_255)
      | ~ v8_lattices(A_255)
      | ~ v6_lattices(A_255)
      | ~ m1_subset_1(B_256,u1_struct_0(A_255))
      | ~ v4_lattice3(A_255)
      | ~ v10_lattices(A_255)
      | ~ l3_lattices(A_255)
      | v2_struct_0(A_255) ) ),
    inference(resolution,[status(thm)],[c_1054,c_40])).

tff(c_1140,plain,(
    ! [A_257,B_258] :
      ( k2_lattices(A_257,k15_lattice3(A_257,k1_xboole_0),B_258) = k15_lattice3(A_257,k1_xboole_0)
      | ~ v9_lattices(A_257)
      | ~ v8_lattices(A_257)
      | ~ v6_lattices(A_257)
      | ~ m1_subset_1(B_258,u1_struct_0(A_257))
      | ~ v4_lattice3(A_257)
      | ~ v10_lattices(A_257)
      | ~ l3_lattices(A_257)
      | v2_struct_0(A_257) ) ),
    inference(resolution,[status(thm)],[c_60,c_1135])).

tff(c_1156,plain,(
    ! [A_27,B_36] :
      ( k2_lattices(A_27,k15_lattice3(A_27,k1_xboole_0),'#skF_3'(A_27,B_36)) = k15_lattice3(A_27,k1_xboole_0)
      | ~ v9_lattices(A_27)
      | ~ v8_lattices(A_27)
      | ~ v6_lattices(A_27)
      | ~ v4_lattice3(A_27)
      | ~ v10_lattices(A_27)
      | ~ l3_lattices(A_27)
      | v13_lattices(A_27)
      | ~ m1_subset_1(B_36,u1_struct_0(A_27))
      | ~ l1_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_44,c_1140])).

tff(c_68,plain,(
    ! [A_54,B_63,C_64] :
      ( r2_hidden('#skF_6'(A_54,B_63,C_64),B_63)
      | r3_lattices(A_54,k15_lattice3(A_54,B_63),k15_lattice3(A_54,C_64))
      | ~ l3_lattices(A_54)
      | ~ v4_lattice3(A_54)
      | ~ v10_lattices(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_596,plain,(
    ! [A_164,B_165,C_166] :
      ( r1_lattices(A_164,B_165,C_166)
      | ~ r3_lattices(A_164,B_165,C_166)
      | ~ m1_subset_1(C_166,u1_struct_0(A_164))
      | ~ m1_subset_1(B_165,u1_struct_0(A_164))
      | ~ l3_lattices(A_164)
      | ~ v9_lattices(A_164)
      | ~ v8_lattices(A_164)
      | ~ v6_lattices(A_164)
      | v2_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1770,plain,(
    ! [A_341,B_342,C_343] :
      ( r1_lattices(A_341,k15_lattice3(A_341,B_342),k15_lattice3(A_341,C_343))
      | ~ m1_subset_1(k15_lattice3(A_341,C_343),u1_struct_0(A_341))
      | ~ m1_subset_1(k15_lattice3(A_341,B_342),u1_struct_0(A_341))
      | ~ v9_lattices(A_341)
      | ~ v8_lattices(A_341)
      | ~ v6_lattices(A_341)
      | r2_hidden('#skF_6'(A_341,B_342,C_343),B_342)
      | ~ l3_lattices(A_341)
      | ~ v4_lattice3(A_341)
      | ~ v10_lattices(A_341)
      | v2_struct_0(A_341) ) ),
    inference(resolution,[status(thm)],[c_68,c_596])).

tff(c_1996,plain,(
    ! [A_382,B_383,C_384] :
      ( k2_lattices(A_382,k15_lattice3(A_382,B_383),k15_lattice3(A_382,C_384)) = k15_lattice3(A_382,B_383)
      | ~ m1_subset_1(k15_lattice3(A_382,C_384),u1_struct_0(A_382))
      | ~ m1_subset_1(k15_lattice3(A_382,B_383),u1_struct_0(A_382))
      | ~ v9_lattices(A_382)
      | ~ v8_lattices(A_382)
      | ~ v6_lattices(A_382)
      | r2_hidden('#skF_6'(A_382,B_383,C_384),B_383)
      | ~ l3_lattices(A_382)
      | ~ v4_lattice3(A_382)
      | ~ v10_lattices(A_382)
      | v2_struct_0(A_382) ) ),
    inference(resolution,[status(thm)],[c_1770,c_40])).

tff(c_2002,plain,(
    ! [A_385,B_386,B_387] :
      ( k2_lattices(A_385,k15_lattice3(A_385,B_386),k15_lattice3(A_385,B_387)) = k15_lattice3(A_385,B_386)
      | ~ m1_subset_1(k15_lattice3(A_385,B_386),u1_struct_0(A_385))
      | ~ v9_lattices(A_385)
      | ~ v8_lattices(A_385)
      | ~ v6_lattices(A_385)
      | r2_hidden('#skF_6'(A_385,B_386,B_387),B_386)
      | ~ v4_lattice3(A_385)
      | ~ v10_lattices(A_385)
      | ~ l3_lattices(A_385)
      | v2_struct_0(A_385) ) ),
    inference(resolution,[status(thm)],[c_60,c_1996])).

tff(c_2008,plain,(
    ! [A_388,B_389,B_390] :
      ( k2_lattices(A_388,k15_lattice3(A_388,B_389),k15_lattice3(A_388,B_390)) = k15_lattice3(A_388,B_389)
      | ~ v9_lattices(A_388)
      | ~ v8_lattices(A_388)
      | ~ v6_lattices(A_388)
      | r2_hidden('#skF_6'(A_388,B_389,B_390),B_389)
      | ~ v4_lattice3(A_388)
      | ~ v10_lattices(A_388)
      | ~ l3_lattices(A_388)
      | v2_struct_0(A_388) ) ),
    inference(resolution,[status(thm)],[c_60,c_2002])).

tff(c_357,plain,(
    ! [A_122,C_123,B_124] :
      ( k2_lattices(A_122,C_123,B_124) = k2_lattices(A_122,B_124,C_123)
      | ~ m1_subset_1(C_123,u1_struct_0(A_122))
      | ~ m1_subset_1(B_124,u1_struct_0(A_122))
      | ~ v6_lattices(A_122)
      | ~ l1_lattices(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_672,plain,(
    ! [A_178,B_179,B_180] :
      ( k2_lattices(A_178,k15_lattice3(A_178,B_179),B_180) = k2_lattices(A_178,B_180,k15_lattice3(A_178,B_179))
      | ~ m1_subset_1(B_180,u1_struct_0(A_178))
      | ~ v6_lattices(A_178)
      | ~ l1_lattices(A_178)
      | ~ l3_lattices(A_178)
      | v2_struct_0(A_178) ) ),
    inference(resolution,[status(thm)],[c_60,c_357])).

tff(c_692,plain,(
    ! [A_49,B_50,B_179] :
      ( k2_lattices(A_49,k15_lattice3(A_49,B_50),k15_lattice3(A_49,B_179)) = k2_lattices(A_49,k15_lattice3(A_49,B_179),k15_lattice3(A_49,B_50))
      | ~ v6_lattices(A_49)
      | ~ l1_lattices(A_49)
      | ~ l3_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_60,c_672])).

tff(c_2089,plain,(
    ! [A_397,B_398,B_399] :
      ( k2_lattices(A_397,k15_lattice3(A_397,B_398),k15_lattice3(A_397,B_399)) = k15_lattice3(A_397,B_399)
      | ~ v6_lattices(A_397)
      | ~ l1_lattices(A_397)
      | ~ l3_lattices(A_397)
      | v2_struct_0(A_397)
      | ~ v9_lattices(A_397)
      | ~ v8_lattices(A_397)
      | ~ v6_lattices(A_397)
      | r2_hidden('#skF_6'(A_397,B_399,B_398),B_399)
      | ~ v4_lattice3(A_397)
      | ~ v10_lattices(A_397)
      | ~ l3_lattices(A_397)
      | v2_struct_0(A_397) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2008,c_692])).

tff(c_2170,plain,(
    ! [B_403,A_404,B_405] :
      ( ~ r1_tarski(B_403,'#skF_6'(A_404,B_403,B_405))
      | k2_lattices(A_404,k15_lattice3(A_404,B_405),k15_lattice3(A_404,B_403)) = k15_lattice3(A_404,B_403)
      | ~ l1_lattices(A_404)
      | ~ v9_lattices(A_404)
      | ~ v8_lattices(A_404)
      | ~ v6_lattices(A_404)
      | ~ v4_lattice3(A_404)
      | ~ v10_lattices(A_404)
      | ~ l3_lattices(A_404)
      | v2_struct_0(A_404) ) ),
    inference(resolution,[status(thm)],[c_2089,c_4])).

tff(c_2175,plain,(
    ! [A_406,B_407] :
      ( k2_lattices(A_406,k15_lattice3(A_406,B_407),k15_lattice3(A_406,k1_xboole_0)) = k15_lattice3(A_406,k1_xboole_0)
      | ~ l1_lattices(A_406)
      | ~ v9_lattices(A_406)
      | ~ v8_lattices(A_406)
      | ~ v6_lattices(A_406)
      | ~ v4_lattice3(A_406)
      | ~ v10_lattices(A_406)
      | ~ l3_lattices(A_406)
      | v2_struct_0(A_406) ) ),
    inference(resolution,[status(thm)],[c_2,c_2170])).

tff(c_2235,plain,(
    ! [A_408,B_409] :
      ( k2_lattices(A_408,B_409,k15_lattice3(A_408,k1_xboole_0)) = k15_lattice3(A_408,k1_xboole_0)
      | ~ l1_lattices(A_408)
      | ~ v9_lattices(A_408)
      | ~ v8_lattices(A_408)
      | ~ v6_lattices(A_408)
      | ~ v4_lattice3(A_408)
      | ~ v10_lattices(A_408)
      | ~ l3_lattices(A_408)
      | v2_struct_0(A_408)
      | ~ m1_subset_1(B_409,u1_struct_0(A_408))
      | ~ l3_lattices(A_408)
      | ~ v4_lattice3(A_408)
      | ~ v10_lattices(A_408)
      | v2_struct_0(A_408) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_2175])).

tff(c_2295,plain,(
    ! [A_412,B_413] :
      ( k2_lattices(A_412,'#skF_3'(A_412,B_413),k15_lattice3(A_412,k1_xboole_0)) = k15_lattice3(A_412,k1_xboole_0)
      | ~ v9_lattices(A_412)
      | ~ v8_lattices(A_412)
      | ~ v6_lattices(A_412)
      | ~ l3_lattices(A_412)
      | ~ v4_lattice3(A_412)
      | ~ v10_lattices(A_412)
      | v13_lattices(A_412)
      | ~ m1_subset_1(B_413,u1_struct_0(A_412))
      | ~ l1_lattices(A_412)
      | v2_struct_0(A_412) ) ),
    inference(resolution,[status(thm)],[c_44,c_2235])).

tff(c_42,plain,(
    ! [A_27,B_36] :
      ( k2_lattices(A_27,'#skF_3'(A_27,B_36),B_36) != B_36
      | k2_lattices(A_27,B_36,'#skF_3'(A_27,B_36)) != B_36
      | v13_lattices(A_27)
      | ~ m1_subset_1(B_36,u1_struct_0(A_27))
      | ~ l1_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2336,plain,(
    ! [A_416] :
      ( k2_lattices(A_416,k15_lattice3(A_416,k1_xboole_0),'#skF_3'(A_416,k15_lattice3(A_416,k1_xboole_0))) != k15_lattice3(A_416,k1_xboole_0)
      | ~ v9_lattices(A_416)
      | ~ v8_lattices(A_416)
      | ~ v6_lattices(A_416)
      | ~ l3_lattices(A_416)
      | ~ v4_lattice3(A_416)
      | ~ v10_lattices(A_416)
      | v13_lattices(A_416)
      | ~ m1_subset_1(k15_lattice3(A_416,k1_xboole_0),u1_struct_0(A_416))
      | ~ l1_lattices(A_416)
      | v2_struct_0(A_416) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2295,c_42])).

tff(c_2342,plain,(
    ! [A_417] :
      ( ~ v9_lattices(A_417)
      | ~ v8_lattices(A_417)
      | ~ v6_lattices(A_417)
      | ~ v4_lattice3(A_417)
      | ~ v10_lattices(A_417)
      | ~ l3_lattices(A_417)
      | v13_lattices(A_417)
      | ~ m1_subset_1(k15_lattice3(A_417,k1_xboole_0),u1_struct_0(A_417))
      | ~ l1_lattices(A_417)
      | v2_struct_0(A_417) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1156,c_2336])).

tff(c_2371,plain,(
    ! [A_421] :
      ( ~ v9_lattices(A_421)
      | ~ v8_lattices(A_421)
      | ~ v6_lattices(A_421)
      | ~ v4_lattice3(A_421)
      | ~ v10_lattices(A_421)
      | v13_lattices(A_421)
      | ~ l1_lattices(A_421)
      | ~ l3_lattices(A_421)
      | v2_struct_0(A_421) ) ),
    inference(resolution,[status(thm)],[c_60,c_2342])).

tff(c_2376,plain,(
    ! [A_422] :
      ( ~ v8_lattices(A_422)
      | ~ v6_lattices(A_422)
      | ~ v4_lattice3(A_422)
      | v13_lattices(A_422)
      | ~ l1_lattices(A_422)
      | ~ v10_lattices(A_422)
      | v2_struct_0(A_422)
      | ~ l3_lattices(A_422) ) ),
    inference(resolution,[status(thm)],[c_6,c_2371])).

tff(c_2381,plain,(
    ! [A_423] :
      ( ~ v6_lattices(A_423)
      | ~ v4_lattice3(A_423)
      | v13_lattices(A_423)
      | ~ l1_lattices(A_423)
      | ~ v10_lattices(A_423)
      | v2_struct_0(A_423)
      | ~ l3_lattices(A_423) ) ),
    inference(resolution,[status(thm)],[c_8,c_2376])).

tff(c_2386,plain,(
    ! [A_424] :
      ( ~ v4_lattice3(A_424)
      | v13_lattices(A_424)
      | ~ l1_lattices(A_424)
      | ~ v10_lattices(A_424)
      | v2_struct_0(A_424)
      | ~ l3_lattices(A_424) ) ),
    inference(resolution,[status(thm)],[c_12,c_2381])).

tff(c_2389,plain,
    ( v13_lattices('#skF_7')
    | ~ l1_lattices('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l3_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_76,c_2386])).

tff(c_2392,plain,
    ( v13_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_78,c_89,c_2389])).

tff(c_2394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_95,c_2392])).

tff(c_2396,plain,(
    v13_lattices('#skF_7') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_28,plain,(
    ! [A_15] :
      ( m1_subset_1(k5_lattices(A_15),u1_struct_0(A_15))
      | ~ l1_lattices(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_46,plain,(
    ! [A_27] :
      ( m1_subset_1('#skF_2'(A_27),u1_struct_0(A_27))
      | ~ v13_lattices(A_27)
      | ~ l1_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2575,plain,(
    ! [A_466,C_467] :
      ( k2_lattices(A_466,k5_lattices(A_466),C_467) = k5_lattices(A_466)
      | ~ m1_subset_1(C_467,u1_struct_0(A_466))
      | ~ m1_subset_1(k5_lattices(A_466),u1_struct_0(A_466))
      | ~ v13_lattices(A_466)
      | ~ l1_lattices(A_466)
      | v2_struct_0(A_466) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2597,plain,(
    ! [A_468] :
      ( k2_lattices(A_468,k5_lattices(A_468),'#skF_2'(A_468)) = k5_lattices(A_468)
      | ~ m1_subset_1(k5_lattices(A_468),u1_struct_0(A_468))
      | ~ v13_lattices(A_468)
      | ~ l1_lattices(A_468)
      | v2_struct_0(A_468) ) ),
    inference(resolution,[status(thm)],[c_46,c_2575])).

tff(c_2601,plain,(
    ! [A_469] :
      ( k2_lattices(A_469,k5_lattices(A_469),'#skF_2'(A_469)) = k5_lattices(A_469)
      | ~ v13_lattices(A_469)
      | ~ l1_lattices(A_469)
      | v2_struct_0(A_469) ) ),
    inference(resolution,[status(thm)],[c_28,c_2597])).

tff(c_2456,plain,(
    ! [A_446,C_447] :
      ( k2_lattices(A_446,C_447,'#skF_2'(A_446)) = '#skF_2'(A_446)
      | ~ m1_subset_1(C_447,u1_struct_0(A_446))
      | ~ v13_lattices(A_446)
      | ~ l1_lattices(A_446)
      | v2_struct_0(A_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2474,plain,(
    ! [A_15] :
      ( k2_lattices(A_15,k5_lattices(A_15),'#skF_2'(A_15)) = '#skF_2'(A_15)
      | ~ v13_lattices(A_15)
      | ~ l1_lattices(A_15)
      | v2_struct_0(A_15) ) ),
    inference(resolution,[status(thm)],[c_28,c_2456])).

tff(c_2607,plain,(
    ! [A_469] :
      ( k5_lattices(A_469) = '#skF_2'(A_469)
      | ~ v13_lattices(A_469)
      | ~ l1_lattices(A_469)
      | v2_struct_0(A_469)
      | ~ v13_lattices(A_469)
      | ~ l1_lattices(A_469)
      | v2_struct_0(A_469) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2601,c_2474])).

tff(c_2651,plain,(
    ! [A_473] :
      ( k5_lattices(A_473) = '#skF_2'(A_473)
      | ~ v13_lattices(A_473)
      | ~ l1_lattices(A_473)
      | v2_struct_0(A_473) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2607])).

tff(c_2654,plain,
    ( k5_lattices('#skF_7') = '#skF_2'('#skF_7')
    | ~ v13_lattices('#skF_7')
    | ~ l1_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_2651,c_80])).

tff(c_2657,plain,(
    k5_lattices('#skF_7') = '#skF_2'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_2396,c_2654])).

tff(c_2395,plain,(
    k15_lattice3('#skF_7',k1_xboole_0) != k5_lattices('#skF_7') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_2658,plain,(
    k15_lattice3('#skF_7',k1_xboole_0) != '#skF_2'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2657,c_2395])).

tff(c_2671,plain,
    ( m1_subset_1('#skF_2'('#skF_7'),u1_struct_0('#skF_7'))
    | ~ l1_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2657,c_28])).

tff(c_2684,plain,
    ( m1_subset_1('#skF_2'('#skF_7'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_2671])).

tff(c_2685,plain,(
    m1_subset_1('#skF_2'('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2684])).

tff(c_2733,plain,(
    ! [A_474,C_475,B_476] :
      ( k2_lattices(A_474,C_475,B_476) = k2_lattices(A_474,B_476,C_475)
      | ~ m1_subset_1(C_475,u1_struct_0(A_474))
      | ~ m1_subset_1(B_476,u1_struct_0(A_474))
      | ~ v6_lattices(A_474)
      | ~ l1_lattices(A_474)
      | v2_struct_0(A_474) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_2735,plain,(
    ! [B_476] :
      ( k2_lattices('#skF_7',B_476,'#skF_2'('#skF_7')) = k2_lattices('#skF_7','#skF_2'('#skF_7'),B_476)
      | ~ m1_subset_1(B_476,u1_struct_0('#skF_7'))
      | ~ v6_lattices('#skF_7')
      | ~ l1_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2685,c_2733])).

tff(c_2752,plain,(
    ! [B_476] :
      ( k2_lattices('#skF_7',B_476,'#skF_2'('#skF_7')) = k2_lattices('#skF_7','#skF_2'('#skF_7'),B_476)
      | ~ m1_subset_1(B_476,u1_struct_0('#skF_7'))
      | ~ v6_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_2735])).

tff(c_2753,plain,(
    ! [B_476] :
      ( k2_lattices('#skF_7',B_476,'#skF_2'('#skF_7')) = k2_lattices('#skF_7','#skF_2'('#skF_7'),B_476)
      | ~ m1_subset_1(B_476,u1_struct_0('#skF_7'))
      | ~ v6_lattices('#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2752])).

tff(c_2763,plain,(
    ~ v6_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2753])).

tff(c_2766,plain,
    ( ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l3_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_2763])).

tff(c_2769,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_78,c_2766])).

tff(c_2771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2769])).

tff(c_2773,plain,(
    v6_lattices('#skF_7') ),
    inference(splitRight,[status(thm)],[c_2753])).

tff(c_3392,plain,(
    ! [A_516,B_517,C_518] :
      ( r1_lattices(A_516,B_517,C_518)
      | k2_lattices(A_516,B_517,C_518) != B_517
      | ~ m1_subset_1(C_518,u1_struct_0(A_516))
      | ~ m1_subset_1(B_517,u1_struct_0(A_516))
      | ~ l3_lattices(A_516)
      | ~ v9_lattices(A_516)
      | ~ v8_lattices(A_516)
      | v2_struct_0(A_516) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3394,plain,(
    ! [B_517] :
      ( r1_lattices('#skF_7',B_517,'#skF_2'('#skF_7'))
      | k2_lattices('#skF_7',B_517,'#skF_2'('#skF_7')) != B_517
      | ~ m1_subset_1(B_517,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v9_lattices('#skF_7')
      | ~ v8_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2685,c_3392])).

tff(c_3411,plain,(
    ! [B_517] :
      ( r1_lattices('#skF_7',B_517,'#skF_2'('#skF_7'))
      | k2_lattices('#skF_7',B_517,'#skF_2'('#skF_7')) != B_517
      | ~ m1_subset_1(B_517,u1_struct_0('#skF_7'))
      | ~ v9_lattices('#skF_7')
      | ~ v8_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3394])).

tff(c_3412,plain,(
    ! [B_517] :
      ( r1_lattices('#skF_7',B_517,'#skF_2'('#skF_7'))
      | k2_lattices('#skF_7',B_517,'#skF_2'('#skF_7')) != B_517
      | ~ m1_subset_1(B_517,u1_struct_0('#skF_7'))
      | ~ v9_lattices('#skF_7')
      | ~ v8_lattices('#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_3411])).

tff(c_3424,plain,(
    ~ v8_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3412])).

tff(c_3427,plain,
    ( ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l3_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_8,c_3424])).

tff(c_3430,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_78,c_3427])).

tff(c_3432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_3430])).

tff(c_3434,plain,(
    v8_lattices('#skF_7') ),
    inference(splitRight,[status(thm)],[c_3412])).

tff(c_3433,plain,(
    ! [B_517] :
      ( ~ v9_lattices('#skF_7')
      | r1_lattices('#skF_7',B_517,'#skF_2'('#skF_7'))
      | k2_lattices('#skF_7',B_517,'#skF_2'('#skF_7')) != B_517
      | ~ m1_subset_1(B_517,u1_struct_0('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_3412])).

tff(c_3435,plain,(
    ~ v9_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3433])).

tff(c_3438,plain,
    ( ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l3_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_3435])).

tff(c_3441,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_78,c_3438])).

tff(c_3443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_3441])).

tff(c_3445,plain,(
    v9_lattices('#skF_7') ),
    inference(splitRight,[status(thm)],[c_3433])).

tff(c_2774,plain,(
    ! [B_477] :
      ( k2_lattices('#skF_7',B_477,'#skF_2'('#skF_7')) = k2_lattices('#skF_7','#skF_2'('#skF_7'),B_477)
      | ~ m1_subset_1(B_477,u1_struct_0('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_2753])).

tff(c_2801,plain,(
    ! [B_50] :
      ( k2_lattices('#skF_7',k15_lattice3('#skF_7',B_50),'#skF_2'('#skF_7')) = k2_lattices('#skF_7','#skF_2'('#skF_7'),k15_lattice3('#skF_7',B_50))
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_60,c_2774])).

tff(c_2830,plain,(
    ! [B_50] :
      ( k2_lattices('#skF_7',k15_lattice3('#skF_7',B_50),'#skF_2'('#skF_7')) = k2_lattices('#skF_7','#skF_2'('#skF_7'),k15_lattice3('#skF_7',B_50))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2801])).

tff(c_2836,plain,(
    ! [B_478] : k2_lattices('#skF_7',k15_lattice3('#skF_7',B_478),'#skF_2'('#skF_7')) = k2_lattices('#skF_7','#skF_2'('#skF_7'),k15_lattice3('#skF_7',B_478)) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2830])).

tff(c_2473,plain,(
    ! [A_49,B_50] :
      ( k2_lattices(A_49,k15_lattice3(A_49,B_50),'#skF_2'(A_49)) = '#skF_2'(A_49)
      | ~ v13_lattices(A_49)
      | ~ l1_lattices(A_49)
      | ~ l3_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_60,c_2456])).

tff(c_2842,plain,(
    ! [B_478] :
      ( k2_lattices('#skF_7','#skF_2'('#skF_7'),k15_lattice3('#skF_7',B_478)) = '#skF_2'('#skF_7')
      | ~ v13_lattices('#skF_7')
      | ~ l1_lattices('#skF_7')
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2836,c_2473])).

tff(c_2856,plain,(
    ! [B_478] :
      ( k2_lattices('#skF_7','#skF_2'('#skF_7'),k15_lattice3('#skF_7',B_478)) = '#skF_2'('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_89,c_2396,c_2842])).

tff(c_2857,plain,(
    ! [B_478] : k2_lattices('#skF_7','#skF_2'('#skF_7'),k15_lattice3('#skF_7',B_478)) = '#skF_2'('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2856])).

tff(c_2831,plain,(
    ! [B_50] : k2_lattices('#skF_7',k15_lattice3('#skF_7',B_50),'#skF_2'('#skF_7')) = k2_lattices('#skF_7','#skF_2'('#skF_7'),k15_lattice3('#skF_7',B_50)) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2830])).

tff(c_2865,plain,(
    ! [B_50] : k2_lattices('#skF_7',k15_lattice3('#skF_7',B_50),'#skF_2'('#skF_7')) = '#skF_2'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2857,c_2831])).

tff(c_2564,plain,(
    ! [A_463,B_464,C_465] :
      ( r2_hidden('#skF_6'(A_463,B_464,C_465),B_464)
      | r3_lattices(A_463,k15_lattice3(A_463,B_464),k15_lattice3(A_463,C_465))
      | ~ l3_lattices(A_463)
      | ~ v4_lattice3(A_463)
      | ~ v10_lattices(A_463)
      | v2_struct_0(A_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_3387,plain,(
    ! [B_513,A_514,C_515] :
      ( ~ r1_tarski(B_513,'#skF_6'(A_514,B_513,C_515))
      | r3_lattices(A_514,k15_lattice3(A_514,B_513),k15_lattice3(A_514,C_515))
      | ~ l3_lattices(A_514)
      | ~ v4_lattice3(A_514)
      | ~ v10_lattices(A_514)
      | v2_struct_0(A_514) ) ),
    inference(resolution,[status(thm)],[c_2564,c_4])).

tff(c_3420,plain,(
    ! [A_519,C_520] :
      ( r3_lattices(A_519,k15_lattice3(A_519,k1_xboole_0),k15_lattice3(A_519,C_520))
      | ~ l3_lattices(A_519)
      | ~ v4_lattice3(A_519)
      | ~ v10_lattices(A_519)
      | v2_struct_0(A_519) ) ),
    inference(resolution,[status(thm)],[c_2,c_3387])).

tff(c_3820,plain,(
    ! [A_567,B_568] :
      ( r3_lattices(A_567,k15_lattice3(A_567,k1_xboole_0),B_568)
      | ~ l3_lattices(A_567)
      | ~ v4_lattice3(A_567)
      | ~ v10_lattices(A_567)
      | v2_struct_0(A_567)
      | ~ m1_subset_1(B_568,u1_struct_0(A_567))
      | ~ l3_lattices(A_567)
      | ~ v4_lattice3(A_567)
      | ~ v10_lattices(A_567)
      | v2_struct_0(A_567) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_3420])).

tff(c_4175,plain,(
    ! [A_603,B_604] :
      ( r1_lattices(A_603,k15_lattice3(A_603,k1_xboole_0),B_604)
      | ~ m1_subset_1(k15_lattice3(A_603,k1_xboole_0),u1_struct_0(A_603))
      | ~ v9_lattices(A_603)
      | ~ v8_lattices(A_603)
      | ~ v6_lattices(A_603)
      | ~ m1_subset_1(B_604,u1_struct_0(A_603))
      | ~ l3_lattices(A_603)
      | ~ v4_lattice3(A_603)
      | ~ v10_lattices(A_603)
      | v2_struct_0(A_603) ) ),
    inference(resolution,[status(thm)],[c_3820,c_36])).

tff(c_4180,plain,(
    ! [A_605,B_606] :
      ( r1_lattices(A_605,k15_lattice3(A_605,k1_xboole_0),B_606)
      | ~ v9_lattices(A_605)
      | ~ v8_lattices(A_605)
      | ~ v6_lattices(A_605)
      | ~ m1_subset_1(B_606,u1_struct_0(A_605))
      | ~ v4_lattice3(A_605)
      | ~ v10_lattices(A_605)
      | ~ l3_lattices(A_605)
      | v2_struct_0(A_605) ) ),
    inference(resolution,[status(thm)],[c_60,c_4175])).

tff(c_4293,plain,(
    ! [A_621,B_622] :
      ( k2_lattices(A_621,k15_lattice3(A_621,k1_xboole_0),B_622) = k15_lattice3(A_621,k1_xboole_0)
      | ~ m1_subset_1(k15_lattice3(A_621,k1_xboole_0),u1_struct_0(A_621))
      | ~ v9_lattices(A_621)
      | ~ v8_lattices(A_621)
      | ~ v6_lattices(A_621)
      | ~ m1_subset_1(B_622,u1_struct_0(A_621))
      | ~ v4_lattice3(A_621)
      | ~ v10_lattices(A_621)
      | ~ l3_lattices(A_621)
      | v2_struct_0(A_621) ) ),
    inference(resolution,[status(thm)],[c_4180,c_40])).

tff(c_4298,plain,(
    ! [A_623,B_624] :
      ( k2_lattices(A_623,k15_lattice3(A_623,k1_xboole_0),B_624) = k15_lattice3(A_623,k1_xboole_0)
      | ~ v9_lattices(A_623)
      | ~ v8_lattices(A_623)
      | ~ v6_lattices(A_623)
      | ~ m1_subset_1(B_624,u1_struct_0(A_623))
      | ~ v4_lattice3(A_623)
      | ~ v10_lattices(A_623)
      | ~ l3_lattices(A_623)
      | v2_struct_0(A_623) ) ),
    inference(resolution,[status(thm)],[c_60,c_4293])).

tff(c_4300,plain,
    ( k2_lattices('#skF_7',k15_lattice3('#skF_7',k1_xboole_0),'#skF_2'('#skF_7')) = k15_lattice3('#skF_7',k1_xboole_0)
    | ~ v9_lattices('#skF_7')
    | ~ v8_lattices('#skF_7')
    | ~ v6_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2685,c_4298])).

tff(c_4317,plain,
    ( k15_lattice3('#skF_7',k1_xboole_0) = '#skF_2'('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_78,c_76,c_2773,c_3434,c_3445,c_2865,c_4300])).

tff(c_4319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2658,c_4317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:59:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.79/2.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/2.64  
% 7.79/2.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/2.65  %$ r3_lattices > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k6_domain_1 > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_6 > #skF_7 > #skF_3 > #skF_1
% 7.79/2.65  
% 7.79/2.65  %Foreground sorts:
% 7.79/2.65  
% 7.79/2.65  
% 7.79/2.65  %Background operators:
% 7.79/2.65  
% 7.79/2.65  
% 7.79/2.65  %Foreground operators:
% 7.79/2.65  tff(l3_lattices, type, l3_lattices: $i > $o).
% 7.79/2.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.79/2.65  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 7.79/2.65  tff('#skF_5', type, '#skF_5': $i > $i).
% 7.79/2.65  tff(l2_lattices, type, l2_lattices: $i > $o).
% 7.79/2.65  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.79/2.65  tff('#skF_4', type, '#skF_4': $i > $i).
% 7.79/2.65  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 7.79/2.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.79/2.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.79/2.65  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 7.79/2.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.79/2.65  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 7.79/2.65  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 7.79/2.65  tff(l1_lattices, type, l1_lattices: $i > $o).
% 7.79/2.65  tff('#skF_7', type, '#skF_7': $i).
% 7.79/2.65  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.79/2.65  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 7.79/2.65  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 7.79/2.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.79/2.65  tff(v4_lattices, type, v4_lattices: $i > $o).
% 7.79/2.65  tff(v6_lattices, type, v6_lattices: $i > $o).
% 7.79/2.65  tff(v9_lattices, type, v9_lattices: $i > $o).
% 7.79/2.65  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 7.79/2.65  tff(v5_lattices, type, v5_lattices: $i > $o).
% 7.79/2.65  tff(v10_lattices, type, v10_lattices: $i > $o).
% 7.79/2.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.79/2.65  tff(v13_lattices, type, v13_lattices: $i > $o).
% 7.79/2.65  tff(v8_lattices, type, v8_lattices: $i > $o).
% 7.79/2.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.79/2.65  tff(k5_lattices, type, k5_lattices: $i > $i).
% 7.79/2.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.79/2.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.79/2.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.79/2.65  tff(v7_lattices, type, v7_lattices: $i > $o).
% 7.79/2.65  
% 8.02/2.67  tff(f_226, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) & (k5_lattices(A) = k15_lattice3(A, k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_lattice3)).
% 8.02/2.67  tff(f_86, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 8.02/2.67  tff(f_54, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 8.02/2.67  tff(f_163, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 8.02/2.67  tff(f_141, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_lattices)).
% 8.02/2.67  tff(f_179, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((k15_lattice3(A, k6_domain_1(u1_struct_0(A), B)) = B) & (k16_lattice3(A, k6_domain_1(u1_struct_0(A), B)) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_lattice3)).
% 8.02/2.67  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.02/2.67  tff(f_205, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: ((![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, B) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ~(r3_lattices(A, D, E) & r2_hidden(E, C))))))) => r3_lattices(A, k15_lattice3(A, B), k15_lattice3(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_lattice3)).
% 8.02/2.67  tff(f_32, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.02/2.67  tff(f_105, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 8.02/2.67  tff(f_124, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 8.02/2.67  tff(f_156, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v6_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, C) = k2_lattices(A, C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_lattices)).
% 8.02/2.67  tff(f_80, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 8.02/2.67  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 8.02/2.67  tff(c_80, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_226])).
% 8.02/2.67  tff(c_74, plain, (l3_lattices('#skF_7')), inference(cnfTransformation, [status(thm)], [f_226])).
% 8.02/2.67  tff(c_85, plain, (![A_71]: (l1_lattices(A_71) | ~l3_lattices(A_71))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.02/2.67  tff(c_89, plain, (l1_lattices('#skF_7')), inference(resolution, [status(thm)], [c_74, c_85])).
% 8.02/2.67  tff(c_78, plain, (v10_lattices('#skF_7')), inference(cnfTransformation, [status(thm)], [f_226])).
% 8.02/2.67  tff(c_72, plain, (k15_lattice3('#skF_7', k1_xboole_0)!=k5_lattices('#skF_7') | ~l3_lattices('#skF_7') | ~v13_lattices('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_226])).
% 8.02/2.67  tff(c_82, plain, (k15_lattice3('#skF_7', k1_xboole_0)!=k5_lattices('#skF_7') | ~v13_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72])).
% 8.02/2.67  tff(c_83, plain, (k15_lattice3('#skF_7', k1_xboole_0)!=k5_lattices('#skF_7') | ~v13_lattices('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_80, c_82])).
% 8.02/2.67  tff(c_95, plain, (~v13_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_83])).
% 8.02/2.67  tff(c_76, plain, (v4_lattice3('#skF_7')), inference(cnfTransformation, [status(thm)], [f_226])).
% 8.02/2.67  tff(c_12, plain, (![A_4]: (v6_lattices(A_4) | ~v10_lattices(A_4) | v2_struct_0(A_4) | ~l3_lattices(A_4))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.02/2.67  tff(c_8, plain, (![A_4]: (v8_lattices(A_4) | ~v10_lattices(A_4) | v2_struct_0(A_4) | ~l3_lattices(A_4))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.02/2.67  tff(c_6, plain, (![A_4]: (v9_lattices(A_4) | ~v10_lattices(A_4) | v2_struct_0(A_4) | ~l3_lattices(A_4))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.02/2.67  tff(c_60, plain, (![A_49, B_50]: (m1_subset_1(k15_lattice3(A_49, B_50), u1_struct_0(A_49)) | ~l3_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.02/2.67  tff(c_44, plain, (![A_27, B_36]: (m1_subset_1('#skF_3'(A_27, B_36), u1_struct_0(A_27)) | v13_lattices(A_27) | ~m1_subset_1(B_36, u1_struct_0(A_27)) | ~l1_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.02/2.67  tff(c_64, plain, (![A_51, B_53]: (k15_lattice3(A_51, k6_domain_1(u1_struct_0(A_51), B_53))=B_53 | ~m1_subset_1(B_53, u1_struct_0(A_51)) | ~l3_lattices(A_51) | ~v4_lattice3(A_51) | ~v10_lattices(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.02/2.67  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.02/2.67  tff(c_263, plain, (![A_111, B_112, C_113]: (r2_hidden('#skF_6'(A_111, B_112, C_113), B_112) | r3_lattices(A_111, k15_lattice3(A_111, B_112), k15_lattice3(A_111, C_113)) | ~l3_lattices(A_111) | ~v4_lattice3(A_111) | ~v10_lattices(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_205])).
% 8.02/2.67  tff(c_4, plain, (![B_3, A_2]: (~r1_tarski(B_3, A_2) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.02/2.67  tff(c_561, plain, (![B_153, A_154, C_155]: (~r1_tarski(B_153, '#skF_6'(A_154, B_153, C_155)) | r3_lattices(A_154, k15_lattice3(A_154, B_153), k15_lattice3(A_154, C_155)) | ~l3_lattices(A_154) | ~v4_lattice3(A_154) | ~v10_lattices(A_154) | v2_struct_0(A_154))), inference(resolution, [status(thm)], [c_263, c_4])).
% 8.02/2.67  tff(c_566, plain, (![A_156, C_157]: (r3_lattices(A_156, k15_lattice3(A_156, k1_xboole_0), k15_lattice3(A_156, C_157)) | ~l3_lattices(A_156) | ~v4_lattice3(A_156) | ~v10_lattices(A_156) | v2_struct_0(A_156))), inference(resolution, [status(thm)], [c_2, c_561])).
% 8.02/2.67  tff(c_813, plain, (![A_204, B_205]: (r3_lattices(A_204, k15_lattice3(A_204, k1_xboole_0), B_205) | ~l3_lattices(A_204) | ~v4_lattice3(A_204) | ~v10_lattices(A_204) | v2_struct_0(A_204) | ~m1_subset_1(B_205, u1_struct_0(A_204)) | ~l3_lattices(A_204) | ~v4_lattice3(A_204) | ~v10_lattices(A_204) | v2_struct_0(A_204))), inference(superposition, [status(thm), theory('equality')], [c_64, c_566])).
% 8.02/2.67  tff(c_36, plain, (![A_17, B_18, C_19]: (r1_lattices(A_17, B_18, C_19) | ~r3_lattices(A_17, B_18, C_19) | ~m1_subset_1(C_19, u1_struct_0(A_17)) | ~m1_subset_1(B_18, u1_struct_0(A_17)) | ~l3_lattices(A_17) | ~v9_lattices(A_17) | ~v8_lattices(A_17) | ~v6_lattices(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.02/2.67  tff(c_1049, plain, (![A_239, B_240]: (r1_lattices(A_239, k15_lattice3(A_239, k1_xboole_0), B_240) | ~m1_subset_1(k15_lattice3(A_239, k1_xboole_0), u1_struct_0(A_239)) | ~v9_lattices(A_239) | ~v8_lattices(A_239) | ~v6_lattices(A_239) | ~m1_subset_1(B_240, u1_struct_0(A_239)) | ~l3_lattices(A_239) | ~v4_lattice3(A_239) | ~v10_lattices(A_239) | v2_struct_0(A_239))), inference(resolution, [status(thm)], [c_813, c_36])).
% 8.02/2.67  tff(c_1054, plain, (![A_241, B_242]: (r1_lattices(A_241, k15_lattice3(A_241, k1_xboole_0), B_242) | ~v9_lattices(A_241) | ~v8_lattices(A_241) | ~v6_lattices(A_241) | ~m1_subset_1(B_242, u1_struct_0(A_241)) | ~v4_lattice3(A_241) | ~v10_lattices(A_241) | ~l3_lattices(A_241) | v2_struct_0(A_241))), inference(resolution, [status(thm)], [c_60, c_1049])).
% 8.02/2.67  tff(c_40, plain, (![A_20, B_24, C_26]: (k2_lattices(A_20, B_24, C_26)=B_24 | ~r1_lattices(A_20, B_24, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_20)) | ~m1_subset_1(B_24, u1_struct_0(A_20)) | ~l3_lattices(A_20) | ~v9_lattices(A_20) | ~v8_lattices(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.02/2.67  tff(c_1135, plain, (![A_255, B_256]: (k2_lattices(A_255, k15_lattice3(A_255, k1_xboole_0), B_256)=k15_lattice3(A_255, k1_xboole_0) | ~m1_subset_1(k15_lattice3(A_255, k1_xboole_0), u1_struct_0(A_255)) | ~v9_lattices(A_255) | ~v8_lattices(A_255) | ~v6_lattices(A_255) | ~m1_subset_1(B_256, u1_struct_0(A_255)) | ~v4_lattice3(A_255) | ~v10_lattices(A_255) | ~l3_lattices(A_255) | v2_struct_0(A_255))), inference(resolution, [status(thm)], [c_1054, c_40])).
% 8.02/2.67  tff(c_1140, plain, (![A_257, B_258]: (k2_lattices(A_257, k15_lattice3(A_257, k1_xboole_0), B_258)=k15_lattice3(A_257, k1_xboole_0) | ~v9_lattices(A_257) | ~v8_lattices(A_257) | ~v6_lattices(A_257) | ~m1_subset_1(B_258, u1_struct_0(A_257)) | ~v4_lattice3(A_257) | ~v10_lattices(A_257) | ~l3_lattices(A_257) | v2_struct_0(A_257))), inference(resolution, [status(thm)], [c_60, c_1135])).
% 8.02/2.67  tff(c_1156, plain, (![A_27, B_36]: (k2_lattices(A_27, k15_lattice3(A_27, k1_xboole_0), '#skF_3'(A_27, B_36))=k15_lattice3(A_27, k1_xboole_0) | ~v9_lattices(A_27) | ~v8_lattices(A_27) | ~v6_lattices(A_27) | ~v4_lattice3(A_27) | ~v10_lattices(A_27) | ~l3_lattices(A_27) | v13_lattices(A_27) | ~m1_subset_1(B_36, u1_struct_0(A_27)) | ~l1_lattices(A_27) | v2_struct_0(A_27))), inference(resolution, [status(thm)], [c_44, c_1140])).
% 8.02/2.67  tff(c_68, plain, (![A_54, B_63, C_64]: (r2_hidden('#skF_6'(A_54, B_63, C_64), B_63) | r3_lattices(A_54, k15_lattice3(A_54, B_63), k15_lattice3(A_54, C_64)) | ~l3_lattices(A_54) | ~v4_lattice3(A_54) | ~v10_lattices(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_205])).
% 8.02/2.67  tff(c_596, plain, (![A_164, B_165, C_166]: (r1_lattices(A_164, B_165, C_166) | ~r3_lattices(A_164, B_165, C_166) | ~m1_subset_1(C_166, u1_struct_0(A_164)) | ~m1_subset_1(B_165, u1_struct_0(A_164)) | ~l3_lattices(A_164) | ~v9_lattices(A_164) | ~v8_lattices(A_164) | ~v6_lattices(A_164) | v2_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.02/2.67  tff(c_1770, plain, (![A_341, B_342, C_343]: (r1_lattices(A_341, k15_lattice3(A_341, B_342), k15_lattice3(A_341, C_343)) | ~m1_subset_1(k15_lattice3(A_341, C_343), u1_struct_0(A_341)) | ~m1_subset_1(k15_lattice3(A_341, B_342), u1_struct_0(A_341)) | ~v9_lattices(A_341) | ~v8_lattices(A_341) | ~v6_lattices(A_341) | r2_hidden('#skF_6'(A_341, B_342, C_343), B_342) | ~l3_lattices(A_341) | ~v4_lattice3(A_341) | ~v10_lattices(A_341) | v2_struct_0(A_341))), inference(resolution, [status(thm)], [c_68, c_596])).
% 8.02/2.67  tff(c_1996, plain, (![A_382, B_383, C_384]: (k2_lattices(A_382, k15_lattice3(A_382, B_383), k15_lattice3(A_382, C_384))=k15_lattice3(A_382, B_383) | ~m1_subset_1(k15_lattice3(A_382, C_384), u1_struct_0(A_382)) | ~m1_subset_1(k15_lattice3(A_382, B_383), u1_struct_0(A_382)) | ~v9_lattices(A_382) | ~v8_lattices(A_382) | ~v6_lattices(A_382) | r2_hidden('#skF_6'(A_382, B_383, C_384), B_383) | ~l3_lattices(A_382) | ~v4_lattice3(A_382) | ~v10_lattices(A_382) | v2_struct_0(A_382))), inference(resolution, [status(thm)], [c_1770, c_40])).
% 8.02/2.67  tff(c_2002, plain, (![A_385, B_386, B_387]: (k2_lattices(A_385, k15_lattice3(A_385, B_386), k15_lattice3(A_385, B_387))=k15_lattice3(A_385, B_386) | ~m1_subset_1(k15_lattice3(A_385, B_386), u1_struct_0(A_385)) | ~v9_lattices(A_385) | ~v8_lattices(A_385) | ~v6_lattices(A_385) | r2_hidden('#skF_6'(A_385, B_386, B_387), B_386) | ~v4_lattice3(A_385) | ~v10_lattices(A_385) | ~l3_lattices(A_385) | v2_struct_0(A_385))), inference(resolution, [status(thm)], [c_60, c_1996])).
% 8.02/2.67  tff(c_2008, plain, (![A_388, B_389, B_390]: (k2_lattices(A_388, k15_lattice3(A_388, B_389), k15_lattice3(A_388, B_390))=k15_lattice3(A_388, B_389) | ~v9_lattices(A_388) | ~v8_lattices(A_388) | ~v6_lattices(A_388) | r2_hidden('#skF_6'(A_388, B_389, B_390), B_389) | ~v4_lattice3(A_388) | ~v10_lattices(A_388) | ~l3_lattices(A_388) | v2_struct_0(A_388))), inference(resolution, [status(thm)], [c_60, c_2002])).
% 8.02/2.67  tff(c_357, plain, (![A_122, C_123, B_124]: (k2_lattices(A_122, C_123, B_124)=k2_lattices(A_122, B_124, C_123) | ~m1_subset_1(C_123, u1_struct_0(A_122)) | ~m1_subset_1(B_124, u1_struct_0(A_122)) | ~v6_lattices(A_122) | ~l1_lattices(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.02/2.67  tff(c_672, plain, (![A_178, B_179, B_180]: (k2_lattices(A_178, k15_lattice3(A_178, B_179), B_180)=k2_lattices(A_178, B_180, k15_lattice3(A_178, B_179)) | ~m1_subset_1(B_180, u1_struct_0(A_178)) | ~v6_lattices(A_178) | ~l1_lattices(A_178) | ~l3_lattices(A_178) | v2_struct_0(A_178))), inference(resolution, [status(thm)], [c_60, c_357])).
% 8.02/2.67  tff(c_692, plain, (![A_49, B_50, B_179]: (k2_lattices(A_49, k15_lattice3(A_49, B_50), k15_lattice3(A_49, B_179))=k2_lattices(A_49, k15_lattice3(A_49, B_179), k15_lattice3(A_49, B_50)) | ~v6_lattices(A_49) | ~l1_lattices(A_49) | ~l3_lattices(A_49) | v2_struct_0(A_49))), inference(resolution, [status(thm)], [c_60, c_672])).
% 8.02/2.67  tff(c_2089, plain, (![A_397, B_398, B_399]: (k2_lattices(A_397, k15_lattice3(A_397, B_398), k15_lattice3(A_397, B_399))=k15_lattice3(A_397, B_399) | ~v6_lattices(A_397) | ~l1_lattices(A_397) | ~l3_lattices(A_397) | v2_struct_0(A_397) | ~v9_lattices(A_397) | ~v8_lattices(A_397) | ~v6_lattices(A_397) | r2_hidden('#skF_6'(A_397, B_399, B_398), B_399) | ~v4_lattice3(A_397) | ~v10_lattices(A_397) | ~l3_lattices(A_397) | v2_struct_0(A_397))), inference(superposition, [status(thm), theory('equality')], [c_2008, c_692])).
% 8.02/2.67  tff(c_2170, plain, (![B_403, A_404, B_405]: (~r1_tarski(B_403, '#skF_6'(A_404, B_403, B_405)) | k2_lattices(A_404, k15_lattice3(A_404, B_405), k15_lattice3(A_404, B_403))=k15_lattice3(A_404, B_403) | ~l1_lattices(A_404) | ~v9_lattices(A_404) | ~v8_lattices(A_404) | ~v6_lattices(A_404) | ~v4_lattice3(A_404) | ~v10_lattices(A_404) | ~l3_lattices(A_404) | v2_struct_0(A_404))), inference(resolution, [status(thm)], [c_2089, c_4])).
% 8.02/2.67  tff(c_2175, plain, (![A_406, B_407]: (k2_lattices(A_406, k15_lattice3(A_406, B_407), k15_lattice3(A_406, k1_xboole_0))=k15_lattice3(A_406, k1_xboole_0) | ~l1_lattices(A_406) | ~v9_lattices(A_406) | ~v8_lattices(A_406) | ~v6_lattices(A_406) | ~v4_lattice3(A_406) | ~v10_lattices(A_406) | ~l3_lattices(A_406) | v2_struct_0(A_406))), inference(resolution, [status(thm)], [c_2, c_2170])).
% 8.02/2.67  tff(c_2235, plain, (![A_408, B_409]: (k2_lattices(A_408, B_409, k15_lattice3(A_408, k1_xboole_0))=k15_lattice3(A_408, k1_xboole_0) | ~l1_lattices(A_408) | ~v9_lattices(A_408) | ~v8_lattices(A_408) | ~v6_lattices(A_408) | ~v4_lattice3(A_408) | ~v10_lattices(A_408) | ~l3_lattices(A_408) | v2_struct_0(A_408) | ~m1_subset_1(B_409, u1_struct_0(A_408)) | ~l3_lattices(A_408) | ~v4_lattice3(A_408) | ~v10_lattices(A_408) | v2_struct_0(A_408))), inference(superposition, [status(thm), theory('equality')], [c_64, c_2175])).
% 8.02/2.67  tff(c_2295, plain, (![A_412, B_413]: (k2_lattices(A_412, '#skF_3'(A_412, B_413), k15_lattice3(A_412, k1_xboole_0))=k15_lattice3(A_412, k1_xboole_0) | ~v9_lattices(A_412) | ~v8_lattices(A_412) | ~v6_lattices(A_412) | ~l3_lattices(A_412) | ~v4_lattice3(A_412) | ~v10_lattices(A_412) | v13_lattices(A_412) | ~m1_subset_1(B_413, u1_struct_0(A_412)) | ~l1_lattices(A_412) | v2_struct_0(A_412))), inference(resolution, [status(thm)], [c_44, c_2235])).
% 8.02/2.67  tff(c_42, plain, (![A_27, B_36]: (k2_lattices(A_27, '#skF_3'(A_27, B_36), B_36)!=B_36 | k2_lattices(A_27, B_36, '#skF_3'(A_27, B_36))!=B_36 | v13_lattices(A_27) | ~m1_subset_1(B_36, u1_struct_0(A_27)) | ~l1_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.02/2.67  tff(c_2336, plain, (![A_416]: (k2_lattices(A_416, k15_lattice3(A_416, k1_xboole_0), '#skF_3'(A_416, k15_lattice3(A_416, k1_xboole_0)))!=k15_lattice3(A_416, k1_xboole_0) | ~v9_lattices(A_416) | ~v8_lattices(A_416) | ~v6_lattices(A_416) | ~l3_lattices(A_416) | ~v4_lattice3(A_416) | ~v10_lattices(A_416) | v13_lattices(A_416) | ~m1_subset_1(k15_lattice3(A_416, k1_xboole_0), u1_struct_0(A_416)) | ~l1_lattices(A_416) | v2_struct_0(A_416))), inference(superposition, [status(thm), theory('equality')], [c_2295, c_42])).
% 8.02/2.67  tff(c_2342, plain, (![A_417]: (~v9_lattices(A_417) | ~v8_lattices(A_417) | ~v6_lattices(A_417) | ~v4_lattice3(A_417) | ~v10_lattices(A_417) | ~l3_lattices(A_417) | v13_lattices(A_417) | ~m1_subset_1(k15_lattice3(A_417, k1_xboole_0), u1_struct_0(A_417)) | ~l1_lattices(A_417) | v2_struct_0(A_417))), inference(superposition, [status(thm), theory('equality')], [c_1156, c_2336])).
% 8.02/2.67  tff(c_2371, plain, (![A_421]: (~v9_lattices(A_421) | ~v8_lattices(A_421) | ~v6_lattices(A_421) | ~v4_lattice3(A_421) | ~v10_lattices(A_421) | v13_lattices(A_421) | ~l1_lattices(A_421) | ~l3_lattices(A_421) | v2_struct_0(A_421))), inference(resolution, [status(thm)], [c_60, c_2342])).
% 8.02/2.67  tff(c_2376, plain, (![A_422]: (~v8_lattices(A_422) | ~v6_lattices(A_422) | ~v4_lattice3(A_422) | v13_lattices(A_422) | ~l1_lattices(A_422) | ~v10_lattices(A_422) | v2_struct_0(A_422) | ~l3_lattices(A_422))), inference(resolution, [status(thm)], [c_6, c_2371])).
% 8.02/2.67  tff(c_2381, plain, (![A_423]: (~v6_lattices(A_423) | ~v4_lattice3(A_423) | v13_lattices(A_423) | ~l1_lattices(A_423) | ~v10_lattices(A_423) | v2_struct_0(A_423) | ~l3_lattices(A_423))), inference(resolution, [status(thm)], [c_8, c_2376])).
% 8.02/2.67  tff(c_2386, plain, (![A_424]: (~v4_lattice3(A_424) | v13_lattices(A_424) | ~l1_lattices(A_424) | ~v10_lattices(A_424) | v2_struct_0(A_424) | ~l3_lattices(A_424))), inference(resolution, [status(thm)], [c_12, c_2381])).
% 8.02/2.67  tff(c_2389, plain, (v13_lattices('#skF_7') | ~l1_lattices('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7')), inference(resolution, [status(thm)], [c_76, c_2386])).
% 8.02/2.67  tff(c_2392, plain, (v13_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_78, c_89, c_2389])).
% 8.02/2.67  tff(c_2394, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_95, c_2392])).
% 8.02/2.67  tff(c_2396, plain, (v13_lattices('#skF_7')), inference(splitRight, [status(thm)], [c_83])).
% 8.02/2.67  tff(c_28, plain, (![A_15]: (m1_subset_1(k5_lattices(A_15), u1_struct_0(A_15)) | ~l1_lattices(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.02/2.67  tff(c_46, plain, (![A_27]: (m1_subset_1('#skF_2'(A_27), u1_struct_0(A_27)) | ~v13_lattices(A_27) | ~l1_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.02/2.67  tff(c_2575, plain, (![A_466, C_467]: (k2_lattices(A_466, k5_lattices(A_466), C_467)=k5_lattices(A_466) | ~m1_subset_1(C_467, u1_struct_0(A_466)) | ~m1_subset_1(k5_lattices(A_466), u1_struct_0(A_466)) | ~v13_lattices(A_466) | ~l1_lattices(A_466) | v2_struct_0(A_466))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.02/2.67  tff(c_2597, plain, (![A_468]: (k2_lattices(A_468, k5_lattices(A_468), '#skF_2'(A_468))=k5_lattices(A_468) | ~m1_subset_1(k5_lattices(A_468), u1_struct_0(A_468)) | ~v13_lattices(A_468) | ~l1_lattices(A_468) | v2_struct_0(A_468))), inference(resolution, [status(thm)], [c_46, c_2575])).
% 8.02/2.67  tff(c_2601, plain, (![A_469]: (k2_lattices(A_469, k5_lattices(A_469), '#skF_2'(A_469))=k5_lattices(A_469) | ~v13_lattices(A_469) | ~l1_lattices(A_469) | v2_struct_0(A_469))), inference(resolution, [status(thm)], [c_28, c_2597])).
% 8.02/2.67  tff(c_2456, plain, (![A_446, C_447]: (k2_lattices(A_446, C_447, '#skF_2'(A_446))='#skF_2'(A_446) | ~m1_subset_1(C_447, u1_struct_0(A_446)) | ~v13_lattices(A_446) | ~l1_lattices(A_446) | v2_struct_0(A_446))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.02/2.67  tff(c_2474, plain, (![A_15]: (k2_lattices(A_15, k5_lattices(A_15), '#skF_2'(A_15))='#skF_2'(A_15) | ~v13_lattices(A_15) | ~l1_lattices(A_15) | v2_struct_0(A_15))), inference(resolution, [status(thm)], [c_28, c_2456])).
% 8.02/2.67  tff(c_2607, plain, (![A_469]: (k5_lattices(A_469)='#skF_2'(A_469) | ~v13_lattices(A_469) | ~l1_lattices(A_469) | v2_struct_0(A_469) | ~v13_lattices(A_469) | ~l1_lattices(A_469) | v2_struct_0(A_469))), inference(superposition, [status(thm), theory('equality')], [c_2601, c_2474])).
% 8.02/2.67  tff(c_2651, plain, (![A_473]: (k5_lattices(A_473)='#skF_2'(A_473) | ~v13_lattices(A_473) | ~l1_lattices(A_473) | v2_struct_0(A_473))), inference(factorization, [status(thm), theory('equality')], [c_2607])).
% 8.02/2.67  tff(c_2654, plain, (k5_lattices('#skF_7')='#skF_2'('#skF_7') | ~v13_lattices('#skF_7') | ~l1_lattices('#skF_7')), inference(resolution, [status(thm)], [c_2651, c_80])).
% 8.02/2.67  tff(c_2657, plain, (k5_lattices('#skF_7')='#skF_2'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_2396, c_2654])).
% 8.02/2.67  tff(c_2395, plain, (k15_lattice3('#skF_7', k1_xboole_0)!=k5_lattices('#skF_7')), inference(splitRight, [status(thm)], [c_83])).
% 8.02/2.67  tff(c_2658, plain, (k15_lattice3('#skF_7', k1_xboole_0)!='#skF_2'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2657, c_2395])).
% 8.02/2.67  tff(c_2671, plain, (m1_subset_1('#skF_2'('#skF_7'), u1_struct_0('#skF_7')) | ~l1_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2657, c_28])).
% 8.02/2.67  tff(c_2684, plain, (m1_subset_1('#skF_2'('#skF_7'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_2671])).
% 8.02/2.67  tff(c_2685, plain, (m1_subset_1('#skF_2'('#skF_7'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_80, c_2684])).
% 8.02/2.67  tff(c_2733, plain, (![A_474, C_475, B_476]: (k2_lattices(A_474, C_475, B_476)=k2_lattices(A_474, B_476, C_475) | ~m1_subset_1(C_475, u1_struct_0(A_474)) | ~m1_subset_1(B_476, u1_struct_0(A_474)) | ~v6_lattices(A_474) | ~l1_lattices(A_474) | v2_struct_0(A_474))), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.02/2.67  tff(c_2735, plain, (![B_476]: (k2_lattices('#skF_7', B_476, '#skF_2'('#skF_7'))=k2_lattices('#skF_7', '#skF_2'('#skF_7'), B_476) | ~m1_subset_1(B_476, u1_struct_0('#skF_7')) | ~v6_lattices('#skF_7') | ~l1_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_2685, c_2733])).
% 8.02/2.67  tff(c_2752, plain, (![B_476]: (k2_lattices('#skF_7', B_476, '#skF_2'('#skF_7'))=k2_lattices('#skF_7', '#skF_2'('#skF_7'), B_476) | ~m1_subset_1(B_476, u1_struct_0('#skF_7')) | ~v6_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_2735])).
% 8.02/2.67  tff(c_2753, plain, (![B_476]: (k2_lattices('#skF_7', B_476, '#skF_2'('#skF_7'))=k2_lattices('#skF_7', '#skF_2'('#skF_7'), B_476) | ~m1_subset_1(B_476, u1_struct_0('#skF_7')) | ~v6_lattices('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_80, c_2752])).
% 8.02/2.67  tff(c_2763, plain, (~v6_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_2753])).
% 8.02/2.67  tff(c_2766, plain, (~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7')), inference(resolution, [status(thm)], [c_12, c_2763])).
% 8.02/2.67  tff(c_2769, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_78, c_2766])).
% 8.02/2.67  tff(c_2771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_2769])).
% 8.02/2.67  tff(c_2773, plain, (v6_lattices('#skF_7')), inference(splitRight, [status(thm)], [c_2753])).
% 8.02/2.67  tff(c_3392, plain, (![A_516, B_517, C_518]: (r1_lattices(A_516, B_517, C_518) | k2_lattices(A_516, B_517, C_518)!=B_517 | ~m1_subset_1(C_518, u1_struct_0(A_516)) | ~m1_subset_1(B_517, u1_struct_0(A_516)) | ~l3_lattices(A_516) | ~v9_lattices(A_516) | ~v8_lattices(A_516) | v2_struct_0(A_516))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.02/2.67  tff(c_3394, plain, (![B_517]: (r1_lattices('#skF_7', B_517, '#skF_2'('#skF_7')) | k2_lattices('#skF_7', B_517, '#skF_2'('#skF_7'))!=B_517 | ~m1_subset_1(B_517, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_2685, c_3392])).
% 8.02/2.67  tff(c_3411, plain, (![B_517]: (r1_lattices('#skF_7', B_517, '#skF_2'('#skF_7')) | k2_lattices('#skF_7', B_517, '#skF_2'('#skF_7'))!=B_517 | ~m1_subset_1(B_517, u1_struct_0('#skF_7')) | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3394])).
% 8.02/2.67  tff(c_3412, plain, (![B_517]: (r1_lattices('#skF_7', B_517, '#skF_2'('#skF_7')) | k2_lattices('#skF_7', B_517, '#skF_2'('#skF_7'))!=B_517 | ~m1_subset_1(B_517, u1_struct_0('#skF_7')) | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_80, c_3411])).
% 8.02/2.67  tff(c_3424, plain, (~v8_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_3412])).
% 8.02/2.67  tff(c_3427, plain, (~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7')), inference(resolution, [status(thm)], [c_8, c_3424])).
% 8.02/2.67  tff(c_3430, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_78, c_3427])).
% 8.02/2.67  tff(c_3432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_3430])).
% 8.02/2.67  tff(c_3434, plain, (v8_lattices('#skF_7')), inference(splitRight, [status(thm)], [c_3412])).
% 8.02/2.67  tff(c_3433, plain, (![B_517]: (~v9_lattices('#skF_7') | r1_lattices('#skF_7', B_517, '#skF_2'('#skF_7')) | k2_lattices('#skF_7', B_517, '#skF_2'('#skF_7'))!=B_517 | ~m1_subset_1(B_517, u1_struct_0('#skF_7')))), inference(splitRight, [status(thm)], [c_3412])).
% 8.02/2.67  tff(c_3435, plain, (~v9_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_3433])).
% 8.02/2.67  tff(c_3438, plain, (~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7')), inference(resolution, [status(thm)], [c_6, c_3435])).
% 8.02/2.67  tff(c_3441, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_78, c_3438])).
% 8.02/2.67  tff(c_3443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_3441])).
% 8.02/2.67  tff(c_3445, plain, (v9_lattices('#skF_7')), inference(splitRight, [status(thm)], [c_3433])).
% 8.02/2.67  tff(c_2774, plain, (![B_477]: (k2_lattices('#skF_7', B_477, '#skF_2'('#skF_7'))=k2_lattices('#skF_7', '#skF_2'('#skF_7'), B_477) | ~m1_subset_1(B_477, u1_struct_0('#skF_7')))), inference(splitRight, [status(thm)], [c_2753])).
% 8.02/2.67  tff(c_2801, plain, (![B_50]: (k2_lattices('#skF_7', k15_lattice3('#skF_7', B_50), '#skF_2'('#skF_7'))=k2_lattices('#skF_7', '#skF_2'('#skF_7'), k15_lattice3('#skF_7', B_50)) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_60, c_2774])).
% 8.02/2.67  tff(c_2830, plain, (![B_50]: (k2_lattices('#skF_7', k15_lattice3('#skF_7', B_50), '#skF_2'('#skF_7'))=k2_lattices('#skF_7', '#skF_2'('#skF_7'), k15_lattice3('#skF_7', B_50)) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2801])).
% 8.02/2.67  tff(c_2836, plain, (![B_478]: (k2_lattices('#skF_7', k15_lattice3('#skF_7', B_478), '#skF_2'('#skF_7'))=k2_lattices('#skF_7', '#skF_2'('#skF_7'), k15_lattice3('#skF_7', B_478)))), inference(negUnitSimplification, [status(thm)], [c_80, c_2830])).
% 8.02/2.67  tff(c_2473, plain, (![A_49, B_50]: (k2_lattices(A_49, k15_lattice3(A_49, B_50), '#skF_2'(A_49))='#skF_2'(A_49) | ~v13_lattices(A_49) | ~l1_lattices(A_49) | ~l3_lattices(A_49) | v2_struct_0(A_49))), inference(resolution, [status(thm)], [c_60, c_2456])).
% 8.02/2.67  tff(c_2842, plain, (![B_478]: (k2_lattices('#skF_7', '#skF_2'('#skF_7'), k15_lattice3('#skF_7', B_478))='#skF_2'('#skF_7') | ~v13_lattices('#skF_7') | ~l1_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2836, c_2473])).
% 8.02/2.67  tff(c_2856, plain, (![B_478]: (k2_lattices('#skF_7', '#skF_2'('#skF_7'), k15_lattice3('#skF_7', B_478))='#skF_2'('#skF_7') | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_89, c_2396, c_2842])).
% 8.02/2.67  tff(c_2857, plain, (![B_478]: (k2_lattices('#skF_7', '#skF_2'('#skF_7'), k15_lattice3('#skF_7', B_478))='#skF_2'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_80, c_2856])).
% 8.02/2.67  tff(c_2831, plain, (![B_50]: (k2_lattices('#skF_7', k15_lattice3('#skF_7', B_50), '#skF_2'('#skF_7'))=k2_lattices('#skF_7', '#skF_2'('#skF_7'), k15_lattice3('#skF_7', B_50)))), inference(negUnitSimplification, [status(thm)], [c_80, c_2830])).
% 8.02/2.67  tff(c_2865, plain, (![B_50]: (k2_lattices('#skF_7', k15_lattice3('#skF_7', B_50), '#skF_2'('#skF_7'))='#skF_2'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2857, c_2831])).
% 8.02/2.67  tff(c_2564, plain, (![A_463, B_464, C_465]: (r2_hidden('#skF_6'(A_463, B_464, C_465), B_464) | r3_lattices(A_463, k15_lattice3(A_463, B_464), k15_lattice3(A_463, C_465)) | ~l3_lattices(A_463) | ~v4_lattice3(A_463) | ~v10_lattices(A_463) | v2_struct_0(A_463))), inference(cnfTransformation, [status(thm)], [f_205])).
% 8.02/2.67  tff(c_3387, plain, (![B_513, A_514, C_515]: (~r1_tarski(B_513, '#skF_6'(A_514, B_513, C_515)) | r3_lattices(A_514, k15_lattice3(A_514, B_513), k15_lattice3(A_514, C_515)) | ~l3_lattices(A_514) | ~v4_lattice3(A_514) | ~v10_lattices(A_514) | v2_struct_0(A_514))), inference(resolution, [status(thm)], [c_2564, c_4])).
% 8.02/2.67  tff(c_3420, plain, (![A_519, C_520]: (r3_lattices(A_519, k15_lattice3(A_519, k1_xboole_0), k15_lattice3(A_519, C_520)) | ~l3_lattices(A_519) | ~v4_lattice3(A_519) | ~v10_lattices(A_519) | v2_struct_0(A_519))), inference(resolution, [status(thm)], [c_2, c_3387])).
% 8.02/2.67  tff(c_3820, plain, (![A_567, B_568]: (r3_lattices(A_567, k15_lattice3(A_567, k1_xboole_0), B_568) | ~l3_lattices(A_567) | ~v4_lattice3(A_567) | ~v10_lattices(A_567) | v2_struct_0(A_567) | ~m1_subset_1(B_568, u1_struct_0(A_567)) | ~l3_lattices(A_567) | ~v4_lattice3(A_567) | ~v10_lattices(A_567) | v2_struct_0(A_567))), inference(superposition, [status(thm), theory('equality')], [c_64, c_3420])).
% 8.02/2.67  tff(c_4175, plain, (![A_603, B_604]: (r1_lattices(A_603, k15_lattice3(A_603, k1_xboole_0), B_604) | ~m1_subset_1(k15_lattice3(A_603, k1_xboole_0), u1_struct_0(A_603)) | ~v9_lattices(A_603) | ~v8_lattices(A_603) | ~v6_lattices(A_603) | ~m1_subset_1(B_604, u1_struct_0(A_603)) | ~l3_lattices(A_603) | ~v4_lattice3(A_603) | ~v10_lattices(A_603) | v2_struct_0(A_603))), inference(resolution, [status(thm)], [c_3820, c_36])).
% 8.02/2.67  tff(c_4180, plain, (![A_605, B_606]: (r1_lattices(A_605, k15_lattice3(A_605, k1_xboole_0), B_606) | ~v9_lattices(A_605) | ~v8_lattices(A_605) | ~v6_lattices(A_605) | ~m1_subset_1(B_606, u1_struct_0(A_605)) | ~v4_lattice3(A_605) | ~v10_lattices(A_605) | ~l3_lattices(A_605) | v2_struct_0(A_605))), inference(resolution, [status(thm)], [c_60, c_4175])).
% 8.02/2.67  tff(c_4293, plain, (![A_621, B_622]: (k2_lattices(A_621, k15_lattice3(A_621, k1_xboole_0), B_622)=k15_lattice3(A_621, k1_xboole_0) | ~m1_subset_1(k15_lattice3(A_621, k1_xboole_0), u1_struct_0(A_621)) | ~v9_lattices(A_621) | ~v8_lattices(A_621) | ~v6_lattices(A_621) | ~m1_subset_1(B_622, u1_struct_0(A_621)) | ~v4_lattice3(A_621) | ~v10_lattices(A_621) | ~l3_lattices(A_621) | v2_struct_0(A_621))), inference(resolution, [status(thm)], [c_4180, c_40])).
% 8.02/2.67  tff(c_4298, plain, (![A_623, B_624]: (k2_lattices(A_623, k15_lattice3(A_623, k1_xboole_0), B_624)=k15_lattice3(A_623, k1_xboole_0) | ~v9_lattices(A_623) | ~v8_lattices(A_623) | ~v6_lattices(A_623) | ~m1_subset_1(B_624, u1_struct_0(A_623)) | ~v4_lattice3(A_623) | ~v10_lattices(A_623) | ~l3_lattices(A_623) | v2_struct_0(A_623))), inference(resolution, [status(thm)], [c_60, c_4293])).
% 8.02/2.67  tff(c_4300, plain, (k2_lattices('#skF_7', k15_lattice3('#skF_7', k1_xboole_0), '#skF_2'('#skF_7'))=k15_lattice3('#skF_7', k1_xboole_0) | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | ~v6_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_2685, c_4298])).
% 8.02/2.67  tff(c_4317, plain, (k15_lattice3('#skF_7', k1_xboole_0)='#skF_2'('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_78, c_76, c_2773, c_3434, c_3445, c_2865, c_4300])).
% 8.02/2.67  tff(c_4319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_2658, c_4317])).
% 8.02/2.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.02/2.67  
% 8.02/2.67  Inference rules
% 8.02/2.67  ----------------------
% 8.02/2.67  #Ref     : 0
% 8.02/2.67  #Sup     : 1011
% 8.02/2.67  #Fact    : 4
% 8.02/2.67  #Define  : 0
% 8.02/2.67  #Split   : 4
% 8.02/2.67  #Chain   : 0
% 8.02/2.67  #Close   : 0
% 8.02/2.67  
% 8.02/2.67  Ordering : KBO
% 8.02/2.67  
% 8.02/2.67  Simplification rules
% 8.02/2.67  ----------------------
% 8.02/2.67  #Subsume      : 246
% 8.02/2.67  #Demod        : 454
% 8.02/2.67  #Tautology    : 440
% 8.02/2.67  #SimpNegUnit  : 115
% 8.02/2.67  #BackRed      : 2
% 8.02/2.67  
% 8.02/2.67  #Partial instantiations: 0
% 8.02/2.67  #Strategies tried      : 1
% 8.02/2.67  
% 8.02/2.67  Timing (in seconds)
% 8.02/2.67  ----------------------
% 8.02/2.68  Preprocessing        : 0.39
% 8.02/2.68  Parsing              : 0.21
% 8.02/2.68  CNF conversion       : 0.03
% 8.02/2.68  Main loop            : 1.45
% 8.02/2.68  Inferencing          : 0.64
% 8.02/2.68  Reduction            : 0.32
% 8.02/2.68  Demodulation         : 0.20
% 8.02/2.68  BG Simplification    : 0.09
% 8.02/2.68  Subsumption          : 0.31
% 8.02/2.68  Abstraction          : 0.07
% 8.02/2.68  MUC search           : 0.00
% 8.02/2.68  Cooper               : 0.00
% 8.02/2.68  Total                : 1.89
% 8.02/2.68  Index Insertion      : 0.00
% 8.02/2.68  Index Deletion       : 0.00
% 8.02/2.68  Index Matching       : 0.00
% 8.02/2.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
