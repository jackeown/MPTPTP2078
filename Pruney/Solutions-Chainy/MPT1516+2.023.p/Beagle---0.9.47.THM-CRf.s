%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:54 EST 2020

% Result     : Theorem 11.76s
% Output     : CNFRefutation 11.76s
% Verified   : 
% Statistics : Number of formulae       :  179 (1251 expanded)
%              Number of leaves         :   53 ( 446 expanded)
%              Depth                    :   29
%              Number of atoms          :  685 (5261 expanded)
%              Number of equality atoms :   71 ( 664 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > k6_domain_1 > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_7 > #skF_2 > #skF_4 > #skF_9 > #skF_3 > #skF_8 > #skF_1 > #skF_5 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

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

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(k5_lattices,type,(
    k5_lattices: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_237,negated_conjecture,(
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

tff(f_174,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_116,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).

tff(f_190,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( k15_lattice3(A,k6_domain_1(u1_struct_0(A),B)) = B
            & k16_lattice3(A,k6_domain_1(u1_struct_0(A),B)) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattice3)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_216,axiom,(
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

tff(f_135,axiom,(
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

tff(f_88,axiom,(
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

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v9_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k2_lattices(A,B,k1_lattices(A,B,C)) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

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

tff(c_88,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_82,plain,(
    l3_lattices('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_86,plain,(
    v10_lattices('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_6,plain,(
    ! [A_4] :
      ( v9_lattices(A_4)
      | ~ v10_lattices(A_4)
      | v2_struct_0(A_4)
      | ~ l3_lattices(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_68,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(k15_lattice3(A_60,B_61),u1_struct_0(A_60))
      | ~ l3_lattices(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_93,plain,(
    ! [A_82] :
      ( l1_lattices(A_82)
      | ~ l3_lattices(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_97,plain,(
    l1_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_82,c_93])).

tff(c_80,plain,
    ( k15_lattice3('#skF_9',k1_xboole_0) != k5_lattices('#skF_9')
    | ~ l3_lattices('#skF_9')
    | ~ v13_lattices('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_90,plain,
    ( k15_lattice3('#skF_9',k1_xboole_0) != k5_lattices('#skF_9')
    | ~ v13_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80])).

tff(c_91,plain,
    ( k15_lattice3('#skF_9',k1_xboole_0) != k5_lattices('#skF_9')
    | ~ v13_lattices('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_90])).

tff(c_103,plain,(
    ~ v13_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_98,plain,(
    ! [A_83] :
      ( l2_lattices(A_83)
      | ~ l3_lattices(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_102,plain,(
    l2_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_82,c_98])).

tff(c_84,plain,(
    v4_lattice3('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

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

tff(c_52,plain,(
    ! [A_38,B_47] :
      ( m1_subset_1('#skF_5'(A_38,B_47),u1_struct_0(A_38))
      | v13_lattices(A_38)
      | ~ m1_subset_1(B_47,u1_struct_0(A_38))
      | ~ l1_lattices(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_72,plain,(
    ! [A_62,B_64] :
      ( k15_lattice3(A_62,k6_domain_1(u1_struct_0(A_62),B_64)) = B_64
      | ~ m1_subset_1(B_64,u1_struct_0(A_62))
      | ~ l3_lattices(A_62)
      | ~ v4_lattice3(A_62)
      | ~ v10_lattices(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_487,plain,(
    ! [A_149,B_150,C_151] :
      ( r2_hidden('#skF_8'(A_149,B_150,C_151),B_150)
      | r3_lattices(A_149,k15_lattice3(A_149,B_150),k15_lattice3(A_149,C_151))
      | ~ l3_lattices(A_149)
      | ~ v4_lattice3(A_149)
      | ~ v10_lattices(A_149)
      | v2_struct_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( ~ r1_tarski(B_3,A_2)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_769,plain,(
    ! [B_190,A_191,C_192] :
      ( ~ r1_tarski(B_190,'#skF_8'(A_191,B_190,C_192))
      | r3_lattices(A_191,k15_lattice3(A_191,B_190),k15_lattice3(A_191,C_192))
      | ~ l3_lattices(A_191)
      | ~ v4_lattice3(A_191)
      | ~ v10_lattices(A_191)
      | v2_struct_0(A_191) ) ),
    inference(resolution,[status(thm)],[c_487,c_4])).

tff(c_774,plain,(
    ! [A_193,C_194] :
      ( r3_lattices(A_193,k15_lattice3(A_193,k1_xboole_0),k15_lattice3(A_193,C_194))
      | ~ l3_lattices(A_193)
      | ~ v4_lattice3(A_193)
      | ~ v10_lattices(A_193)
      | v2_struct_0(A_193) ) ),
    inference(resolution,[status(thm)],[c_2,c_769])).

tff(c_1219,plain,(
    ! [A_267,B_268] :
      ( r3_lattices(A_267,k15_lattice3(A_267,k1_xboole_0),B_268)
      | ~ l3_lattices(A_267)
      | ~ v4_lattice3(A_267)
      | ~ v10_lattices(A_267)
      | v2_struct_0(A_267)
      | ~ m1_subset_1(B_268,u1_struct_0(A_267))
      | ~ l3_lattices(A_267)
      | ~ v4_lattice3(A_267)
      | ~ v10_lattices(A_267)
      | v2_struct_0(A_267) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_774])).

tff(c_48,plain,(
    ! [A_35,B_36,C_37] :
      ( r1_lattices(A_35,B_36,C_37)
      | ~ r3_lattices(A_35,B_36,C_37)
      | ~ m1_subset_1(C_37,u1_struct_0(A_35))
      | ~ m1_subset_1(B_36,u1_struct_0(A_35))
      | ~ l3_lattices(A_35)
      | ~ v9_lattices(A_35)
      | ~ v8_lattices(A_35)
      | ~ v6_lattices(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1492,plain,(
    ! [A_303,B_304] :
      ( r1_lattices(A_303,k15_lattice3(A_303,k1_xboole_0),B_304)
      | ~ m1_subset_1(k15_lattice3(A_303,k1_xboole_0),u1_struct_0(A_303))
      | ~ v9_lattices(A_303)
      | ~ v8_lattices(A_303)
      | ~ v6_lattices(A_303)
      | ~ m1_subset_1(B_304,u1_struct_0(A_303))
      | ~ l3_lattices(A_303)
      | ~ v4_lattice3(A_303)
      | ~ v10_lattices(A_303)
      | v2_struct_0(A_303) ) ),
    inference(resolution,[status(thm)],[c_1219,c_48])).

tff(c_1525,plain,(
    ! [A_308,B_309] :
      ( r1_lattices(A_308,k15_lattice3(A_308,k1_xboole_0),B_309)
      | ~ v9_lattices(A_308)
      | ~ v8_lattices(A_308)
      | ~ v6_lattices(A_308)
      | ~ m1_subset_1(B_309,u1_struct_0(A_308))
      | ~ v4_lattice3(A_308)
      | ~ v10_lattices(A_308)
      | ~ l3_lattices(A_308)
      | v2_struct_0(A_308) ) ),
    inference(resolution,[status(thm)],[c_68,c_1492])).

tff(c_30,plain,(
    ! [A_15,B_19,C_21] :
      ( k1_lattices(A_15,B_19,C_21) = C_21
      | ~ r1_lattices(A_15,B_19,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_15))
      | ~ m1_subset_1(B_19,u1_struct_0(A_15))
      | ~ l2_lattices(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1649,plain,(
    ! [A_326,B_327] :
      ( k1_lattices(A_326,k15_lattice3(A_326,k1_xboole_0),B_327) = B_327
      | ~ m1_subset_1(k15_lattice3(A_326,k1_xboole_0),u1_struct_0(A_326))
      | ~ l2_lattices(A_326)
      | ~ v9_lattices(A_326)
      | ~ v8_lattices(A_326)
      | ~ v6_lattices(A_326)
      | ~ m1_subset_1(B_327,u1_struct_0(A_326))
      | ~ v4_lattice3(A_326)
      | ~ v10_lattices(A_326)
      | ~ l3_lattices(A_326)
      | v2_struct_0(A_326) ) ),
    inference(resolution,[status(thm)],[c_1525,c_30])).

tff(c_1654,plain,(
    ! [A_328,B_329] :
      ( k1_lattices(A_328,k15_lattice3(A_328,k1_xboole_0),B_329) = B_329
      | ~ l2_lattices(A_328)
      | ~ v9_lattices(A_328)
      | ~ v8_lattices(A_328)
      | ~ v6_lattices(A_328)
      | ~ m1_subset_1(B_329,u1_struct_0(A_328))
      | ~ v4_lattice3(A_328)
      | ~ v10_lattices(A_328)
      | ~ l3_lattices(A_328)
      | v2_struct_0(A_328) ) ),
    inference(resolution,[status(thm)],[c_68,c_1649])).

tff(c_1682,plain,(
    ! [A_330,B_331] :
      ( k1_lattices(A_330,k15_lattice3(A_330,k1_xboole_0),k15_lattice3(A_330,B_331)) = k15_lattice3(A_330,B_331)
      | ~ l2_lattices(A_330)
      | ~ v9_lattices(A_330)
      | ~ v8_lattices(A_330)
      | ~ v6_lattices(A_330)
      | ~ v4_lattice3(A_330)
      | ~ v10_lattices(A_330)
      | ~ l3_lattices(A_330)
      | v2_struct_0(A_330) ) ),
    inference(resolution,[status(thm)],[c_68,c_1654])).

tff(c_379,plain,(
    ! [A_137,B_138,C_139] :
      ( k2_lattices(A_137,B_138,k1_lattices(A_137,B_138,C_139)) = B_138
      | ~ m1_subset_1(C_139,u1_struct_0(A_137))
      | ~ m1_subset_1(B_138,u1_struct_0(A_137))
      | ~ v9_lattices(A_137)
      | ~ l3_lattices(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_405,plain,(
    ! [A_60,B_138,B_61] :
      ( k2_lattices(A_60,B_138,k1_lattices(A_60,B_138,k15_lattice3(A_60,B_61))) = B_138
      | ~ m1_subset_1(B_138,u1_struct_0(A_60))
      | ~ v9_lattices(A_60)
      | ~ l3_lattices(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_68,c_379])).

tff(c_2208,plain,(
    ! [A_415,B_416] :
      ( k2_lattices(A_415,k15_lattice3(A_415,k1_xboole_0),k15_lattice3(A_415,B_416)) = k15_lattice3(A_415,k1_xboole_0)
      | ~ m1_subset_1(k15_lattice3(A_415,k1_xboole_0),u1_struct_0(A_415))
      | ~ v9_lattices(A_415)
      | ~ l3_lattices(A_415)
      | v2_struct_0(A_415)
      | ~ l2_lattices(A_415)
      | ~ v9_lattices(A_415)
      | ~ v8_lattices(A_415)
      | ~ v6_lattices(A_415)
      | ~ v4_lattice3(A_415)
      | ~ v10_lattices(A_415)
      | ~ l3_lattices(A_415)
      | v2_struct_0(A_415) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1682,c_405])).

tff(c_2213,plain,(
    ! [A_417,B_418] :
      ( k2_lattices(A_417,k15_lattice3(A_417,k1_xboole_0),k15_lattice3(A_417,B_418)) = k15_lattice3(A_417,k1_xboole_0)
      | ~ l2_lattices(A_417)
      | ~ v9_lattices(A_417)
      | ~ v8_lattices(A_417)
      | ~ v6_lattices(A_417)
      | ~ v4_lattice3(A_417)
      | ~ v10_lattices(A_417)
      | ~ l3_lattices(A_417)
      | v2_struct_0(A_417) ) ),
    inference(resolution,[status(thm)],[c_68,c_2208])).

tff(c_2306,plain,(
    ! [A_424,B_425] :
      ( k2_lattices(A_424,k15_lattice3(A_424,k1_xboole_0),B_425) = k15_lattice3(A_424,k1_xboole_0)
      | ~ l2_lattices(A_424)
      | ~ v9_lattices(A_424)
      | ~ v8_lattices(A_424)
      | ~ v6_lattices(A_424)
      | ~ v4_lattice3(A_424)
      | ~ v10_lattices(A_424)
      | ~ l3_lattices(A_424)
      | v2_struct_0(A_424)
      | ~ m1_subset_1(B_425,u1_struct_0(A_424))
      | ~ l3_lattices(A_424)
      | ~ v4_lattice3(A_424)
      | ~ v10_lattices(A_424)
      | v2_struct_0(A_424) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2213])).

tff(c_2332,plain,(
    ! [A_38,B_47] :
      ( k2_lattices(A_38,k15_lattice3(A_38,k1_xboole_0),'#skF_5'(A_38,B_47)) = k15_lattice3(A_38,k1_xboole_0)
      | ~ l2_lattices(A_38)
      | ~ v9_lattices(A_38)
      | ~ v8_lattices(A_38)
      | ~ v6_lattices(A_38)
      | ~ l3_lattices(A_38)
      | ~ v4_lattice3(A_38)
      | ~ v10_lattices(A_38)
      | v13_lattices(A_38)
      | ~ m1_subset_1(B_47,u1_struct_0(A_38))
      | ~ l1_lattices(A_38)
      | v2_struct_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_52,c_2306])).

tff(c_446,plain,(
    ! [A_144,C_145,B_146] :
      ( k2_lattices(A_144,C_145,B_146) = k2_lattices(A_144,B_146,C_145)
      | ~ m1_subset_1(C_145,u1_struct_0(A_144))
      | ~ m1_subset_1(B_146,u1_struct_0(A_144))
      | ~ v6_lattices(A_144)
      | ~ l1_lattices(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_983,plain,(
    ! [A_233,B_234,B_235] :
      ( k2_lattices(A_233,k15_lattice3(A_233,B_234),B_235) = k2_lattices(A_233,B_235,k15_lattice3(A_233,B_234))
      | ~ m1_subset_1(B_235,u1_struct_0(A_233))
      | ~ v6_lattices(A_233)
      | ~ l1_lattices(A_233)
      | ~ l3_lattices(A_233)
      | v2_struct_0(A_233) ) ),
    inference(resolution,[status(thm)],[c_68,c_446])).

tff(c_1009,plain,(
    ! [A_60,B_61,B_234] :
      ( k2_lattices(A_60,k15_lattice3(A_60,B_61),k15_lattice3(A_60,B_234)) = k2_lattices(A_60,k15_lattice3(A_60,B_234),k15_lattice3(A_60,B_61))
      | ~ v6_lattices(A_60)
      | ~ l1_lattices(A_60)
      | ~ l3_lattices(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_68,c_983])).

tff(c_2247,plain,(
    ! [A_419,B_420] :
      ( k2_lattices(A_419,k15_lattice3(A_419,B_420),k15_lattice3(A_419,k1_xboole_0)) = k15_lattice3(A_419,k1_xboole_0)
      | ~ v6_lattices(A_419)
      | ~ l1_lattices(A_419)
      | ~ l3_lattices(A_419)
      | v2_struct_0(A_419)
      | ~ l2_lattices(A_419)
      | ~ v9_lattices(A_419)
      | ~ v8_lattices(A_419)
      | ~ v6_lattices(A_419)
      | ~ v4_lattice3(A_419)
      | ~ v10_lattices(A_419)
      | ~ l3_lattices(A_419)
      | v2_struct_0(A_419) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2213,c_1009])).

tff(c_3743,plain,(
    ! [A_530,B_531] :
      ( k2_lattices(A_530,B_531,k15_lattice3(A_530,k1_xboole_0)) = k15_lattice3(A_530,k1_xboole_0)
      | ~ v6_lattices(A_530)
      | ~ l1_lattices(A_530)
      | ~ l3_lattices(A_530)
      | v2_struct_0(A_530)
      | ~ l2_lattices(A_530)
      | ~ v9_lattices(A_530)
      | ~ v8_lattices(A_530)
      | ~ v6_lattices(A_530)
      | ~ v4_lattice3(A_530)
      | ~ v10_lattices(A_530)
      | ~ l3_lattices(A_530)
      | v2_struct_0(A_530)
      | ~ m1_subset_1(B_531,u1_struct_0(A_530))
      | ~ l3_lattices(A_530)
      | ~ v4_lattice3(A_530)
      | ~ v10_lattices(A_530)
      | v2_struct_0(A_530) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2247])).

tff(c_3796,plain,(
    ! [A_533,B_534] :
      ( k2_lattices(A_533,'#skF_5'(A_533,B_534),k15_lattice3(A_533,k1_xboole_0)) = k15_lattice3(A_533,k1_xboole_0)
      | ~ l2_lattices(A_533)
      | ~ v9_lattices(A_533)
      | ~ v8_lattices(A_533)
      | ~ v6_lattices(A_533)
      | ~ l3_lattices(A_533)
      | ~ v4_lattice3(A_533)
      | ~ v10_lattices(A_533)
      | v13_lattices(A_533)
      | ~ m1_subset_1(B_534,u1_struct_0(A_533))
      | ~ l1_lattices(A_533)
      | v2_struct_0(A_533) ) ),
    inference(resolution,[status(thm)],[c_52,c_3743])).

tff(c_50,plain,(
    ! [A_38,B_47] :
      ( k2_lattices(A_38,'#skF_5'(A_38,B_47),B_47) != B_47
      | k2_lattices(A_38,B_47,'#skF_5'(A_38,B_47)) != B_47
      | v13_lattices(A_38)
      | ~ m1_subset_1(B_47,u1_struct_0(A_38))
      | ~ l1_lattices(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_3882,plain,(
    ! [A_539] :
      ( k2_lattices(A_539,k15_lattice3(A_539,k1_xboole_0),'#skF_5'(A_539,k15_lattice3(A_539,k1_xboole_0))) != k15_lattice3(A_539,k1_xboole_0)
      | ~ l2_lattices(A_539)
      | ~ v9_lattices(A_539)
      | ~ v8_lattices(A_539)
      | ~ v6_lattices(A_539)
      | ~ l3_lattices(A_539)
      | ~ v4_lattice3(A_539)
      | ~ v10_lattices(A_539)
      | v13_lattices(A_539)
      | ~ m1_subset_1(k15_lattice3(A_539,k1_xboole_0),u1_struct_0(A_539))
      | ~ l1_lattices(A_539)
      | v2_struct_0(A_539) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3796,c_50])).

tff(c_3937,plain,(
    ! [A_544] :
      ( ~ l2_lattices(A_544)
      | ~ v9_lattices(A_544)
      | ~ v8_lattices(A_544)
      | ~ v6_lattices(A_544)
      | ~ l3_lattices(A_544)
      | ~ v4_lattice3(A_544)
      | ~ v10_lattices(A_544)
      | v13_lattices(A_544)
      | ~ m1_subset_1(k15_lattice3(A_544,k1_xboole_0),u1_struct_0(A_544))
      | ~ l1_lattices(A_544)
      | v2_struct_0(A_544) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2332,c_3882])).

tff(c_3943,plain,(
    ! [A_545] :
      ( ~ l2_lattices(A_545)
      | ~ v9_lattices(A_545)
      | ~ v8_lattices(A_545)
      | ~ v6_lattices(A_545)
      | ~ v4_lattice3(A_545)
      | ~ v10_lattices(A_545)
      | v13_lattices(A_545)
      | ~ l1_lattices(A_545)
      | ~ l3_lattices(A_545)
      | v2_struct_0(A_545) ) ),
    inference(resolution,[status(thm)],[c_68,c_3937])).

tff(c_3948,plain,(
    ! [A_546] :
      ( ~ l2_lattices(A_546)
      | ~ v8_lattices(A_546)
      | ~ v6_lattices(A_546)
      | ~ v4_lattice3(A_546)
      | v13_lattices(A_546)
      | ~ l1_lattices(A_546)
      | ~ v10_lattices(A_546)
      | v2_struct_0(A_546)
      | ~ l3_lattices(A_546) ) ),
    inference(resolution,[status(thm)],[c_6,c_3943])).

tff(c_3953,plain,(
    ! [A_547] :
      ( ~ l2_lattices(A_547)
      | ~ v6_lattices(A_547)
      | ~ v4_lattice3(A_547)
      | v13_lattices(A_547)
      | ~ l1_lattices(A_547)
      | ~ v10_lattices(A_547)
      | v2_struct_0(A_547)
      | ~ l3_lattices(A_547) ) ),
    inference(resolution,[status(thm)],[c_8,c_3948])).

tff(c_3958,plain,(
    ! [A_548] :
      ( ~ l2_lattices(A_548)
      | ~ v4_lattice3(A_548)
      | v13_lattices(A_548)
      | ~ l1_lattices(A_548)
      | ~ v10_lattices(A_548)
      | v2_struct_0(A_548)
      | ~ l3_lattices(A_548) ) ),
    inference(resolution,[status(thm)],[c_12,c_3953])).

tff(c_3961,plain,
    ( ~ l2_lattices('#skF_9')
    | v13_lattices('#skF_9')
    | ~ l1_lattices('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_84,c_3958])).

tff(c_3964,plain,
    ( v13_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_86,c_97,c_102,c_3961])).

tff(c_3966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_103,c_3964])).

tff(c_3968,plain,(
    v13_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_40,plain,(
    ! [A_33] :
      ( m1_subset_1(k5_lattices(A_33),u1_struct_0(A_33))
      | ~ l1_lattices(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_54,plain,(
    ! [A_38] :
      ( m1_subset_1('#skF_4'(A_38),u1_struct_0(A_38))
      | ~ v13_lattices(A_38)
      | ~ l1_lattices(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_4227,plain,(
    ! [A_603,C_604] :
      ( k2_lattices(A_603,k5_lattices(A_603),C_604) = k5_lattices(A_603)
      | ~ m1_subset_1(C_604,u1_struct_0(A_603))
      | ~ m1_subset_1(k5_lattices(A_603),u1_struct_0(A_603))
      | ~ v13_lattices(A_603)
      | ~ l1_lattices(A_603)
      | v2_struct_0(A_603) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4255,plain,(
    ! [A_605] :
      ( k2_lattices(A_605,k5_lattices(A_605),'#skF_4'(A_605)) = k5_lattices(A_605)
      | ~ m1_subset_1(k5_lattices(A_605),u1_struct_0(A_605))
      | ~ v13_lattices(A_605)
      | ~ l1_lattices(A_605)
      | v2_struct_0(A_605) ) ),
    inference(resolution,[status(thm)],[c_54,c_4227])).

tff(c_4259,plain,(
    ! [A_606] :
      ( k2_lattices(A_606,k5_lattices(A_606),'#skF_4'(A_606)) = k5_lattices(A_606)
      | ~ v13_lattices(A_606)
      | ~ l1_lattices(A_606)
      | v2_struct_0(A_606) ) ),
    inference(resolution,[status(thm)],[c_40,c_4255])).

tff(c_3984,plain,(
    ! [A_567,C_568] :
      ( k2_lattices(A_567,C_568,'#skF_4'(A_567)) = '#skF_4'(A_567)
      | ~ m1_subset_1(C_568,u1_struct_0(A_567))
      | ~ v13_lattices(A_567)
      | ~ l1_lattices(A_567)
      | v2_struct_0(A_567) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_4008,plain,(
    ! [A_33] :
      ( k2_lattices(A_33,k5_lattices(A_33),'#skF_4'(A_33)) = '#skF_4'(A_33)
      | ~ v13_lattices(A_33)
      | ~ l1_lattices(A_33)
      | v2_struct_0(A_33) ) ),
    inference(resolution,[status(thm)],[c_40,c_3984])).

tff(c_4265,plain,(
    ! [A_606] :
      ( k5_lattices(A_606) = '#skF_4'(A_606)
      | ~ v13_lattices(A_606)
      | ~ l1_lattices(A_606)
      | v2_struct_0(A_606)
      | ~ v13_lattices(A_606)
      | ~ l1_lattices(A_606)
      | v2_struct_0(A_606) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4259,c_4008])).

tff(c_4315,plain,(
    ! [A_610] :
      ( k5_lattices(A_610) = '#skF_4'(A_610)
      | ~ v13_lattices(A_610)
      | ~ l1_lattices(A_610)
      | v2_struct_0(A_610) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_4265])).

tff(c_4318,plain,
    ( k5_lattices('#skF_9') = '#skF_4'('#skF_9')
    | ~ v13_lattices('#skF_9')
    | ~ l1_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_4315,c_88])).

tff(c_4321,plain,(
    k5_lattices('#skF_9') = '#skF_4'('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_3968,c_4318])).

tff(c_3967,plain,(
    k15_lattice3('#skF_9',k1_xboole_0) != k5_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_4322,plain,(
    k15_lattice3('#skF_9',k1_xboole_0) != '#skF_4'('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4321,c_3967])).

tff(c_38,plain,(
    ! [A_22] :
      ( m1_subset_1('#skF_2'(A_22),u1_struct_0(A_22))
      | v9_lattices(A_22)
      | ~ l3_lattices(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4335,plain,
    ( m1_subset_1('#skF_4'('#skF_9'),u1_struct_0('#skF_9'))
    | ~ l1_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_4321,c_40])).

tff(c_4348,plain,
    ( m1_subset_1('#skF_4'('#skF_9'),u1_struct_0('#skF_9'))
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_4335])).

tff(c_4349,plain,(
    m1_subset_1('#skF_4'('#skF_9'),u1_struct_0('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_4348])).

tff(c_4402,plain,(
    ! [A_611,C_612,B_613] :
      ( k2_lattices(A_611,C_612,B_613) = k2_lattices(A_611,B_613,C_612)
      | ~ m1_subset_1(C_612,u1_struct_0(A_611))
      | ~ m1_subset_1(B_613,u1_struct_0(A_611))
      | ~ v6_lattices(A_611)
      | ~ l1_lattices(A_611)
      | v2_struct_0(A_611) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_4404,plain,(
    ! [B_613] :
      ( k2_lattices('#skF_9',B_613,'#skF_4'('#skF_9')) = k2_lattices('#skF_9','#skF_4'('#skF_9'),B_613)
      | ~ m1_subset_1(B_613,u1_struct_0('#skF_9'))
      | ~ v6_lattices('#skF_9')
      | ~ l1_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_4349,c_4402])).

tff(c_4425,plain,(
    ! [B_613] :
      ( k2_lattices('#skF_9',B_613,'#skF_4'('#skF_9')) = k2_lattices('#skF_9','#skF_4'('#skF_9'),B_613)
      | ~ m1_subset_1(B_613,u1_struct_0('#skF_9'))
      | ~ v6_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_4404])).

tff(c_4426,plain,(
    ! [B_613] :
      ( k2_lattices('#skF_9',B_613,'#skF_4'('#skF_9')) = k2_lattices('#skF_9','#skF_4'('#skF_9'),B_613)
      | ~ m1_subset_1(B_613,u1_struct_0('#skF_9'))
      | ~ v6_lattices('#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_4425])).

tff(c_4446,plain,(
    ~ v6_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_4426])).

tff(c_4449,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_12,c_4446])).

tff(c_4452,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_86,c_4449])).

tff(c_4454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_4452])).

tff(c_4491,plain,(
    ! [B_618] :
      ( k2_lattices('#skF_9',B_618,'#skF_4'('#skF_9')) = k2_lattices('#skF_9','#skF_4'('#skF_9'),B_618)
      | ~ m1_subset_1(B_618,u1_struct_0('#skF_9')) ) ),
    inference(splitRight,[status(thm)],[c_4426])).

tff(c_4506,plain,
    ( k2_lattices('#skF_9','#skF_2'('#skF_9'),'#skF_4'('#skF_9')) = k2_lattices('#skF_9','#skF_4'('#skF_9'),'#skF_2'('#skF_9'))
    | v9_lattices('#skF_9')
    | ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_38,c_4491])).

tff(c_4543,plain,
    ( k2_lattices('#skF_9','#skF_2'('#skF_9'),'#skF_4'('#skF_9')) = k2_lattices('#skF_9','#skF_4'('#skF_9'),'#skF_2'('#skF_9'))
    | v9_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_4506])).

tff(c_4544,plain,
    ( k2_lattices('#skF_9','#skF_2'('#skF_9'),'#skF_4'('#skF_9')) = k2_lattices('#skF_9','#skF_4'('#skF_9'),'#skF_2'('#skF_9'))
    | v9_lattices('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_4543])).

tff(c_4569,plain,(
    v9_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_4544])).

tff(c_4526,plain,(
    ! [B_61] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',B_61),'#skF_4'('#skF_9')) = k2_lattices('#skF_9','#skF_4'('#skF_9'),k15_lattice3('#skF_9',B_61))
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_68,c_4491])).

tff(c_4563,plain,(
    ! [B_61] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',B_61),'#skF_4'('#skF_9')) = k2_lattices('#skF_9','#skF_4'('#skF_9'),k15_lattice3('#skF_9',B_61))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_4526])).

tff(c_4571,plain,(
    ! [B_619] : k2_lattices('#skF_9',k15_lattice3('#skF_9',B_619),'#skF_4'('#skF_9')) = k2_lattices('#skF_9','#skF_4'('#skF_9'),k15_lattice3('#skF_9',B_619)) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_4563])).

tff(c_4007,plain,(
    ! [A_60,B_61] :
      ( k2_lattices(A_60,k15_lattice3(A_60,B_61),'#skF_4'(A_60)) = '#skF_4'(A_60)
      | ~ v13_lattices(A_60)
      | ~ l1_lattices(A_60)
      | ~ l3_lattices(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_68,c_3984])).

tff(c_4577,plain,(
    ! [B_619] :
      ( k2_lattices('#skF_9','#skF_4'('#skF_9'),k15_lattice3('#skF_9',B_619)) = '#skF_4'('#skF_9')
      | ~ v13_lattices('#skF_9')
      | ~ l1_lattices('#skF_9')
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4571,c_4007])).

tff(c_4591,plain,(
    ! [B_619] :
      ( k2_lattices('#skF_9','#skF_4'('#skF_9'),k15_lattice3('#skF_9',B_619)) = '#skF_4'('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_97,c_3968,c_4577])).

tff(c_4592,plain,(
    ! [B_619] : k2_lattices('#skF_9','#skF_4'('#skF_9'),k15_lattice3('#skF_9',B_619)) = '#skF_4'('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_4591])).

tff(c_4564,plain,(
    ! [B_61] : k2_lattices('#skF_9',k15_lattice3('#skF_9',B_61),'#skF_4'('#skF_9')) = k2_lattices('#skF_9','#skF_4'('#skF_9'),k15_lattice3('#skF_9',B_61)) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_4563])).

tff(c_4600,plain,(
    ! [B_61] : k2_lattices('#skF_9',k15_lattice3('#skF_9',B_61),'#skF_4'('#skF_9')) = '#skF_4'('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4592,c_4564])).

tff(c_4456,plain,(
    v6_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_4426])).

tff(c_5067,plain,(
    ! [A_647,B_648,C_649] :
      ( r3_lattices(A_647,B_648,C_649)
      | ~ r1_lattices(A_647,B_648,C_649)
      | ~ m1_subset_1(C_649,u1_struct_0(A_647))
      | ~ m1_subset_1(B_648,u1_struct_0(A_647))
      | ~ l3_lattices(A_647)
      | ~ v9_lattices(A_647)
      | ~ v8_lattices(A_647)
      | ~ v6_lattices(A_647)
      | v2_struct_0(A_647) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_5069,plain,(
    ! [B_648] :
      ( r3_lattices('#skF_9',B_648,'#skF_4'('#skF_9'))
      | ~ r1_lattices('#skF_9',B_648,'#skF_4'('#skF_9'))
      | ~ m1_subset_1(B_648,u1_struct_0('#skF_9'))
      | ~ l3_lattices('#skF_9')
      | ~ v9_lattices('#skF_9')
      | ~ v8_lattices('#skF_9')
      | ~ v6_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_4349,c_5067])).

tff(c_5090,plain,(
    ! [B_648] :
      ( r3_lattices('#skF_9',B_648,'#skF_4'('#skF_9'))
      | ~ r1_lattices('#skF_9',B_648,'#skF_4'('#skF_9'))
      | ~ m1_subset_1(B_648,u1_struct_0('#skF_9'))
      | ~ v8_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4456,c_4569,c_82,c_5069])).

tff(c_5091,plain,(
    ! [B_648] :
      ( r3_lattices('#skF_9',B_648,'#skF_4'('#skF_9'))
      | ~ r1_lattices('#skF_9',B_648,'#skF_4'('#skF_9'))
      | ~ m1_subset_1(B_648,u1_struct_0('#skF_9'))
      | ~ v8_lattices('#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_5090])).

tff(c_5101,plain,(
    ~ v8_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_5091])).

tff(c_5104,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_8,c_5101])).

tff(c_5107,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_86,c_5104])).

tff(c_5109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_5107])).

tff(c_5111,plain,(
    v8_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_5091])).

tff(c_4216,plain,(
    ! [A_600,B_601,C_602] :
      ( r2_hidden('#skF_8'(A_600,B_601,C_602),B_601)
      | r3_lattices(A_600,k15_lattice3(A_600,B_601),k15_lattice3(A_600,C_602))
      | ~ l3_lattices(A_600)
      | ~ v4_lattice3(A_600)
      | ~ v10_lattices(A_600)
      | v2_struct_0(A_600) ) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_5319,plain,(
    ! [B_672,A_673,C_674] :
      ( ~ r1_tarski(B_672,'#skF_8'(A_673,B_672,C_674))
      | r3_lattices(A_673,k15_lattice3(A_673,B_672),k15_lattice3(A_673,C_674))
      | ~ l3_lattices(A_673)
      | ~ v4_lattice3(A_673)
      | ~ v10_lattices(A_673)
      | v2_struct_0(A_673) ) ),
    inference(resolution,[status(thm)],[c_4216,c_4])).

tff(c_5324,plain,(
    ! [A_675,C_676] :
      ( r3_lattices(A_675,k15_lattice3(A_675,k1_xboole_0),k15_lattice3(A_675,C_676))
      | ~ l3_lattices(A_675)
      | ~ v4_lattice3(A_675)
      | ~ v10_lattices(A_675)
      | v2_struct_0(A_675) ) ),
    inference(resolution,[status(thm)],[c_2,c_5319])).

tff(c_5993,plain,(
    ! [A_754,B_755] :
      ( r3_lattices(A_754,k15_lattice3(A_754,k1_xboole_0),B_755)
      | ~ l3_lattices(A_754)
      | ~ v4_lattice3(A_754)
      | ~ v10_lattices(A_754)
      | v2_struct_0(A_754)
      | ~ m1_subset_1(B_755,u1_struct_0(A_754))
      | ~ l3_lattices(A_754)
      | ~ v4_lattice3(A_754)
      | ~ v10_lattices(A_754)
      | v2_struct_0(A_754) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_5324])).

tff(c_6396,plain,(
    ! [A_794,B_795] :
      ( r1_lattices(A_794,k15_lattice3(A_794,k1_xboole_0),B_795)
      | ~ m1_subset_1(k15_lattice3(A_794,k1_xboole_0),u1_struct_0(A_794))
      | ~ v9_lattices(A_794)
      | ~ v8_lattices(A_794)
      | ~ v6_lattices(A_794)
      | ~ m1_subset_1(B_795,u1_struct_0(A_794))
      | ~ l3_lattices(A_794)
      | ~ v4_lattice3(A_794)
      | ~ v10_lattices(A_794)
      | v2_struct_0(A_794) ) ),
    inference(resolution,[status(thm)],[c_5993,c_48])).

tff(c_6412,plain,(
    ! [A_799,B_800] :
      ( r1_lattices(A_799,k15_lattice3(A_799,k1_xboole_0),B_800)
      | ~ v9_lattices(A_799)
      | ~ v8_lattices(A_799)
      | ~ v6_lattices(A_799)
      | ~ m1_subset_1(B_800,u1_struct_0(A_799))
      | ~ v4_lattice3(A_799)
      | ~ v10_lattices(A_799)
      | ~ l3_lattices(A_799)
      | v2_struct_0(A_799) ) ),
    inference(resolution,[status(thm)],[c_68,c_6396])).

tff(c_6577,plain,(
    ! [A_819,B_820] :
      ( k1_lattices(A_819,k15_lattice3(A_819,k1_xboole_0),B_820) = B_820
      | ~ m1_subset_1(k15_lattice3(A_819,k1_xboole_0),u1_struct_0(A_819))
      | ~ l2_lattices(A_819)
      | ~ v9_lattices(A_819)
      | ~ v8_lattices(A_819)
      | ~ v6_lattices(A_819)
      | ~ m1_subset_1(B_820,u1_struct_0(A_819))
      | ~ v4_lattice3(A_819)
      | ~ v10_lattices(A_819)
      | ~ l3_lattices(A_819)
      | v2_struct_0(A_819) ) ),
    inference(resolution,[status(thm)],[c_6412,c_30])).

tff(c_6582,plain,(
    ! [A_821,B_822] :
      ( k1_lattices(A_821,k15_lattice3(A_821,k1_xboole_0),B_822) = B_822
      | ~ l2_lattices(A_821)
      | ~ v9_lattices(A_821)
      | ~ v8_lattices(A_821)
      | ~ v6_lattices(A_821)
      | ~ m1_subset_1(B_822,u1_struct_0(A_821))
      | ~ v4_lattice3(A_821)
      | ~ v10_lattices(A_821)
      | ~ l3_lattices(A_821)
      | v2_struct_0(A_821) ) ),
    inference(resolution,[status(thm)],[c_68,c_6577])).

tff(c_6584,plain,
    ( k1_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),'#skF_4'('#skF_9')) = '#skF_4'('#skF_9')
    | ~ l2_lattices('#skF_9')
    | ~ v9_lattices('#skF_9')
    | ~ v8_lattices('#skF_9')
    | ~ v6_lattices('#skF_9')
    | ~ v4_lattice3('#skF_9')
    | ~ v10_lattices('#skF_9')
    | ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_4349,c_6582])).

tff(c_6605,plain,
    ( k1_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),'#skF_4'('#skF_9')) = '#skF_4'('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_86,c_84,c_4456,c_5111,c_4569,c_102,c_6584])).

tff(c_6606,plain,(
    k1_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),'#skF_4'('#skF_9')) = '#skF_4'('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_6605])).

tff(c_4457,plain,(
    ! [A_615,B_616,C_617] :
      ( k2_lattices(A_615,B_616,k1_lattices(A_615,B_616,C_617)) = B_616
      | ~ m1_subset_1(C_617,u1_struct_0(A_615))
      | ~ m1_subset_1(B_616,u1_struct_0(A_615))
      | ~ v9_lattices(A_615)
      | ~ l3_lattices(A_615)
      | v2_struct_0(A_615) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4487,plain,(
    ! [A_38,B_616] :
      ( k2_lattices(A_38,B_616,k1_lattices(A_38,B_616,'#skF_4'(A_38))) = B_616
      | ~ m1_subset_1(B_616,u1_struct_0(A_38))
      | ~ v9_lattices(A_38)
      | ~ l3_lattices(A_38)
      | ~ v13_lattices(A_38)
      | ~ l1_lattices(A_38)
      | v2_struct_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_54,c_4457])).

tff(c_6619,plain,
    ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),'#skF_4'('#skF_9')) = k15_lattice3('#skF_9',k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3('#skF_9',k1_xboole_0),u1_struct_0('#skF_9'))
    | ~ v9_lattices('#skF_9')
    | ~ l3_lattices('#skF_9')
    | ~ v13_lattices('#skF_9')
    | ~ l1_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_6606,c_4487])).

tff(c_6626,plain,
    ( k15_lattice3('#skF_9',k1_xboole_0) = '#skF_4'('#skF_9')
    | ~ m1_subset_1(k15_lattice3('#skF_9',k1_xboole_0),u1_struct_0('#skF_9'))
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_3968,c_82,c_4569,c_4600,c_6619])).

tff(c_6627,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_9',k1_xboole_0),u1_struct_0('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_4322,c_6626])).

tff(c_6633,plain,
    ( ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_68,c_6627])).

tff(c_6636,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_6633])).

tff(c_6638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_6636])).

tff(c_6640,plain,(
    ~ v9_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_4544])).

tff(c_6643,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_6,c_6640])).

tff(c_6646,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_86,c_6643])).

tff(c_6648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_6646])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:41:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.76/4.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.76/4.55  
% 11.76/4.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.76/4.55  %$ r3_lattices > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > k6_domain_1 > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_7 > #skF_2 > #skF_4 > #skF_9 > #skF_3 > #skF_8 > #skF_1 > #skF_5 > #skF_6
% 11.76/4.55  
% 11.76/4.55  %Foreground sorts:
% 11.76/4.55  
% 11.76/4.55  
% 11.76/4.55  %Background operators:
% 11.76/4.55  
% 11.76/4.55  
% 11.76/4.55  %Foreground operators:
% 11.76/4.55  tff(l3_lattices, type, l3_lattices: $i > $o).
% 11.76/4.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.76/4.55  tff('#skF_7', type, '#skF_7': $i > $i).
% 11.76/4.55  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 11.76/4.55  tff(l2_lattices, type, l2_lattices: $i > $o).
% 11.76/4.55  tff('#skF_2', type, '#skF_2': $i > $i).
% 11.76/4.55  tff('#skF_4', type, '#skF_4': $i > $i).
% 11.76/4.55  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 11.76/4.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.76/4.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.76/4.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.76/4.55  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 11.76/4.55  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 11.76/4.55  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 11.76/4.55  tff(l1_lattices, type, l1_lattices: $i > $o).
% 11.76/4.55  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 11.76/4.55  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 11.76/4.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.76/4.55  tff(v4_lattices, type, v4_lattices: $i > $o).
% 11.76/4.55  tff(v6_lattices, type, v6_lattices: $i > $o).
% 11.76/4.55  tff(v9_lattices, type, v9_lattices: $i > $o).
% 11.76/4.55  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 11.76/4.55  tff(v5_lattices, type, v5_lattices: $i > $o).
% 11.76/4.55  tff(v10_lattices, type, v10_lattices: $i > $o).
% 11.76/4.55  tff('#skF_9', type, '#skF_9': $i).
% 11.76/4.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.76/4.55  tff(v13_lattices, type, v13_lattices: $i > $o).
% 11.76/4.55  tff('#skF_3', type, '#skF_3': $i > $i).
% 11.76/4.55  tff(v8_lattices, type, v8_lattices: $i > $o).
% 11.76/4.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.76/4.55  tff(k5_lattices, type, k5_lattices: $i > $i).
% 11.76/4.55  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 11.76/4.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.76/4.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.76/4.55  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 11.76/4.55  tff('#skF_6', type, '#skF_6': $i > $i).
% 11.76/4.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.76/4.55  tff(v7_lattices, type, v7_lattices: $i > $o).
% 11.76/4.55  
% 11.76/4.58  tff(f_237, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) & (k5_lattices(A) = k15_lattice3(A, k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattice3)).
% 11.76/4.58  tff(f_54, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 11.76/4.58  tff(f_174, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 11.76/4.58  tff(f_116, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 11.76/4.58  tff(f_152, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_lattices)).
% 11.76/4.58  tff(f_190, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((k15_lattice3(A, k6_domain_1(u1_struct_0(A), B)) = B) & (k16_lattice3(A, k6_domain_1(u1_struct_0(A), B)) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_lattice3)).
% 11.76/4.58  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.76/4.58  tff(f_216, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: ((![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, B) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ~(r3_lattices(A, D, E) & r2_hidden(E, C))))))) => r3_lattices(A, k15_lattice3(A, B), k15_lattice3(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_lattice3)).
% 11.76/4.58  tff(f_32, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 11.76/4.58  tff(f_135, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 11.76/4.58  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 11.76/4.58  tff(f_103, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v9_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, B, C)) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattices)).
% 11.76/4.58  tff(f_167, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v6_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, C) = k2_lattices(A, C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_lattices)).
% 11.76/4.58  tff(f_110, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 11.76/4.58  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 11.76/4.58  tff(c_88, plain, (~v2_struct_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_237])).
% 11.76/4.58  tff(c_82, plain, (l3_lattices('#skF_9')), inference(cnfTransformation, [status(thm)], [f_237])).
% 11.76/4.58  tff(c_86, plain, (v10_lattices('#skF_9')), inference(cnfTransformation, [status(thm)], [f_237])).
% 11.76/4.58  tff(c_6, plain, (![A_4]: (v9_lattices(A_4) | ~v10_lattices(A_4) | v2_struct_0(A_4) | ~l3_lattices(A_4))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.76/4.58  tff(c_68, plain, (![A_60, B_61]: (m1_subset_1(k15_lattice3(A_60, B_61), u1_struct_0(A_60)) | ~l3_lattices(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_174])).
% 11.76/4.58  tff(c_93, plain, (![A_82]: (l1_lattices(A_82) | ~l3_lattices(A_82))), inference(cnfTransformation, [status(thm)], [f_116])).
% 11.76/4.58  tff(c_97, plain, (l1_lattices('#skF_9')), inference(resolution, [status(thm)], [c_82, c_93])).
% 11.76/4.58  tff(c_80, plain, (k15_lattice3('#skF_9', k1_xboole_0)!=k5_lattices('#skF_9') | ~l3_lattices('#skF_9') | ~v13_lattices('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_237])).
% 11.76/4.58  tff(c_90, plain, (k15_lattice3('#skF_9', k1_xboole_0)!=k5_lattices('#skF_9') | ~v13_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80])).
% 11.76/4.58  tff(c_91, plain, (k15_lattice3('#skF_9', k1_xboole_0)!=k5_lattices('#skF_9') | ~v13_lattices('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_88, c_90])).
% 11.76/4.58  tff(c_103, plain, (~v13_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_91])).
% 11.76/4.58  tff(c_98, plain, (![A_83]: (l2_lattices(A_83) | ~l3_lattices(A_83))), inference(cnfTransformation, [status(thm)], [f_116])).
% 11.76/4.58  tff(c_102, plain, (l2_lattices('#skF_9')), inference(resolution, [status(thm)], [c_82, c_98])).
% 11.76/4.58  tff(c_84, plain, (v4_lattice3('#skF_9')), inference(cnfTransformation, [status(thm)], [f_237])).
% 11.76/4.58  tff(c_12, plain, (![A_4]: (v6_lattices(A_4) | ~v10_lattices(A_4) | v2_struct_0(A_4) | ~l3_lattices(A_4))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.76/4.58  tff(c_8, plain, (![A_4]: (v8_lattices(A_4) | ~v10_lattices(A_4) | v2_struct_0(A_4) | ~l3_lattices(A_4))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.76/4.58  tff(c_52, plain, (![A_38, B_47]: (m1_subset_1('#skF_5'(A_38, B_47), u1_struct_0(A_38)) | v13_lattices(A_38) | ~m1_subset_1(B_47, u1_struct_0(A_38)) | ~l1_lattices(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_152])).
% 11.76/4.58  tff(c_72, plain, (![A_62, B_64]: (k15_lattice3(A_62, k6_domain_1(u1_struct_0(A_62), B_64))=B_64 | ~m1_subset_1(B_64, u1_struct_0(A_62)) | ~l3_lattices(A_62) | ~v4_lattice3(A_62) | ~v10_lattices(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_190])).
% 11.76/4.58  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.76/4.58  tff(c_487, plain, (![A_149, B_150, C_151]: (r2_hidden('#skF_8'(A_149, B_150, C_151), B_150) | r3_lattices(A_149, k15_lattice3(A_149, B_150), k15_lattice3(A_149, C_151)) | ~l3_lattices(A_149) | ~v4_lattice3(A_149) | ~v10_lattices(A_149) | v2_struct_0(A_149))), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.76/4.58  tff(c_4, plain, (![B_3, A_2]: (~r1_tarski(B_3, A_2) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.76/4.58  tff(c_769, plain, (![B_190, A_191, C_192]: (~r1_tarski(B_190, '#skF_8'(A_191, B_190, C_192)) | r3_lattices(A_191, k15_lattice3(A_191, B_190), k15_lattice3(A_191, C_192)) | ~l3_lattices(A_191) | ~v4_lattice3(A_191) | ~v10_lattices(A_191) | v2_struct_0(A_191))), inference(resolution, [status(thm)], [c_487, c_4])).
% 11.76/4.58  tff(c_774, plain, (![A_193, C_194]: (r3_lattices(A_193, k15_lattice3(A_193, k1_xboole_0), k15_lattice3(A_193, C_194)) | ~l3_lattices(A_193) | ~v4_lattice3(A_193) | ~v10_lattices(A_193) | v2_struct_0(A_193))), inference(resolution, [status(thm)], [c_2, c_769])).
% 11.76/4.58  tff(c_1219, plain, (![A_267, B_268]: (r3_lattices(A_267, k15_lattice3(A_267, k1_xboole_0), B_268) | ~l3_lattices(A_267) | ~v4_lattice3(A_267) | ~v10_lattices(A_267) | v2_struct_0(A_267) | ~m1_subset_1(B_268, u1_struct_0(A_267)) | ~l3_lattices(A_267) | ~v4_lattice3(A_267) | ~v10_lattices(A_267) | v2_struct_0(A_267))), inference(superposition, [status(thm), theory('equality')], [c_72, c_774])).
% 11.76/4.58  tff(c_48, plain, (![A_35, B_36, C_37]: (r1_lattices(A_35, B_36, C_37) | ~r3_lattices(A_35, B_36, C_37) | ~m1_subset_1(C_37, u1_struct_0(A_35)) | ~m1_subset_1(B_36, u1_struct_0(A_35)) | ~l3_lattices(A_35) | ~v9_lattices(A_35) | ~v8_lattices(A_35) | ~v6_lattices(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_135])).
% 11.76/4.58  tff(c_1492, plain, (![A_303, B_304]: (r1_lattices(A_303, k15_lattice3(A_303, k1_xboole_0), B_304) | ~m1_subset_1(k15_lattice3(A_303, k1_xboole_0), u1_struct_0(A_303)) | ~v9_lattices(A_303) | ~v8_lattices(A_303) | ~v6_lattices(A_303) | ~m1_subset_1(B_304, u1_struct_0(A_303)) | ~l3_lattices(A_303) | ~v4_lattice3(A_303) | ~v10_lattices(A_303) | v2_struct_0(A_303))), inference(resolution, [status(thm)], [c_1219, c_48])).
% 11.76/4.58  tff(c_1525, plain, (![A_308, B_309]: (r1_lattices(A_308, k15_lattice3(A_308, k1_xboole_0), B_309) | ~v9_lattices(A_308) | ~v8_lattices(A_308) | ~v6_lattices(A_308) | ~m1_subset_1(B_309, u1_struct_0(A_308)) | ~v4_lattice3(A_308) | ~v10_lattices(A_308) | ~l3_lattices(A_308) | v2_struct_0(A_308))), inference(resolution, [status(thm)], [c_68, c_1492])).
% 11.76/4.58  tff(c_30, plain, (![A_15, B_19, C_21]: (k1_lattices(A_15, B_19, C_21)=C_21 | ~r1_lattices(A_15, B_19, C_21) | ~m1_subset_1(C_21, u1_struct_0(A_15)) | ~m1_subset_1(B_19, u1_struct_0(A_15)) | ~l2_lattices(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.76/4.58  tff(c_1649, plain, (![A_326, B_327]: (k1_lattices(A_326, k15_lattice3(A_326, k1_xboole_0), B_327)=B_327 | ~m1_subset_1(k15_lattice3(A_326, k1_xboole_0), u1_struct_0(A_326)) | ~l2_lattices(A_326) | ~v9_lattices(A_326) | ~v8_lattices(A_326) | ~v6_lattices(A_326) | ~m1_subset_1(B_327, u1_struct_0(A_326)) | ~v4_lattice3(A_326) | ~v10_lattices(A_326) | ~l3_lattices(A_326) | v2_struct_0(A_326))), inference(resolution, [status(thm)], [c_1525, c_30])).
% 11.76/4.58  tff(c_1654, plain, (![A_328, B_329]: (k1_lattices(A_328, k15_lattice3(A_328, k1_xboole_0), B_329)=B_329 | ~l2_lattices(A_328) | ~v9_lattices(A_328) | ~v8_lattices(A_328) | ~v6_lattices(A_328) | ~m1_subset_1(B_329, u1_struct_0(A_328)) | ~v4_lattice3(A_328) | ~v10_lattices(A_328) | ~l3_lattices(A_328) | v2_struct_0(A_328))), inference(resolution, [status(thm)], [c_68, c_1649])).
% 11.76/4.58  tff(c_1682, plain, (![A_330, B_331]: (k1_lattices(A_330, k15_lattice3(A_330, k1_xboole_0), k15_lattice3(A_330, B_331))=k15_lattice3(A_330, B_331) | ~l2_lattices(A_330) | ~v9_lattices(A_330) | ~v8_lattices(A_330) | ~v6_lattices(A_330) | ~v4_lattice3(A_330) | ~v10_lattices(A_330) | ~l3_lattices(A_330) | v2_struct_0(A_330))), inference(resolution, [status(thm)], [c_68, c_1654])).
% 11.76/4.58  tff(c_379, plain, (![A_137, B_138, C_139]: (k2_lattices(A_137, B_138, k1_lattices(A_137, B_138, C_139))=B_138 | ~m1_subset_1(C_139, u1_struct_0(A_137)) | ~m1_subset_1(B_138, u1_struct_0(A_137)) | ~v9_lattices(A_137) | ~l3_lattices(A_137) | v2_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.76/4.58  tff(c_405, plain, (![A_60, B_138, B_61]: (k2_lattices(A_60, B_138, k1_lattices(A_60, B_138, k15_lattice3(A_60, B_61)))=B_138 | ~m1_subset_1(B_138, u1_struct_0(A_60)) | ~v9_lattices(A_60) | ~l3_lattices(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_68, c_379])).
% 11.76/4.58  tff(c_2208, plain, (![A_415, B_416]: (k2_lattices(A_415, k15_lattice3(A_415, k1_xboole_0), k15_lattice3(A_415, B_416))=k15_lattice3(A_415, k1_xboole_0) | ~m1_subset_1(k15_lattice3(A_415, k1_xboole_0), u1_struct_0(A_415)) | ~v9_lattices(A_415) | ~l3_lattices(A_415) | v2_struct_0(A_415) | ~l2_lattices(A_415) | ~v9_lattices(A_415) | ~v8_lattices(A_415) | ~v6_lattices(A_415) | ~v4_lattice3(A_415) | ~v10_lattices(A_415) | ~l3_lattices(A_415) | v2_struct_0(A_415))), inference(superposition, [status(thm), theory('equality')], [c_1682, c_405])).
% 11.76/4.58  tff(c_2213, plain, (![A_417, B_418]: (k2_lattices(A_417, k15_lattice3(A_417, k1_xboole_0), k15_lattice3(A_417, B_418))=k15_lattice3(A_417, k1_xboole_0) | ~l2_lattices(A_417) | ~v9_lattices(A_417) | ~v8_lattices(A_417) | ~v6_lattices(A_417) | ~v4_lattice3(A_417) | ~v10_lattices(A_417) | ~l3_lattices(A_417) | v2_struct_0(A_417))), inference(resolution, [status(thm)], [c_68, c_2208])).
% 11.76/4.58  tff(c_2306, plain, (![A_424, B_425]: (k2_lattices(A_424, k15_lattice3(A_424, k1_xboole_0), B_425)=k15_lattice3(A_424, k1_xboole_0) | ~l2_lattices(A_424) | ~v9_lattices(A_424) | ~v8_lattices(A_424) | ~v6_lattices(A_424) | ~v4_lattice3(A_424) | ~v10_lattices(A_424) | ~l3_lattices(A_424) | v2_struct_0(A_424) | ~m1_subset_1(B_425, u1_struct_0(A_424)) | ~l3_lattices(A_424) | ~v4_lattice3(A_424) | ~v10_lattices(A_424) | v2_struct_0(A_424))), inference(superposition, [status(thm), theory('equality')], [c_72, c_2213])).
% 11.76/4.58  tff(c_2332, plain, (![A_38, B_47]: (k2_lattices(A_38, k15_lattice3(A_38, k1_xboole_0), '#skF_5'(A_38, B_47))=k15_lattice3(A_38, k1_xboole_0) | ~l2_lattices(A_38) | ~v9_lattices(A_38) | ~v8_lattices(A_38) | ~v6_lattices(A_38) | ~l3_lattices(A_38) | ~v4_lattice3(A_38) | ~v10_lattices(A_38) | v13_lattices(A_38) | ~m1_subset_1(B_47, u1_struct_0(A_38)) | ~l1_lattices(A_38) | v2_struct_0(A_38))), inference(resolution, [status(thm)], [c_52, c_2306])).
% 11.76/4.58  tff(c_446, plain, (![A_144, C_145, B_146]: (k2_lattices(A_144, C_145, B_146)=k2_lattices(A_144, B_146, C_145) | ~m1_subset_1(C_145, u1_struct_0(A_144)) | ~m1_subset_1(B_146, u1_struct_0(A_144)) | ~v6_lattices(A_144) | ~l1_lattices(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.76/4.58  tff(c_983, plain, (![A_233, B_234, B_235]: (k2_lattices(A_233, k15_lattice3(A_233, B_234), B_235)=k2_lattices(A_233, B_235, k15_lattice3(A_233, B_234)) | ~m1_subset_1(B_235, u1_struct_0(A_233)) | ~v6_lattices(A_233) | ~l1_lattices(A_233) | ~l3_lattices(A_233) | v2_struct_0(A_233))), inference(resolution, [status(thm)], [c_68, c_446])).
% 11.76/4.58  tff(c_1009, plain, (![A_60, B_61, B_234]: (k2_lattices(A_60, k15_lattice3(A_60, B_61), k15_lattice3(A_60, B_234))=k2_lattices(A_60, k15_lattice3(A_60, B_234), k15_lattice3(A_60, B_61)) | ~v6_lattices(A_60) | ~l1_lattices(A_60) | ~l3_lattices(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_68, c_983])).
% 11.76/4.58  tff(c_2247, plain, (![A_419, B_420]: (k2_lattices(A_419, k15_lattice3(A_419, B_420), k15_lattice3(A_419, k1_xboole_0))=k15_lattice3(A_419, k1_xboole_0) | ~v6_lattices(A_419) | ~l1_lattices(A_419) | ~l3_lattices(A_419) | v2_struct_0(A_419) | ~l2_lattices(A_419) | ~v9_lattices(A_419) | ~v8_lattices(A_419) | ~v6_lattices(A_419) | ~v4_lattice3(A_419) | ~v10_lattices(A_419) | ~l3_lattices(A_419) | v2_struct_0(A_419))), inference(superposition, [status(thm), theory('equality')], [c_2213, c_1009])).
% 11.76/4.58  tff(c_3743, plain, (![A_530, B_531]: (k2_lattices(A_530, B_531, k15_lattice3(A_530, k1_xboole_0))=k15_lattice3(A_530, k1_xboole_0) | ~v6_lattices(A_530) | ~l1_lattices(A_530) | ~l3_lattices(A_530) | v2_struct_0(A_530) | ~l2_lattices(A_530) | ~v9_lattices(A_530) | ~v8_lattices(A_530) | ~v6_lattices(A_530) | ~v4_lattice3(A_530) | ~v10_lattices(A_530) | ~l3_lattices(A_530) | v2_struct_0(A_530) | ~m1_subset_1(B_531, u1_struct_0(A_530)) | ~l3_lattices(A_530) | ~v4_lattice3(A_530) | ~v10_lattices(A_530) | v2_struct_0(A_530))), inference(superposition, [status(thm), theory('equality')], [c_72, c_2247])).
% 11.76/4.58  tff(c_3796, plain, (![A_533, B_534]: (k2_lattices(A_533, '#skF_5'(A_533, B_534), k15_lattice3(A_533, k1_xboole_0))=k15_lattice3(A_533, k1_xboole_0) | ~l2_lattices(A_533) | ~v9_lattices(A_533) | ~v8_lattices(A_533) | ~v6_lattices(A_533) | ~l3_lattices(A_533) | ~v4_lattice3(A_533) | ~v10_lattices(A_533) | v13_lattices(A_533) | ~m1_subset_1(B_534, u1_struct_0(A_533)) | ~l1_lattices(A_533) | v2_struct_0(A_533))), inference(resolution, [status(thm)], [c_52, c_3743])).
% 11.76/4.58  tff(c_50, plain, (![A_38, B_47]: (k2_lattices(A_38, '#skF_5'(A_38, B_47), B_47)!=B_47 | k2_lattices(A_38, B_47, '#skF_5'(A_38, B_47))!=B_47 | v13_lattices(A_38) | ~m1_subset_1(B_47, u1_struct_0(A_38)) | ~l1_lattices(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_152])).
% 11.76/4.58  tff(c_3882, plain, (![A_539]: (k2_lattices(A_539, k15_lattice3(A_539, k1_xboole_0), '#skF_5'(A_539, k15_lattice3(A_539, k1_xboole_0)))!=k15_lattice3(A_539, k1_xboole_0) | ~l2_lattices(A_539) | ~v9_lattices(A_539) | ~v8_lattices(A_539) | ~v6_lattices(A_539) | ~l3_lattices(A_539) | ~v4_lattice3(A_539) | ~v10_lattices(A_539) | v13_lattices(A_539) | ~m1_subset_1(k15_lattice3(A_539, k1_xboole_0), u1_struct_0(A_539)) | ~l1_lattices(A_539) | v2_struct_0(A_539))), inference(superposition, [status(thm), theory('equality')], [c_3796, c_50])).
% 11.76/4.58  tff(c_3937, plain, (![A_544]: (~l2_lattices(A_544) | ~v9_lattices(A_544) | ~v8_lattices(A_544) | ~v6_lattices(A_544) | ~l3_lattices(A_544) | ~v4_lattice3(A_544) | ~v10_lattices(A_544) | v13_lattices(A_544) | ~m1_subset_1(k15_lattice3(A_544, k1_xboole_0), u1_struct_0(A_544)) | ~l1_lattices(A_544) | v2_struct_0(A_544))), inference(superposition, [status(thm), theory('equality')], [c_2332, c_3882])).
% 11.76/4.58  tff(c_3943, plain, (![A_545]: (~l2_lattices(A_545) | ~v9_lattices(A_545) | ~v8_lattices(A_545) | ~v6_lattices(A_545) | ~v4_lattice3(A_545) | ~v10_lattices(A_545) | v13_lattices(A_545) | ~l1_lattices(A_545) | ~l3_lattices(A_545) | v2_struct_0(A_545))), inference(resolution, [status(thm)], [c_68, c_3937])).
% 11.76/4.58  tff(c_3948, plain, (![A_546]: (~l2_lattices(A_546) | ~v8_lattices(A_546) | ~v6_lattices(A_546) | ~v4_lattice3(A_546) | v13_lattices(A_546) | ~l1_lattices(A_546) | ~v10_lattices(A_546) | v2_struct_0(A_546) | ~l3_lattices(A_546))), inference(resolution, [status(thm)], [c_6, c_3943])).
% 11.76/4.58  tff(c_3953, plain, (![A_547]: (~l2_lattices(A_547) | ~v6_lattices(A_547) | ~v4_lattice3(A_547) | v13_lattices(A_547) | ~l1_lattices(A_547) | ~v10_lattices(A_547) | v2_struct_0(A_547) | ~l3_lattices(A_547))), inference(resolution, [status(thm)], [c_8, c_3948])).
% 11.76/4.58  tff(c_3958, plain, (![A_548]: (~l2_lattices(A_548) | ~v4_lattice3(A_548) | v13_lattices(A_548) | ~l1_lattices(A_548) | ~v10_lattices(A_548) | v2_struct_0(A_548) | ~l3_lattices(A_548))), inference(resolution, [status(thm)], [c_12, c_3953])).
% 11.76/4.58  tff(c_3961, plain, (~l2_lattices('#skF_9') | v13_lattices('#skF_9') | ~l1_lattices('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_84, c_3958])).
% 11.76/4.58  tff(c_3964, plain, (v13_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_86, c_97, c_102, c_3961])).
% 11.76/4.58  tff(c_3966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_103, c_3964])).
% 11.76/4.58  tff(c_3968, plain, (v13_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_91])).
% 11.76/4.58  tff(c_40, plain, (![A_33]: (m1_subset_1(k5_lattices(A_33), u1_struct_0(A_33)) | ~l1_lattices(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.76/4.58  tff(c_54, plain, (![A_38]: (m1_subset_1('#skF_4'(A_38), u1_struct_0(A_38)) | ~v13_lattices(A_38) | ~l1_lattices(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_152])).
% 11.76/4.58  tff(c_4227, plain, (![A_603, C_604]: (k2_lattices(A_603, k5_lattices(A_603), C_604)=k5_lattices(A_603) | ~m1_subset_1(C_604, u1_struct_0(A_603)) | ~m1_subset_1(k5_lattices(A_603), u1_struct_0(A_603)) | ~v13_lattices(A_603) | ~l1_lattices(A_603) | v2_struct_0(A_603))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.76/4.58  tff(c_4255, plain, (![A_605]: (k2_lattices(A_605, k5_lattices(A_605), '#skF_4'(A_605))=k5_lattices(A_605) | ~m1_subset_1(k5_lattices(A_605), u1_struct_0(A_605)) | ~v13_lattices(A_605) | ~l1_lattices(A_605) | v2_struct_0(A_605))), inference(resolution, [status(thm)], [c_54, c_4227])).
% 11.76/4.58  tff(c_4259, plain, (![A_606]: (k2_lattices(A_606, k5_lattices(A_606), '#skF_4'(A_606))=k5_lattices(A_606) | ~v13_lattices(A_606) | ~l1_lattices(A_606) | v2_struct_0(A_606))), inference(resolution, [status(thm)], [c_40, c_4255])).
% 11.76/4.58  tff(c_3984, plain, (![A_567, C_568]: (k2_lattices(A_567, C_568, '#skF_4'(A_567))='#skF_4'(A_567) | ~m1_subset_1(C_568, u1_struct_0(A_567)) | ~v13_lattices(A_567) | ~l1_lattices(A_567) | v2_struct_0(A_567))), inference(cnfTransformation, [status(thm)], [f_152])).
% 11.76/4.58  tff(c_4008, plain, (![A_33]: (k2_lattices(A_33, k5_lattices(A_33), '#skF_4'(A_33))='#skF_4'(A_33) | ~v13_lattices(A_33) | ~l1_lattices(A_33) | v2_struct_0(A_33))), inference(resolution, [status(thm)], [c_40, c_3984])).
% 11.76/4.58  tff(c_4265, plain, (![A_606]: (k5_lattices(A_606)='#skF_4'(A_606) | ~v13_lattices(A_606) | ~l1_lattices(A_606) | v2_struct_0(A_606) | ~v13_lattices(A_606) | ~l1_lattices(A_606) | v2_struct_0(A_606))), inference(superposition, [status(thm), theory('equality')], [c_4259, c_4008])).
% 11.76/4.58  tff(c_4315, plain, (![A_610]: (k5_lattices(A_610)='#skF_4'(A_610) | ~v13_lattices(A_610) | ~l1_lattices(A_610) | v2_struct_0(A_610))), inference(factorization, [status(thm), theory('equality')], [c_4265])).
% 11.76/4.58  tff(c_4318, plain, (k5_lattices('#skF_9')='#skF_4'('#skF_9') | ~v13_lattices('#skF_9') | ~l1_lattices('#skF_9')), inference(resolution, [status(thm)], [c_4315, c_88])).
% 11.76/4.58  tff(c_4321, plain, (k5_lattices('#skF_9')='#skF_4'('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_3968, c_4318])).
% 11.76/4.58  tff(c_3967, plain, (k15_lattice3('#skF_9', k1_xboole_0)!=k5_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_91])).
% 11.76/4.58  tff(c_4322, plain, (k15_lattice3('#skF_9', k1_xboole_0)!='#skF_4'('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4321, c_3967])).
% 11.76/4.58  tff(c_38, plain, (![A_22]: (m1_subset_1('#skF_2'(A_22), u1_struct_0(A_22)) | v9_lattices(A_22) | ~l3_lattices(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.76/4.58  tff(c_4335, plain, (m1_subset_1('#skF_4'('#skF_9'), u1_struct_0('#skF_9')) | ~l1_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_4321, c_40])).
% 11.76/4.58  tff(c_4348, plain, (m1_subset_1('#skF_4'('#skF_9'), u1_struct_0('#skF_9')) | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_4335])).
% 11.76/4.58  tff(c_4349, plain, (m1_subset_1('#skF_4'('#skF_9'), u1_struct_0('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_88, c_4348])).
% 11.76/4.58  tff(c_4402, plain, (![A_611, C_612, B_613]: (k2_lattices(A_611, C_612, B_613)=k2_lattices(A_611, B_613, C_612) | ~m1_subset_1(C_612, u1_struct_0(A_611)) | ~m1_subset_1(B_613, u1_struct_0(A_611)) | ~v6_lattices(A_611) | ~l1_lattices(A_611) | v2_struct_0(A_611))), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.76/4.58  tff(c_4404, plain, (![B_613]: (k2_lattices('#skF_9', B_613, '#skF_4'('#skF_9'))=k2_lattices('#skF_9', '#skF_4'('#skF_9'), B_613) | ~m1_subset_1(B_613, u1_struct_0('#skF_9')) | ~v6_lattices('#skF_9') | ~l1_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_4349, c_4402])).
% 11.76/4.58  tff(c_4425, plain, (![B_613]: (k2_lattices('#skF_9', B_613, '#skF_4'('#skF_9'))=k2_lattices('#skF_9', '#skF_4'('#skF_9'), B_613) | ~m1_subset_1(B_613, u1_struct_0('#skF_9')) | ~v6_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_4404])).
% 11.76/4.58  tff(c_4426, plain, (![B_613]: (k2_lattices('#skF_9', B_613, '#skF_4'('#skF_9'))=k2_lattices('#skF_9', '#skF_4'('#skF_9'), B_613) | ~m1_subset_1(B_613, u1_struct_0('#skF_9')) | ~v6_lattices('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_88, c_4425])).
% 11.76/4.58  tff(c_4446, plain, (~v6_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_4426])).
% 11.76/4.58  tff(c_4449, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_12, c_4446])).
% 11.76/4.58  tff(c_4452, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_86, c_4449])).
% 11.76/4.58  tff(c_4454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_4452])).
% 11.76/4.58  tff(c_4491, plain, (![B_618]: (k2_lattices('#skF_9', B_618, '#skF_4'('#skF_9'))=k2_lattices('#skF_9', '#skF_4'('#skF_9'), B_618) | ~m1_subset_1(B_618, u1_struct_0('#skF_9')))), inference(splitRight, [status(thm)], [c_4426])).
% 11.76/4.58  tff(c_4506, plain, (k2_lattices('#skF_9', '#skF_2'('#skF_9'), '#skF_4'('#skF_9'))=k2_lattices('#skF_9', '#skF_4'('#skF_9'), '#skF_2'('#skF_9')) | v9_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_38, c_4491])).
% 11.76/4.58  tff(c_4543, plain, (k2_lattices('#skF_9', '#skF_2'('#skF_9'), '#skF_4'('#skF_9'))=k2_lattices('#skF_9', '#skF_4'('#skF_9'), '#skF_2'('#skF_9')) | v9_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_4506])).
% 11.76/4.58  tff(c_4544, plain, (k2_lattices('#skF_9', '#skF_2'('#skF_9'), '#skF_4'('#skF_9'))=k2_lattices('#skF_9', '#skF_4'('#skF_9'), '#skF_2'('#skF_9')) | v9_lattices('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_88, c_4543])).
% 11.76/4.58  tff(c_4569, plain, (v9_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_4544])).
% 11.76/4.58  tff(c_4526, plain, (![B_61]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_61), '#skF_4'('#skF_9'))=k2_lattices('#skF_9', '#skF_4'('#skF_9'), k15_lattice3('#skF_9', B_61)) | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_68, c_4491])).
% 11.76/4.58  tff(c_4563, plain, (![B_61]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_61), '#skF_4'('#skF_9'))=k2_lattices('#skF_9', '#skF_4'('#skF_9'), k15_lattice3('#skF_9', B_61)) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_4526])).
% 11.76/4.58  tff(c_4571, plain, (![B_619]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_619), '#skF_4'('#skF_9'))=k2_lattices('#skF_9', '#skF_4'('#skF_9'), k15_lattice3('#skF_9', B_619)))), inference(negUnitSimplification, [status(thm)], [c_88, c_4563])).
% 11.76/4.58  tff(c_4007, plain, (![A_60, B_61]: (k2_lattices(A_60, k15_lattice3(A_60, B_61), '#skF_4'(A_60))='#skF_4'(A_60) | ~v13_lattices(A_60) | ~l1_lattices(A_60) | ~l3_lattices(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_68, c_3984])).
% 11.76/4.58  tff(c_4577, plain, (![B_619]: (k2_lattices('#skF_9', '#skF_4'('#skF_9'), k15_lattice3('#skF_9', B_619))='#skF_4'('#skF_9') | ~v13_lattices('#skF_9') | ~l1_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_4571, c_4007])).
% 11.76/4.58  tff(c_4591, plain, (![B_619]: (k2_lattices('#skF_9', '#skF_4'('#skF_9'), k15_lattice3('#skF_9', B_619))='#skF_4'('#skF_9') | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_97, c_3968, c_4577])).
% 11.76/4.58  tff(c_4592, plain, (![B_619]: (k2_lattices('#skF_9', '#skF_4'('#skF_9'), k15_lattice3('#skF_9', B_619))='#skF_4'('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_88, c_4591])).
% 11.76/4.58  tff(c_4564, plain, (![B_61]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_61), '#skF_4'('#skF_9'))=k2_lattices('#skF_9', '#skF_4'('#skF_9'), k15_lattice3('#skF_9', B_61)))), inference(negUnitSimplification, [status(thm)], [c_88, c_4563])).
% 11.76/4.58  tff(c_4600, plain, (![B_61]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_61), '#skF_4'('#skF_9'))='#skF_4'('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_4592, c_4564])).
% 11.76/4.58  tff(c_4456, plain, (v6_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_4426])).
% 11.76/4.58  tff(c_5067, plain, (![A_647, B_648, C_649]: (r3_lattices(A_647, B_648, C_649) | ~r1_lattices(A_647, B_648, C_649) | ~m1_subset_1(C_649, u1_struct_0(A_647)) | ~m1_subset_1(B_648, u1_struct_0(A_647)) | ~l3_lattices(A_647) | ~v9_lattices(A_647) | ~v8_lattices(A_647) | ~v6_lattices(A_647) | v2_struct_0(A_647))), inference(cnfTransformation, [status(thm)], [f_135])).
% 11.76/4.58  tff(c_5069, plain, (![B_648]: (r3_lattices('#skF_9', B_648, '#skF_4'('#skF_9')) | ~r1_lattices('#skF_9', B_648, '#skF_4'('#skF_9')) | ~m1_subset_1(B_648, u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_4349, c_5067])).
% 11.76/4.58  tff(c_5090, plain, (![B_648]: (r3_lattices('#skF_9', B_648, '#skF_4'('#skF_9')) | ~r1_lattices('#skF_9', B_648, '#skF_4'('#skF_9')) | ~m1_subset_1(B_648, u1_struct_0('#skF_9')) | ~v8_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_4456, c_4569, c_82, c_5069])).
% 11.76/4.58  tff(c_5091, plain, (![B_648]: (r3_lattices('#skF_9', B_648, '#skF_4'('#skF_9')) | ~r1_lattices('#skF_9', B_648, '#skF_4'('#skF_9')) | ~m1_subset_1(B_648, u1_struct_0('#skF_9')) | ~v8_lattices('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_88, c_5090])).
% 11.76/4.58  tff(c_5101, plain, (~v8_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_5091])).
% 11.76/4.58  tff(c_5104, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_8, c_5101])).
% 11.76/4.58  tff(c_5107, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_86, c_5104])).
% 11.76/4.58  tff(c_5109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_5107])).
% 11.76/4.58  tff(c_5111, plain, (v8_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_5091])).
% 11.76/4.58  tff(c_4216, plain, (![A_600, B_601, C_602]: (r2_hidden('#skF_8'(A_600, B_601, C_602), B_601) | r3_lattices(A_600, k15_lattice3(A_600, B_601), k15_lattice3(A_600, C_602)) | ~l3_lattices(A_600) | ~v4_lattice3(A_600) | ~v10_lattices(A_600) | v2_struct_0(A_600))), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.76/4.58  tff(c_5319, plain, (![B_672, A_673, C_674]: (~r1_tarski(B_672, '#skF_8'(A_673, B_672, C_674)) | r3_lattices(A_673, k15_lattice3(A_673, B_672), k15_lattice3(A_673, C_674)) | ~l3_lattices(A_673) | ~v4_lattice3(A_673) | ~v10_lattices(A_673) | v2_struct_0(A_673))), inference(resolution, [status(thm)], [c_4216, c_4])).
% 11.76/4.58  tff(c_5324, plain, (![A_675, C_676]: (r3_lattices(A_675, k15_lattice3(A_675, k1_xboole_0), k15_lattice3(A_675, C_676)) | ~l3_lattices(A_675) | ~v4_lattice3(A_675) | ~v10_lattices(A_675) | v2_struct_0(A_675))), inference(resolution, [status(thm)], [c_2, c_5319])).
% 11.76/4.58  tff(c_5993, plain, (![A_754, B_755]: (r3_lattices(A_754, k15_lattice3(A_754, k1_xboole_0), B_755) | ~l3_lattices(A_754) | ~v4_lattice3(A_754) | ~v10_lattices(A_754) | v2_struct_0(A_754) | ~m1_subset_1(B_755, u1_struct_0(A_754)) | ~l3_lattices(A_754) | ~v4_lattice3(A_754) | ~v10_lattices(A_754) | v2_struct_0(A_754))), inference(superposition, [status(thm), theory('equality')], [c_72, c_5324])).
% 11.76/4.58  tff(c_6396, plain, (![A_794, B_795]: (r1_lattices(A_794, k15_lattice3(A_794, k1_xboole_0), B_795) | ~m1_subset_1(k15_lattice3(A_794, k1_xboole_0), u1_struct_0(A_794)) | ~v9_lattices(A_794) | ~v8_lattices(A_794) | ~v6_lattices(A_794) | ~m1_subset_1(B_795, u1_struct_0(A_794)) | ~l3_lattices(A_794) | ~v4_lattice3(A_794) | ~v10_lattices(A_794) | v2_struct_0(A_794))), inference(resolution, [status(thm)], [c_5993, c_48])).
% 11.76/4.58  tff(c_6412, plain, (![A_799, B_800]: (r1_lattices(A_799, k15_lattice3(A_799, k1_xboole_0), B_800) | ~v9_lattices(A_799) | ~v8_lattices(A_799) | ~v6_lattices(A_799) | ~m1_subset_1(B_800, u1_struct_0(A_799)) | ~v4_lattice3(A_799) | ~v10_lattices(A_799) | ~l3_lattices(A_799) | v2_struct_0(A_799))), inference(resolution, [status(thm)], [c_68, c_6396])).
% 11.76/4.58  tff(c_6577, plain, (![A_819, B_820]: (k1_lattices(A_819, k15_lattice3(A_819, k1_xboole_0), B_820)=B_820 | ~m1_subset_1(k15_lattice3(A_819, k1_xboole_0), u1_struct_0(A_819)) | ~l2_lattices(A_819) | ~v9_lattices(A_819) | ~v8_lattices(A_819) | ~v6_lattices(A_819) | ~m1_subset_1(B_820, u1_struct_0(A_819)) | ~v4_lattice3(A_819) | ~v10_lattices(A_819) | ~l3_lattices(A_819) | v2_struct_0(A_819))), inference(resolution, [status(thm)], [c_6412, c_30])).
% 11.76/4.58  tff(c_6582, plain, (![A_821, B_822]: (k1_lattices(A_821, k15_lattice3(A_821, k1_xboole_0), B_822)=B_822 | ~l2_lattices(A_821) | ~v9_lattices(A_821) | ~v8_lattices(A_821) | ~v6_lattices(A_821) | ~m1_subset_1(B_822, u1_struct_0(A_821)) | ~v4_lattice3(A_821) | ~v10_lattices(A_821) | ~l3_lattices(A_821) | v2_struct_0(A_821))), inference(resolution, [status(thm)], [c_68, c_6577])).
% 11.76/4.58  tff(c_6584, plain, (k1_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), '#skF_4'('#skF_9'))='#skF_4'('#skF_9') | ~l2_lattices('#skF_9') | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_4349, c_6582])).
% 11.76/4.58  tff(c_6605, plain, (k1_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), '#skF_4'('#skF_9'))='#skF_4'('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_86, c_84, c_4456, c_5111, c_4569, c_102, c_6584])).
% 11.76/4.58  tff(c_6606, plain, (k1_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), '#skF_4'('#skF_9'))='#skF_4'('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_88, c_6605])).
% 11.76/4.58  tff(c_4457, plain, (![A_615, B_616, C_617]: (k2_lattices(A_615, B_616, k1_lattices(A_615, B_616, C_617))=B_616 | ~m1_subset_1(C_617, u1_struct_0(A_615)) | ~m1_subset_1(B_616, u1_struct_0(A_615)) | ~v9_lattices(A_615) | ~l3_lattices(A_615) | v2_struct_0(A_615))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.76/4.58  tff(c_4487, plain, (![A_38, B_616]: (k2_lattices(A_38, B_616, k1_lattices(A_38, B_616, '#skF_4'(A_38)))=B_616 | ~m1_subset_1(B_616, u1_struct_0(A_38)) | ~v9_lattices(A_38) | ~l3_lattices(A_38) | ~v13_lattices(A_38) | ~l1_lattices(A_38) | v2_struct_0(A_38))), inference(resolution, [status(thm)], [c_54, c_4457])).
% 11.76/4.58  tff(c_6619, plain, (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), '#skF_4'('#skF_9'))=k15_lattice3('#skF_9', k1_xboole_0) | ~m1_subset_1(k15_lattice3('#skF_9', k1_xboole_0), u1_struct_0('#skF_9')) | ~v9_lattices('#skF_9') | ~l3_lattices('#skF_9') | ~v13_lattices('#skF_9') | ~l1_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_6606, c_4487])).
% 11.76/4.58  tff(c_6626, plain, (k15_lattice3('#skF_9', k1_xboole_0)='#skF_4'('#skF_9') | ~m1_subset_1(k15_lattice3('#skF_9', k1_xboole_0), u1_struct_0('#skF_9')) | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_3968, c_82, c_4569, c_4600, c_6619])).
% 11.76/4.58  tff(c_6627, plain, (~m1_subset_1(k15_lattice3('#skF_9', k1_xboole_0), u1_struct_0('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_88, c_4322, c_6626])).
% 11.76/4.58  tff(c_6633, plain, (~l3_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_68, c_6627])).
% 11.76/4.58  tff(c_6636, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_6633])).
% 11.76/4.58  tff(c_6638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_6636])).
% 11.76/4.58  tff(c_6640, plain, (~v9_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_4544])).
% 11.76/4.58  tff(c_6643, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_6, c_6640])).
% 11.76/4.58  tff(c_6646, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_86, c_6643])).
% 11.76/4.58  tff(c_6648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_6646])).
% 11.76/4.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.76/4.58  
% 11.76/4.58  Inference rules
% 11.76/4.58  ----------------------
% 11.76/4.58  #Ref     : 0
% 11.76/4.58  #Sup     : 1624
% 11.76/4.58  #Fact    : 4
% 11.76/4.58  #Define  : 0
% 11.76/4.58  #Split   : 4
% 11.76/4.58  #Chain   : 0
% 11.76/4.58  #Close   : 0
% 11.76/4.58  
% 11.76/4.58  Ordering : KBO
% 11.76/4.58  
% 11.76/4.58  Simplification rules
% 11.76/4.58  ----------------------
% 11.76/4.58  #Subsume      : 402
% 11.76/4.58  #Demod        : 560
% 11.76/4.58  #Tautology    : 706
% 11.76/4.58  #SimpNegUnit  : 146
% 11.76/4.58  #BackRed      : 2
% 11.76/4.58  
% 11.76/4.58  #Partial instantiations: 0
% 11.76/4.58  #Strategies tried      : 1
% 11.76/4.58  
% 11.76/4.58  Timing (in seconds)
% 11.76/4.58  ----------------------
% 11.76/4.58  Preprocessing        : 0.38
% 12.07/4.58  Parsing              : 0.19
% 12.07/4.58  CNF conversion       : 0.03
% 12.07/4.58  Main loop            : 3.40
% 12.07/4.58  Inferencing          : 1.02
% 12.07/4.58  Reduction            : 0.44
% 12.07/4.58  Demodulation         : 0.29
% 12.07/4.58  BG Simplification    : 0.09
% 12.07/4.58  Subsumption          : 1.73
% 12.07/4.58  Abstraction          : 0.09
% 12.07/4.58  MUC search           : 0.00
% 12.07/4.58  Cooper               : 0.00
% 12.07/4.58  Total                : 3.84
% 12.07/4.58  Index Insertion      : 0.00
% 12.07/4.58  Index Deletion       : 0.00
% 12.07/4.58  Index Matching       : 0.00
% 12.07/4.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
